package main

import (
	"errors"
	"fmt"
	"math"
	"math/rand"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"slices"
	"sort"
	"strconv"
	"strings"
	"time"
	"unicode/utf8"
	"unsafe"

	"github.com/steelseries/golisp"
	"github.com/xyproto/vt"
)

type elVector struct {
	items []*golisp.Data
}

type runtimeState struct {
	gameName         string
	mainFilePath     string
	loadPaths        []string
	loadingFeatures  map[string]bool
	env              *golisp.SymbolTableFrame
	grid             map[[2]int]*golisp.Data
	gridWidth        int
	gridHeight       int
	gridDefault      *golisp.Data
	gridDisplay      *golisp.Data
	displayMode      *golisp.Data
	providedFeatures map[string]bool
	symbolProps      map[string]map[string]*golisp.Data
	messages         []string
	timers           map[string]*elTimer
	buffers          map[string]*elBuffer
	windows          map[int]*elWindow
	selectedWindowID int
	nextWindowID     int
	menus            map[string]*golisp.Data
	scores           map[string][]int64
	warned           map[string]bool
	funcByName       map[string]*golisp.Data
	requireShim      bool
	matchData        []int
	matchString      string
	matchInString    bool
	matchBuffer      *elBuffer
	timerSeq         int
	errorParents     map[string]string
}

type elTimer struct {
	period   float64
	callback *golisp.Data
	active   bool
	nextFire time.Time
}

type elBuffer struct {
	name     string
	object   *golisp.Data
	localMap *golisp.Data
	hooks    map[string][]*golisp.Data
	text     []rune
	point    int
}

type elWindow struct {
	id     int
	object *golisp.Data
	buffer *elBuffer
}

type elWindowConfiguration struct {
	selectedWindowID int
	bufferByWindowID map[int]string
}

type throwSignal struct {
	tag   string
	value *golisp.Data
}

func (t throwSignal) Error() string {
	return "throw: " + t.tag
}

type elSignal struct {
	condition string
	data      *golisp.Data
}

func (s elSignal) Error() string {
	if s.condition == "" {
		return "signal"
	}
	return "signal: " + s.condition
}

var rtGlobal *runtimeState

var missingFnPatterns = []*regexp.Regexp{
	regexp.MustCompile(`function or macro expected for ([^.\s)]+)\.`),
	regexp.MustCompile(`void: ([^\s)]+)`),
}

type elKeymap struct {
	bindings map[string]*golisp.Data
	fullMap  *golisp.Data
}

func main() {
	if len(os.Args) != 2 {
		fmt.Fprintf(os.Stderr, "usage: %s <game.el>\n", filepath.Base(os.Args[0]))
		os.Exit(2)
	}
	filePath := os.Args[1]
	if filepath.Ext(filePath) != ".el" {
		fmt.Fprintf(os.Stderr, "expected a .el file, got %s\n", filePath)
		os.Exit(2)
	}
	if _, err := os.Stat(filePath); err != nil {
		alt := filepath.Join("/home/alexander/clones/emacs-master/lisp/play", filepath.Base(filePath))
		if _, err2 := os.Stat(alt); err2 == nil {
			filePath = alt
		}
	}
	entry := strings.TrimSuffix(filepath.Base(filePath), filepath.Ext(filePath))
	entrySymbol := entry
	if len(entrySymbol) > 0 && isDigit(entrySymbol[0]) {
		entrySymbol = normalizeLeadingDigitSymbol(entrySymbol)
	}

	rt := &runtimeState{
		gameName:     entry,
		mainFilePath: filePath,
		grid:         make(map[[2]int]*golisp.Data),
		gridDefault:  golisp.EmptyCons(),
		displayMode:  golisp.Intern("glyph"),
		providedFeatures: map[string]bool{
			"cl-lib": true, "gamegrid": true, "seq": true, "subr-x": true,
			"outline": true, "ps-print": true, "ps-print-loaddefs": true,
			"icons": true, "wid-edit": true, "easymenu": true,
		},
		loadingFeatures: make(map[string]bool),
		symbolProps:     make(map[string]map[string]*golisp.Data),
		timers:          make(map[string]*elTimer),
		buffers:         make(map[string]*elBuffer),
		windows:         make(map[int]*elWindow),
		nextWindowID:    1,
		menus:           make(map[string]*golisp.Data),
		scores:          make(map[string][]int64),
		warned:          make(map[string]bool),
		funcByName:      make(map[string]*golisp.Data),
		requireShim:     os.Getenv("ELRUN_REQUIRE_SHIM") == "1",
		errorParents: map[string]string{
			"error": "",
			"quit":  "error",
		},
	}
	rtGlobal = rt
	rt.ensureInitialWindowAndBuffer()
	installElispCompat(rt)

	env := golisp.NewSymbolTableFrameBelow(golisp.Global, "etetris")
	rt.env = env
	rt.loadPaths = []string{
		filepath.Dir(filePath),
		"/home/alexander/clones/emacs-master/lisp/play",
		"/home/alexander/clones/emacs-master/lisp",
	}

	if err := rt.loadElispFile(filePath); err != nil {
		fmt.Fprintf(os.Stderr, "load %s: %v\n", filePath, err)
		os.Exit(1)
	}

	fmt.Printf("loaded %s into elisp-compat environment\n", filePath)

	entrySymbol = rt.selectEntrySymbol(filePath, entrySymbol, env)
	rt.seedInitialTextBufferIfNeeded(entrySymbol)
	invoked := false
	if entrySymbol == "life" {
		if err := rt.startLifeSession(env); err != nil {
			fmt.Fprintf(os.Stderr, "invoke %s: %v\n", entrySymbol, err)
			os.Exit(1)
		}
		invoked = true
	}
	if !invoked && !rt.hasStandaloneAction() {
		if err := rt.invokeEntry(entrySymbol, env); err != nil {
			fmt.Fprintf(os.Stderr, "invoke %s: %v\n", entrySymbol, err)
			os.Exit(1)
		}
	}
	if rt.gridWidth == 0 && len(rt.timers) == 0 && !rt.shouldRunTextLoop() {
		if rt.setupStandaloneAction(entrySymbol, env) {
			// continue into interactive loop below
		} else {
			fmt.Fprintf(os.Stderr, "play: command finished without interactive loop (%s)\n", entrySymbol)
			return
		}
	}

	if err := runGameLoop(rt, env); err != nil {
		fmt.Fprintf(os.Stderr, "play: %v\n", err)
		os.Exit(1)
	}
}

func shouldRetryInvokeWithNil(msg string) bool {
	return strings.Contains(msg, "parameters") && strings.Contains(msg, "received 0")
}

func makeNilArgs(n int) string {
	if n <= 0 {
		return ""
	}
	var b strings.Builder
	for i := range n {
		if i > 0 {
			b.WriteByte(' ')
		}
		b.WriteString("nil")
	}
	return b.String()
}

func makeZeroArgs(n int) string {
	if n <= 0 {
		return ""
	}
	var b strings.Builder
	for i := range n {
		if i > 0 {
			b.WriteByte(' ')
		}
		b.WriteString("0")
	}
	return b.String()
}

func parseExpectedArgCount(msg string) (int, bool) {
	re := regexp.MustCompile(`expected(?: at least)? ([0-9]+) parameters`)
	m := re.FindStringSubmatch(msg)
	if len(m) != 2 {
		return 0, false
	}
	n, err := strconv.Atoi(m[1])
	if err != nil {
		return 0, false
	}
	return n, true
}

func (rt *runtimeState) invokeEntry(entrySymbol string, env *golisp.SymbolTableFrame) error {
	fn := env.ValueOf(golisp.Intern(entrySymbol))
	if !golisp.FunctionOrPrimitiveP(fn) {
		rt.warnOnce("missing-entry-"+entrySymbol, "entry function is not defined: %s", entrySymbol)
		return nil
	}

	type attempt struct {
		n    int
		fill string
	}
	attempts := []attempt{{n: 0, fill: ""}}
	seen := map[string]bool{"0:": true}
	var lastErr error
	for tries := 0; tries < 24 && len(attempts) > 0; tries++ {
		a := attempts[0]
		attempts = attempts[1:]
		form := "(" + entrySymbol
		if a.n > 0 {
			if a.fill == "0" {
				form += " " + makeZeroArgs(a.n)
			} else {
				form += " " + makeNilArgs(a.n)
			}
		}
		form += ")"
		_, err := golisp.ParseAndEvalInEnvironment(form, env)
		if err == nil {
			return nil
		}
		lastErr = err
		msg := err.Error()
		if name, ok := missingFunctionFromError(msg); ok {
			return fmt.Errorf("needed elisp function is not implemented: %s", name)
		}
		if shouldRetryInvokeWithNil(msg) {
			if n, ok := parseExpectedArgCount(msg); ok && n > 0 && n <= 8 {
				k := strconv.Itoa(n) + ":nil"
				if !seen[k] {
					seen[k] = true
					attempts = append(attempts, attempt{n: n, fill: "nil"})
				}
				continue
			}
		}
		if (strings.Contains(msg, "Number expected, received ()") || strings.Contains(msg, "expected a number, received ()") || strings.Contains(msg, "requires a integer as it's first argument")) && a.n > 0 && a.fill == "nil" {
			k := strconv.Itoa(a.n) + ":0"
			if !seen[k] {
				seen[k] = true
				attempts = append(attempts, attempt{n: a.n, fill: "0"})
				continue
			}
		}
		break
	}
	if lastErr == nil {
		return nil
	}
	return lastErr
}

func (rt *runtimeState) shouldRunTextLoop() bool {
	if rt.gameName == "dunnet" {
		return true
	}
	if rt.gameName == "spook" {
		return true
	}
	buf := rt.currentBuffer()
	if buf == nil {
		return false
	}
	return buf.localMap != nil && isKeymap(buf.localMap)
}

func (rt *runtimeState) selectEntrySymbol(path, fallback string, env *golisp.SymbolTableFrame) string {
	candidates := []string{fallback}
	known := map[string][]string{
		"animate":    {"animate-birthday-present"},
		"dissociate": {"dissociated-press"},
		"morse":      {"morse-region", "morse-region-read"},
		"studly":     {"studlify-region"},
	}
	base := strings.TrimSuffix(filepath.Base(path), filepath.Ext(path))
	if ks, ok := known[base]; ok {
		candidates = append(candidates, ks...)
	}
	if source, err := os.ReadFile(path); err == nil {
		// Prefer explicit autoload entrypoints, avoid picking random helper functions.
		re := regexp.MustCompile(`(?ms)^\s*;;;###autoload\s*\n\s*\(defun\s+([a-zA-Z0-9:+*/<>=!?$%._-]+)`)
		for _, m := range re.FindAllStringSubmatch(string(source), -1) {
			if len(m) == 2 {
				candidates = append(candidates, m[1])
			}
		}
	}
	seen := map[string]bool{}
	for _, c := range candidates {
		if c == "" || seen[c] {
			continue
		}
		seen[c] = true
		if fn := env.ValueOf(golisp.Intern(c)); golisp.FunctionOrPrimitiveP(fn) {
			return c
		}
	}
	return fallback
}

func (rt *runtimeState) seedInitialTextBufferIfNeeded(entrySymbol string) {
	needsSeed := map[string]bool{
		"dissociated-press": true,
	}
	if !needsSeed[entrySymbol] {
		return
	}
	buf := rt.currentBuffer()
	if buf == nil || len(buf.text) > 0 {
		return
	}
	source, err := os.ReadFile(rt.mainFilePath)
	if err != nil || len(source) == 0 {
		return
	}
	buf.text = []rune(string(source))
	buf.point = 0
}

func (rt *runtimeState) ensureStandaloneTextLoopBuffer() *elBuffer {
	buf := rt.currentBuffer()
	if buf == nil {
		buf = rt.ensureBuffer("*scratch*")
		rt.selectedWindow().buffer = buf
	}
	if buf.localMap == nil || !isKeymap(buf.localMap) {
		buf.localMap = keymapObject(newKeymap())
	}
	return buf
}

func (rt *runtimeState) evalForm(form string, env *golisp.SymbolTableFrame) error {
	_, err := golisp.ParseAndEvalInEnvironment(form, env)
	return err
}

func (rt *runtimeState) hasStandaloneAction() bool {
	switch rt.gameName {
	case "cookie1", "gamegrid", "gametree", "handwrite", "hanoi", "morse", "studly":
		return true
	default:
		return false
	}
}

func (rt *runtimeState) setupStandaloneAction(entrySymbol string, env *golisp.SymbolTableFrame) bool {
	switch rt.gameName {
	case "cookie1":
		buf := rt.ensureStandaloneTextLoopBuffer()
		buf.text = append([]rune{}, []rune("cookie1 loaded.\nPress Ctrl-C or Esc to quit.\n\n")...)
		buf.point = len(buf.text)
		form := fmt.Sprintf("(cookie %q \"Loading phrase...\" \"Done.\")", "/home/alexander/clones/emacs-master/etc/spook.lines")
		if err := rt.evalForm(form, env); err != nil {
			_, _ = insertImpl(golisp.ArrayToList([]*golisp.Data{golisp.StringWithValue("Could not load cookie phrase file.\n")}), nil)
		}
		return true
	case "gamegrid":
		buf := rt.ensureStandaloneTextLoopBuffer()
		buf.text = []rune("gamegrid.el is a support library.\nRun tetris.el, snake.el, or pong.el to see it in use.\n\nPress Ctrl-C or Esc to quit.\n")
		buf.point = len(buf.text)
		return true
	case "gametree":
		buf := rt.ensureStandaloneTextLoopBuffer()
		buf.text = []rune("gametree.el is a support library.\nRun gomoku.el to exercise it.\n\nPress Ctrl-C or Esc to quit.\n")
		buf.point = len(buf.text)
		return true
	case "handwrite":
		_ = rt.evalForm("(handwrite)", env)
		buf := rt.ensureStandaloneTextLoopBuffer()
		if len(buf.text) == 0 {
			buf.text = []rune("handwrite initialized.\nPress Ctrl-C or Esc to quit.\n")
			buf.point = len(buf.text)
		}
		return true
	case "hanoi":
		if err := rt.evalForm("(hanoi-unix)", env); err == nil {
			return true
		}
		if err := rt.evalForm("(hanoi 5)", env); err == nil {
			return true
		}
		buf := rt.ensureStandaloneTextLoopBuffer()
		buf.text = []rune("hanoi failed to start demo mode.\nPress Ctrl-C or Esc to quit.\n")
		buf.point = len(buf.text)
		return true
	case "morse":
		buf := rt.ensureStandaloneTextLoopBuffer()
		buf.text = []rune("sos test message")
		buf.point = 0
		_ = rt.evalForm("(morse-region (point-min) (point-max))", env)
		buf.point = len(buf.text)
		_, _ = insertImpl(golisp.ArrayToList([]*golisp.Data{golisp.StringWithValue("\n\nPress Ctrl-C or Esc to quit.\n")}), nil)
		return true
	case "studly":
		buf := rt.ensureStandaloneTextLoopBuffer()
		buf.text = []rune("studlify this sample text")
		buf.point = 0
		_ = rt.evalForm("(studlify-buffer)", env)
		buf.point = len(buf.text)
		_, _ = insertImpl(golisp.ArrayToList([]*golisp.Data{golisp.StringWithValue("\n\nPress Ctrl-C or Esc to quit.\n")}), nil)
		return true
	default:
		_ = entrySymbol
		return false
	}
}

func integerpImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	return golisp.BooleanWithValue(golisp.IntegerP(golisp.Car(args))), nil
}

func (rt *runtimeState) startLifeSession(env *golisp.SymbolTableFrame) error {
	// `life' itself is an infinite elisp loop. Run setup once and tick via timers
	// so updates happen inside the runtime loop where rendering/input lives.
	if err := rt.call("life-setup", env); err != nil {
		return err
	}
	step := 0.5
	if v := env.ValueOf(golisp.Intern("life-step-time")); golisp.NumberP(v) {
		if golisp.IntegerP(v) {
			step = float64(golisp.IntegerValue(v))
		} else {
			step = float64(golisp.FloatValue(v))
		}
	}
	if step <= 0 {
		step = 0.1
	}
	rt.timers["life"] = &elTimer{
		period:   step,
		callback: golisp.Intern("life--tick"),
		active:   true,
		nextFire: time.Now().Add(time.Duration(step * float64(time.Second))),
	}
	return nil
}

func installElispCompat(rt *runtimeState) {
	golisp.Global.BindToProtected(golisp.Intern("t"), golisp.BooleanWithValue(true))
	golisp.Global.BindToProtected(golisp.Intern("gamegrid-display-mode"), rt.displayMode)
	golisp.Global.BindToProtected(golisp.Intern("most-positive-fixnum"), golisp.IntegerWithValue(1<<61-1))
	golisp.Global.BindToProtected(golisp.Intern("most-negative-fixnum"), golisp.IntegerWithValue(-(1 << 61)))
	golisp.Global.BindToProtected(golisp.Intern("data-directory"), golisp.StringWithValue("/home/alexander/clones/emacs-master/etc/"))
	golisp.Global.BindToProtected(golisp.Intern("exec-directory"), golisp.StringWithValue("/home/alexander/clones/emacs-master/lib-src/"))
	_, _ = golisp.Global.BindTo(golisp.Intern("fill-column"), golisp.IntegerWithValue(70))

	golisp.MakeSpecialForm("setq", "*", setqImpl)
	golisp.MakeSpecialForm("setq-local", "*", setqImpl)
	golisp.MakeSpecialForm("defun", ">=2", defunImpl)
	golisp.MakeSpecialForm("defvar", "*", defvarImpl)
	golisp.MakeSpecialForm("defvar-local", "*", defvarImpl)
	golisp.MakeSpecialForm("defconst", "*", defvarImpl)
	golisp.MakeSpecialForm("defcustom", "*", defvarImpl)
	golisp.MakeSpecialForm("defmacro", ">=3", defmacroImpl)
	golisp.MakeSpecialForm("defsubst", ">=2", defsubstImpl)
	golisp.MakeSpecialForm("defface", ">=2", deffaceImpl)
	golisp.MakeSpecialForm("defalias", "2|3", defaliasImpl)
	golisp.MakeSpecialForm("defgroup", ">=1", defgroupImpl)
	golisp.MakeSpecialForm("defvar-keymap", "*", defvarKeymapImpl)
	golisp.MakeSpecialForm("define-derived-mode", "*", defineDerivedModeImpl)
	golisp.MakeSpecialForm("vector-literal", "*", vectorLiteralImpl)
	golisp.MakeSpecialForm("while", ">=1", whileImpl)
	golisp.MakeSpecialForm("let", ">=1", letImpl)
	golisp.MakeSpecialForm("let*", ">=1", letStarImpl)
	golisp.MakeSpecialForm("dotimes", ">=2", dotimesImpl)
	golisp.MakeSpecialForm("cl-loop", ">=8", clLoopImpl)
	golisp.MakeSpecialForm("cl-rotatef", "2", clRotatefImpl)
	golisp.MakeSpecialForm("pop", "1", popImpl)
	golisp.MakeSpecialForm("push", "2", pushImpl)
	golisp.MakeSpecialForm("incf", "1|2", incfImpl)
	golisp.MakeSpecialForm("decf", "1|2", decfImpl)
	golisp.MakeSpecialForm("setcdr", "2", setcdrImpl)
	golisp.MakeSpecialForm("eval-when-compile", "*", beginAliasImpl)
	golisp.MakeSpecialForm("eval-and-compile", "*", beginAliasImpl)
	golisp.MakeSpecialForm("progn", "*", beginAliasImpl)
	golisp.MakeSpecialForm("prog1", ">=1", prog1Impl)
	golisp.MakeSpecialForm("prog2", ">=2", prog2Impl)
	golisp.MakeSpecialForm("when", ">=1", whenImpl)
	golisp.MakeSpecialForm("unless", ">=1", unlessImpl)
	golisp.MakeSpecialForm("if", ">=2", ifImpl)
	golisp.MakeSpecialForm("pcase", ">=2", pcaseImpl)
	golisp.MakeSpecialForm("dolist", ">=2", dolistImpl)
	golisp.MakeSpecialForm("catch", ">=1", catchImpl)
	golisp.MakeSpecialForm("ignore-errors", "*", ignoreErrorsImpl)
	golisp.MakeSpecialForm("condition-case", ">=3", conditionCaseImpl)
	golisp.MakeSpecialForm("unwind-protect", ">=1", unwindProtectImpl)
	golisp.MakeSpecialForm("save-current-buffer", "*", saveCurrentBufferImpl)
	golisp.MakeSpecialForm("save-excursion", "*", beginAliasImpl)
	golisp.MakeSpecialForm("with-current-buffer", ">=2", withCurrentBufferImpl)
	golisp.MakeSpecialForm("with-temp-buffer", ">=1", withTempBufferImpl)

	golisp.MakePrimitiveFunction("vector", "*", vectorImpl)
	golisp.MakePrimitiveFunction("car", "1", carImpl)
	golisp.MakePrimitiveFunction("cdr", "1", cdrImpl)
	golisp.MakePrimitiveFunction("make-vector", "2", makeVectorImpl)
	golisp.MakePrimitiveFunction("aref", "2", arefImpl)
	golisp.MakePrimitiveFunction("aset", "3", asetImpl)
	golisp.MakePrimitiveFunction("elt", "2", arefImpl)
	golisp.MakePrimitiveFunction("length", "1", lengthImpl)
	golisp.MakePrimitiveFunction("nth", "2", nthImpl)
	golisp.MakePrimitiveFunction("last", "1", lastImpl)
	golisp.MakePrimitiveFunction("nthcdr", "2", nthcdrImpl)
	golisp.MakePrimitiveFunction("nreverse", "1", nreverseImpl)
	golisp.MakePrimitiveFunction("random", "1", randomImpl)
	golisp.MakePrimitiveFunction("concat", "*", concatImpl)
	golisp.MakePrimitiveFunction("substring", "2|3", substringImpl)
	golisp.MakePrimitiveFunction("vconcat", "*", vconcatImpl)
	golisp.MakePrimitiveFunction("sit-for", "1|2", sitForImpl)
	golisp.MakePrimitiveFunction("sleep-for", "1|2|3", sleepForImpl)
	golisp.MakePrimitiveFunction("run-at-time", "2|3|4", runAtTimeImpl)
	golisp.MakePrimitiveFunction("cancel-timer", "1", cancelTimerImpl)
	golisp.MakePrimitiveFunction("numberp", "1", unaryAlias("number?"))
	golisp.MakePrimitiveFunction("integerp", "1", integerpImpl)
	golisp.MakePrimitiveFunction("zerop", "1", unaryAlias("zero?"))
	golisp.MakePrimitiveFunction("eq", "2", binaryAlias("eq?"))
	golisp.MakePrimitiveFunction("equal", "2", equalImpl)
	golisp.MakePrimitiveFunction("set", "2", setImpl)
	golisp.MakePrimitiveFunction("functionp", "1", functionpImpl)
	golisp.MakePrimitiveFunction("atom", "1", atomImpl)
	golisp.MakePrimitiveFunction("listp", "1", listpImpl)
	golisp.MakePrimitiveFunction("=", "2", binaryAlias("=="))
	golisp.MakePrimitiveFunction("/=", "2", binaryAlias("!="))
	golisp.MakePrimitiveFunction("<", ">=2", lessImpl)
	golisp.MakePrimitiveFunction("<=", ">=2", lessEqImpl)
	golisp.MakePrimitiveFunction(">", ">=2", greaterImpl)
	golisp.MakePrimitiveFunction(">=", ">=2", greaterEqImpl)
	golisp.MakePrimitiveFunction("interactive", "*", interactiveImpl)
	golisp.MakePrimitiveFunction("called-interactively-p", "0|1", calledInteractivelyPImpl)
	golisp.MakePrimitiveFunction("input-pending-p", "0", nilBoolImpl)
	golisp.MakePrimitiveFunction("turn-on-auto-fill", "0", firstArgOrNil)
	golisp.MakePrimitiveFunction("auto-fill-mode", "0|1", firstArgOrNil)
	golisp.MakePrimitiveFunction("do-auto-fill", "0|1", firstArgOrNil)
	golisp.MakePrimitiveFunction("derived-mode-p", ">=1", derivedModePImpl)
	golisp.MakePrimitiveFunction("symbolp", "1", symbolpImpl)
	golisp.MakePrimitiveFunction("intern", "1|2", internImpl)
	golisp.MakePrimitiveFunction("symbol-name", "1", symbolNameImpl)
	golisp.MakePrimitiveFunction("symbol-value", "1", symbolValueImpl)
	golisp.MakePrimitiveFunction("symbol-function", "1", symbolFunctionImpl)
	golisp.MakePrimitiveFunction("intern-soft", "1|2", internSoftImpl)
	golisp.MakePrimitiveFunction("stringp", "1", stringpImpl)
	golisp.MakePrimitiveFunction("facep", "1", facepImpl)
	golisp.MakePrimitiveFunction("natnump", "1", natnumpImpl)
	golisp.MakePrimitiveFunction("regexp-quote", "1", regexpQuoteImpl)
	golisp.MakePrimitiveFunction("copy-face", "2|3|4", copyFaceImpl)
	golisp.MakePrimitiveFunction("current-time", "0", currentTimeImpl)
	golisp.MakePrimitiveFunction("time-convert", "1|2", timeConvertImpl)
	golisp.MakePrimitiveFunction("time-equal-p", "2", timeEqualPImpl)
	golisp.MakePrimitiveFunction("current-time-string", "0|1", currentTimeStringImpl)
	golisp.MakePrimitiveFunction("define-error", "1|2|3", defineErrorImpl)
	golisp.MakePrimitiveFunction("force-mode-line-update", "0|1", forceModeLineUpdateImpl)
	golisp.MakePrimitiveFunction("fset", "2", fsetImpl)
	golisp.MakePrimitiveFunction("rplaca", "2", rplacaImpl)
	golisp.MakePrimitiveFunction("get", "2", rt.getImpl)
	golisp.MakePrimitiveFunction("require", "*", rt.requireImpl)
	golisp.MakePrimitiveFunction("load", "1|2|3|4", rt.loadImpl)
	golisp.MakePrimitiveFunction("provide", "1", rt.provideImpl)
	golisp.MakePrimitiveFunction("throw", "2", throwImpl)
	golisp.MakePrimitiveFunction("signal", "2", signalImpl)
	golisp.MakePrimitiveFunction("funcall", ">=1", rt.funcallImpl)
	golisp.MakePrimitiveFunction("call-fn", ">=1", rt.callFnImpl)
	golisp.MakePrimitiveFunction("run-hooks", ">=1", rt.runHooksImpl)
	golisp.MakePrimitiveFunction("add-hook", ">=2", rt.addHookImpl)
	golisp.MakePrimitiveFunction("easy-menu-define", ">=4", rt.easyMenuDefineImpl)
	golisp.MakePrimitiveFunction("use-local-map", "1", rt.useLocalMapImpl)
	golisp.MakePrimitiveFunction("current-local-map", "0", rt.currentLocalMapImpl)
	golisp.MakePrimitiveFunction("put", "3", rt.putImpl)
	golisp.MakePrimitiveFunction("switch-to-buffer", "1|2", rt.switchToBufferImpl)
	golisp.MakePrimitiveFunction("kill-buffer", "0|1", rt.killBufferImpl)
	golisp.MakePrimitiveFunction("bury-buffer", "0|1", rt.buryBufferImpl)
	golisp.MakePrimitiveFunction("select-window", "1", rt.selectWindowImpl)
	golisp.MakePrimitiveFunction("select-frame", "1|2", selectFrameImpl)
	golisp.MakePrimitiveFunction("selected-window", "0", rt.selectedWindowImpl)
	golisp.MakePrimitiveFunction("selected-frame", "0", selectedFrameImpl)
	golisp.MakePrimitiveFunction("frame-selected-window", "0|1", frameSelectedWindowImpl)
	golisp.MakePrimitiveFunction("frame-visible-p", "0|1", frameVisiblePImpl)
	golisp.MakePrimitiveFunction("visible-frame-list", "0", visibleFrameListImpl)
	golisp.MakePrimitiveFunction("window-frame", "0|1", windowFrameImpl)
	golisp.MakePrimitiveFunction("frame-parameter", "2", frameParameterImpl)
	golisp.MakePrimitiveFunction("modify-frame-parameters", "2", firstArg)
	golisp.MakePrimitiveFunction("set-frame-selected-window", "2|3", firstArg)
	golisp.MakePrimitiveFunction("frame-monitor-attributes", "0|1", frameMonitorAttributesImpl)
	golisp.MakePrimitiveFunction("set-window-start", "2|3", setWindowStartImpl)
	golisp.MakePrimitiveFunction("set-window-point", "2", setWindowPointImpl)
	golisp.MakePrimitiveFunction("set-window-buffer", "2|3", rt.setWindowBufferImpl)
	golisp.MakePrimitiveFunction("window-start", "0|1", windowStartImpl)
	golisp.MakePrimitiveFunction("window-end", "0|1|2", windowEndImpl)
	golisp.MakePrimitiveFunction("window-point", "0|1", windowPointImpl)
	golisp.MakePrimitiveFunction("get-buffer-window", "1|2", rt.getBufferWindowImpl)
	golisp.MakePrimitiveFunction("current-buffer", "0", rt.currentBufferImpl)
	golisp.MakePrimitiveFunction("message", "*", rt.messageImpl)
	golisp.MakePrimitiveFunction("error", ">=1", errorImpl)
	golisp.MakePrimitiveFunction("user-error", ">=1", rt.userErrorImpl)
	golisp.MakePrimitiveFunction("read-string", "1|2|3|4|5", readStringImpl)
	golisp.MakePrimitiveFunction("format", "*", formatImpl)
	golisp.MakePrimitiveFunction("apply", ">=2", applyImpl)
	golisp.MakePrimitiveFunction("make-sparse-keymap", "0|1", makeSparseKeymapImpl)
	golisp.MakePrimitiveFunction("define-key", "3", defineKeyImpl)
	golisp.MakePrimitiveFunction("keymap-set", "3", keymapSetImpl)
	golisp.MakePrimitiveFunction("obarray-make", "1", obarrayMakeImpl)
	golisp.MakePrimitiveFunction("expand-file-name", "1|2", expandFileNameImpl)
	golisp.MakePrimitiveFunction("substitute-in-file-name", "1", substituteInFileNameImpl)
	golisp.MakePrimitiveFunction("executable-find", "1", executableFindImpl)
	golisp.MakePrimitiveFunction("locate-user-emacs-file", "1|2", locateUserEmacsFileImpl)
	golisp.MakePrimitiveFunction("define-obsolete-function-alias", ">=3", defineObsoleteFunctionAliasImpl)
	golisp.MakePrimitiveFunction("make-obsolete-variable", ">=2", makeObsoleteVariableImpl)
	golisp.MakePrimitiveFunction("make-obsolete", ">=2", makeObsoleteImpl)
	golisp.MakePrimitiveFunction("frame-height", "0|1", frameHeightImpl)
	golisp.MakePrimitiveFunction("frame-width", "0|1", frameWidthImpl)
	golisp.MakePrimitiveFunction("window-height", "0|1", windowHeightImpl)
	golisp.MakePrimitiveFunction("window-width", "0|1", windowWidthImpl)
	golisp.MakePrimitiveFunction("window-body-pixel-edges", "0|1", windowBodyPixelEdgesImpl)
	golisp.MakePrimitiveFunction("line-pixel-height", "0|1", linePixelHeightImpl)
	golisp.MakePrimitiveFunction("display-color-p", "0|1", displayColorPImpl)
	golisp.MakePrimitiveFunction("display-images-p", "0|1", displayImagesPImpl)
	golisp.MakePrimitiveFunction("char-to-string", "1", charToStringImpl)
	golisp.MakePrimitiveFunction("string-to-char", "1", stringToCharImpl)
	golisp.MakePrimitiveFunction("min", ">=1", minImpl)
	golisp.MakePrimitiveFunction("max", ">=1", maxImpl)
	golisp.MakePrimitiveFunction("abs", "1", absImpl)
	golisp.MakePrimitiveFunction("floor", "1|2", floorImpl)
	golisp.MakePrimitiveFunction("oddp", "1", oddpImpl)
	golisp.MakePrimitiveFunction("evenp", "1", evenpImpl)
	golisp.MakePrimitiveFunction("copy", "1", copySequenceImpl)
	golisp.MakePrimitiveFunction("make-string", "2|3", makeStringImpl)
	golisp.MakePrimitiveFunction("mapcar", "2", mapcarImpl)
	golisp.MakePrimitiveFunction("mapc", "2", mapcImpl)
	golisp.MakePrimitiveFunction("nconc", "*", nconcImpl)
	golisp.MakePrimitiveFunction("delq", "2", delqImpl)
	golisp.MakePrimitiveFunction("split-string", "1|2|3|4", splitStringImpl)
	golisp.MakePrimitiveFunction("mapconcat", "3", mapconcatImpl)
	golisp.MakePrimitiveFunction("downcase", "1", downcaseImpl)
	golisp.MakePrimitiveFunction("capitalize", "1", capitalizeImpl)
	golisp.MakePrimitiveFunction("prin1-to-string", "1|2", prin1ToStringImpl)
	golisp.MakePrimitiveFunction("insert", "*", insertImpl)
	golisp.MakePrimitiveFunction("insert-file-contents", "1|2|3|4|5", insertFileContentsImpl)
	golisp.MakePrimitiveFunction("insert-char", "1|2|3", insertCharImpl)
	golisp.MakePrimitiveFunction("erase-buffer", "0", eraseBufferImpl)
	golisp.MakePrimitiveFunction("delete-blank-lines", "0", deleteBlankLinesImpl)
	golisp.MakePrimitiveFunction("buffer-disable-undo", "0|1", firstArgOrNil)
	golisp.MakePrimitiveFunction("buffer-live-p", "1", bufferLivePImpl)
	golisp.MakePrimitiveFunction("generate-new-buffer", "1", rt.generateNewBufferImpl)
	golisp.MakePrimitiveFunction("file-readable-p", "1", fileReadablePImpl)
	golisp.MakePrimitiveFunction("file-exists-p", "1", fileExistsPImpl)
	golisp.MakePrimitiveFunction("file-attributes", "1|2|3|4", fileAttributesImpl)
	golisp.MakePrimitiveFunction("file-attribute-modification-time", "1", fileAttributeModificationTimeImpl)
	golisp.MakePrimitiveFunction("set-buffer-modified-p", "0|1", firstArgOrNil)
	golisp.MakePrimitiveFunction("buffer-list", "0|1", rt.bufferListImpl)
	golisp.MakePrimitiveFunction("undo-boundary", "0", nilValueImpl)
	golisp.MakePrimitiveFunction("primitive-undo", "2", primitiveUndoImpl)
	golisp.MakePrimitiveFunction("get-buffer-create", "1", getBufferCreateImpl)
	golisp.MakePrimitiveFunction("get-scratch-buffer-create", "0", getScratchBufferCreateImpl)
	golisp.MakePrimitiveFunction("get-buffer", "1", getBufferImpl)
	golisp.MakePrimitiveFunction("buffer-name", "0|1", bufferNameImpl)
	golisp.MakePrimitiveFunction("buffer-local-value", "2", bufferLocalValueImpl)
	golisp.MakePrimitiveFunction("point", "0", pointImpl)
	golisp.MakePrimitiveFunction("el-point", "0", pointImpl)
	golisp.MakePrimitiveFunction("point-min", "0", pointMinImpl)
	golisp.MakePrimitiveFunction("point-max", "0", pointMaxImpl)
	golisp.MakePrimitiveFunction("eobp", "0", eobpImpl)
	golisp.MakePrimitiveFunction("bolp", "0", bolpImpl)
	golisp.MakePrimitiveFunction("eolp", "0", eolpImpl)
	golisp.MakePrimitiveFunction("following-char", "0", followingCharImpl)
	golisp.MakePrimitiveFunction("char-after", "0|1", charAfterImpl)
	golisp.MakePrimitiveFunction("preceding-char", "0", precedingCharImpl)
	golisp.MakePrimitiveFunction("current-column", "0", currentColumnImpl)
	golisp.MakePrimitiveFunction("vertical-motion", "1|2", verticalMotionImpl)
	golisp.MakePrimitiveFunction("forward-line", "0|1", forwardLineImpl)
	golisp.MakePrimitiveFunction("beginning-of-line", "0|1", beginningOfLineImpl)
	golisp.MakePrimitiveFunction("forward-char", "0|1", forwardCharImpl)
	golisp.MakePrimitiveFunction("end-of-line", "0|1", endOfLineImpl)
	golisp.MakePrimitiveFunction("backward-char", "0|1", backwardCharImpl)
	golisp.MakePrimitiveFunction("count-lines", "2", countLinesImpl)
	golisp.MakePrimitiveFunction("looking-at", "1", lookingAtImpl)
	golisp.MakePrimitiveFunction("search-backward", "1|2|3", searchBackwardImpl)
	golisp.MakePrimitiveFunction("search-forward", "1|2|3", searchForwardImpl)
	golisp.MakePrimitiveFunction("search-forward-regexp", "1|2|3", searchForwardRegexpImpl)
	golisp.MakePrimitiveFunction("re-search-forward", "1|2|3", searchForwardRegexpImpl)
	golisp.MakePrimitiveFunction("skip-chars-forward", "1|2", skipCharsForwardImpl)
	golisp.MakePrimitiveFunction("subst-char-in-region", "4|5", substCharInRegionImpl)
	golisp.MakePrimitiveFunction("goto-char", "1", gotoCharImpl)
	golisp.MakePrimitiveFunction("line-end-position", "0|1", lineEndPositionImpl)
	golisp.MakePrimitiveFunction("next-single-property-change", "2|3|4", nextSinglePropertyChangeImpl)
	golisp.MakePrimitiveFunction("delete-region", "2", deleteRegionImpl)
	golisp.MakePrimitiveFunction("delete-char", "0|1", deleteCharImpl)
	golisp.MakePrimitiveFunction("backward-word", "0|1", backwardWordImpl)
	golisp.MakePrimitiveFunction("append-to-buffer", "3", rt.appendToBufferImpl)
	golisp.MakePrimitiveFunction("insert-buffer-substring", "1|2|3", rt.insertBufferSubstringImpl)
	golisp.MakePrimitiveFunction("buffer-substring", "2", bufferSubstringImpl)
	golisp.MakePrimitiveFunction("buffer-substring-no-properties", "2", bufferSubstringImpl)
	golisp.MakePrimitiveFunction("insert-rectangle", "1", insertRectangleImpl)
	golisp.MakePrimitiveFunction("newline", "0|1", newlineImpl)
	golisp.MakePrimitiveFunction("move-to-column", "1|2", moveToColumnImpl)
	golisp.MakePrimitiveFunction("indent-to", "1|2", indentToImpl)
	golisp.MakePrimitiveFunction("fill-region-as-paragraph", "2|3|4|5", firstArgOrNil)
	golisp.MakePrimitiveFunction("pop-to-buffer-same-window", "1|2", rt.popToBufferSameWindowImpl)
	golisp.MakePrimitiveFunction("y-or-n-p", "1", yesImpl)
	golisp.MakePrimitiveFunction("yes-or-no-p", "1", yesImpl)
	golisp.MakePrimitiveFunction("string-equal", "2", stringEqualImpl)
	golisp.MakePrimitiveFunction("string=", "2", stringEqualImpl)
	golisp.MakePrimitiveFunction("string-match-p", "2|3", stringMatchPImpl)
	golisp.MakePrimitiveFunction("string-match", "2|3|4", stringMatchImpl)
	golisp.MakePrimitiveFunction("string-suffix-p", "2|3|4", stringSuffixPImpl)
	golisp.MakePrimitiveFunction("copy-sequence", "1", copySequenceImpl)
	golisp.MakePrimitiveFunction("number-to-string", "1", numberToStringImpl)
	golisp.MakePrimitiveFunction("int-to-string", "1", numberToStringImpl)
	golisp.MakePrimitiveFunction("replace-match", "1|2|3|4|5", replaceMatchImpl)
	golisp.MakePrimitiveFunction("set-match-data", "1|2", setMatchDataImpl)
	golisp.MakePrimitiveFunction("match-beginning", "1", matchBeginningImpl)
	golisp.MakePrimitiveFunction("match-end", "1", matchEndImpl)
	golisp.MakePrimitiveFunction("get-text-property", "2|3|4", firstArgOrNil)
	golisp.MakePrimitiveFunction("put-text-property", "4|5", addTextPropertiesImpl)
	golisp.MakePrimitiveFunction("add-text-properties", "3|4", addTextPropertiesImpl)
	golisp.MakePrimitiveFunction("set-text-properties", "3|4", setTextPropertiesImpl)
	golisp.MakePrimitiveFunction("remove-overlays", "0|1|2|3", removeOverlaysImpl)
	golisp.MakePrimitiveFunction("remove-text-properties", "3|4", removeTextPropertiesImpl)
	golisp.MakePrimitiveFunction("untabify", "1|2", untabifyImpl)
	golisp.MakePrimitiveFunction("lpr-print-region", "2|3|4|5", lprPrintRegionImpl)
	golisp.MakePrimitiveFunction("current-window-configuration", "0|1", currentWindowConfigurationImpl)
	golisp.MakePrimitiveFunction("set-window-configuration", "1", setWindowConfigurationImpl)
	golisp.MakePrimitiveFunction("set-face-background", "2|3|4", setFaceBackgroundImpl)
	golisp.MakePrimitiveFunction("set-face-foreground", "2|3|4", setFaceBackgroundImpl)
	golisp.MakePrimitiveFunction("modify-syntax-entry", "2|3", modifySyntaxEntryImpl)
	golisp.MakePrimitiveFunction("prefix-numeric-value", "1", prefixNumericValueImpl)
	golisp.MakePrimitiveFunction("make-bool-vector", "2", makeBoolVectorImpl)
	golisp.MakePrimitiveFunction("make-syntax-table", "0|1", makeSyntaxTableImpl)
	golisp.MakePrimitiveFunction("seq-find", "2|3", seqFindImpl)
	golisp.MakePrimitiveFunction("seq-random-elt", "1", seqRandomEltImpl)
	golisp.MakePrimitiveFunction("fillarray", "2", fillarrayImpl)
	golisp.MakePrimitiveFunction("null", "1", nullImpl)
	golisp.MakePrimitiveFunction("identity", "1", firstArg)
	golisp.MakePrimitiveFunction("recenter", "0|1", firstArgOrNil)
	golisp.MakePrimitiveFunction("redisplay", "0|1", firstArgOrNil)
	golisp.MakePrimitiveFunction("1", "*", firstArgOrNil)
	golisp.MakeSpecialForm("declare-function", "*", declareFunctionImpl)

	bindGamegrid(rt)
}

func bindGamegrid(rt *runtimeState) {
	golisp.MakePrimitiveFunction("gamegrid-init", "1", rt.gamegridInitImpl)
	golisp.MakePrimitiveFunction("gamegrid-init-buffer", "3", rt.gamegridInitBufferImpl)
	golisp.MakePrimitiveFunction("gamegrid-kill-timer", "0", rt.gamegridKillTimerImpl)
	golisp.MakePrimitiveFunction("gamegrid-start-timer", "2", rt.gamegridStartTimerImpl)
	golisp.MakePrimitiveFunction("gamegrid-set-timer", "1", rt.gamegridSetTimerImpl)
	golisp.MakePrimitiveFunction("gamegrid-add-score", "2", rt.gamegridAddScoreImpl)
	golisp.MakePrimitiveFunction("gamegrid-set-cell", "3", rt.gamegridSetCellImpl)
	golisp.MakePrimitiveFunction("gamegrid-get-cell", "2", rt.gamegridGetCellImpl)
}

func (rt *runtimeState) loadElispFile(path string) error {
	source, err := os.ReadFile(path)
	if err != nil {
		return err
	}
	preprocessed, err := preprocessElisp(string(source))
	if err != nil {
		return err
	}
	_, err = golisp.ParseAndEvalAllInEnvironment(preprocessed, rt.env)
	if err == nil {
		return nil
	}
	name, ok := missingFunctionFromError(err.Error())
	if !ok {
		return err
	}
	return fmt.Errorf("needed elisp function is not implemented: %s", name)
}

func (rt *runtimeState) resolveFeatureFile(feature string) (string, bool) {
	candidates := []string{feature + ".el", strings.ReplaceAll(feature, "-", "/") + ".el"}
	for _, dir := range rt.loadPaths {
		for _, rel := range candidates {
			p := filepath.Join(dir, rel)
			if st, err := os.Stat(p); err == nil && !st.IsDir() {
				return p, true
			}
		}
	}
	return "", false
}

func (rt *runtimeState) warnf(format string, args ...any) {
	fmt.Fprintf(os.Stderr, "[etetris] "+format+"\n", args...)
}

func (rt *runtimeState) warnOnce(key, format string, args ...any) {
	if rt.warned[key] {
		return
	}
	rt.warned[key] = true
	rt.warnf(format, args...)
}

func missingFunctionFromError(msg string) (string, bool) {
	for _, re := range missingFnPatterns {
		m := re.FindStringSubmatch(msg)
		if len(m) == 2 {
			name := strings.TrimSpace(m[1])
			name = strings.Trim(name, "'`\",")
			if name != "" {
				allDigits := true
				for i := 0; i < len(name); i++ {
					if name[i] < '0' || name[i] > '9' {
						allDigits = false
						break
					}
				}
				if allDigits {
					return "", false
				}
			}
			if name != "" {
				return name, true
			}
		}
	}
	return "", false
}

func (rt *runtimeState) registerFunction(name string, fn *golisp.Data) {
	if name == "" || fn == nil {
		return
	}
	rt.funcByName[name] = fn
}

func (rt *runtimeState) ensureInitialWindowAndBuffer() {
	buf := rt.ensureBuffer("*scratch*")
	win := rt.newWindowForBuffer(buf)
	rt.selectedWindowID = win.id
}

func (rt *runtimeState) ensureBuffer(name string) *elBuffer {
	if b, ok := rt.buffers[name]; ok {
		return b
	}
	b := &elBuffer{
		name:  name,
		hooks: make(map[string][]*golisp.Data),
	}
	b.object = golisp.ObjectWithTypeAndValue("el-buffer", unsafe.Pointer(b))
	rt.buffers[name] = b
	return b
}

func (rt *runtimeState) newWindowForBuffer(buf *elBuffer) *elWindow {
	id := rt.nextWindowID
	rt.nextWindowID++
	w := &elWindow{id: id, buffer: buf}
	w.object = golisp.ObjectWithTypeAndValue("el-window", unsafe.Pointer(w))
	rt.windows[id] = w
	return w
}

func (rt *runtimeState) selectedWindow() *elWindow {
	if w, ok := rt.windows[rt.selectedWindowID]; ok {
		return w
	}
	for _, w := range rt.windows {
		rt.selectedWindowID = w.id
		return w
	}
	rt.ensureInitialWindowAndBuffer()
	return rt.windows[rt.selectedWindowID]
}

func (rt *runtimeState) currentBuffer() *elBuffer {
	return rt.selectedWindow().buffer
}

func featureName(d *golisp.Data) string {
	if golisp.NilP(d) {
		return ""
	}
	switch {
	case golisp.SymbolP(d), golisp.StringP(d):
		return golisp.StringValue(d)
	default:
		return golisp.String(d)
	}
}

func byteToRuneOffset(s string, n int) int {
	if n <= 0 {
		return 0
	}
	if n > len(s) {
		n = len(s)
	}
	return utf8.RuneCountInString(s[:n])
}

func (rt *runtimeState) clearMatchData() {
	rt.matchData = nil
	rt.matchString = ""
	rt.matchInString = false
	rt.matchBuffer = nil
}

func (rt *runtimeState) setStringMatchData(s string, runeBase int, submatchIdx []int) {
	if len(submatchIdx) == 0 {
		rt.clearMatchData()
		return
	}
	rt.matchData = make([]int, 0, len(submatchIdx))
	for i := 0; i+1 < len(submatchIdx); i += 2 {
		a, b := submatchIdx[i], submatchIdx[i+1]
		if a < 0 || b < 0 {
			rt.matchData = append(rt.matchData, -1, -1)
			continue
		}
		ra := runeBase + byteToRuneOffset(s, a)
		rb := runeBase + byteToRuneOffset(s, b)
		rt.matchData = append(rt.matchData, ra, rb)
	}
	rt.matchString = s
	rt.matchInString = true
	rt.matchBuffer = nil
}

func (rt *runtimeState) setBufferMatchData(buf *elBuffer, segment string, runeBase int, submatchIdx []int) {
	if len(submatchIdx) == 0 {
		rt.clearMatchData()
		return
	}
	rt.matchData = make([]int, 0, len(submatchIdx))
	for i := 0; i+1 < len(submatchIdx); i += 2 {
		a, b := submatchIdx[i], submatchIdx[i+1]
		if a < 0 || b < 0 {
			rt.matchData = append(rt.matchData, -1, -1)
			continue
		}
		// Buffer positions are 1-based in Emacs.
		ra := runeBase + byteToRuneOffset(segment, a) + 1
		rb := runeBase + byteToRuneOffset(segment, b) + 1
		rt.matchData = append(rt.matchData, ra, rb)
	}
	rt.matchString = ""
	rt.matchInString = false
	rt.matchBuffer = buf
}

func (rt *runtimeState) requireImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	feature := golisp.Car(args)
	name := featureName(feature)
	if rt.providedFeatures[name] {
		return feature, nil
	}
	if rt.loadingFeatures[name] {
		return feature, nil
	}
	if p, ok := rt.resolveFeatureFile(name); ok {
		rt.loadingFeatures[name] = true
		err := rt.loadElispFile(p)
		delete(rt.loadingFeatures, name)
		if err == nil {
			rt.providedFeatures[name] = true
			return feature, nil
		}
		rt.warnf("require failed to load %s from %s: %v", name, p, err)
	}
	noError := false
	if golisp.NotNilP(golisp.Cddr(args)) {
		noError = golisp.BooleanValue(golisp.Caddr(args))
	}
	if noError {
		return golisp.EmptyCons(), nil
	}
	if rt.requireShim {
		rt.warnOnce("require-missing-"+name, "required feature %s is not available; providing empty shim", name)
		rt.providedFeatures[name] = true
		return feature, nil
	}
	return nil, fmt.Errorf("required feature is not available: %s", name)
}

func (rt *runtimeState) loadImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	target := featureName(golisp.Car(args))
	path := target
	if !strings.HasSuffix(path, ".el") {
		if p, ok := rt.resolveFeatureFile(target); ok {
			path = p
		} else if p, ok := rt.resolveFeatureFile(path); ok {
			path = p
		} else {
			path = target + ".el"
		}
	}
	if err := rt.loadElispFile(path); err != nil {
		return nil, err
	}
	return golisp.BooleanWithValue(true), nil
}

func (rt *runtimeState) provideImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	feature := golisp.Car(args)
	rt.providedFeatures[featureName(feature)] = true
	return feature, nil
}

func throwImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	tag := featureName(golisp.Car(args))
	val := golisp.Cadr(args)
	return nil, throwSignal{tag: tag, value: val}
}

func signalImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	cond := golisp.Car(args)
	if !golisp.SymbolP(cond) {
		return nil, fmt.Errorf("signal expects condition symbol, got %s", golisp.String(cond))
	}
	return nil, elSignal{condition: golisp.StringValue(cond), data: golisp.Cadr(args)}
}

func (rt *runtimeState) funcallImpl(args *golisp.Data, env *golisp.SymbolTableFrame) (*golisp.Data, error) {
	f := golisp.Car(args)
	if golisp.SymbolP(f) {
		f = env.ValueOf(f)
	}
	if !golisp.FunctionOrPrimitiveP(f) {
		return nil, fmt.Errorf("funcall expects function, got %s", golisp.String(f))
	}
	return golisp.ApplyWithoutEval(f, golisp.Cdr(args), env)
}

func (rt *runtimeState) callFnImpl(args *golisp.Data, env *golisp.SymbolTableFrame) (*golisp.Data, error) {
	name := featureName(golisp.Car(args))
	fn := rt.funcByName[name]
	if !golisp.FunctionOrPrimitiveP(fn) {
		return nil, fmt.Errorf("call-fn unknown function: %s", name)
	}
	return golisp.ApplyWithoutEval(fn, golisp.Cdr(args), env)
}

func (rt *runtimeState) runHooksImpl(args *golisp.Data, env *golisp.SymbolTableFrame) (*golisp.Data, error) {
	result := golisp.EmptyCons()
	for c := args; golisp.NotNilP(c); c = golisp.Cdr(c) {
		h := golisp.Car(c)
		if !golisp.SymbolP(h) {
			continue
		}
		hookVar := env.ValueOf(h)
		if golisp.NilP(hookVar) {
			continue
		}
		if golisp.FunctionOrPrimitiveP(hookVar) {
			r, err := golisp.ApplyWithoutEval(hookVar, golisp.EmptyCons(), env)
			if err != nil {
				return nil, err
			}
			result = r
			continue
		}
		if golisp.ListP(hookVar) {
			for e := hookVar; golisp.NotNilP(e); e = golisp.Cdr(e) {
				fn := golisp.Car(e)
				if golisp.SymbolP(fn) {
					fn = env.ValueOf(fn)
				}
				if !golisp.FunctionOrPrimitiveP(fn) {
					continue
				}
				r, err := golisp.ApplyWithoutEval(fn, golisp.EmptyCons(), env)
				if err != nil {
					return nil, err
				}
				result = r
			}
		}
	}
	return result, nil
}

func (rt *runtimeState) addHookImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	hook := featureName(golisp.Car(args))
	fn := golisp.Cadr(args)
	isLocal := false
	if golisp.NotNilP(golisp.Cdddr(args)) {
		isLocal = golisp.BooleanValue(golisp.Car(golisp.Cdddr(args)))
	}
	if isLocal {
		buf := rt.currentBuffer()
		buf.hooks[hook] = append(buf.hooks[hook], fn)
	} else {
		if rt.buffers["*global*"] == nil {
			rt.buffers["*global*"] = &elBuffer{name: "*global*", hooks: make(map[string][]*golisp.Data)}
		}
		rt.buffers["*global*"].hooks[hook] = append(rt.buffers["*global*"].hooks[hook], fn)
	}
	return fn, nil
}

func (rt *runtimeState) easyMenuDefineImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	menuName := featureName(golisp.Car(args))
	definition := golisp.Car(golisp.Cdddr(args))
	rt.menus[menuName] = definition
	return golisp.Intern(menuName), nil
}

func (rt *runtimeState) useLocalMapImpl(args *golisp.Data, env *golisp.SymbolTableFrame) (*golisp.Data, error) {
	m := golisp.Car(args)
	if golisp.SymbolP(m) {
		m = env.ValueOf(m)
	}
	rt.currentBuffer().localMap = m
	return m, nil
}

func (rt *runtimeState) currentLocalMapImpl(_ *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	m := rt.currentBuffer().localMap
	if m == nil {
		return golisp.EmptyCons(), nil
	}
	return m, nil
}

func (rt *runtimeState) putImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	sym := featureName(golisp.Car(args))
	prop := featureName(golisp.Cadr(args))
	val := golisp.Caddr(args)
	props, ok := rt.symbolProps[sym]
	if !ok {
		props = make(map[string]*golisp.Data)
		rt.symbolProps[sym] = props
	}
	props[prop] = val
	return val, nil
}

func (rt *runtimeState) getImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	sym := featureName(golisp.Car(args))
	prop := featureName(golisp.Cadr(args))
	if props, ok := rt.symbolProps[sym]; ok {
		if v, ok := props[prop]; ok {
			return v, nil
		}
	}
	return golisp.EmptyCons(), nil
}

func bufferNameFromArg(d *golisp.Data) string {
	if golisp.ObjectP(d) && golisp.ObjectType(d) == "el-buffer" {
		return (*elBuffer)(golisp.ObjectValue(d)).name
	}
	return featureName(d)
}

func (rt *runtimeState) switchToBufferImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	name := bufferNameFromArg(golisp.Car(args))
	buf := rt.ensureBuffer(name)
	rt.selectedWindow().buffer = buf
	return buf.object, nil
}

func (rt *runtimeState) generateNewBufferImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	base := featureName(golisp.Car(args))
	if base == "" {
		base = "*buffer*"
	}
	name := base
	if _, exists := rt.buffers[name]; exists {
		for i := 2; ; i++ {
			cand := fmt.Sprintf("%s<%d>", base, i)
			if _, ok := rt.buffers[cand]; !ok {
				name = cand
				break
			}
		}
	}
	return rt.ensureBuffer(name).object, nil
}

func (rt *runtimeState) killBufferImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	name := rt.currentBuffer().name
	if golisp.NotNilP(args) {
		name = bufferNameFromArg(golisp.Car(args))
	}
	delete(rt.buffers, name)
	if len(rt.buffers) == 0 {
		rt.ensureInitialWindowAndBuffer()
	} else if rt.currentBuffer().name == name {
		rt.selectedWindow().buffer = rt.ensureBuffer("*scratch*")
	}
	return golisp.BooleanWithValue(true), nil
}

func (rt *runtimeState) buryBufferImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	name := rt.currentBuffer().name
	if golisp.NotNilP(args) {
		name = bufferNameFromArg(golisp.Car(args))
	}
	if rt.currentBuffer().name == name {
		rt.selectedWindow().buffer = rt.ensureBuffer("*scratch*")
	}
	return golisp.BooleanWithValue(true), nil
}

func (rt *runtimeState) popToBufferSameWindowImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	return rt.switchToBufferImpl(args, nil)
}

func (rt *runtimeState) selectWindowImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	wv := golisp.Car(args)
	if !golisp.ObjectP(wv) || golisp.ObjectType(wv) != "el-window" {
		return nil, fmt.Errorf("select-window expects window object, got %s", golisp.String(wv))
	}
	w := (*elWindow)(golisp.ObjectValue(wv))
	rt.windows[w.id] = w
	rt.selectedWindowID = w.id
	return w.object, nil
}

func (rt *runtimeState) selectedWindowImpl(_ *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	return rt.selectedWindow().object, nil
}

func (rt *runtimeState) getBufferWindowImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	name := bufferNameFromArg(golisp.Car(args))
	for _, w := range rt.windows {
		if w.buffer != nil && w.buffer.name == name {
			return w.object, nil
		}
	}
	return golisp.EmptyCons(), nil
}

func (rt *runtimeState) setWindowBufferImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	wv := golisp.Car(args)
	bv := golisp.Cadr(args)
	name := bufferNameFromArg(bv)
	buf := rt.ensureBuffer(name)
	if golisp.ObjectP(wv) && golisp.ObjectType(wv) == "el-window" {
		w := (*elWindow)(golisp.ObjectValue(wv))
		w.buffer = buf
		rt.windows[w.id] = w
		return buf.object, nil
	}
	rt.selectedWindow().buffer = buf
	return buf.object, nil
}

func (rt *runtimeState) currentBufferImpl(_ *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	return rt.currentBuffer().object, nil
}

func (rt *runtimeState) bufferListImpl(_ *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	names := make([]string, 0, len(rt.buffers))
	for name := range rt.buffers {
		names = append(names, name)
	}
	sort.Strings(names)
	out := make([]*golisp.Data, 0, len(names))
	for _, name := range names {
		out = append(out, rt.buffers[name].object)
	}
	return golisp.ArrayToList(out), nil
}

func (rt *runtimeState) appendToBufferImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	dstName := bufferNameFromArg(golisp.Car(args))
	start := int(golisp.IntegerValue(golisp.Cadr(args))) - 1
	end := int(golisp.IntegerValue(golisp.Caddr(args))) - 1
	src := rt.currentBuffer()
	dst := rt.ensureBuffer(dstName)
	if src == nil || dst == nil {
		return golisp.EmptyCons(), nil
	}
	if start < 0 {
		start = 0
	}
	if end < start {
		end = start
	}
	if start > len(src.text) {
		start = len(src.text)
	}
	if end > len(src.text) {
		end = len(src.text)
	}
	dst.text = append(dst.text, src.text[start:end]...)
	return golisp.EmptyCons(), nil
}

func (rt *runtimeState) insertBufferSubstringImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	srcName := bufferNameFromArg(golisp.Car(args))
	src, ok := rt.buffers[srcName]
	if !ok || src == nil {
		return golisp.EmptyCons(), nil
	}
	start := 0
	end := len(src.text)
	if golisp.NotNilP(golisp.Cdr(args)) && golisp.IntegerP(golisp.Cadr(args)) {
		start = int(golisp.IntegerValue(golisp.Cadr(args))) - 1
	}
	if golisp.NotNilP(golisp.Cddr(args)) && golisp.IntegerP(golisp.Caddr(args)) {
		end = int(golisp.IntegerValue(golisp.Caddr(args))) - 1
	}
	if start < 0 {
		start = 0
	}
	if end < start {
		end = start
	}
	if end > len(src.text) {
		end = len(src.text)
	}
	dst := rt.currentBuffer()
	if dst == nil {
		return golisp.EmptyCons(), nil
	}
	dst.text = append(dst.text[:dst.point], append(src.text[start:end], dst.text[dst.point:]...)...)
	dst.point += end - start
	return golisp.EmptyCons(), nil
}

func bufferSubstringImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	buf := rtGlobal.currentBuffer()
	if buf == nil {
		return golisp.StringWithValue(""), nil
	}
	start := int(golisp.IntegerValue(golisp.Car(args))) - 1
	end := int(golisp.IntegerValue(golisp.Cadr(args))) - 1
	if start < 0 {
		start = 0
	}
	if end < 0 {
		end = 0
	}
	if start > len(buf.text) {
		start = len(buf.text)
	}
	if end > len(buf.text) {
		end = len(buf.text)
	}
	if start > end {
		start, end = end, start
	}
	return golisp.StringWithValue(string(buf.text[start:end])), nil
}

func (rt *runtimeState) messageImpl(args *golisp.Data, env *golisp.SymbolTableFrame) (*golisp.Data, error) {
	if golisp.NilP(args) {
		return golisp.EmptyCons(), nil
	}
	msg := ""
	if golisp.StringP(golisp.Car(args)) {
		formatted, err := formatImpl(args, env)
		if err != nil {
			return nil, err
		}
		msg = golisp.StringValue(formatted)
	} else {
		msg = golisp.String(golisp.Car(args))
	}
	rt.messages = append(rt.messages, msg)
	return golisp.StringWithValue(msg), nil
}

func errorImpl(args *golisp.Data, env *golisp.SymbolTableFrame) (*golisp.Data, error) {
	if golisp.NilP(args) {
		return nil, fmt.Errorf("error")
	}
	if golisp.StringP(golisp.Car(args)) {
		formatted, err := formatImpl(args, env)
		if err != nil {
			return nil, err
		}
		return nil, fmt.Errorf("%s", golisp.StringValue(formatted))
	}
	return nil, fmt.Errorf("%s", golisp.String(golisp.Car(args)))
}

func readStringImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	// In TTY mode, text games gather input via key handling.
	// For compatibility callers, return INITIAL-INPUT if provided, otherwise empty.
	if golisp.NotNilP(golisp.Cddr(args)) {
		init := golisp.Caddr(args)
		if golisp.StringP(init) {
			return init, nil
		}
	}
	return golisp.StringWithValue(""), nil
}

func (rt *runtimeState) userErrorImpl(args *golisp.Data, env *golisp.SymbolTableFrame) (*golisp.Data, error) {
	msg := "user-error"
	if golisp.NotNilP(args) {
		if golisp.StringP(golisp.Car(args)) {
			formatted, err := formatImpl(args, env)
			if err != nil {
				return nil, err
			}
			msg = golisp.StringValue(formatted)
		} else {
			msg = golisp.String(golisp.Car(args))
		}
	}
	return nil, fmt.Errorf("%s", msg)
}

func (rt *runtimeState) gamegridInitImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	rt.gridDisplay = golisp.Car(args)
	return rt.gridDisplay, nil
}

func (rt *runtimeState) gamegridInitBufferImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	width := int(golisp.IntegerValue(golisp.Car(args)))
	height := int(golisp.IntegerValue(golisp.Cadr(args)))
	fill := golisp.Caddr(args)
	rt.gridWidth = width
	rt.gridHeight = height
	rt.gridDefault = fill
	rt.grid = make(map[[2]int]*golisp.Data, width*height)
	for y := range height {
		for x := range width {
			rt.grid[[2]int{x, y}] = fill
		}
	}
	return fill, nil
}

func (rt *runtimeState) gamegridKillTimerImpl(_ *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	delete(rt.timers, "gamegrid")
	return golisp.EmptyCons(), nil
}

func (rt *runtimeState) gamegridStartTimerImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	period := golisp.FloatValue(golisp.Car(args))
	callback := golisp.Cadr(args)
	p := float64(period)
	if p <= 0 {
		p = 0.1
	}
	rt.timers["gamegrid"] = &elTimer{period: p, callback: callback, active: true, nextFire: time.Now().Add(time.Duration(p * float64(time.Second)))}
	return callback, nil
}

func (rt *runtimeState) gamegridSetTimerImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	period := golisp.FloatValue(golisp.Car(args))
	t := rt.timers["gamegrid"]
	if t == nil {
		t = &elTimer{active: true}
		rt.timers["gamegrid"] = t
	}
	p := float64(period)
	if p <= 0 {
		p = 0.1
	}
	t.period = p
	t.nextFire = time.Now().Add(time.Duration(p * float64(time.Second)))
	return golisp.FloatWithValue(period), nil
}

func (rt *runtimeState) gamegridAddScoreImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	file := featureName(golisp.Car(args))
	score := golisp.IntegerValue(golisp.Cadr(args))
	rt.scores[file] = append(rt.scores[file], score)
	line := fmt.Sprintf("%d\t%d\n", time.Now().Unix(), score)
	if f, err := os.OpenFile(file, os.O_CREATE|os.O_WRONLY|os.O_APPEND, 0o600); err == nil {
		_, _ = f.WriteString(line)
		_ = f.Close()
	}
	return golisp.IntegerWithValue(score), nil
}

func (rt *runtimeState) gamegridSetCellImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	x := int(golisp.IntegerValue(golisp.Car(args)))
	y := int(golisp.IntegerValue(golisp.Cadr(args)))
	v := golisp.Caddr(args)
	if rt.gridWidth > 0 && rt.gridHeight > 0 && (x < 0 || y < 0 || x >= rt.gridWidth || y >= rt.gridHeight) {
		rt.warnOnce(fmt.Sprintf("cell-oob-%d-%d", x, y), "gamegrid-set-cell out of bounds: x=%d y=%d size=%dx%d", x, y, rt.gridWidth, rt.gridHeight)
	}
	rt.grid[[2]int{x, y}] = v
	return v, nil
}

func (rt *runtimeState) gamegridGetCellImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	x := int(golisp.IntegerValue(golisp.Car(args)))
	y := int(golisp.IntegerValue(golisp.Cadr(args)))
	if v, ok := rt.grid[[2]int{x, y}]; ok {
		return v, nil
	}
	return rt.gridDefault, nil
}

func setqImpl(args *golisp.Data, env *golisp.SymbolTableFrame) (*golisp.Data, error) {
	if golisp.Length(args)%2 != 0 {
		return nil, errors.New("setq expects an even number of forms")
	}
	result := golisp.EmptyCons()
	for c := args; golisp.NotNilP(c); c = golisp.Cddr(c) {
		sym := golisp.Car(c)
		if !golisp.SymbolP(sym) {
			return nil, fmt.Errorf("setq target must be a symbol, got %s", golisp.String(sym))
		}
		value, err := golisp.Eval(golisp.Cadr(c), env)
		if err != nil {
			return nil, err
		}
		if _, err := env.SetTo(sym, value); err != nil {
			if _, bindErr := env.BindTo(sym, value); bindErr != nil {
				return nil, bindErr
			}
		}
		result = value
	}
	return result, nil
}

func defunImpl(args *golisp.Data, env *golisp.SymbolTableFrame) (*golisp.Data, error) {
	name := golisp.Car(args)
	params := golisp.Cadr(args)
	body := golisp.Cddr(args)
	if golisp.NilP(body) {
		body = golisp.ArrayToList([]*golisp.Data{golisp.EmptyCons()})
	}
	if !golisp.SymbolP(name) {
		return nil, fmt.Errorf("defun name must be a symbol, got %s", golisp.String(name))
	}
	if hasElispArgMarkers(params) {
		fn := makeElispDefunWithOptional(name, params, body, env)
		_, err := env.BindLocallyTo(name, fn)
		rtGlobal.registerFunction(golisp.StringValue(name), fn)
		return fn, err
	}
	fn := golisp.FunctionWithNameParamsBodyAndParent(golisp.StringValue(name), params, body, env)
	_, err := env.BindLocallyTo(name, fn)
	rtGlobal.registerFunction(golisp.StringValue(name), fn)
	return fn, err
}

func hasElispArgMarkers(params *golisp.Data) bool {
	for c := params; golisp.NotNilP(c); c = golisp.Cdr(c) {
		p := golisp.Car(c)
		if golisp.SymbolP(p) {
			n := golisp.StringValue(p)
			if n == "&optional" || n == "&rest" {
				return true
			}
		}
	}
	return false
}

type elispParamSpec struct {
	required []*golisp.Data
	optional []*golisp.Data
	rest     *golisp.Data
}

func parseElispParamSpec(params *golisp.Data) (elispParamSpec, error) {
	spec := elispParamSpec{}
	mode := "required"
	for c := params; golisp.NotNilP(c); c = golisp.Cdr(c) {
		p := golisp.Car(c)
		if !golisp.SymbolP(p) {
			return spec, fmt.Errorf("defun parameter must be symbol, got %s", golisp.String(p))
		}
		name := golisp.StringValue(p)
		switch name {
		case "&optional":
			mode = "optional"
			continue
		case "&rest":
			mode = "rest"
			continue
		}
		switch mode {
		case "required":
			spec.required = append(spec.required, p)
		case "optional":
			spec.optional = append(spec.optional, p)
		case "rest":
			spec.rest = p
			mode = "after-rest"
		default:
			return spec, fmt.Errorf("unexpected parameter after &rest: %s", name)
		}
	}
	return spec, nil
}

func makeElispDefunWithOptional(name, params, body *golisp.Data, parent *golisp.SymbolTableFrame) *golisp.Data {
	fnName := golisp.StringValue(name)
	pf := &golisp.PrimitiveFunction{
		Name:            fnName,
		Special:         false,
		ArgRestrictions: []golisp.ArgRestriction{{Type: golisp.ARGS_ANY}},
		IsRestricted:    false,
		Body: func(args *golisp.Data, callEnv *golisp.SymbolTableFrame) (*golisp.Data, error) {
			spec, err := parseElispParamSpec(params)
			if err != nil {
				return nil, err
			}
			local := golisp.NewSymbolTableFrameBelow(parent, fnName)
			local.Previous = callEnv
			argArr := golisp.ToArray(args)
			if len(argArr) < len(spec.required) {
				return nil, fmt.Errorf("%s expected at least %d parameters, received %d", fnName, len(spec.required), len(argArr))
			}
			idx := 0
			for _, s := range spec.required {
				if _, err := local.BindLocallyTo(s, argArr[idx]); err != nil {
					return nil, err
				}
				idx++
			}
			for _, s := range spec.optional {
				v := golisp.EmptyCons()
				if idx < len(argArr) {
					v = argArr[idx]
					idx++
				}
				if _, err := local.BindLocallyTo(s, v); err != nil {
					return nil, err
				}
			}
			if spec.rest != nil {
				rest := golisp.EmptyCons()
				if idx < len(argArr) {
					rest = golisp.ArrayToList(argArr[idx:])
				}
				if _, err := local.BindLocallyTo(spec.rest, rest); err != nil {
					return nil, err
				}
				idx = len(argArr)
			}
			if idx < len(argArr) {
				return nil, fmt.Errorf("%s expected %d parameters, received %d", fnName, idx, len(argArr))
			}
			return evalLetBody(body, local)
		},
	}
	return golisp.PrimitiveWithNameAndFunc(fnName, pf)
}

func defsubstImpl(args *golisp.Data, env *golisp.SymbolTableFrame) (*golisp.Data, error) {
	if golisp.Length(args) < 2 {
		return nil, errors.New("defsubst expects at least name and arglist")
	}
	if golisp.NilP(golisp.Cddr(args)) {
		args = golisp.Append(args, golisp.ArrayToList([]*golisp.Data{golisp.EmptyCons()}))
	}
	return defunImpl(args, env)
}

func defmacroImpl(args *golisp.Data, env *golisp.SymbolTableFrame) (*golisp.Data, error) {
	name := golisp.Car(args)
	params := golisp.Cadr(args)
	body := golisp.Cddr(args)
	if !golisp.SymbolP(name) {
		return nil, fmt.Errorf("defmacro name must be a symbol, got %s", golisp.String(name))
	}
	var macroBody *golisp.Data
	switch golisp.Length(body) {
	case 0:
		macroBody = golisp.EmptyCons()
	case 1:
		macroBody = golisp.Car(body)
	default:
		macroBody = golisp.Cons(golisp.Intern("begin"), body)
	}
	m := golisp.MacroWithNameParamsBodyAndParent(golisp.StringValue(name), params, macroBody, env)
	_, err := env.BindLocallyTo(name, m)
	return m, err
}

func deffaceImpl(args *golisp.Data, env *golisp.SymbolTableFrame) (*golisp.Data, error) {
	name := golisp.Car(args)
	if !golisp.SymbolP(name) {
		return nil, fmt.Errorf("defface target must be a symbol, got %s", golisp.String(name))
	}
	if _, err := env.BindLocallyTo(name, name); err != nil {
		return nil, err
	}
	return name, nil
}

func defaliasImpl(args *golisp.Data, env *golisp.SymbolTableFrame) (*golisp.Data, error) {
	name := golisp.Car(args)
	if golisp.PairP(name) && golisp.StringValue(golisp.Car(name)) == "quote" {
		name = golisp.Cadr(name)
	}
	if !golisp.SymbolP(name) {
		return nil, fmt.Errorf("defalias target must be a symbol, got %s", golisp.String(name))
	}
	valueExpr := golisp.Cadr(args)
	if golisp.PairP(valueExpr) && golisp.StringValue(golisp.Car(valueExpr)) == "quote" {
		valueExpr = golisp.Cadr(valueExpr)
	}
	v, err := golisp.Eval(valueExpr, env)
	if err != nil {
		return nil, err
	}
	_, err = env.BindLocallyTo(name, v)
	return name, err
}

func defvarImpl(args *golisp.Data, env *golisp.SymbolTableFrame) (*golisp.Data, error) {
	name := golisp.Car(args)
	if !golisp.SymbolP(name) {
		return nil, fmt.Errorf("defvar target must be a symbol, got %s", golisp.String(name))
	}
	value := golisp.EmptyCons()
	if golisp.NotNilP(golisp.Cdr(args)) {
		v, err := golisp.Eval(golisp.Cadr(args), env)
		if err != nil {
			return nil, err
		}
		value = v
	}
	if _, err := env.BindLocallyTo(name, value); err != nil {
		return nil, err
	}
	return name, nil
}

func defvarKeymapImpl(args *golisp.Data, env *golisp.SymbolTableFrame) (*golisp.Data, error) {
	name := golisp.Car(args)
	if !golisp.SymbolP(name) {
		return nil, fmt.Errorf("defvar-keymap target must be a symbol, got %s", golisp.String(name))
	}
	km := newKeymap()
	full := false
	for c := golisp.Cdr(args); golisp.NotNilP(c); {
		k := golisp.Car(c)
		c = golisp.Cdr(c)
		if golisp.SymbolP(k) && strings.HasPrefix(golisp.StringValue(k), ":") {
			if golisp.StringValue(k) == ":full" && golisp.NotNilP(c) && golisp.NotNilP(golisp.Car(c)) {
				full = true
			}
			if golisp.NotNilP(c) {
				c = golisp.Cdr(c)
			}
			continue
		}
		if golisp.NilP(c) {
			break
		}
		v := golisp.Car(c)
		c = golisp.Cdr(c)
		key := keySpecString(k, env)
		if key == "" {
			continue
		}
		km.bindings[key] = v
	}
	if full {
		items := make([]*golisp.Data, 256)
		for i := range items {
			items[i] = golisp.EmptyCons()
		}
		km.fullMap = newElVector(items)
	}
	_, err := env.BindLocallyTo(name, keymapObject(km))
	return name, err
}

func newKeymap() *elKeymap {
	return &elKeymap{bindings: make(map[string]*golisp.Data)}
}

func keymapObject(km *elKeymap) *golisp.Data {
	return golisp.ObjectWithTypeAndValue("el-keymap", unsafe.Pointer(km))
}

func isKeymap(d *golisp.Data) bool {
	return golisp.ObjectP(d) && golisp.ObjectType(d) == "el-keymap"
}

func asKeymap(d *golisp.Data) *elKeymap {
	return (*elKeymap)(golisp.ObjectValue(d))
}

func keySpecString(d *golisp.Data, env *golisp.SymbolTableFrame) string {
	switch {
	case golisp.StringP(d):
		return golisp.StringValue(d)
	case golisp.IntegerP(d):
		n := int(golisp.IntegerValue(d))
		if n >= 32 && n <= 126 {
			return string(rune(n))
		}
		switch n {
		case 9:
			return "TAB"
		case 10, 13:
			return "RET"
		case 27:
			return "ESC"
		}
		return ""
	case golisp.SymbolP(d):
		if env != nil {
			if v := env.ValueOf(d); golisp.StringP(v) {
				return golisp.StringValue(v)
			}
		}
		switch golisp.StringValue(d) {
		case "tab":
			return "TAB"
		case "return":
			return "RET"
		case "escape":
			return "ESC"
		default:
			return golisp.StringValue(d)
		}
	case isElVector(d):
		vec := asElVector(d)
		if len(vec.items) == 0 {
			return ""
		}
		return keySpecString(vec.items[0], env)
	default:
		return ""
	}
}

func makeSparseKeymapImpl(_ *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	return keymapObject(newKeymap()), nil
}

func defineKeyImpl(args *golisp.Data, env *golisp.SymbolTableFrame) (*golisp.Data, error) {
	m := golisp.Car(args)
	var mSym *golisp.Data
	if golisp.SymbolP(m) {
		mSym = m
	} else if golisp.PairP(m) && golisp.SymbolP(golisp.Car(m)) && golisp.StringValue(golisp.Car(m)) == "quote" {
		q := golisp.Cadr(m)
		if golisp.SymbolP(q) {
			mSym = q
			m = q
		}
	}
	k := golisp.Cadr(args)
	def := golisp.Caddr(args)
	if golisp.SymbolP(m) {
		m = env.ValueOf(m)
	}
	if golisp.NilP(m) && mSym != nil {
		m = keymapObject(newKeymap())
		if _, err := env.BindTo(mSym, m); err != nil {
			if _, err2 := env.BindLocallyTo(mSym, m); err2 != nil {
				return nil, err2
			}
		}
	}
	if !isKeymap(m) {
		m = keymapObject(newKeymap())
		if mSym != nil {
			if _, err := env.BindTo(mSym, m); err != nil {
				_, _ = env.BindLocallyTo(mSym, m)
			}
		}
	}
	key := keySpecString(k, env)
	if key == "" {
		return nil, fmt.Errorf("define-key unsupported key spec: %s", golisp.String(k))
	}
	km := asKeymap(m)
	km.bindings[key] = def
	if km.fullMap != nil && len(key) == 1 {
		_, _ = asetImpl(golisp.ArrayToList([]*golisp.Data{
			km.fullMap,
			golisp.IntegerWithValue(int64(key[0])),
			def,
		}), env)
	}
	return def, nil
}

func keymapSetImpl(args *golisp.Data, env *golisp.SymbolTableFrame) (*golisp.Data, error) {
	return defineKeyImpl(args, env)
}

func obarrayMakeImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	n := max(golisp.IntegerValue(golisp.Car(args)), 0)
	items := make([]*golisp.Data, int(n))
	for i := range items {
		items[i] = golisp.EmptyCons()
	}
	return newElVector(items), nil
}

func expandFileNameImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	name := featureName(golisp.Car(args))
	if filepath.IsAbs(name) {
		return golisp.StringWithValue(filepath.Clean(name)), nil
	}
	base := ""
	if golisp.NotNilP(golisp.Cdr(args)) {
		base = featureName(golisp.Cadr(args))
	}
	if base == "" {
		home, _ := os.UserHomeDir()
		base = home
	}
	return golisp.StringWithValue(filepath.Clean(filepath.Join(base, name))), nil
}

func substituteInFileNameImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	s := featureName(golisp.Car(args))
	if strings.HasPrefix(s, "~") {
		if home, err := os.UserHomeDir(); err == nil {
			if s == "~" {
				s = home
			} else if after, ok := strings.CutPrefix(s, "~/"); ok {
				s = filepath.Join(home, after)
			}
		}
	}
	return golisp.StringWithValue(os.ExpandEnv(s)), nil
}

func executableFindImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	name := featureName(golisp.Car(args))
	if name == "" {
		return golisp.EmptyCons(), nil
	}
	p, err := exec.LookPath(name)
	if err != nil {
		// Emacs callers often guard with (or (executable-find ..) (error ..)).
		// Returning NAME keeps optional external tools from hard-failing startup.
		return golisp.StringWithValue(name), nil
	}
	return golisp.StringWithValue(p), nil
}

func locateUserEmacsFileImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	home, _ := os.UserHomeDir()
	root := filepath.Join(home, ".emacs.d")
	name := featureName(golisp.Car(args))
	if name == "" {
		return golisp.StringWithValue(root), nil
	}
	return golisp.StringWithValue(filepath.Join(root, name)), nil
}

func defineObsoleteFunctionAliasImpl(args *golisp.Data, env *golisp.SymbolTableFrame) (*golisp.Data, error) {
	return defaliasImpl(args, env)
}

func makeObsoleteVariableImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	// Emacs uses this for metadata/warnings; runtime behavior can be a no-op.
	return golisp.Car(args), nil
}

func makeObsoleteImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	// Compatibility no-op for obsolete warnings.
	return golisp.Car(args), nil
}

func copyFaceImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	return golisp.Car(args), nil
}

func currentTimeImpl(_ *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	return golisp.IntegerWithValue(time.Now().Unix()), nil
}

func timeConvertImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	// Minimal compatibility: pass through current-time tuples and numbers.
	return golisp.Car(args), nil
}

func timeEqualPImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	return golisp.BooleanWithValue(golisp.IsEqual(golisp.Car(args), golisp.Cadr(args))), nil
}

func currentTimeStringImpl(_ *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	return golisp.StringWithValue(time.Now().Format("Mon Jan _2 15:04:05 2006")), nil
}

func defineErrorImpl(args *golisp.Data, env *golisp.SymbolTableFrame) (*golisp.Data, error) {
	name := golisp.Car(args)
	if !golisp.SymbolP(name) {
		return nil, fmt.Errorf("define-error expects symbol, got %s", golisp.String(name))
	}
	parent := "error"
	if golisp.NotNilP(golisp.Cddr(args)) && golisp.SymbolP(golisp.Caddr(args)) {
		parent = golisp.StringValue(golisp.Caddr(args))
	}
	if rtGlobal != nil {
		rtGlobal.errorParents[golisp.StringValue(name)] = parent
	}
	_, _ = env.BindTo(name, name)
	return name, nil
}

func forceModeLineUpdateImpl(_ *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	return golisp.BooleanWithValue(true), nil
}

func fsetImpl(args *golisp.Data, env *golisp.SymbolTableFrame) (*golisp.Data, error) {
	sym := golisp.Car(args)
	if golisp.PairP(sym) && golisp.SymbolP(golisp.Car(sym)) && golisp.StringValue(golisp.Car(sym)) == "quote" {
		sym = golisp.Cadr(sym)
	}
	if !golisp.SymbolP(sym) {
		return nil, fmt.Errorf("fset expects symbol as first argument, got %s", golisp.String(sym))
	}
	valExpr := golisp.Cadr(args)
	if golisp.PairP(valExpr) && golisp.SymbolP(golisp.Car(valExpr)) && golisp.StringValue(golisp.Car(valExpr)) == "quote" {
		valExpr = golisp.Cadr(valExpr)
	}
	val, err := golisp.Eval(valExpr, env)
	if err != nil {
		return nil, err
	}
	if _, err := env.SetTo(sym, val); err != nil {
		if _, err2 := env.BindTo(sym, val); err2 != nil {
			return nil, err2
		}
	}
	return val, nil
}

func rplacaImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	cell := golisp.Car(args)
	val := golisp.Cadr(args)
	if !golisp.PairP(cell) {
		return nil, fmt.Errorf("rplaca expects cons cell, got %s", golisp.String(cell))
	}
	golisp.ConsValue(cell).Car = val
	return val, nil
}

func declareFunctionImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	if golisp.NotNilP(args) {
		return golisp.Car(args), nil
	}
	return golisp.EmptyCons(), nil
}

func frameHeightImpl(_ *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	return golisp.IntegerWithValue(40), nil
}

func frameWidthImpl(_ *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	return golisp.IntegerWithValue(120), nil
}

func windowHeightImpl(_ *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	return golisp.IntegerWithValue(40), nil
}

func windowWidthImpl(_ *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	return golisp.IntegerWithValue(120), nil
}

func charToStringImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	c := golisp.Car(args)
	if golisp.IntegerP(c) {
		return golisp.StringWithValue(string(rune(golisp.IntegerValue(c)))), nil
	}
	if golisp.StringP(c) {
		return c, nil
	}
	return golisp.StringWithValue(golisp.String(c)), nil
}

func stringToCharImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	s := featureName(golisp.Car(args))
	r := []rune(s)
	if len(r) == 0 {
		return golisp.IntegerWithValue(0), nil
	}
	return golisp.IntegerWithValue(int64(r[0])), nil
}

func minImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	best := golisp.Car(args)
	if !golisp.NumberP(best) {
		return nil, fmt.Errorf("min expects numbers, got %s", golisp.String(best))
	}
	bestF := float64(golisp.FloatValue(best))
	if golisp.IntegerP(best) {
		bestF = float64(golisp.IntegerValue(best))
	}
	allInt := golisp.IntegerP(best)
	for c := golisp.Cdr(args); golisp.NotNilP(c); c = golisp.Cdr(c) {
		v := golisp.Car(c)
		if !golisp.NumberP(v) {
			return nil, fmt.Errorf("min expects numbers, got %s", golisp.String(v))
		}
		f := float64(golisp.FloatValue(v))
		if golisp.IntegerP(v) {
			f = float64(golisp.IntegerValue(v))
		} else {
			allInt = false
		}
		if f < bestF {
			bestF = f
		}
	}
	if allInt {
		return golisp.IntegerWithValue(int64(bestF)), nil
	}
	return golisp.FloatWithValue(float32(bestF)), nil
}

func maxImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	best := golisp.Car(args)
	if !golisp.NumberP(best) {
		return nil, fmt.Errorf("max expects numbers, got %s", golisp.String(best))
	}
	bestF := float64(golisp.FloatValue(best))
	if golisp.IntegerP(best) {
		bestF = float64(golisp.IntegerValue(best))
	}
	allInt := golisp.IntegerP(best)
	for c := golisp.Cdr(args); golisp.NotNilP(c); c = golisp.Cdr(c) {
		v := golisp.Car(c)
		if !golisp.NumberP(v) {
			return nil, fmt.Errorf("max expects numbers, got %s", golisp.String(v))
		}
		f := float64(golisp.FloatValue(v))
		if golisp.IntegerP(v) {
			f = float64(golisp.IntegerValue(v))
		} else {
			allInt = false
		}
		if f > bestF {
			bestF = f
		}
	}
	if allInt {
		return golisp.IntegerWithValue(int64(bestF)), nil
	}
	return golisp.FloatWithValue(float32(bestF)), nil
}

func absImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	v := golisp.Car(args)
	switch {
	case golisp.IntegerP(v):
		n := golisp.IntegerValue(v)
		if n < 0 {
			n = -n
		}
		return golisp.IntegerWithValue(n), nil
	case golisp.FloatP(v):
		f := float64(golisp.FloatValue(v))
		if f < 0 {
			f = -f
		}
		return golisp.FloatWithValue(float32(f)), nil
	default:
		return golisp.IntegerWithValue(0), nil
	}
}

func floorImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	a := golisp.Car(args)
	num, ok := numberAsFloat(a)
	if !ok {
		return golisp.IntegerWithValue(0), nil
	}
	if golisp.NotNilP(golisp.Cdr(args)) {
		b := golisp.Cadr(args)
		den, ok := numberAsFloat(b)
		if !ok || den == 0 {
			return golisp.IntegerWithValue(0), nil
		}
		num = num / den
	}
	return golisp.IntegerWithValue(int64(math.Floor(num))), nil
}

func oddpImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	v := golisp.Car(args)
	if !golisp.IntegerP(v) {
		return golisp.BooleanWithValue(false), nil
	}
	return golisp.BooleanWithValue((golisp.IntegerValue(v) % 2) != 0), nil
}

func evenpImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	v := golisp.Car(args)
	if !golisp.IntegerP(v) {
		return golisp.BooleanWithValue(false), nil
	}
	return golisp.BooleanWithValue((golisp.IntegerValue(v) % 2) == 0), nil
}

func equalImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	return golisp.BooleanWithValue(golisp.IsEqual(golisp.Car(args), golisp.Cadr(args))), nil
}

func numberAsFloat(v *golisp.Data) (float64, bool) {
	switch {
	case golisp.IntegerP(v):
		return float64(golisp.IntegerValue(v)), true
	case golisp.FloatP(v):
		return float64(golisp.FloatValue(v)), true
	default:
		return 0, false
	}
}

func compareChain(args *golisp.Data, cmp func(a, b float64) bool) (*golisp.Data, error) {
	items := golisp.ToArray(args)
	if len(items) < 2 {
		return nil, fmt.Errorf("comparison expects at least 2 arguments")
	}
	prev, ok := numberAsFloat(items[0])
	if !ok {
		return golisp.BooleanWithValue(false), nil
	}
	for i := 1; i < len(items); i++ {
		cur, ok := numberAsFloat(items[i])
		if !ok {
			return golisp.BooleanWithValue(false), nil
		}
		if !cmp(prev, cur) {
			return golisp.BooleanWithValue(false), nil
		}
		prev = cur
	}
	return golisp.BooleanWithValue(true), nil
}

func lessImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	return compareChain(args, func(a, b float64) bool { return a < b })
}

func lessEqImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	return compareChain(args, func(a, b float64) bool { return a <= b })
}

func greaterImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	return compareChain(args, func(a, b float64) bool { return a > b })
}

func greaterEqImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	return compareChain(args, func(a, b float64) bool { return a >= b })
}

func setImpl(args *golisp.Data, env *golisp.SymbolTableFrame) (*golisp.Data, error) {
	s := golisp.Car(args)
	v := golisp.Cadr(args)
	if !golisp.SymbolP(s) {
		return nil, fmt.Errorf("set expects symbol as first argument, got %s", golisp.String(s))
	}
	if _, err := env.SetTo(s, v); err != nil {
		if _, err2 := env.BindTo(s, v); err2 != nil {
			return nil, err2
		}
	}
	return v, nil
}

func functionpImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	v := golisp.Car(args)
	return golisp.BooleanWithValue(golisp.FunctionOrPrimitiveP(v) || golisp.MacroP(v)), nil
}

func atomImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	return golisp.BooleanWithValue(!golisp.PairP(golisp.Car(args))), nil
}

func listpImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	v := golisp.Car(args)
	return golisp.BooleanWithValue(golisp.NilP(v) || golisp.ListP(v)), nil
}

func symbolpImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	return golisp.BooleanWithValue(golisp.SymbolP(golisp.Car(args))), nil
}

func internImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	name := featureName(golisp.Car(args))
	if name == "" {
		return golisp.EmptyCons(), nil
	}
	return golisp.Intern(name), nil
}

func symbolNameImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	s := golisp.Car(args)
	if golisp.SymbolP(s) {
		return golisp.StringWithValue(golisp.StringValue(s)), nil
	}
	return golisp.StringWithValue(golisp.String(s)), nil
}

func stringpImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	return golisp.BooleanWithValue(golisp.StringP(golisp.Car(args))), nil
}

func facepImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	v := golisp.Car(args)
	return golisp.BooleanWithValue(golisp.SymbolP(v) || golisp.StringP(v)), nil
}

func symbolValueImpl(args *golisp.Data, env *golisp.SymbolTableFrame) (*golisp.Data, error) {
	s := golisp.Car(args)
	if !golisp.SymbolP(s) {
		return nil, fmt.Errorf("symbol-value expects symbol, got %s", golisp.String(s))
	}
	return env.ValueOf(s), nil
}

func symbolFunctionImpl(args *golisp.Data, env *golisp.SymbolTableFrame) (*golisp.Data, error) {
	s := golisp.Car(args)
	if !golisp.SymbolP(s) {
		return golisp.EmptyCons(), nil
	}
	v := env.ValueOf(s)
	if golisp.FunctionOrPrimitiveP(v) || golisp.MacroP(v) {
		return v, nil
	}
	return golisp.EmptyCons(), nil
}

func internSoftImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	name := featureName(golisp.Car(args))
	if name == "" {
		return golisp.EmptyCons(), nil
	}
	return golisp.Intern(name), nil
}

func natnumpImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	v := golisp.Car(args)
	return golisp.BooleanWithValue(golisp.IntegerP(v) && golisp.IntegerValue(v) >= 0), nil
}

func regexpQuoteImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	return golisp.StringWithValue(regexp.QuoteMeta(featureName(golisp.Car(args)))), nil
}

func displayColorPImpl(_ *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	return golisp.BooleanWithValue(true), nil
}

func displayImagesPImpl(_ *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	return golisp.BooleanWithValue(false), nil
}

func frameVisiblePImpl(_ *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	return golisp.BooleanWithValue(true), nil
}

func visibleFrameListImpl(_ *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	return golisp.ArrayToList([]*golisp.Data{golisp.Intern("frame-0")}), nil
}

func selectedFrameImpl(_ *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	return golisp.Intern("frame-0"), nil
}

func frameSelectedWindowImpl(_ *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	return rtGlobal.selectedWindow().object, nil
}

func selectFrameImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	if golisp.NotNilP(args) {
		return golisp.Car(args), nil
	}
	return selectedFrameImpl(nil, nil)
}

func windowFrameImpl(_ *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	return golisp.Intern("frame-0"), nil
}

func frameParameterImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	param := featureName(golisp.Cadr(args))
	switch param {
	case "cursor-type":
		return golisp.Intern("box"), nil
	default:
		return golisp.EmptyCons(), nil
	}
}

func frameMonitorAttributesImpl(_ *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	// Minimal subset expected by gamegrid: geometry and workarea vectors.
	geom := golisp.ArrayToList([]*golisp.Data{
		golisp.IntegerWithValue(0), golisp.IntegerWithValue(0),
		golisp.IntegerWithValue(1024), golisp.IntegerWithValue(768),
	})
	work := golisp.ArrayToList([]*golisp.Data{
		golisp.IntegerWithValue(0), golisp.IntegerWithValue(0),
		golisp.IntegerWithValue(1024), golisp.IntegerWithValue(768),
	})
	return golisp.ArrayToList([]*golisp.Data{
		golisp.Cons(golisp.Intern("geometry"), geom),
		golisp.Cons(golisp.Intern("workarea"), work),
	}), nil
}

func windowBodyPixelEdgesImpl(_ *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	// left top right bottom
	return golisp.ArrayToList([]*golisp.Data{
		golisp.IntegerWithValue(0),
		golisp.IntegerWithValue(0),
		golisp.IntegerWithValue(1024),
		golisp.IntegerWithValue(768),
	}), nil
}

func linePixelHeightImpl(_ *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	return golisp.IntegerWithValue(1), nil
}

func makeStringImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	n := int(golisp.IntegerValue(golisp.Car(args)))
	fill := golisp.Cadr(args)
	if n < 0 {
		n = 0
	}
	ch := rune(0)
	if golisp.IntegerP(fill) {
		ch = rune(golisp.IntegerValue(fill))
	} else {
		s := featureName(fill)
		if s != "" {
			ch = []rune(s)[0]
		}
	}
	if ch == 0 {
		ch = ' '
	}
	items := make([]*golisp.Data, n)
	for i := 0; i < n; i++ {
		items[i] = golisp.IntegerWithValue(int64(ch))
	}
	return newElVector(items), nil
}

func mapcarImpl(args *golisp.Data, env *golisp.SymbolTableFrame) (*golisp.Data, error) {
	fn := golisp.Car(args)
	if golisp.PairP(fn) && golisp.SymbolP(golisp.Car(fn)) && golisp.StringValue(golisp.Car(fn)) == "quote" {
		fn = golisp.Cadr(fn)
	}
	seq := golisp.Cadr(args)
	out := make([]*golisp.Data, 0)
	var iterate *golisp.Data
	switch {
	case golisp.StringP(seq):
		rs := []rune(golisp.StringValue(seq))
		items := make([]*golisp.Data, 0, len(rs))
		for _, r := range rs {
			items = append(items, golisp.IntegerWithValue(int64(r)))
		}
		iterate = golisp.ArrayToList(items)
	case golisp.ListP(seq):
		iterate = seq
	case isElVector(seq):
		iterate = golisp.ArrayToList(asElVector(seq).items)
	default:
		return golisp.EmptyCons(), nil
	}
	for c := iterate; golisp.NotNilP(c); c = golisp.Cdr(c) {
		item := golisp.Car(c)
		call := golisp.ArrayToList([]*golisp.Data{fn, item})
		v, err := rtGlobal.funcallImpl(call, env)
		if err != nil {
			return nil, err
		}
		out = append(out, v)
	}
	return golisp.ArrayToList(out), nil
}

func mapcImpl(args *golisp.Data, env *golisp.SymbolTableFrame) (*golisp.Data, error) {
	_, err := mapcarImpl(args, env)
	if err != nil {
		return nil, err
	}
	return golisp.Cadr(args), nil
}

func nconcImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	acc := make([]*golisp.Data, 0)
	for c := args; golisp.NotNilP(c); c = golisp.Cdr(c) {
		v := golisp.Car(c)
		if golisp.ListP(v) {
			acc = append(acc, golisp.ToArray(v)...)
		}
	}
	return golisp.ArrayToList(acc), nil
}

func delqImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	item := golisp.Car(args)
	seq := golisp.Cadr(args)
	if !golisp.ListP(seq) {
		return golisp.EmptyCons(), nil
	}
	out := make([]*golisp.Data, 0)
	for c := seq; golisp.NotNilP(c); c = golisp.Cdr(c) {
		v := golisp.Car(c)
		if golisp.IsEqual(v, item) {
			continue
		}
		out = append(out, v)
	}
	return golisp.ArrayToList(out), nil
}

func splitStringImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	s := featureName(golisp.Car(args))
	sep := " "
	if golisp.NotNilP(golisp.Cdr(args)) {
		raw := featureName(golisp.Cadr(args))
		if raw != "" {
			sep = raw
		}
	}
	parts := strings.Split(s, sep)
	out := make([]*golisp.Data, 0, len(parts))
	for _, p := range parts {
		if p == "" {
			continue
		}
		out = append(out, golisp.StringWithValue(p))
	}
	return golisp.ArrayToList(out), nil
}

func mapconcatImpl(args *golisp.Data, env *golisp.SymbolTableFrame) (*golisp.Data, error) {
	fn := golisp.Car(args)
	seq := golisp.Cadr(args)
	sep := featureName(golisp.Caddr(args))
	call := golisp.ArrayToList([]*golisp.Data{fn, seq})
	mapped, err := mapcarImpl(call, env)
	if err != nil {
		return nil, err
	}
	parts := make([]string, 0)
	for c := mapped; golisp.NotNilP(c); c = golisp.Cdr(c) {
		parts = append(parts, featureName(golisp.Car(c)))
	}
	return golisp.StringWithValue(strings.Join(parts, sep)), nil
}

func downcaseImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	return golisp.StringWithValue(strings.ToLower(featureName(golisp.Car(args)))), nil
}

func capitalizeImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	s := []rune(strings.ToLower(featureName(golisp.Car(args))))
	inWord := false
	for i, r := range s {
		if (r >= 'a' && r <= 'z') || (r >= '0' && r <= '9') {
			if !inWord && r >= 'a' && r <= 'z' {
				s[i] = rune(r - 32)
			}
			inWord = true
		} else {
			inWord = false
		}
	}
	return golisp.StringWithValue(string(s)), nil
}

func prin1ToStringImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	return golisp.StringWithValue(golisp.String(golisp.Car(args))), nil
}

func makeSyntaxTableImpl(_ *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	return keymapObject(newKeymap()), nil
}

func modifySyntaxEntryImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	return golisp.Car(args), nil
}

func setTextPropertiesImpl(_ *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	return golisp.BooleanWithValue(true), nil
}

func setFaceBackgroundImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	return golisp.Cadr(args), nil
}

func insertImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	buf := rtGlobal.currentBuffer()
	if buf == nil {
		return golisp.EmptyCons(), nil
	}
	if buf.point < 0 {
		buf.point = 0
	}
	if buf.point > len(buf.text) {
		buf.point = len(buf.text)
	}
	var sb strings.Builder
	for c := args; golisp.NotNilP(c); c = golisp.Cdr(c) {
		v := golisp.Car(c)
		switch {
		case golisp.IntegerP(v):
			sb.WriteRune(rune(golisp.IntegerValue(v)))
		case golisp.StringP(v), golisp.SymbolP(v):
			sb.WriteString(golisp.StringValue(v))
		default:
			sb.WriteString(golisp.String(v))
		}
	}
	rs := []rune(sb.String())
	if len(rs) == 0 {
		return golisp.EmptyCons(), nil
	}
	left := append([]rune{}, buf.text[:buf.point]...)
	right := append([]rune{}, buf.text[buf.point:]...)
	buf.text = append(left, append(rs, right...)...)
	buf.point += len(rs)
	return golisp.EmptyCons(), nil
}

func insertFileContentsImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	path := featureName(golisp.Car(args))
	data, err := os.ReadFile(path)
	if err != nil {
		return golisp.EmptyCons(), nil
	}
	_, _ = insertImpl(golisp.ArrayToList([]*golisp.Data{golisp.StringWithValue(string(data))}), nil)
	return golisp.ArrayToList([]*golisp.Data{
		golisp.StringWithValue(path),
		golisp.IntegerWithValue(int64(len(data))),
	}), nil
}

func insertCharImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	chv := golisp.Car(args)
	n := 1
	if golisp.NotNilP(golisp.Cdr(args)) && golisp.IntegerP(golisp.Cadr(args)) {
		n = int(golisp.IntegerValue(golisp.Cadr(args)))
	}
	if n < 0 {
		n = 0
	}
	ch := rune(0)
	if golisp.IntegerP(chv) {
		ch = rune(golisp.IntegerValue(chv))
	} else {
		s := featureName(chv)
		if s != "" {
			ch = []rune(s)[0]
		}
	}
	if ch == 0 {
		ch = ' '
	}
	callArgs := make([]*golisp.Data, 0, n)
	for i := 0; i < n; i++ {
		callArgs = append(callArgs, golisp.IntegerWithValue(int64(ch)))
	}
	return insertImpl(golisp.ArrayToList(callArgs), nil)
}

func eraseBufferImpl(_ *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	buf := rtGlobal.currentBuffer()
	if buf != nil {
		buf.text = nil
		buf.point = 0
	}
	return golisp.EmptyCons(), nil
}

func deleteBlankLinesImpl(_ *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	buf := rtGlobal.currentBuffer()
	if buf == nil || len(buf.text) == 0 {
		return golisp.EmptyCons(), nil
	}
	lines := strings.Split(string(buf.text), "\n")
	out := make([]string, 0, len(lines))
	for _, ln := range lines {
		if strings.TrimSpace(ln) == "" {
			continue
		}
		out = append(out, ln)
	}
	buf.text = []rune(strings.Join(out, "\n"))
	if buf.point > len(buf.text) {
		buf.point = len(buf.text)
	}
	return golisp.EmptyCons(), nil
}

func fileReadablePImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	path := featureName(golisp.Car(args))
	_, err := os.Stat(path)
	return golisp.BooleanWithValue(err == nil), nil
}

func fileExistsPImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	path := featureName(golisp.Car(args))
	_, err := os.Stat(path)
	return golisp.BooleanWithValue(err == nil), nil
}

func fileAttributesImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	path := featureName(golisp.Car(args))
	st, err := os.Stat(path)
	if err != nil {
		return golisp.EmptyCons(), nil
	}
	mtime := golisp.IntegerWithValue(st.ModTime().Unix())
	// Minimal shape compatible with file-attribute-modification-time (slot 5).
	return golisp.ArrayToList([]*golisp.Data{
		golisp.EmptyCons(),
		golisp.IntegerWithValue(1),
		golisp.IntegerWithValue(1),
		golisp.IntegerWithValue(0),
		golisp.IntegerWithValue(st.Size()),
		mtime,
		golisp.IntegerWithValue(0),
		golisp.EmptyCons(),
		golisp.IntegerWithValue(int64(st.Mode().Perm())),
		golisp.EmptyCons(),
		golisp.IntegerWithValue(0),
		golisp.IntegerWithValue(0),
	}), nil
}

func fileAttributeModificationTimeImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	attrs := golisp.Car(args)
	// If file-attributes returns a list, Emacs stores mtime around slot 5.
	if golisp.ListP(attrs) {
		cur := attrs
		for i := 0; i < 5 && golisp.NotNilP(cur); i++ {
			cur = golisp.Cdr(cur)
		}
		if golisp.NotNilP(cur) {
			return golisp.Car(cur), nil
		}
	}
	return currentTimeImpl(nil, nil)
}

func bufferLivePImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	b := golisp.Car(args)
	ok := golisp.ObjectP(b) && golisp.ObjectType(b) == "el-buffer"
	return golisp.BooleanWithValue(ok), nil
}

func getBufferCreateImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	name := featureName(golisp.Car(args))
	return rtGlobal.ensureBuffer(name).object, nil
}

func getScratchBufferCreateImpl(_ *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	return rtGlobal.ensureBuffer("*scratch*").object, nil
}

func getBufferImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	name := featureName(golisp.Car(args))
	if b, ok := rtGlobal.buffers[name]; ok {
		return b.object, nil
	}
	return golisp.EmptyCons(), nil
}

func bufferNameImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	if golisp.NilP(args) {
		return golisp.StringWithValue(rtGlobal.currentBuffer().name), nil
	}
	return golisp.StringWithValue(bufferNameFromArg(golisp.Car(args))), nil
}

func bufferLocalValueImpl(args *golisp.Data, env *golisp.SymbolTableFrame) (*golisp.Data, error) {
	sym := golisp.Car(args)
	if !golisp.SymbolP(sym) {
		return golisp.EmptyCons(), nil
	}
	return env.ValueOf(sym), nil
}

func pointImpl(_ *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	buf := rtGlobal.currentBuffer()
	if buf == nil {
		return golisp.IntegerWithValue(1), nil
	}
	return golisp.IntegerWithValue(int64(buf.point + 1)), nil
}

func setWindowStartImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	return golisp.Cadr(args), nil
}

func setWindowPointImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	p := golisp.Cadr(args)
	if golisp.IntegerP(p) {
		buf := rtGlobal.currentBuffer()
		if buf != nil {
			n := min(max(int(golisp.IntegerValue(p))-1, 0), len(buf.text))
			buf.point = n
		}
	}
	return p, nil
}

func windowStartImpl(_ *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	return golisp.IntegerWithValue(1), nil
}

func windowEndImpl(_ *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	buf := rtGlobal.currentBuffer()
	if buf == nil {
		return golisp.IntegerWithValue(1), nil
	}
	return golisp.IntegerWithValue(int64(len(buf.text) + 1)), nil
}

func windowPointImpl(_ *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	buf := rtGlobal.currentBuffer()
	if buf == nil {
		return golisp.IntegerWithValue(1), nil
	}
	return golisp.IntegerWithValue(int64(buf.point + 1)), nil
}

func pointMinImpl(_ *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	return golisp.IntegerWithValue(1), nil
}

func pointMaxImpl(_ *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	buf := rtGlobal.currentBuffer()
	if buf == nil {
		return golisp.IntegerWithValue(1), nil
	}
	return golisp.IntegerWithValue(int64(len(buf.text) + 1)), nil
}

func followingCharImpl(_ *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	buf := rtGlobal.currentBuffer()
	if buf == nil || buf.point >= len(buf.text) {
		return golisp.IntegerWithValue(0), nil
	}
	return golisp.IntegerWithValue(int64(buf.text[buf.point])), nil
}

func charAfterImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	buf := rtGlobal.currentBuffer()
	if buf == nil {
		return golisp.IntegerWithValue(0), nil
	}
	p := buf.point
	if golisp.NotNilP(args) && golisp.IntegerP(golisp.Car(args)) {
		p = int(golisp.IntegerValue(golisp.Car(args))) - 1
	}
	if p < 0 || p >= len(buf.text) {
		return golisp.IntegerWithValue(0), nil
	}
	return golisp.IntegerWithValue(int64(buf.text[p])), nil
}

func precedingCharImpl(_ *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	buf := rtGlobal.currentBuffer()
	if buf == nil || buf.point <= 0 || buf.point-1 >= len(buf.text) {
		return golisp.IntegerWithValue(0), nil
	}
	return golisp.IntegerWithValue(int64(buf.text[buf.point-1])), nil
}

func eobpImpl(_ *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	buf := rtGlobal.currentBuffer()
	if buf == nil {
		return golisp.BooleanWithValue(true), nil
	}
	return golisp.BooleanWithValue(buf.point >= len(buf.text)), nil
}

func forwardLineImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	buf := rtGlobal.currentBuffer()
	if buf == nil {
		return golisp.IntegerWithValue(0), nil
	}
	n := 1
	if golisp.NotNilP(args) && golisp.IntegerP(golisp.Car(args)) {
		n = int(golisp.IntegerValue(golisp.Car(args)))
	}
	if n == 0 {
		return golisp.IntegerWithValue(0), nil
	}
	lineStart := buf.point
	for lineStart > 0 && buf.text[lineStart-1] != '\n' {
		lineStart--
	}
	col := buf.point - lineStart
	moveOne := func(dir int) bool {
		if dir > 0 {
			i := buf.point
			for i < len(buf.text) && buf.text[i] != '\n' {
				i++
			}
			if i >= len(buf.text) {
				buf.point = len(buf.text)
				return false
			}
			i++
			j := i
			for j < len(buf.text) && buf.text[j] != '\n' && (j-i) < col {
				j++
			}
			buf.point = j
			return true
		}
		i := buf.point
		for i > 0 && buf.text[i-1] != '\n' {
			i--
		}
		if i == 0 {
			buf.point = 0
			return false
		}
		i--
		for i > 0 && buf.text[i-1] != '\n' {
			i--
		}
		j := i
		for j < len(buf.text) && buf.text[j] != '\n' && (j-i) < col {
			j++
		}
		buf.point = j
		return true
	}
	remaining := 0
	if n > 0 {
		for k := 0; k < n; k++ {
			if !moveOne(1) {
				remaining = n - k
				break
			}
		}
	} else {
		for k := 0; k < -n; k++ {
			if !moveOne(-1) {
				remaining = -n - k
				break
			}
		}
	}
	return golisp.IntegerWithValue(int64(remaining)), nil
}

func beginningOfLineImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	buf := rtGlobal.currentBuffer()
	if buf == nil {
		return golisp.IntegerWithValue(1), nil
	}
	n := 1
	if golisp.NotNilP(args) && golisp.IntegerP(golisp.Car(args)) {
		n = int(golisp.IntegerValue(golisp.Car(args)))
	}
	if n != 1 {
		_, _ = forwardLineImpl(golisp.ArrayToList([]*golisp.Data{golisp.IntegerWithValue(int64(n - 1))}), nil)
	}
	for buf.point > 0 && buf.text[buf.point-1] != '\n' {
		buf.point--
	}
	return golisp.IntegerWithValue(int64(buf.point + 1)), nil
}

func forwardCharImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	buf := rtGlobal.currentBuffer()
	if buf == nil {
		return golisp.IntegerWithValue(1), nil
	}
	n := 1
	if golisp.NotNilP(args) && golisp.IntegerP(golisp.Car(args)) {
		n = int(golisp.IntegerValue(golisp.Car(args)))
	}
	buf.point += n
	if buf.point < 0 {
		buf.point = 0
	}
	if buf.point > len(buf.text) {
		buf.point = len(buf.text)
	}
	return golisp.IntegerWithValue(int64(buf.point + 1)), nil
}

func endOfLineImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	buf := rtGlobal.currentBuffer()
	if buf == nil {
		return golisp.IntegerWithValue(1), nil
	}
	n := 1
	if golisp.NotNilP(args) && golisp.IntegerP(golisp.Car(args)) {
		n = int(golisp.IntegerValue(golisp.Car(args)))
	}
	if n != 1 {
		_, _ = forwardLineImpl(golisp.ArrayToList([]*golisp.Data{golisp.IntegerWithValue(int64(n - 1))}), nil)
	}
	for buf.point < len(buf.text) && buf.text[buf.point] != '\n' {
		buf.point++
	}
	return golisp.IntegerWithValue(int64(buf.point + 1)), nil
}

func backwardCharImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	buf := rtGlobal.currentBuffer()
	if buf == nil {
		return golisp.IntegerWithValue(1), nil
	}
	n := 1
	if golisp.NotNilP(args) && golisp.IntegerP(golisp.Car(args)) {
		n = int(golisp.IntegerValue(golisp.Car(args)))
	}
	buf.point -= n
	if buf.point < 0 {
		buf.point = 0
	}
	if buf.point > len(buf.text) {
		buf.point = len(buf.text)
	}
	return golisp.IntegerWithValue(int64(buf.point + 1)), nil
}

func countLinesImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	buf := rtGlobal.currentBuffer()
	if buf == nil {
		return golisp.IntegerWithValue(0), nil
	}
	s := int(golisp.IntegerValue(golisp.Car(args))) - 1
	e := int(golisp.IntegerValue(golisp.Cadr(args))) - 1
	if s < 0 {
		s = 0
	}
	if e < 0 {
		e = 0
	}
	if s > len(buf.text) {
		s = len(buf.text)
	}
	if e > len(buf.text) {
		e = len(buf.text)
	}
	if s > e {
		s, e = e, s
	}
	c := 0
	for i := s; i < e && i < len(buf.text); i++ {
		if buf.text[i] == '\n' {
			c++
		}
	}
	return golisp.IntegerWithValue(int64(c)), nil
}

func lookingAtImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	buf := rtGlobal.currentBuffer()
	if buf == nil {
		return golisp.BooleanWithValue(false), nil
	}
	pat := featureName(golisp.Car(args))
	re, err := regexp.Compile(pat)
	if err != nil {
		rtGlobal.clearMatchData()
		return golisp.BooleanWithValue(false), nil
	}
	if buf.point < 0 {
		buf.point = 0
	}
	if buf.point > len(buf.text) {
		buf.point = len(buf.text)
	}
	segment := string(buf.text[buf.point:])
	m := re.FindStringSubmatchIndex(segment)
	if m != nil && m[0] == 0 {
		rtGlobal.setBufferMatchData(buf, segment, buf.point, m)
		return golisp.BooleanWithValue(true), nil
	}
	rtGlobal.clearMatchData()
	return golisp.BooleanWithValue(false), nil
}

func searchBackwardImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	buf := rtGlobal.currentBuffer()
	if buf == nil {
		return golisp.EmptyCons(), nil
	}
	needle := featureName(golisp.Car(args))
	if needle == "" {
		return golisp.IntegerWithValue(int64(buf.point + 1)), nil
	}
	limit := 0
	if golisp.NotNilP(golisp.Cdr(args)) && golisp.IntegerP(golisp.Cadr(args)) {
		limit = max(int(golisp.IntegerValue(golisp.Cadr(args)))-1, 0)
	}
	segment := string(buf.text)
	if buf.point > len(buf.text) {
		buf.point = len(buf.text)
	}
	seg := segment[limit:buf.point]
	idx := strings.LastIndex(seg, needle)
	if idx < 0 {
		rtGlobal.clearMatchData()
		return golisp.EmptyCons(), nil
	}
	rtGlobal.matchData = []int{limit + idx + 1, limit + idx + len([]rune(needle)) + 1}
	rtGlobal.matchInString = false
	rtGlobal.matchString = ""
	rtGlobal.matchBuffer = buf
	buf.point = limit + idx
	return golisp.IntegerWithValue(int64(buf.point + 1)), nil
}

func searchForwardImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	buf := rtGlobal.currentBuffer()
	if buf == nil {
		return golisp.EmptyCons(), nil
	}
	needle := featureName(golisp.Car(args))
	if needle == "" {
		return golisp.IntegerWithValue(int64(buf.point + 1)), nil
	}
	limit := len(buf.text)
	if golisp.NotNilP(golisp.Cdr(args)) && golisp.IntegerP(golisp.Cadr(args)) {
		limit = min(max(int(golisp.IntegerValue(golisp.Cadr(args)))-1, 0), len(buf.text))
	}
	if buf.point < 0 {
		buf.point = 0
	}
	if buf.point > len(buf.text) {
		buf.point = len(buf.text)
	}
	seg := string(buf.text[buf.point:limit])
	idx := strings.Index(seg, needle)
	if idx < 0 {
		rtGlobal.clearMatchData()
		return golisp.EmptyCons(), nil
	}
	start := buf.point + idx
	end := start + len([]rune(needle))
	rtGlobal.matchData = []int{start + 1, end + 1}
	rtGlobal.matchInString = false
	rtGlobal.matchString = ""
	rtGlobal.matchBuffer = buf
	buf.point = buf.point + idx + len([]rune(needle))
	return golisp.IntegerWithValue(int64(buf.point + 1)), nil
}

func searchForwardRegexpImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	buf := rtGlobal.currentBuffer()
	if buf == nil {
		return golisp.EmptyCons(), nil
	}
	pat := featureName(golisp.Car(args))
	limit := len(buf.text)
	if golisp.NotNilP(golisp.Cdr(args)) && golisp.IntegerP(golisp.Cadr(args)) {
		limit = min(max(int(golisp.IntegerValue(golisp.Cadr(args)))-1, 0), len(buf.text))
	}
	if buf.point < 0 {
		buf.point = 0
	}
	if buf.point > len(buf.text) {
		buf.point = len(buf.text)
	}
	re, err := regexp.Compile(pat)
	if err != nil {
		rtGlobal.clearMatchData()
		return golisp.EmptyCons(), nil
	}
	seg := string(buf.text[buf.point:limit])
	loc := re.FindStringSubmatchIndex(seg)
	if loc == nil {
		rtGlobal.clearMatchData()
		return golisp.EmptyCons(), nil
	}
	rtGlobal.setBufferMatchData(buf, seg, buf.point, loc)
	buf.point = buf.point + loc[1]
	return golisp.IntegerWithValue(int64(buf.point + 1)), nil
}

func skipCharsForwardImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	buf := rtGlobal.currentBuffer()
	if buf == nil {
		return golisp.IntegerWithValue(0), nil
	}
	set := featureName(golisp.Car(args))
	limit := len(buf.text)
	if golisp.NotNilP(golisp.Cdr(args)) && golisp.IntegerP(golisp.Cadr(args)) {
		limit = min(max(int(golisp.IntegerValue(golisp.Cadr(args)))-1, 0), len(buf.text))
	}
	allowed := make(map[rune]bool, len(set))
	for _, r := range set {
		allowed[r] = true
	}
	start := buf.point
	for buf.point < limit {
		r := buf.text[buf.point]
		if !allowed[r] {
			break
		}
		buf.point++
	}
	return golisp.IntegerWithValue(int64(buf.point - start)), nil
}

func substCharInRegionImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	buf := rtGlobal.currentBuffer()
	if buf == nil {
		return golisp.EmptyCons(), nil
	}
	start := int(golisp.IntegerValue(golisp.Car(args))) - 1
	end := int(golisp.IntegerValue(golisp.Cadr(args))) - 1
	oldCh := rune(golisp.IntegerValue(golisp.Caddr(args)))
	newCh := rune(golisp.IntegerValue(golisp.Car(golisp.Cdddr(args))))
	if start < 0 {
		start = 0
	}
	if end < start {
		end = start
	}
	if end > len(buf.text) {
		end = len(buf.text)
	}
	changed := int64(0)
	for i := start; i < end; i++ {
		if buf.text[i] == oldCh {
			buf.text[i] = newCh
			changed++
		}
	}
	return golisp.IntegerWithValue(changed), nil
}

func bolpImpl(_ *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	buf := rtGlobal.currentBuffer()
	if buf == nil || buf.point <= 0 {
		return golisp.BooleanWithValue(true), nil
	}
	return golisp.BooleanWithValue(buf.text[buf.point-1] == '\n'), nil
}

func eolpImpl(_ *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	buf := rtGlobal.currentBuffer()
	if buf == nil || buf.point >= len(buf.text) {
		return golisp.BooleanWithValue(true), nil
	}
	return golisp.BooleanWithValue(buf.text[buf.point] == '\n'), nil
}

func currentColumnImpl(_ *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	buf := rtGlobal.currentBuffer()
	if buf == nil || buf.point <= 0 {
		return golisp.IntegerWithValue(0), nil
	}
	col := 0
	for i := buf.point - 1; i >= 0; i-- {
		if buf.text[i] == '\n' {
			break
		}
		col++
	}
	return golisp.IntegerWithValue(int64(col)), nil
}

func verticalMotionImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	lines := 0
	if golisp.NotNilP(args) && golisp.IntegerP(golisp.Car(args)) {
		lines = int(golisp.IntegerValue(golisp.Car(args)))
	}
	remaining, err := forwardLineImpl(golisp.ArrayToList([]*golisp.Data{
		golisp.IntegerWithValue(int64(lines)),
	}), nil)
	if err != nil {
		return nil, err
	}
	return remaining, nil
}

func gotoCharImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	buf := rtGlobal.currentBuffer()
	if buf == nil {
		return golisp.IntegerWithValue(1), nil
	}
	p := min(max(int(golisp.IntegerValue(golisp.Car(args)))-1, 0), len(buf.text))
	buf.point = p
	return golisp.IntegerWithValue(int64(buf.point + 1)), nil
}

func lineEndPositionImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	buf := rtGlobal.currentBuffer()
	if buf == nil {
		return golisp.IntegerWithValue(1), nil
	}
	orig := buf.point
	n := 1
	if golisp.NotNilP(args) && golisp.IntegerP(golisp.Car(args)) {
		n = int(golisp.IntegerValue(golisp.Car(args)))
	}
	if n != 1 {
		_, _ = forwardLineImpl(golisp.ArrayToList([]*golisp.Data{golisp.IntegerWithValue(int64(n - 1))}), nil)
	}
	p := buf.point
	for p < len(buf.text) && buf.text[p] != '\n' {
		p++
	}
	buf.point = orig
	return golisp.IntegerWithValue(int64(p + 1)), nil
}

func nextSinglePropertyChangeImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	pos := int64(1)
	if golisp.IntegerP(golisp.Car(args)) {
		pos = golisp.IntegerValue(golisp.Car(args))
	}
	if golisp.NotNilP(golisp.Cdddr(args)) && golisp.IntegerP(golisp.Car(golisp.Cdddr(args))) {
		return golisp.Car(golisp.Cdddr(args)), nil
	}
	buf := rtGlobal.currentBuffer()
	limit := int64(1)
	if buf != nil {
		limit = int64(len(buf.text) + 1)
	}
	if pos < limit {
		return golisp.IntegerWithValue(pos + 1), nil
	}
	return golisp.IntegerWithValue(limit), nil
}

func deleteRegionImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	buf := rtGlobal.currentBuffer()
	if buf == nil {
		return golisp.EmptyCons(), nil
	}
	start := int(golisp.IntegerValue(golisp.Car(args))) - 1
	end := int(golisp.IntegerValue(golisp.Cadr(args))) - 1
	if start > end {
		start, end = end, start
	}
	if start < 0 {
		start = 0
	}
	if end < 0 {
		end = 0
	}
	if start > len(buf.text) {
		start = len(buf.text)
	}
	if end > len(buf.text) {
		end = len(buf.text)
	}
	if start < end {
		buf.text = append(append([]rune{}, buf.text[:start]...), buf.text[end:]...)
		if buf.point > end {
			buf.point -= end - start
		} else if buf.point > start {
			buf.point = start
		}
	}
	if buf.point < 0 {
		buf.point = 0
	}
	if buf.point > len(buf.text) {
		buf.point = len(buf.text)
	}
	return golisp.EmptyCons(), nil
}

func deleteCharImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	buf := rtGlobal.currentBuffer()
	if buf == nil {
		return golisp.EmptyCons(), nil
	}
	n := 1
	if golisp.NotNilP(args) && golisp.IntegerP(golisp.Car(args)) {
		n = int(golisp.IntegerValue(golisp.Car(args)))
	}
	if n == 0 {
		return golisp.EmptyCons(), nil
	}
	if n > 0 {
		start := buf.point
		end := min(start+n, len(buf.text))
		if start < 0 {
			start = 0
		}
		if start < end {
			buf.text = append(append([]rune{}, buf.text[:start]...), buf.text[end:]...)
		}
		return golisp.EmptyCons(), nil
	}
	n = -n
	start := buf.point - n
	end := buf.point
	if start < 0 {
		start = 0
	}
	if end > len(buf.text) {
		end = len(buf.text)
	}
	if start < end {
		buf.text = append(append([]rune{}, buf.text[:start]...), buf.text[end:]...)
		buf.point = start
	}
	return golisp.EmptyCons(), nil
}

func backwardWordImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	buf := rtGlobal.currentBuffer()
	if buf == nil {
		return golisp.IntegerWithValue(1), nil
	}
	n := 1
	if golisp.NotNilP(args) && golisp.IntegerP(golisp.Car(args)) {
		n = int(golisp.IntegerValue(golisp.Car(args)))
	}
	if n < 0 {
		n = 0
	}
	for k := 0; k < n; k++ {
		for buf.point > 0 && !isWordRune(buf.text[buf.point-1]) {
			buf.point--
		}
		for buf.point > 0 && isWordRune(buf.text[buf.point-1]) {
			buf.point--
		}
	}
	return golisp.IntegerWithValue(int64(buf.point + 1)), nil
}

func insertRectangleImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	rect := golisp.Car(args)
	lines := []string{}
	switch {
	case golisp.ListP(rect):
		for c := rect; golisp.NotNilP(c); c = golisp.Cdr(c) {
			lines = append(lines, featureName(golisp.Car(c)))
		}
	case isElVector(rect):
		for _, it := range asElVector(rect).items {
			lines = append(lines, featureName(it))
		}
	default:
		lines = append(lines, featureName(rect))
	}
	for i, ln := range lines {
		_, _ = insertImpl(golisp.ArrayToList([]*golisp.Data{golisp.StringWithValue(ln)}), nil)
		if i != len(lines)-1 {
			_, _ = insertImpl(golisp.ArrayToList([]*golisp.Data{golisp.IntegerWithValue('\n')}), nil)
		}
	}
	return golisp.EmptyCons(), nil
}

func newlineImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	n := 1
	if golisp.NotNilP(args) && golisp.IntegerP(golisp.Car(args)) {
		n = int(golisp.IntegerValue(golisp.Car(args)))
	}
	if n < 0 {
		n = 0
	}
	callArgs := make([]*golisp.Data, 0, n)
	for i := 0; i < n; i++ {
		callArgs = append(callArgs, golisp.IntegerWithValue('\n'))
	}
	return insertImpl(golisp.ArrayToList(callArgs), nil)
}

func moveToColumnImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	buf := rtGlobal.currentBuffer()
	if buf == nil {
		return golisp.IntegerWithValue(0), nil
	}
	col := max(int(golisp.IntegerValue(golisp.Car(args))), 0)
	lineStart := buf.point
	for lineStart > 0 && buf.text[lineStart-1] != '\n' {
		lineStart--
	}
	lineEnd := lineStart
	for lineEnd < len(buf.text) && buf.text[lineEnd] != '\n' {
		lineEnd++
	}
	newPoint := min(lineStart+col, lineEnd)
	buf.point = newPoint
	return golisp.IntegerWithValue(int64(buf.point - lineStart)), nil
}

func indentToImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	buf := rtGlobal.currentBuffer()
	if buf == nil {
		return golisp.IntegerWithValue(0), nil
	}
	target := max(int(golisp.IntegerValue(golisp.Car(args))), 0)
	col := 0
	for i := buf.point - 1; i >= 0; i-- {
		if buf.text[i] == '\n' {
			break
		}
		col++
	}
	if col >= target {
		return golisp.IntegerWithValue(int64(col)), nil
	}
	spaces := target - col
	insert := strings.Repeat(" ", spaces)
	_, _ = insertImpl(golisp.ArrayToList([]*golisp.Data{golisp.StringWithValue(insert)}), nil)
	return golisp.IntegerWithValue(int64(target)), nil
}

func yesImpl(_ *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	return golisp.BooleanWithValue(true), nil
}

func nilBoolImpl(_ *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	return golisp.BooleanWithValue(false), nil
}

func nilValueImpl(_ *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	return golisp.EmptyCons(), nil
}

func primitiveUndoImpl(_ *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	// Undo is not modeled in this runtime; return nil so callers can terminate
	// undo walks safely.
	return golisp.EmptyCons(), nil
}

func stringEqualImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	a := featureName(golisp.Car(args))
	b := featureName(golisp.Cadr(args))
	return golisp.BooleanWithValue(a == b), nil
}

func stringMatchPImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	pat := featureName(golisp.Car(args))
	s := featureName(golisp.Cadr(args))
	start := 0
	if golisp.NotNilP(golisp.Cddr(args)) && golisp.IntegerP(golisp.Caddr(args)) {
		start = int(golisp.IntegerValue(golisp.Caddr(args)))
	}
	if start < 0 {
		start = 0
	}
	rs := []rune(s)
	if start > len(rs) {
		start = len(rs)
	}
	re, err := regexp.Compile(pat)
	if err != nil {
		rtGlobal.clearMatchData()
		return golisp.EmptyCons(), nil
	}
	segment := string(rs[start:])
	loc := re.FindStringSubmatchIndex(segment)
	if loc == nil {
		rtGlobal.clearMatchData()
		return golisp.EmptyCons(), nil
	}
	rtGlobal.setStringMatchData(segment, start, loc)
	return golisp.IntegerWithValue(int64(rtGlobal.matchData[0])), nil
}

func stringMatchImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	return stringMatchPImpl(args, nil)
}

func stringSuffixPImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	suf := featureName(golisp.Car(args))
	s := featureName(golisp.Cadr(args))
	ignoreCase := false
	if golisp.NotNilP(golisp.Cddr(args)) {
		ignoreCase = golisp.BooleanValue(golisp.Caddr(args))
	}
	if ignoreCase {
		suf = strings.ToLower(suf)
		s = strings.ToLower(s)
	}
	return golisp.BooleanWithValue(strings.HasSuffix(s, suf)), nil
}

func copySequenceImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	v := golisp.Car(args)
	switch {
	case golisp.StringP(v):
		return golisp.StringWithValue(golisp.StringValue(v)), nil
	case golisp.ListP(v):
		items := golisp.ToArray(v)
		cp := make([]*golisp.Data, len(items))
		copy(cp, items)
		return golisp.ArrayToList(cp), nil
	case isElVector(v):
		items := asElVector(v).items
		cp := make([]*golisp.Data, len(items))
		copy(cp, items)
		return newElVector(cp), nil
	default:
		return v, nil
	}
}

func expandReplacementTemplate(template string, matched []string) string {
	var b strings.Builder
	for i := 0; i < len(template); i++ {
		ch := template[i]
		if ch != '\\' || i+1 >= len(template) {
			b.WriteByte(ch)
			continue
		}
		i++
		switch template[i] {
		case '&':
			if len(matched) > 0 {
				b.WriteString(matched[0])
			}
		case '\\':
			b.WriteByte('\\')
		default:
			if template[i] >= '0' && template[i] <= '9' {
				idx := int(template[i] - '0')
				if idx >= 0 && idx < len(matched) {
					b.WriteString(matched[idx])
				}
			} else {
				b.WriteByte(template[i])
			}
		}
	}
	return b.String()
}

func replaceMatchImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	repl := featureName(golisp.Car(args))
	literal := false
	if golisp.NotNilP(golisp.Cddr(args)) {
		literal = golisp.BooleanValue(golisp.Caddr(args))
	}
	subexp := 0
	rest4 := golisp.Cdr(golisp.Cdr(golisp.Cdr(golisp.Cdr(args))))
	if golisp.NotNilP(rest4) && golisp.IntegerP(golisp.Car(rest4)) {
		subexp = int(golisp.IntegerValue(golisp.Car(rest4)))
	}
	if len(rtGlobal.matchData) < 2 {
		return golisp.StringWithValue(repl), nil
	}
	pairIdx := subexp * 2
	if pairIdx+1 >= len(rtGlobal.matchData) {
		return golisp.StringWithValue(repl), nil
	}
	start := rtGlobal.matchData[pairIdx]
	end := rtGlobal.matchData[pairIdx+1]
	if start < 0 || end < 0 {
		return golisp.StringWithValue(repl), nil
	}

	if golisp.Length(args) >= 4 && golisp.StringP(golisp.Car(golisp.Cdddr(args))) {
		s := golisp.StringValue(golisp.Car(golisp.Cdddr(args)))
		rs := []rune(s)
		if start < 0 {
			start = 0
		}
		if end > len(rs) {
			end = len(rs)
		}
		if start > end {
			start, end = end, start
		}
		matched := []string{string(rs[start:end])}
		for i := 2; i+1 < len(rtGlobal.matchData); i += 2 {
			a, b := rtGlobal.matchData[i], rtGlobal.matchData[i+1]
			if a < 0 || b < 0 || a > len(rs) || b > len(rs) || a > b {
				matched = append(matched, "")
				continue
			}
			matched = append(matched, string(rs[a:b]))
		}
		replacement := repl
		if !literal {
			replacement = expandReplacementTemplate(repl, matched)
		}
		out := string(rs[:start]) + replacement + string(rs[end:])
		return golisp.StringWithValue(out), nil
	}

	buf := rtGlobal.currentBuffer()
	if rtGlobal.matchBuffer != nil {
		buf = rtGlobal.matchBuffer
	}
	if buf == nil {
		return golisp.StringWithValue(repl), nil
	}
	// Buffer match data stores 1-based positions.
	start--
	end--
	if start < 0 {
		start = 0
	}
	if end > len(buf.text) {
		end = len(buf.text)
	}
	if start > end {
		start, end = end, start
	}
	matched := []string{string(buf.text[start:end])}
	for i := 2; i+1 < len(rtGlobal.matchData); i += 2 {
		a, b := rtGlobal.matchData[i], rtGlobal.matchData[i+1]
		if a < 0 || b < 0 {
			matched = append(matched, "")
			continue
		}
		a--
		b--
		if a < 0 || b < 0 || a > len(buf.text) || b > len(buf.text) || a > b {
			matched = append(matched, "")
			continue
		}
		matched = append(matched, string(buf.text[a:b]))
	}
	replacement := repl
	if !literal {
		replacement = expandReplacementTemplate(repl, matched)
	}
	replRunes := []rune(replacement)
	buf.text = append(append([]rune{}, buf.text[:start]...), append(replRunes, buf.text[end:]...)...)
	buf.point = start + len(replRunes)
	rtGlobal.clearMatchData()
	return golisp.StringWithValue(replacement), nil
}

func matchBeginningImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	n := 0
	if golisp.NotNilP(args) && golisp.IntegerP(golisp.Car(args)) {
		n = int(golisp.IntegerValue(golisp.Car(args)))
	}
	i := n * 2
	if i+1 >= len(rtGlobal.matchData) || rtGlobal.matchData[i] < 0 {
		return golisp.EmptyCons(), nil
	}
	return golisp.IntegerWithValue(int64(rtGlobal.matchData[i])), nil
}

func matchEndImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	n := 0
	if golisp.NotNilP(args) && golisp.IntegerP(golisp.Car(args)) {
		n = int(golisp.IntegerValue(golisp.Car(args)))
	}
	i := n * 2
	if i+1 >= len(rtGlobal.matchData) || rtGlobal.matchData[i+1] < 0 {
		return golisp.EmptyCons(), nil
	}
	return golisp.IntegerWithValue(int64(rtGlobal.matchData[i+1])), nil
}

func setMatchDataImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	d := golisp.Car(args)
	if golisp.NilP(d) {
		rtGlobal.clearMatchData()
		return golisp.EmptyCons(), nil
	}
	if !golisp.ListP(d) {
		return golisp.EmptyCons(), nil
	}
	md := make([]int, 0, golisp.Length(d))
	for c := d; golisp.NotNilP(c); c = golisp.Cdr(c) {
		v := golisp.Car(c)
		if golisp.IntegerP(v) {
			md = append(md, int(golisp.IntegerValue(v)))
		} else {
			md = append(md, -1)
		}
	}
	rtGlobal.matchData = md
	rtGlobal.matchInString = false
	rtGlobal.matchString = ""
	rtGlobal.matchBuffer = rtGlobal.currentBuffer()
	return d, nil
}

func addTextPropertiesImpl(_ *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	// Text properties are ignored in this runtime.
	return golisp.BooleanWithValue(true), nil
}

func removeOverlaysImpl(_ *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	return golisp.EmptyCons(), nil
}

func removeTextPropertiesImpl(_ *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	return golisp.BooleanWithValue(true), nil
}

func untabifyImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	buf := rtGlobal.currentBuffer()
	if buf == nil {
		return golisp.EmptyCons(), nil
	}
	start := 0
	end := len(buf.text)
	if golisp.NotNilP(args) && golisp.IntegerP(golisp.Car(args)) {
		start = int(golisp.IntegerValue(golisp.Car(args))) - 1
	}
	if golisp.NotNilP(golisp.Cdr(args)) && golisp.IntegerP(golisp.Cadr(args)) {
		end = int(golisp.IntegerValue(golisp.Cadr(args))) - 1
	}
	if start < 0 {
		start = 0
	}
	if end < start {
		end = start
	}
	if end > len(buf.text) {
		end = len(buf.text)
	}
	segment := strings.ReplaceAll(string(buf.text[start:end]), "\t", " ")
	buf.text = append(append([]rune{}, buf.text[:start]...), append([]rune(segment), buf.text[end:]...)...)
	if buf.point > len(buf.text) {
		buf.point = len(buf.text)
	}
	return golisp.EmptyCons(), nil
}

func lprPrintRegionImpl(_ *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	return golisp.BooleanWithValue(true), nil
}

func currentWindowConfigurationImpl(_ *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	cfg := &elWindowConfiguration{
		selectedWindowID: rtGlobal.selectedWindowID,
		bufferByWindowID: make(map[int]string, len(rtGlobal.windows)),
	}
	for id, w := range rtGlobal.windows {
		if w != nil && w.buffer != nil {
			cfg.bufferByWindowID[id] = w.buffer.name
		}
	}
	return golisp.ObjectWithTypeAndValue("el-window-configuration", unsafe.Pointer(cfg)), nil
}

func setWindowConfigurationImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	cfgObj := golisp.Car(args)
	if !golisp.ObjectP(cfgObj) || golisp.ObjectType(cfgObj) != "el-window-configuration" {
		return nil, fmt.Errorf("set-window-configuration expects window-configuration, got %s", golisp.String(cfgObj))
	}
	cfg := (*elWindowConfiguration)(golisp.ObjectValue(cfgObj))
	if cfg == nil {
		return golisp.EmptyCons(), nil
	}
	for id, name := range cfg.bufferByWindowID {
		buf := rtGlobal.ensureBuffer(name)
		w, ok := rtGlobal.windows[id]
		if !ok || w == nil {
			w = &elWindow{id: id}
			w.object = golisp.ObjectWithTypeAndValue("el-window", unsafe.Pointer(w))
			rtGlobal.windows[id] = w
			if rtGlobal.nextWindowID <= id {
				rtGlobal.nextWindowID = id + 1
			}
		}
		w.buffer = buf
	}
	if _, ok := rtGlobal.windows[cfg.selectedWindowID]; ok {
		rtGlobal.selectedWindowID = cfg.selectedWindowID
	}
	return golisp.BooleanWithValue(true), nil
}

func numberToStringImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	v := golisp.Car(args)
	switch {
	case golisp.IntegerP(v):
		return golisp.StringWithValue(strconv.FormatInt(golisp.IntegerValue(v), 10)), nil
	case golisp.FloatP(v):
		return golisp.StringWithValue(strconv.FormatFloat(float64(golisp.FloatValue(v)), 'f', -1, 32)), nil
	default:
		return golisp.StringWithValue(featureName(v)), nil
	}
}

func prefixNumericValueImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	v := golisp.Car(args)
	if golisp.IntegerP(v) {
		return v, nil
	}
	if golisp.NilP(v) {
		return golisp.IntegerWithValue(1), nil
	}
	return golisp.IntegerWithValue(1), nil
}

func makeBoolVectorImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	n := int(golisp.IntegerValue(golisp.Car(args)))
	fill := golisp.Cadr(args)
	items := make([]*golisp.Data, n)
	for i := range n {
		items[i] = fill
	}
	return newElVector(items), nil
}

func seqFindImpl(args *golisp.Data, env *golisp.SymbolTableFrame) (*golisp.Data, error) {
	pred := golisp.Car(args)
	seq := golisp.Cadr(args)
	def := golisp.EmptyCons()
	if golisp.NotNilP(golisp.Cddr(args)) {
		def = golisp.Caddr(args)
	}
	items := make([]*golisp.Data, 0)
	switch {
	case golisp.ListP(seq):
		items = append(items, golisp.ToArray(seq)...)
	case isElVector(seq):
		items = append(items, asElVector(seq).items...)
	case golisp.StringP(seq):
		for _, r := range golisp.StringValue(seq) {
			items = append(items, golisp.IntegerWithValue(int64(r)))
		}
	default:
		return def, nil
	}
	for _, it := range items {
		call := golisp.ArrayToList([]*golisp.Data{pred, it})
		v, err := rtGlobal.funcallImpl(call, env)
		if err != nil {
			return nil, err
		}
		if golisp.BooleanValue(v) {
			return it, nil
		}
	}
	return def, nil
}

func seqRandomEltImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	seq := golisp.Car(args)
	switch {
	case golisp.ListP(seq):
		arr := golisp.ToArray(seq)
		if len(arr) == 0 {
			return golisp.EmptyCons(), nil
		}
		return arr[rand.Intn(len(arr))], nil
	case isElVector(seq):
		arr := asElVector(seq).items
		if len(arr) == 0 {
			return golisp.EmptyCons(), nil
		}
		return arr[rand.Intn(len(arr))], nil
	case golisp.StringP(seq):
		rs := []rune(golisp.StringValue(seq))
		if len(rs) == 0 {
			return golisp.EmptyCons(), nil
		}
		return golisp.IntegerWithValue(int64(rs[rand.Intn(len(rs))])), nil
	default:
		return golisp.EmptyCons(), nil
	}
}

func fillarrayImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	seq := golisp.Car(args)
	fill := golisp.Cadr(args)
	switch {
	case isElVector(seq):
		vec := asElVector(seq)
		for i := range vec.items {
			vec.items[i] = fill
		}
		return seq, nil
	case golisp.ListP(seq):
		for i := 0; i < golisp.Length(seq); i++ {
			golisp.SetNth(seq, i, fill)
		}
		return seq, nil
	default:
		return seq, nil
	}
}

func nullImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	return golisp.BooleanWithValue(golisp.NilP(golisp.Car(args))), nil
}

func defgroupImpl(args *golisp.Data, env *golisp.SymbolTableFrame) (*golisp.Data, error) {
	name := golisp.Car(args)
	if !golisp.SymbolP(name) {
		name = golisp.Intern(golisp.String(name))
	}
	if _, err := env.BindLocallyTo(name, name); err != nil {
		return nil, err
	}
	return name, nil
}

func vectorLiteralImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	out := make([]*golisp.Data, 0, golisp.Length(args))
	for c := args; golisp.NotNilP(c); c = golisp.Cdr(c) {
		out = append(out, materializeLiteral(golisp.Car(c)))
	}
	return newElVector(out), nil
}

func materializeLiteral(d *golisp.Data) *golisp.Data {
	if golisp.PairP(d) {
		head := golisp.Car(d)
		if golisp.SymbolP(head) && golisp.StringValue(head) == "vector-literal" {
			items := make([]*golisp.Data, 0, golisp.Length(golisp.Cdr(d)))
			for c := golisp.Cdr(d); golisp.NotNilP(c); c = golisp.Cdr(c) {
				items = append(items, materializeLiteral(golisp.Car(c)))
			}
			return newElVector(items)
		}
		items := make([]*golisp.Data, 0, golisp.Length(d))
		for c := d; golisp.NotNilP(c); c = golisp.Cdr(c) {
			items = append(items, materializeLiteral(golisp.Car(c)))
		}
		return golisp.ArrayToList(items)
	}
	return d
}

func defineDerivedModeImpl(args *golisp.Data, env *golisp.SymbolTableFrame) (*golisp.Data, error) {
	name := golisp.Car(args)
	if !golisp.SymbolP(name) {
		return nil, fmt.Errorf("define-derived-mode name must be a symbol, got %s", golisp.String(name))
	}
	modeName := golisp.StringValue(name)
	body := golisp.Cdddr(args)
	pf := &golisp.PrimitiveFunction{
		Name:            modeName,
		Special:         false,
		ArgRestrictions: []golisp.ArgRestriction{{Type: golisp.ARGS_ANY}},
		IsRestricted:    false,
		Body: func(_ *golisp.Data, callEnv *golisp.SymbolTableFrame) (*golisp.Data, error) {
			mapSym := golisp.Intern(modeName + "-map")
			if km := callEnv.ValueOf(mapSym); isKeymap(km) {
				rtGlobal.currentBuffer().localMap = km
			}
			return evalLetBody(body, callEnv)
		},
	}
	fn := golisp.PrimitiveWithNameAndFunc(modeName, pf)
	_, err := env.BindLocallyTo(name, fn)
	rtGlobal.registerFunction(modeName, fn)
	return fn, err
}

func whileImpl(args *golisp.Data, env *golisp.SymbolTableFrame) (*golisp.Data, error) {
	condExpr := golisp.Car(args)
	body := golisp.Cdr(args)
	result := golisp.EmptyCons()
	for {
		cond, err := golisp.Eval(condExpr, env)
		if err != nil {
			return nil, err
		}
		if !golisp.BooleanValue(cond) {
			return result, nil
		}
		for b := body; golisp.NotNilP(b); b = golisp.Cdr(b) {
			result, err = golisp.Eval(golisp.Car(b), env)
			if err != nil {
				return nil, err
			}
		}
	}
}

func ifImpl(args *golisp.Data, env *golisp.SymbolTableFrame) (*golisp.Data, error) {
	cond, err := golisp.Eval(golisp.Car(args), env)
	if err != nil {
		return nil, err
	}
	if golisp.BooleanValue(cond) {
		return golisp.Eval(golisp.Cadr(args), env)
	}
	result := golisp.EmptyCons()
	for c := golisp.Cddr(args); golisp.NotNilP(c); c = golisp.Cdr(c) {
		result, err = golisp.Eval(golisp.Car(c), env)
		if err != nil {
			return nil, err
		}
	}
	return result, nil
}

func pcasePatternMatch(pattern, value *golisp.Data, env *golisp.SymbolTableFrame) (bool, *golisp.Data) {
	if golisp.SymbolP(pattern) {
		name := golisp.StringValue(pattern)
		if name == "_" || name == "t" {
			return true, nil
		}
		return true, pattern
	}
	if golisp.PairP(pattern) {
		head := golisp.Car(pattern)
		if golisp.SymbolP(head) && golisp.StringValue(head) == "quote" {
			return golisp.IsEqual(golisp.Cadr(pattern), value), nil
		}
		if golisp.SymbolP(head) && golisp.StringValue(head) == "or" {
			for c := golisp.Cdr(pattern); golisp.NotNilP(c); c = golisp.Cdr(c) {
				if ok, bind := pcasePatternMatch(golisp.Car(c), value, env); ok {
					return true, bind
				}
			}
			return false, nil
		}
	}
	return golisp.IsEqual(pattern, value), nil
}

func pcaseImpl(args *golisp.Data, env *golisp.SymbolTableFrame) (*golisp.Data, error) {
	target, err := golisp.Eval(golisp.Car(args), env)
	if err != nil {
		return nil, err
	}
	clauses := golisp.Cdr(args)
	for c := clauses; golisp.NotNilP(c); c = golisp.Cdr(c) {
		cl := golisp.Car(c)
		if !golisp.PairP(cl) {
			continue
		}
		pat := golisp.Car(cl)
		body := golisp.Cdr(cl)
		ok, bindSym := pcasePatternMatch(pat, target, env)
		if !ok {
			continue
		}
		local := env
		if bindSym != nil && golisp.SymbolP(bindSym) {
			local = golisp.NewSymbolTableFrameBelow(env, "pcase")
			local.Previous = env
			if _, err := local.BindLocallyTo(bindSym, target); err != nil {
				return nil, err
			}
		}
		return evalLetBody(body, local)
	}
	return golisp.EmptyCons(), nil
}

func whenImpl(args *golisp.Data, env *golisp.SymbolTableFrame) (*golisp.Data, error) {
	cond, err := golisp.Eval(golisp.Car(args), env)
	if err != nil {
		return nil, err
	}
	if !golisp.BooleanValue(cond) {
		return golisp.EmptyCons(), nil
	}
	return evalLetBody(golisp.Cdr(args), env)
}

func unlessImpl(args *golisp.Data, env *golisp.SymbolTableFrame) (*golisp.Data, error) {
	cond, err := golisp.Eval(golisp.Car(args), env)
	if err != nil {
		return nil, err
	}
	if golisp.BooleanValue(cond) {
		return golisp.EmptyCons(), nil
	}
	return evalLetBody(golisp.Cdr(args), env)
}

type letBinding struct {
	name  *golisp.Data
	value *golisp.Data
}

func parseElispLetBindings(forms *golisp.Data, env *golisp.SymbolTableFrame, sequential bool) ([]letBinding, error) {
	if !golisp.ListP(forms) {
		return nil, errors.New("let expects a list of bindings")
	}
	bindings := make([]letBinding, 0, golisp.Length(forms))
	evalEnv := env
	local := env
	if sequential {
		local = golisp.NewSymbolTableFrameBelow(env, "let*")
		local.Previous = env
		evalEnv = local
	}

	for c := forms; golisp.NotNilP(c); c = golisp.Cdr(c) {
		b := golisp.Car(c)
		switch {
		case golisp.SymbolP(b):
			if sequential {
				if _, err := local.BindLocallyTo(b, golisp.EmptyCons()); err != nil {
					return nil, err
				}
				continue
			}
			bindings = append(bindings, letBinding{name: b, value: golisp.EmptyCons()})
		case golisp.PairP(b):
			name := golisp.Car(b)
			if !golisp.SymbolP(name) {
				return nil, fmt.Errorf("let binding name must be a symbol, got %s", golisp.String(name))
			}
			value := golisp.EmptyCons()
			rest := golisp.Cdr(b)
			if golisp.NotNilP(rest) {
				var err error
				value, err = golisp.Eval(golisp.Car(rest), evalEnv)
				if err != nil {
					return nil, err
				}
			}
			if sequential {
				if _, err := local.BindLocallyTo(name, value); err != nil {
					return nil, err
				}
				continue
			}
			bindings = append(bindings, letBinding{name: name, value: value})
		default:
			return nil, fmt.Errorf("invalid let binding form: %s", golisp.String(b))
		}
	}

	if sequential {
		arr := make([]letBinding, 0, len(local.Bindings))
		for c := forms; golisp.NotNilP(c); c = golisp.Cdr(c) {
			b := golisp.Car(c)
			name := b
			if golisp.PairP(b) {
				name = golisp.Car(b)
			}
			arr = append(arr, letBinding{name: name, value: local.ValueOf(name)})
		}
		return arr, nil
	}
	return bindings, nil
}

func evalLetBody(body *golisp.Data, env *golisp.SymbolTableFrame) (*golisp.Data, error) {
	result := golisp.EmptyCons()
	var err error
	for c := body; golisp.NotNilP(c); c = golisp.Cdr(c) {
		result, err = golisp.Eval(golisp.Car(c), env)
		if err != nil {
			return nil, err
		}
	}
	return result, nil
}

func letImpl(args *golisp.Data, env *golisp.SymbolTableFrame) (*golisp.Data, error) {
	bindingForms := golisp.Car(args)
	body := golisp.Cdr(args)
	bindings, err := parseElispLetBindings(bindingForms, env, false)
	if err != nil {
		return nil, err
	}
	local := golisp.NewSymbolTableFrameBelow(env, "let")
	local.Previous = env
	for _, b := range bindings {
		if _, err := local.BindLocallyTo(b.name, b.value); err != nil {
			return nil, err
		}
	}
	return evalLetBody(body, local)
}

func letStarImpl(args *golisp.Data, env *golisp.SymbolTableFrame) (*golisp.Data, error) {
	bindingForms := golisp.Car(args)
	body := golisp.Cdr(args)
	if !golisp.ListP(bindingForms) {
		return nil, errors.New("let* expects a list of bindings")
	}
	local := golisp.NewSymbolTableFrameBelow(env, "let*")
	local.Previous = env
	for c := bindingForms; golisp.NotNilP(c); c = golisp.Cdr(c) {
		b := golisp.Car(c)
		switch {
		case golisp.SymbolP(b):
			if _, err := local.BindLocallyTo(b, golisp.EmptyCons()); err != nil {
				return nil, err
			}
		case golisp.PairP(b):
			name := golisp.Car(b)
			if !golisp.SymbolP(name) {
				return nil, fmt.Errorf("let* binding name must be a symbol, got %s", golisp.String(name))
			}
			value := golisp.EmptyCons()
			if golisp.NotNilP(golisp.Cdr(b)) {
				v, err := golisp.Eval(golisp.Cadr(b), local)
				if err != nil {
					return nil, err
				}
				value = v
			}
			if _, err := local.BindLocallyTo(name, value); err != nil {
				return nil, err
			}
		default:
			return nil, fmt.Errorf("invalid let* binding form: %s", golisp.String(b))
		}
	}
	return evalLetBody(body, local)
}

func ignoreErrorsImpl(args *golisp.Data, env *golisp.SymbolTableFrame) (*golisp.Data, error) {
	result := golisp.EmptyCons()
	for c := args; golisp.NotNilP(c); c = golisp.Cdr(c) {
		v, err := golisp.Eval(golisp.Car(c), env)
		if err != nil {
			return golisp.EmptyCons(), nil
		}
		result = v
	}
	return result, nil
}

func catchImpl(args *golisp.Data, env *golisp.SymbolTableFrame) (*golisp.Data, error) {
	tagExpr := golisp.Car(args)
	body := golisp.Cdr(args)
	tagVal, err := golisp.Eval(tagExpr, env)
	if err != nil {
		return nil, err
	}
	tag := featureName(tagVal)
	result := golisp.EmptyCons()
	for b := body; golisp.NotNilP(b); b = golisp.Cdr(b) {
		result, err = golisp.Eval(golisp.Car(b), env)
		if err != nil {
			if sig, ok := err.(throwSignal); ok && sig.tag == tag {
				return sig.value, nil
			}
			return nil, err
		}
	}
	return result, nil
}

func conditionCaseImpl(args *golisp.Data, env *golisp.SymbolTableFrame) (*golisp.Data, error) {
	varName := golisp.Car(args)
	body := golisp.Cadr(args)
	v, err := golisp.Eval(body, env)
	if err == nil {
		return v, nil
	}
	handlers := golisp.Cddr(args)
	errCond := "error"
	switch sig := err.(type) {
	case throwSignal:
		errCond = "throw"
	case elSignal:
		if sig.condition != "" {
			errCond = sig.condition
		}
	}
	errObj := conditionCaseErrorObject(errCond, err)
	for h := handlers; golisp.NotNilP(h); h = golisp.Cdr(h) {
		clause := golisp.Car(h)
		if !golisp.PairP(clause) {
			continue
		}
		spec := golisp.Car(clause)
		if !conditionCaseMatches(spec, errCond) {
			continue
		}
		local := env
		if golisp.SymbolP(varName) && golisp.StringValue(varName) != "nil" {
			local = golisp.NewSymbolTableFrameBelow(env, "condition-case")
			local.Previous = env
			if _, bindErr := local.BindLocallyTo(varName, errObj); bindErr != nil {
				return nil, bindErr
			}
		}
		return evalLetBody(golisp.Cdr(clause), local)
	}
	return nil, err
}

func conditionCaseErrorObject(errCond string, err error) *golisp.Data {
	switch sig := err.(type) {
	case elSignal:
		if golisp.NotNilP(sig.data) {
			return golisp.ArrayToList([]*golisp.Data{
				golisp.Intern(errCond),
				sig.data,
			})
		}
	}
	return golisp.ArrayToList([]*golisp.Data{
		golisp.Intern(errCond),
		golisp.StringWithValue(err.Error()),
	})
}

func conditionCaseMatches(spec *golisp.Data, errCond string) bool {
	switch {
	case golisp.SymbolP(spec):
		return conditionNameMatches(golisp.StringValue(spec), errCond)
	case golisp.ListP(spec):
		for c := spec; golisp.NotNilP(c); c = golisp.Cdr(c) {
			s := golisp.Car(c)
			if golisp.SymbolP(s) && conditionNameMatches(golisp.StringValue(s), errCond) {
				return true
			}
		}
	}
	return false
}

func conditionNameMatches(spec, errCond string) bool {
	if spec == "t" {
		return true
	}
	seen := map[string]bool{}
	for c := errCond; c != ""; c = rtGlobal.errorParents[c] {
		if seen[c] {
			break
		}
		seen[c] = true
		if c == spec {
			return true
		}
		if c == "error" {
			break
		}
	}
	return spec == "error" && errCond == "error"
}

func unwindProtectImpl(args *golisp.Data, env *golisp.SymbolTableFrame) (*golisp.Data, error) {
	protected := golisp.Car(args)
	cleanup := golisp.Cdr(args)
	result, runErr := golisp.Eval(protected, env)
	var cleanupErr error
	for c := cleanup; golisp.NotNilP(c); c = golisp.Cdr(c) {
		_, err := golisp.Eval(golisp.Car(c), env)
		if err != nil && cleanupErr == nil {
			cleanupErr = err
		}
	}
	if runErr != nil {
		return nil, runErr
	}
	if cleanupErr != nil {
		return nil, cleanupErr
	}
	return result, nil
}

func saveCurrentBufferImpl(args *golisp.Data, env *golisp.SymbolTableFrame) (*golisp.Data, error) {
	orig := rtGlobal.currentBuffer()
	defer func() {
		if orig != nil {
			rtGlobal.selectedWindow().buffer = orig
		}
	}()
	return evalLetBody(args, env)
}

func withCurrentBufferImpl(args *golisp.Data, env *golisp.SymbolTableFrame) (*golisp.Data, error) {
	bv, err := golisp.Eval(golisp.Car(args), env)
	if err != nil {
		return nil, err
	}
	name := bufferNameFromArg(bv)
	orig := rtGlobal.currentBuffer()
	rtGlobal.selectedWindow().buffer = rtGlobal.ensureBuffer(name)
	defer func() {
		if orig != nil {
			rtGlobal.selectedWindow().buffer = orig
		}
	}()
	return evalLetBody(golisp.Cdr(args), env)
}

func withTempBufferImpl(args *golisp.Data, env *golisp.SymbolTableFrame) (*golisp.Data, error) {
	orig := rtGlobal.currentBuffer()
	name := fmt.Sprintf("*temp-%d*", time.Now().UnixNano())
	tmp := rtGlobal.ensureBuffer(name)
	rtGlobal.selectedWindow().buffer = tmp
	defer func() {
		delete(rtGlobal.buffers, name)
		if orig != nil {
			rtGlobal.selectedWindow().buffer = orig
		}
	}()
	return evalLetBody(args, env)
}

func dotimesImpl(args *golisp.Data, env *golisp.SymbolTableFrame) (*golisp.Data, error) {
	spec := golisp.Car(args)
	body := golisp.Cdr(args)
	if !golisp.PairP(spec) || !golisp.SymbolP(golisp.Car(spec)) {
		return nil, errors.New("dotimes expects (var count [result]) as first argument")
	}
	varName := golisp.Car(spec)
	countExpr := golisp.Cadr(spec)
	resultExpr := golisp.Caddr(spec)

	countVal, err := golisp.Eval(countExpr, env)
	if err != nil {
		return nil, err
	}
	var count int
	switch {
	case golisp.IntegerP(countVal):
		count = int(golisp.IntegerValue(countVal))
	case golisp.FloatP(countVal):
		count = int(math.Trunc(float64(golisp.FloatValue(countVal))))
	default:
		return nil, fmt.Errorf("dotimes count must be numeric, got %s", golisp.String(countVal))
	}
	if count < 0 {
		count = 0
	}
	local := golisp.NewSymbolTableFrameBelow(env, "dotimes")
	local.Previous = env

	result := golisp.EmptyCons()
	for i := 0; i < count; i++ {
		if _, err := local.BindLocallyTo(varName, golisp.IntegerWithValue(int64(i))); err != nil {
			return nil, err
		}
		for b := body; golisp.NotNilP(b); b = golisp.Cdr(b) {
			result, err = golisp.Eval(golisp.Car(b), local)
			if err != nil {
				return nil, err
			}
		}
	}

	if golisp.NotNilP(resultExpr) {
		return golisp.Eval(resultExpr, local)
	}
	return result, nil
}

func dolistImpl(args *golisp.Data, env *golisp.SymbolTableFrame) (*golisp.Data, error) {
	spec := golisp.Car(args)
	body := golisp.Cdr(args)
	if !golisp.PairP(spec) || !golisp.SymbolP(golisp.Car(spec)) {
		return nil, errors.New("dolist expects (var list [result]) as first argument")
	}
	varName := golisp.Car(spec)
	listExpr := golisp.Cadr(spec)
	resultExpr := golisp.Caddr(spec)
	seq, err := golisp.Eval(listExpr, env)
	if err != nil {
		return nil, err
	}
	local := golisp.NewSymbolTableFrameBelow(env, "dolist")
	local.Previous = env
	result := golisp.EmptyCons()
	var items []*golisp.Data
	switch {
	case golisp.ListP(seq):
		for c := seq; golisp.NotNilP(c); c = golisp.Cdr(c) {
			items = append(items, golisp.Car(c))
		}
	case isElVector(seq):
		items = append(items, asElVector(seq).items...)
	default:
		items = []*golisp.Data{}
	}
	for _, item := range items {
		if _, err := local.BindLocallyTo(varName, item); err != nil {
			return nil, err
		}
		for b := body; golisp.NotNilP(b); b = golisp.Cdr(b) {
			result, err = golisp.Eval(golisp.Car(b), local)
			if err != nil {
				return nil, err
			}
		}
	}
	if golisp.NotNilP(resultExpr) {
		return golisp.Eval(resultExpr, local)
	}
	return result, nil
}

func bindOrSetLocal(env *golisp.SymbolTableFrame, name, value *golisp.Data) error {
	if _, err := env.SetTo(name, value); err == nil {
		return nil
	}
	_, err := env.BindLocallyTo(name, value)
	return err
}

func clLoopImpl(args *golisp.Data, env *golisp.SymbolTableFrame) (*golisp.Data, error) {
	toks := golisp.ToArray(args)
	if len(toks) == 0 {
		return golisp.EmptyCons(), nil
	}
	local := golisp.NewSymbolTableFrameBelow(env, "cl-loop")
	local.Previous = env

	mode := "do" // do | sum | collect
	bodyStart := -1
	var whileExpr *golisp.Data
	var forAssigns []struct {
		name *golisp.Data
		expr *golisp.Data
	}
	var repeatExpr *golisp.Data
	var numericVar *golisp.Data
	var numericStart, numericEnd, numericStep *golisp.Data
	numericCmp := "none" // to | downto | below
	var seqVar *golisp.Data
	var seqExpr *golisp.Data
	seqAcross := false

	for i := 0; i < len(toks); {
		tok := featureName(toks[i])
		switch tok {
		case "do", "sum", "collect":
			mode = tok
			bodyStart = i + 1
			i = len(toks)
			continue
		case "with":
			if i+1 >= len(toks) || !golisp.SymbolP(toks[i+1]) {
				return golisp.EmptyCons(), nil
			}
			name := toks[i+1]
			val := golisp.EmptyCons()
			next := i + 2
			if next < len(toks) && featureName(toks[next]) == "=" {
				next++
			}
			if next < len(toks) {
				v, err := golisp.Eval(toks[next], local)
				if err != nil {
					return nil, err
				}
				val = v
				next++
			}
			if err := bindOrSetLocal(local, name, val); err != nil {
				return nil, err
			}
			i = next
		case "while":
			if i+1 >= len(toks) {
				return golisp.EmptyCons(), nil
			}
			whileExpr = toks[i+1]
			i += 2
		case "repeat":
			if i+1 >= len(toks) {
				return golisp.EmptyCons(), nil
			}
			repeatExpr = toks[i+1]
			i += 2
		case "for":
			if i+2 >= len(toks) || !golisp.SymbolP(toks[i+1]) {
				return golisp.EmptyCons(), nil
			}
			name := toks[i+1]
			op := featureName(toks[i+2])
			switch op {
			case "=":
				if i+3 >= len(toks) {
					return golisp.EmptyCons(), nil
				}
				forAssigns = append(forAssigns, struct {
					name *golisp.Data
					expr *golisp.Data
				}{name: name, expr: toks[i+3]})
				i += 4
			case "in", "across":
				if i+3 >= len(toks) {
					return golisp.EmptyCons(), nil
				}
				seqVar = name
				seqExpr = toks[i+3]
				seqAcross = op == "across"
				i += 4
			case "below":
				if i+3 >= len(toks) {
					return golisp.EmptyCons(), nil
				}
				numericVar = name
				numericStart = golisp.IntegerWithValue(0)
				numericEnd = toks[i+3]
				numericStep = golisp.IntegerWithValue(1)
				numericCmp = "below"
				i += 4
			case "from", "upfrom":
				if i+3 >= len(toks) {
					return golisp.EmptyCons(), nil
				}
				numericVar = name
				numericStart = toks[i+3]
				numericStep = golisp.IntegerWithValue(1)
				j := i + 4
				if op == "upfrom" && j < len(toks) && featureName(toks[j]) == "by" && j+1 < len(toks) {
					numericStep = toks[j+1]
					j += 2
				}
				if j+1 >= len(toks) {
					return golisp.EmptyCons(), nil
				}
				numericCmp = featureName(toks[j])
				numericEnd = toks[j+1]
				i = j + 2
			default:
				// Best effort: ignore unsupported for-clause parts.
				i += 3
			}
		default:
			i++
		}
	}

	if bodyStart < 0 {
		rtGlobal.warnOnce("cl-loop-unsupported", "cl-loop form is not fully supported; skipping unsupported loop")
		return golisp.EmptyCons(), nil
	}
	body := toks[bodyStart:]
	result := golisp.EmptyCons()
	sum := int64(0)
	collected := make([]*golisp.Data, 0)

	seqItems := []*golisp.Data(nil)
	if seqExpr != nil {
		seq, err := golisp.Eval(seqExpr, local)
		if err != nil {
			return nil, err
		}
		switch {
		case golisp.ListP(seq):
			seqItems = golisp.ToArray(seq)
		case isElVector(seq):
			seqItems = append(seqItems, asElVector(seq).items...)
		case seqAcross && golisp.StringP(seq):
			for _, r := range golisp.StringValue(seq) {
				seqItems = append(seqItems, golisp.IntegerWithValue(int64(r)))
			}
		default:
			seqItems = []*golisp.Data{}
		}
	}

	var nStart, nEnd, nStep int64
	if numericVar != nil && numericEnd != nil {
		st := golisp.IntegerWithValue(0)
		if numericStart != nil {
			v, err := golisp.Eval(numericStart, local)
			if err != nil {
				return nil, err
			}
			st = v
		}
		en, err := golisp.Eval(numericEnd, local)
		if err != nil {
			return nil, err
		}
		sp := golisp.IntegerWithValue(1)
		if numericStep != nil {
			v, err := golisp.Eval(numericStep, local)
			if err != nil {
				return nil, err
			}
			sp = v
		}
		if !golisp.IntegerP(st) || !golisp.IntegerP(en) || !golisp.IntegerP(sp) {
			return golisp.EmptyCons(), nil
		}
		nStart = golisp.IntegerValue(st)
		nEnd = golisp.IntegerValue(en)
		nStep = golisp.IntegerValue(sp)
		if nStep == 0 {
			nStep = 1
		}
	}

	repeatCount := -1
	if repeatExpr != nil {
		v, err := golisp.Eval(repeatExpr, local)
		if err != nil {
			return nil, err
		}
		if !golisp.IntegerP(v) {
			return golisp.EmptyCons(), nil
		}
		repeatCount = max(int(golisp.IntegerValue(v)), 0)
	}

	iter := 0
	nVal := nStart
	maxIters := 100000
	for {
		if iter >= maxIters {
			break
		}
		// Loop termination controllers.
		if repeatCount >= 0 && iter >= repeatCount {
			break
		}
		if seqItems != nil {
			if iter >= len(seqItems) {
				break
			}
			if seqVar != nil {
				if err := bindOrSetLocal(local, seqVar, seqItems[iter]); err != nil {
					return nil, err
				}
			}
		}
		if numericVar != nil {
			ok := true
			switch numericCmp {
			case "to":
				ok = nVal <= nEnd
			case "downto":
				ok = nVal >= nEnd
			case "below":
				ok = nVal < nEnd
			}
			if !ok {
				break
			}
			if err := bindOrSetLocal(local, numericVar, golisp.IntegerWithValue(nVal)); err != nil {
				return nil, err
			}
		}
		for _, a := range forAssigns {
			v, err := golisp.Eval(a.expr, local)
			if err != nil {
				return nil, err
			}
			if err := bindOrSetLocal(local, a.name, v); err != nil {
				return nil, err
			}
		}
		if whileExpr != nil {
			cond, err := golisp.Eval(whileExpr, local)
			if err != nil {
				return nil, err
			}
			if !golisp.BooleanValue(cond) {
				break
			}
		}

		switch mode {
		case "sum":
			if len(body) == 0 {
				break
			}
			v, err := golisp.Eval(body[0], local)
			if err != nil {
				return nil, err
			}
			if golisp.IntegerP(v) {
				sum += golisp.IntegerValue(v)
			}
		case "collect":
			if len(body) == 0 {
				break
			}
			v, err := golisp.Eval(body[0], local)
			if err != nil {
				return nil, err
			}
			collected = append(collected, v)
		default:
			for _, form := range body {
				v, err := golisp.Eval(form, local)
				if err != nil {
					return nil, err
				}
				result = v
			}
		}

		iter++
		if numericVar != nil {
			nVal += nStep
		}
	}

	switch mode {
	case "sum":
		return golisp.IntegerWithValue(sum), nil
	case "collect":
		return golisp.ArrayToList(collected), nil
	default:
		return result, nil
	}
}

func clRotatefImpl(args *golisp.Data, env *golisp.SymbolTableFrame) (*golisp.Data, error) {
	lhs := golisp.Car(args)
	rhs := golisp.Cadr(args)

	lseq, lidx, err := evalEltPlace(lhs, env)
	if err != nil {
		return nil, err
	}
	rseq, ridx, err := evalEltPlace(rhs, env)
	if err != nil {
		return nil, err
	}

	lv, err := readElt(lseq, lidx)
	if err != nil {
		return nil, err
	}
	rv, err := readElt(rseq, ridx)
	if err != nil {
		return nil, err
	}
	if err := writeElt(lseq, lidx, rv); err != nil {
		return nil, err
	}
	if err := writeElt(rseq, ridx, lv); err != nil {
		return nil, err
	}
	return rv, nil
}

func popImpl(args *golisp.Data, env *golisp.SymbolTableFrame) (*golisp.Data, error) {
	target := golisp.Car(args)
	if !golisp.SymbolP(target) {
		return nil, errors.New("pop currently supports symbols only")
	}
	seq := env.ValueOf(target)
	if golisp.NilP(seq) {
		return golisp.EmptyCons(), nil
	}
	if !golisp.ListP(seq) {
		return nil, fmt.Errorf("pop target must hold a list, got %s", golisp.String(seq))
	}
	head := golisp.Car(seq)
	tail := golisp.Cdr(seq)
	if _, err := env.SetTo(target, tail); err != nil {
		return nil, err
	}
	return head, nil
}

func pushImpl(args *golisp.Data, env *golisp.SymbolTableFrame) (*golisp.Data, error) {
	value, err := golisp.Eval(golisp.Car(args), env)
	if err != nil {
		return nil, err
	}
	target := golisp.Cadr(args)
	if !golisp.SymbolP(target) {
		return nil, errors.New("push currently supports symbol places only")
	}
	seq := env.ValueOf(target)
	if golisp.NilP(seq) {
		seq = golisp.EmptyCons()
	}
	if !golisp.ListP(seq) {
		return nil, fmt.Errorf("push target must hold a list, got %s", golisp.String(seq))
	}
	newList := golisp.Cons(value, seq)
	if _, err := env.SetTo(target, newList); err != nil {
		if _, err2 := env.BindTo(target, newList); err2 != nil {
			return nil, err2
		}
	}
	return newList, nil
}

func incfImpl(args *golisp.Data, env *golisp.SymbolTableFrame) (*golisp.Data, error) {
	target := golisp.Car(args)
	if !golisp.SymbolP(target) {
		return nil, errors.New("incf currently supports symbol places only")
	}
	step := int64(1)
	if golisp.NotNilP(golisp.Cdr(args)) {
		v, err := golisp.Eval(golisp.Cadr(args), env)
		if err != nil {
			return nil, err
		}
		if !golisp.IntegerP(v) {
			return nil, fmt.Errorf("incf increment must be integer, got %s", golisp.String(v))
		}
		step = golisp.IntegerValue(v)
	}
	cur := env.ValueOf(target)
	if golisp.NilP(cur) {
		cur = golisp.IntegerWithValue(0)
	}
	if !golisp.IntegerP(cur) {
		return nil, fmt.Errorf("incf target must be integer, got %s", golisp.String(cur))
	}
	next := golisp.IntegerWithValue(golisp.IntegerValue(cur) + step)
	if _, err := env.SetTo(target, next); err != nil {
		if _, err2 := env.BindTo(target, next); err2 != nil {
			return nil, err2
		}
	}
	return next, nil
}

func decfImpl(args *golisp.Data, env *golisp.SymbolTableFrame) (*golisp.Data, error) {
	target := golisp.Car(args)
	if !golisp.SymbolP(target) {
		return nil, errors.New("decf currently supports symbol places only")
	}
	step := int64(1)
	if golisp.NotNilP(golisp.Cdr(args)) {
		v, err := golisp.Eval(golisp.Cadr(args), env)
		if err != nil {
			return nil, err
		}
		if !golisp.IntegerP(v) {
			return nil, fmt.Errorf("decf decrement must be integer, got %s", golisp.String(v))
		}
		step = golisp.IntegerValue(v)
	}
	cur := env.ValueOf(target)
	if golisp.NilP(cur) {
		cur = golisp.IntegerWithValue(0)
	}
	if !golisp.IntegerP(cur) {
		return nil, fmt.Errorf("decf target must be integer, got %s", golisp.String(cur))
	}
	next := golisp.IntegerWithValue(golisp.IntegerValue(cur) - step)
	if _, err := env.SetTo(target, next); err != nil {
		if _, err2 := env.BindTo(target, next); err2 != nil {
			return nil, err2
		}
	}
	return next, nil
}

func setcdrImpl(args *golisp.Data, env *golisp.SymbolTableFrame) (*golisp.Data, error) {
	f := env.ValueOf(golisp.Intern("set-cdr!"))
	if !golisp.FunctionOrPrimitiveP(f) {
		return nil, errors.New("set-cdr! is not available")
	}
	return golisp.ApplyWithoutEval(f, args, env)
}

func beginAliasImpl(args *golisp.Data, env *golisp.SymbolTableFrame) (*golisp.Data, error) {
	result := golisp.EmptyCons()
	var err error
	for c := args; golisp.NotNilP(c); c = golisp.Cdr(c) {
		result, err = golisp.Eval(golisp.Car(c), env)
		if err != nil {
			return nil, err
		}
	}
	return result, nil
}

func prog1Impl(args *golisp.Data, env *golisp.SymbolTableFrame) (*golisp.Data, error) {
	first, err := golisp.Eval(golisp.Car(args), env)
	if err != nil {
		return nil, err
	}
	for c := golisp.Cdr(args); golisp.NotNilP(c); c = golisp.Cdr(c) {
		if _, err := golisp.Eval(golisp.Car(c), env); err != nil {
			return nil, err
		}
	}
	return first, nil
}

func prog2Impl(args *golisp.Data, env *golisp.SymbolTableFrame) (*golisp.Data, error) {
	if _, err := golisp.Eval(golisp.Car(args), env); err != nil {
		return nil, err
	}
	return prog1Impl(golisp.Cdr(args), env)
}

func interactiveImpl(_ *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	return golisp.EmptyCons(), nil
}

func calledInteractivelyPImpl(_ *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	return golisp.BooleanWithValue(true), nil
}

func derivedModePImpl(_ *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	return golisp.BooleanWithValue(true), nil
}

func firstArg(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	return golisp.Car(args), nil
}

func firstArgOrNil(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	if golisp.NilP(args) {
		return golisp.EmptyCons(), nil
	}
	return golisp.Car(args), nil
}

func unaryAlias(name string) func(*golisp.Data, *golisp.SymbolTableFrame) (*golisp.Data, error) {
	return func(args *golisp.Data, env *golisp.SymbolTableFrame) (*golisp.Data, error) {
		fn := env.ValueOf(golisp.Intern(name))
		if golisp.NilP(fn) {
			return nil, fmt.Errorf("%s not found", name)
		}
		return golisp.ApplyWithoutEval(fn, args, env)
	}
}

func binaryAlias(name string) func(*golisp.Data, *golisp.SymbolTableFrame) (*golisp.Data, error) {
	return unaryAlias(name)
}

func carImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	v := golisp.Car(args)
	if golisp.NilP(v) || (golisp.SymbolP(v) && golisp.StringValue(v) == "nil") {
		return golisp.EmptyCons(), nil
	}
	if isKeymap(v) {
		km := asKeymap(v)
		if km.fullMap != nil {
			return golisp.Intern("keymap"), nil
		}
		return golisp.EmptyCons(), nil
	}
	if !golisp.PairP(v) && !golisp.ListP(v) {
		return nil, fmt.Errorf("car expects cons cell or nil, got %s", golisp.String(v))
	}
	return golisp.Car(v), nil
}

func cdrImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	v := golisp.Car(args)
	if golisp.NilP(v) || (golisp.SymbolP(v) && golisp.StringValue(v) == "nil") {
		return golisp.EmptyCons(), nil
	}
	if isKeymap(v) {
		km := asKeymap(v)
		if km.fullMap != nil {
			return golisp.ArrayToList([]*golisp.Data{km.fullMap}), nil
		}
		return golisp.EmptyCons(), nil
	}
	if !golisp.PairP(v) && !golisp.ListP(v) {
		return nil, fmt.Errorf("cdr expects cons cell or nil, got %s", golisp.String(v))
	}
	return golisp.Cdr(v), nil
}

func vectorImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	return newElVector(golisp.ToArray(args)), nil
}

func makeVectorImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	n := golisp.Car(args)
	fill := golisp.Cadr(args)
	if !golisp.IntegerP(n) {
		return nil, fmt.Errorf("make-vector length must be integer, got %s", golisp.String(n))
	}
	size := int(golisp.IntegerValue(n))
	if size < 0 {
		return nil, errors.New("make-vector length must be >= 0")
	}
	items := make([]*golisp.Data, size)
	for i := range size {
		items[i] = fill
	}
	return newElVector(items), nil
}

func arefImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	seq := golisp.Car(args)
	idx := golisp.Cadr(args)
	if !golisp.IntegerP(idx) {
		return nil, fmt.Errorf("aref index must be integer, got %s", golisp.String(idx))
	}
	return readElt(seq, int(golisp.IntegerValue(idx)))
}

func asetImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	seq := golisp.Car(args)
	idx := golisp.Cadr(args)
	val := golisp.Caddr(args)
	if !golisp.IntegerP(idx) {
		return nil, fmt.Errorf("aset index must be integer, got %s", golisp.String(idx))
	}
	i := int(golisp.IntegerValue(idx))
	if err := writeElt(seq, i, val); err != nil {
		return nil, err
	}
	return val, nil
}

func lengthImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	v := golisp.Car(args)
	switch {
	case golisp.StringP(v):
		return golisp.IntegerWithValue(int64(len([]rune(golisp.StringValue(v))))), nil
	case golisp.ListP(v):
		return golisp.IntegerWithValue(int64(golisp.Length(v))), nil
	case isElVector(v):
		vec := asElVector(v)
		return golisp.IntegerWithValue(int64(len(vec.items))), nil
	default:
		return nil, fmt.Errorf("length unsupported for %s", golisp.String(v))
	}
}

func nthImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	nv := golisp.Car(args)
	seq := golisp.Cadr(args)
	if !golisp.IntegerP(nv) {
		return nil, fmt.Errorf("nth expects integer index, got %s", golisp.String(nv))
	}
	i := int(golisp.IntegerValue(nv))
	if i < 0 {
		return golisp.EmptyCons(), nil
	}
	switch {
	case golisp.ListP(seq):
		cur := seq
		for step := 0; step < i && golisp.NotNilP(cur); step++ {
			cur = golisp.Cdr(cur)
		}
		if golisp.NilP(cur) {
			return golisp.EmptyCons(), nil
		}
		return golisp.Car(cur), nil
	case isElVector(seq):
		vec := asElVector(seq)
		if i >= len(vec.items) {
			return golisp.EmptyCons(), nil
		}
		return vec.items[i], nil
	default:
		return golisp.EmptyCons(), nil
	}
}

func lastImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	l := golisp.Car(args)
	if golisp.NilP(l) {
		return golisp.EmptyCons(), nil
	}
	if !golisp.ListP(l) {
		return nil, fmt.Errorf("last expects list, got %s", golisp.String(l))
	}
	cur := l
	for golisp.NotNilP(golisp.Cdr(cur)) {
		cur = golisp.Cdr(cur)
	}
	return cur, nil
}

func nthcdrImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	nv := golisp.Car(args)
	l := golisp.Cadr(args)
	if !golisp.IntegerP(nv) {
		return nil, fmt.Errorf("nthcdr expects integer n, got %s", golisp.String(nv))
	}
	n := golisp.IntegerValue(nv)
	cur := l
	for n > 0 && golisp.NotNilP(cur) {
		cur = golisp.Cdr(cur)
		n--
	}
	return cur, nil
}

func nreverseImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	l := golisp.Car(args)
	if golisp.NilP(l) {
		return golisp.EmptyCons(), nil
	}
	if !golisp.ListP(l) {
		return nil, fmt.Errorf("nreverse expects list, got %s", golisp.String(l))
	}
	arr := golisp.ToArray(l)
	for i, j := 0, len(arr)-1; i < j; i, j = i+1, j-1 {
		arr[i], arr[j] = arr[j], arr[i]
	}
	return golisp.ArrayToList(arr), nil
}

func concatImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	var b strings.Builder
	for c := args; golisp.NotNilP(c); c = golisp.Cdr(c) {
		v := golisp.Car(c)
		switch {
		case golisp.StringP(v), golisp.SymbolP(v):
			b.WriteString(golisp.StringValue(v))
		default:
			b.WriteString(golisp.String(v))
		}
	}
	return golisp.StringWithValue(b.String()), nil
}

func substringImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	sv := golisp.Car(args)
	if !golisp.StringP(sv) {
		return nil, fmt.Errorf("substring expects string, got %s", golisp.String(sv))
	}
	rs := []rune(golisp.StringValue(sv))
	start := int(golisp.IntegerValue(golisp.Cadr(args)))
	end := len(rs)
	if golisp.NotNilP(golisp.Cddr(args)) {
		end = int(golisp.IntegerValue(golisp.Caddr(args)))
	}
	if start < 0 {
		start = len(rs) + start
	}
	if end < 0 {
		end = len(rs) + end
	}
	if start < 0 {
		start = 0
	}
	if end > len(rs) {
		end = len(rs)
	}
	if start > end {
		start = end
	}
	return golisp.StringWithValue(string(rs[start:end])), nil
}

func vconcatImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	all := make([]*golisp.Data, 0)
	for c := args; golisp.NotNilP(c); c = golisp.Cdr(c) {
		v := golisp.Car(c)
		switch {
		case isElVector(v):
			all = append(all, asElVector(v).items...)
		case golisp.ListP(v):
			all = append(all, golisp.ToArray(v)...)
		default:
			all = append(all, v)
		}
	}
	return newElVector(all), nil
}

func sitForImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	secs := golisp.FloatValue(golisp.Car(args))
	if secs < 0 {
		secs = 0
	}
	time.Sleep(time.Duration(float64(secs) * float64(time.Second)))
	return golisp.BooleanWithValue(true), nil
}

func sleepForImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	secs := golisp.FloatValue(golisp.Car(args))
	ms := float64(0)
	if golisp.NotNilP(golisp.Cdr(args)) {
		ms = float64(golisp.FloatValue(golisp.Cadr(args)))
	}
	d := max(time.Duration(float64(secs)*float64(time.Second)+ms*float64(time.Millisecond)), 0)
	time.Sleep(d)
	return golisp.EmptyCons(), nil
}

func runAtTimeImpl(args *golisp.Data, env *golisp.SymbolTableFrame) (*golisp.Data, error) {
	delay := golisp.FloatValue(golisp.Car(args))
	repeat := golisp.FloatValue(golisp.Cadr(args))
	callback := golisp.Caddr(args)
	if delay < 0 {
		delay = 0
	}
	rtGlobal.timerSeq++
	id := fmt.Sprintf("timer-%d", rtGlobal.timerSeq)
	t := &elTimer{period: float64(repeat), callback: callback, active: true, nextFire: time.Now().Add(time.Duration(float64(delay) * float64(time.Second)))}
	rtGlobal.timers[id] = t
	if repeat <= 0 {
		t.period = -1
	}
	return golisp.ObjectWithTypeAndValue("el-timer", unsafe.Pointer(t)), nil
}

func cancelTimerImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	tv := golisp.Car(args)
	if golisp.ObjectP(tv) && golisp.ObjectType(tv) == "el-timer" {
		t := (*elTimer)(golisp.ObjectValue(tv))
		t.active = false
		return golisp.BooleanWithValue(true), nil
	}
	return golisp.EmptyCons(), nil
}

func randomImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	n := golisp.Car(args)
	if !golisp.IntegerP(n) {
		return nil, fmt.Errorf("random expects integer bound, got %s", golisp.String(n))
	}
	bound := golisp.IntegerValue(n)
	if bound <= 0 {
		return golisp.IntegerWithValue(0), nil
	}
	return golisp.IntegerWithValue(rand.Int63n(bound)), nil
}

func formatImpl(args *golisp.Data, _ *golisp.SymbolTableFrame) (*golisp.Data, error) {
	if golisp.NilP(args) || !golisp.StringP(golisp.Car(args)) {
		return nil, errors.New("format expects a format string as first argument")
	}
	format := golisp.StringValue(golisp.Car(args))
	var vals []any
	for c := golisp.Cdr(args); golisp.NotNilP(c); c = golisp.Cdr(c) {
		vals = append(vals, toGoValue(golisp.Car(c)))
	}
	return golisp.StringWithValue(fmt.Sprintf(format, vals...)), nil
}

func applyImpl(args *golisp.Data, env *golisp.SymbolTableFrame) (*golisp.Data, error) {
	f := golisp.Car(args)
	if golisp.SymbolP(f) {
		f = env.ValueOf(f)
	}
	if !golisp.FunctionOrPrimitiveP(f) {
		return nil, fmt.Errorf("apply expects a function, got %s", golisp.String(f))
	}
	ary := golisp.ToArray(golisp.Cdr(args))
	if len(ary) == 0 {
		return nil, errors.New("apply requires arguments after the function")
	}
	last := ary[len(ary)-1]
	var argList *golisp.Data
	if golisp.ListP(last) {
		if len(ary) > 1 {
			argList = golisp.ArrayToListWithTail(ary[:len(ary)-1], last)
		} else {
			argList = last
		}
	} else {
		return nil, errors.New("apply last argument must be a list")
	}
	return golisp.ApplyWithoutEval(f, argList, env)
}

func toGoValue(d *golisp.Data) any {
	switch {
	case golisp.IntegerP(d):
		return golisp.IntegerValue(d)
	case golisp.FloatP(d):
		return golisp.FloatValue(d)
	case golisp.StringP(d):
		return golisp.StringValue(d)
	case golisp.BooleanP(d):
		return golisp.BooleanValue(d)
	default:
		return golisp.String(d)
	}
}

func evalEltPlace(place *golisp.Data, env *golisp.SymbolTableFrame) (*golisp.Data, int, error) {
	if !golisp.ListP(place) || golisp.StringValue(golisp.Car(place)) != "elt" {
		return nil, 0, fmt.Errorf("cl-rotatef supports only (elt SEQ INDEX) places, got %s", golisp.String(place))
	}
	seq, err := golisp.Eval(golisp.Cadr(place), env)
	if err != nil {
		return nil, 0, err
	}
	idxVal, err := golisp.Eval(golisp.Caddr(place), env)
	if err != nil {
		return nil, 0, err
	}
	if !golisp.IntegerP(idxVal) {
		return nil, 0, fmt.Errorf("elt index must be integer, got %s", golisp.String(idxVal))
	}
	return seq, int(golisp.IntegerValue(idxVal)), nil
}

func readElt(seq *golisp.Data, idx int) (*golisp.Data, error) {
	if idx < 0 {
		return nil, errors.New("index must be >= 0")
	}
	switch {
	case isElVector(seq):
		vec := asElVector(seq)
		if idx >= len(vec.items) {
			return nil, fmt.Errorf("index %d out of range", idx)
		}
		return vec.items[idx], nil
	case golisp.ListP(seq):
		if idx >= golisp.Length(seq) {
			return nil, fmt.Errorf("index %d out of range", idx)
		}
		return golisp.Nth(seq, idx), nil
	case golisp.StringP(seq):
		r := []rune(golisp.StringValue(seq))
		if idx >= len(r) {
			return nil, fmt.Errorf("index %d out of range", idx)
		}
		return golisp.IntegerWithValue(int64(r[idx])), nil
	default:
		return nil, fmt.Errorf("elt unsupported for %s", golisp.String(seq))
	}
}

func writeElt(seq *golisp.Data, idx int, value *golisp.Data) error {
	if idx < 0 {
		return errors.New("index must be >= 0")
	}
	switch {
	case isElVector(seq):
		vec := asElVector(seq)
		if idx >= len(vec.items) {
			return nil
		}
		vec.items[idx] = value
		return nil
	case golisp.ListP(seq):
		if idx >= golisp.Length(seq) {
			return nil
		}
		golisp.SetNth(seq, idx, value)
		return nil
	default:
		return fmt.Errorf("set elt unsupported for %s", golisp.String(seq))
	}
}

func newElVector(items []*golisp.Data) *golisp.Data {
	v := &elVector{items: items}
	return golisp.ObjectWithTypeAndValue("el-vector", unsafe.Pointer(v))
}

func isElVector(d *golisp.Data) bool {
	return golisp.ObjectP(d) && golisp.ObjectType(d) == "el-vector"
}

func asElVector(d *golisp.Data) *elVector {
	return (*elVector)(golisp.ObjectValue(d))
}

func preprocessElisp(src string) (string, error) {
	var out strings.Builder
	vectorDepth := 0
	inString := false
	inComment := false
	escaped := false

	for i := 0; i < len(src); {
		ch := src[i]

		if inComment {
			out.WriteByte(ch)
			if ch == '\n' {
				inComment = false
			}
			i++
			continue
		}

		if inString {
			out.WriteByte(ch)
			if escaped {
				escaped = false
			} else if ch == '\\' {
				escaped = true
			} else if ch == '"' {
				inString = false
			}
			i++
			continue
		}

		if ch == ';' {
			inComment = true
			out.WriteByte(ch)
			i++
			continue
		}
		if ch == '"' {
			inString = true
			out.WriteByte(ch)
			i++
			continue
		}

		if ch == '#' && i+1 < len(src) && src[i+1] == '\'' {
			out.WriteByte('\'')
			i += 2
			continue
		}
		if ch == '#' {
			if repl, consumed, ok := parseRadixLiteral(src[i:]); ok {
				out.WriteString(repl)
				i += consumed
				continue
			}
		}
		if ch == '\\' && i+1 < len(src) {
			switch src[i+1] {
			case '?':
				out.WriteString(`"?"`)
				i += 2
				continue
			case '.':
				out.WriteString(`"."`)
				i += 2
				continue
			case ',':
				out.WriteString(`","`)
				i += 2
				continue
			case '!':
				out.WriteString(`"!"`)
				i += 2
				continue
			}
		}

		if ch == '1' && i+1 < len(src) && (src[i+1] == '+' || src[i+1] == '-') {
			prev := byte(0)
			if i > 0 {
				prev = src[i-1]
			}
			next := byte(0)
			if i+2 < len(src) {
				next = src[i+2]
			}
			if isDelimiter(prev) && isDelimiter(next) {
				if src[i+1] == '+' {
					out.WriteString("succ")
				} else {
					out.WriteString("pred")
				}
				i += 2
				continue
			}
		}

		if ch == '?' {
			repl, consumed, ok := parseCharLiteral(src[i:])
			if ok {
				out.WriteString(repl)
				i += consumed
				continue
			}
		}

		if ch == '[' {
			out.WriteString("(vector-literal ")
			vectorDepth++
			i++
			continue
		}
		if ch == '(' {
			if tok, n := readTokenAfterParen(src[i:]); tok == "point" || tok == "dun-mode" {
				j := i + n
				for j < len(src) && (src[j] == ' ' || src[j] == '\t' || src[j] == '\n' || src[j] == '\r') {
					j++
				}
				// Rewrite only zero-arg calls in call position.
				if j < len(src) && src[j] == ')' {
					if tok == "point" {
						out.WriteString("(el-point")
					} else {
						out.WriteString("(call-fn 'dun-mode")
					}
					i += n
					continue
				}
			}
		}
		if ch == ']' {
			if vectorDepth == 0 {
				return "", errors.New("unmatched ] in elisp source")
			}
			out.WriteByte(')')
			vectorDepth--
			i++
			continue
		}

		if isDigit(ch) && tokenLooksLikeLeadingDigitSymbol(src, i) {
			tok, n := readToken(src[i:])
			out.WriteString(normalizeLeadingDigitSymbol(tok))
			i += n
			continue
		}

		out.WriteByte(ch)
		i++
	}

	if inString {
		return "", errors.New("unterminated string literal")
	}
	if vectorDepth != 0 {
		return "", errors.New("unmatched [ in elisp source")
	}
	return out.String(), nil
}

func parseCharLiteral(s string) (string, int, bool) {
	if len(s) < 2 || s[0] != '?' {
		return "", 0, false
	}
	if len(s) >= 3 && s[1] == '\\' {
		if len(s) >= 5 && isOctal(s[2]) && isOctal(s[3]) && isOctal(s[4]) {
			v, err := strconv.ParseInt(s[2:5], 8, 32)
			if err != nil {
				return "", 0, false
			}
			return strconv.Itoa(int(v)), 5, true
		}
		if len(s) >= 3 {
			switch s[2] {
			case 'n':
				return "10", 3, true
			case 't':
				return "9", 3, true
			case 'r':
				return "13", 3, true
			case 'f':
				return "12", 3, true
			case 'b':
				return "8", 3, true
			case '\\':
				return strconv.Itoa(int('\\')), 3, true
			case ' ':
				return "32", 3, true
			default:
				return strconv.Itoa(int(s[2])), 3, true
			}
		}
	}
	r, width := rune(s[1]), 1
	if r >= 0x80 {
		r, width = utf8DecodeRuneInString(s[1:])
	}
	if width <= 0 {
		return "", 0, false
	}
	return strconv.Itoa(int(r)), 1 + width, true
}

func parseRadixLiteral(s string) (string, int, bool) {
	if len(s) < 3 || s[0] != '#' {
		return "", 0, false
	}
	base := 0
	switch s[1] {
	case 'o', 'O':
		base = 8
	case 'x', 'X':
		base = 16
	case 'b', 'B':
		base = 2
	default:
		return "", 0, false
	}
	j := 2
	for j < len(s) {
		c := s[j]
		if (c >= '0' && c <= '9') || (base == 16 && ((c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F'))) {
			j++
			continue
		}
		break
	}
	if j == 2 {
		return "", 0, false
	}
	v, err := strconv.ParseInt(s[2:j], base, 64)
	if err != nil {
		return "", 0, false
	}
	return strconv.FormatInt(v, 10), j, true
}

func utf8DecodeRuneInString(s string) (rune, int) {
	if len(s) == 0 {
		return 0, 0
	}
	r := []rune(s)
	if len(r) == 0 {
		return 0, 0
	}
	return r[0], len(string(r[0]))
}

func isOctal(b byte) bool {
	return b >= '0' && b <= '7'
}

func isWordRune(r rune) bool {
	if r == '_' {
		return true
	}
	return (r >= 'a' && r <= 'z') || (r >= 'A' && r <= 'Z') || (r >= '0' && r <= '9')
}

func isDelimiter(b byte) bool {
	if b == 0 {
		return true
	}
	switch b {
	case ' ', '\t', '\n', '\r', '(', ')', '[', ']', '\'', '`', ',', '"':
		return true
	default:
		return false
	}
}

func isDigit(b byte) bool {
	return b >= '0' && b <= '9'
}

func isSymbolChar(b byte) bool {
	if (b >= 'a' && b <= 'z') || (b >= 'A' && b <= 'Z') || isDigit(b) {
		return true
	}
	switch b {
	case '-', '_', ':', '/', '+', '*', '<', '>', '=', '?', '!', '$', '%', '&', '.', '~':
		return true
	default:
		return false
	}
}

func readToken(s string) (string, int) {
	j := 0
	for j < len(s) && isSymbolChar(s[j]) {
		j++
	}
	return s[:j], j
}

func readTokenAfterParen(s string) (string, int) {
	if len(s) < 2 || s[0] != '(' {
		return "", 0
	}
	i := 1
	for i < len(s) && (s[i] == ' ' || s[i] == '\t' || s[i] == '\n' || s[i] == '\r') {
		i++
	}
	tok, n := readToken(s[i:])
	if n == 0 {
		return "", 0
	}
	return tok, i + n
}

func tokenLooksLikeLeadingDigitSymbol(src string, pos int) bool {
	if pos > 0 && !isDelimiter(src[pos-1]) {
		return false
	}
	tok, n := readToken(src[pos:])
	if n == 0 {
		return false
	}
	if pos+n < len(src) && !isDelimiter(src[pos+n]) {
		return false
	}
	hasAlpha := false
	for i := 0; i < len(tok); i++ {
		if (tok[i] >= 'a' && tok[i] <= 'z') || (tok[i] >= 'A' && tok[i] <= 'Z') {
			hasAlpha = true
			break
		}
	}
	return hasAlpha
}

func normalizeLeadingDigitSymbol(tok string) string {
	if tok == "" {
		return tok
	}
	return "n-" + tok
}

const (
	keyPgUp  = 251
	keyLeft  = 252
	keyUp    = 253
	keyRight = 254
	keyDown  = 255
	keyPgDn  = 250
)

func runGameLoop(rt *runtimeState, env *golisp.SymbolTableFrame) error {
	tty, err := vt.NewTTY()
	if err != nil {
		rt.warnf("TTY unavailable, switching to headless loop: %v", err)
		return runHeadlessLoop(rt, env)
	}
	defer tty.Close()

	vt.Init()
	defer func() {
		vt.Close()
		fmt.Print(vt.Stop())
		fmt.Println()
	}()

	c := vt.NewCanvas()
	c.HideCursor()
	tty.SetTimeout(20 * time.Millisecond)

	keyCh := make(chan int, 32)
	stopCh := make(chan struct{})
	defer close(stopCh)
	go func() {
		pending := ""
		for {
			select {
			case <-stopCh:
				return
			default:
			}
			raw := tty.CustomString()
			if raw == "" {
				continue
			}
			keys, rest := parseTTYKeyStream(pending + raw)
			pending = rest
			for _, k := range keys {
				select {
				case keyCh <- k:
				default:
				}
			}
		}
	}()

	ticker := time.NewTicker(16 * time.Millisecond)
	defer ticker.Stop()
	rt.draw(c)
	for range ticker.C {
		if rt.gameName == "dunnet" && golisp.BooleanValue(env.ValueOf(golisp.Intern("dun-dead"))) {
			return nil
		}
		rt.tickTimers(env)
		for {
			select {
			case k := <-keyCh:
				if rt.handleKey(k, env) {
					return nil
				}
			default:
				rt.draw(c)
				goto nextFrame
			}
		}
	nextFrame:
	}
	return nil
}

func parseTTYKeyStream(raw string) ([]int, string) {
	if raw == "" {
		return nil, ""
	}
	if after, ok := strings.CutPrefix(raw, "c:"); ok {
		if n, err := strconv.Atoi(after); err == nil && n > 0 {
			return []int{normalizeVTKeyCode(n)}, ""
		}
	}

	keys := make([]int, 0, len(raw))
	for i := 0; i < len(raw); {
		if raw[i] == 0x1b {
			// Incomplete escape at end: keep for next read chunk.
			if i+1 >= len(raw) {
				return keys, raw[i:]
			}
			// CSI: ESC [ ... final
			if raw[i+1] == '[' {
				j := i + 2
				for j < len(raw) {
					c := raw[j]
					if (c >= '0' && c <= '9') || c == ';' {
						j++
						continue
					}
					break
				}
				if j >= len(raw) {
					return keys, raw[i:]
				}
				switch raw[j] {
				case 'A':
					keys = append(keys, keyUp)
					i = j + 1
					continue
				case 'B':
					keys = append(keys, keyDown)
					i = j + 1
					continue
				case 'C':
					keys = append(keys, keyRight)
					i = j + 1
					continue
				case 'D':
					keys = append(keys, keyLeft)
					i = j + 1
					continue
				case '~':
					param := raw[i+2 : j]
					switch param {
					case "5":
						keys = append(keys, keyPgUp)
					case "6":
						keys = append(keys, keyPgDn)
					}
					i = j + 1
					continue
				case 'u':
					// CSI-u extension: ESC [ <codepoint> ; ... u
					param := raw[i+2 : j]
					if param != "" {
						if head, _, ok := strings.Cut(param, ";"); ok {
							param = head
						}
						if cp, err := strconv.Atoi(param); err == nil && cp > 0 {
							keys = append(keys, normalizeVTKeyCode(cp))
						}
					}
					i = j + 1
					continue
				default:
					// Unknown CSI; consume it.
					i = j + 1
					continue
				}
			}
			// SS3: ESC O A/B/C/D
			if raw[i+1] == 'O' {
				if i+2 >= len(raw) {
					return keys, raw[i:]
				}
				switch raw[i+2] {
				case 'A':
					keys = append(keys, keyUp)
				case 'B':
					keys = append(keys, keyDown)
				case 'C':
					keys = append(keys, keyRight)
				case 'D':
					keys = append(keys, keyLeft)
				// Keypad digits in application mode (SS3).
				case 'p':
					keys = append(keys, int('0'))
				case 'q':
					keys = append(keys, int('1'))
				case 'r':
					keys = append(keys, int('2'))
				case 's':
					keys = append(keys, int('3'))
				case 't':
					keys = append(keys, int('4'))
				case 'u':
					keys = append(keys, int('5'))
				case 'v':
					keys = append(keys, int('6'))
				case 'w':
					keys = append(keys, int('7'))
				case 'x':
					keys = append(keys, int('8'))
				case 'y':
					keys = append(keys, int('9'))
				}
				i += 3
				continue
			}
			// Bare ESC key.
			keys = append(keys, 27)
			i++
			continue
		}

		r, size := utf8.DecodeRuneInString(raw[i:])
		if r == utf8.RuneError && size == 1 {
			i++
			continue
		}
		switch r {
		case '↑':
			keys = append(keys, keyUp)
		case '↓':
			keys = append(keys, keyDown)
		case '←':
			keys = append(keys, keyLeft)
		case '→':
			keys = append(keys, keyRight)
		case '⇞':
			keys = append(keys, keyPgUp)
		case '⇟':
			keys = append(keys, keyPgDn)
		default:
			if r >= 0 && r <= 255 {
				keys = append(keys, int(r))
			}
		}
		i += size
	}
	return keys, ""
}

func normalizeVTKeyCode(k int) int {
	switch k {
	// Common terminal key codes seen from VT backends.
	case 258:
		return keyDown
	case 259:
		return keyUp
	case 260:
		return keyLeft
	case 261:
		return keyRight
	case 338:
		return keyPgDn
	case 339:
		return keyPgUp
	default:
		return k
	}
}

func runHeadlessLoop(rt *runtimeState, env *golisp.SymbolTableFrame) error {
	// Keep timers and text-driven games alive in non-TTY environments.
	deadline := time.Now().Add(30 * time.Second)
	for time.Now().Before(deadline) {
		rt.tickTimers(env)
		if rt.gameName == "dunnet" && golisp.BooleanValue(env.ValueOf(golisp.Intern("dun-dead"))) {
			return nil
		}
		time.Sleep(20 * time.Millisecond)
	}
	return nil
}

func (rt *runtimeState) tickTimers(env *golisp.SymbolTableFrame) {
	now := time.Now()
	for _, t := range rt.timers {
		if t == nil || !t.active {
			continue
		}
		if t.nextFire.IsZero() {
			p := t.period
			if p <= 0 {
				p = 0.05
			}
			t.nextFire = now.Add(time.Duration(p * float64(time.Second)))
			continue
		}
		if now.Before(t.nextFire) {
			continue
		}
		if err := rt.invokeTimerCallback(t.callback, env); err != nil {
			if sig, ok := err.(elSignal); ok {
				// Timer-driven games often use conditions to end a session cleanly.
				if sig.condition == "quit" || sig.condition == "life-extinct" {
					t.active = false
					continue
				}
			}
			if isBenignTimerSignal(err) {
				t.active = false
				continue
			}
			rt.messages = append(rt.messages, "timer error: "+err.Error())
			rt.warnf("timer callback failed; disabling timer: %v", err)
			t.active = false
			continue
		}
		if t.period <= 0 {
			t.active = false
		} else {
			t.nextFire = now.Add(time.Duration(t.period * float64(time.Second)))
		}
	}
}

func (rt *runtimeState) invokeTimerCallback(cb *golisp.Data, env *golisp.SymbolTableFrame) error {
	var fn *golisp.Data
	switch {
	case golisp.SymbolP(cb):
		fn = env.ValueOf(cb)
	case golisp.FunctionOrPrimitiveP(cb):
		fn = cb
	default:
		return fmt.Errorf("unsupported timer callback: %s", golisp.String(cb))
	}
	if !golisp.FunctionOrPrimitiveP(fn) {
		return fmt.Errorf("timer callback resolved to non-function: %s", golisp.String(fn))
	}
	cbArg := rt.currentBuffer().object
	if _, err := golisp.ApplyWithoutEval(fn, golisp.ArrayToList([]*golisp.Data{cbArg}), env); err != nil {
		if _, err0 := golisp.ApplyWithoutEval(fn, golisp.EmptyCons(), env); err0 != nil {
			if _, ok := err0.(elSignal); ok {
				return err0
			}
			if isBenignTimerSignal(err0) {
				return err0
			}
			rt.warnf("timer callback failed with arg and no-arg forms: with-arg=%v no-arg=%v", err, err0)
			return err0
		}
	}
	return nil
}

func isBenignTimerSignal(err error) bool {
	if err == nil {
		return false
	}
	msg := err.Error()
	return strings.Contains(msg, "signal: life-extinct") || strings.Contains(msg, "signal: quit")
}

func (rt *runtimeState) call(name string, env *golisp.SymbolTableFrame) error {
	sym := golisp.Intern(name)
	fn := env.ValueOf(sym)
	if !golisp.FunctionOrPrimitiveP(fn) {
		return fmt.Errorf("function not found: %s", name)
	}
	_, err := golisp.ApplyWithoutEval(fn, golisp.EmptyCons(), env)
	return err
}

func (rt *runtimeState) callFirst(candidates []string, env *golisp.SymbolTableFrame) error {
	for _, name := range candidates {
		sym := golisp.Intern(name)
		if fn := env.ValueOf(sym); golisp.FunctionOrPrimitiveP(fn) {
			_, err := golisp.ApplyWithoutEval(fn, golisp.EmptyCons(), env)
			return err
		}
	}
	rt.warnOnce("missing-candidates-"+strings.Join(candidates, ","), "none of the candidate functions are defined: %s", strings.Join(candidates, ", "))
	return nil
}

func (rt *runtimeState) invokeByName(name string, env *golisp.SymbolTableFrame) error {
	fn := env.ValueOf(golisp.Intern(name))
	if !golisp.FunctionOrPrimitiveP(fn) {
		return fmt.Errorf("function not found: %s", name)
	}
	return rt.invokeBoundCommand(fn, env)
}

func keyCandidates(key int) []string {
	switch key {
	case 10, 13:
		return []string{"\r", "\n", "RET", "C-m"}
	case 9:
		return []string{"\t", "TAB", "<tab>", "C-i"}
	case 27:
		return []string{"ESC", "<escape>"}
	case int(' '):
		return []string{"SPC", " "}
	case 2:
		return []string{"C-b"}
	case 6:
		return []string{"C-f"}
	case 14:
		return []string{"C-n"}
	case 16:
		return []string{"C-p"}
	case keyLeft:
		return []string{"<left>", "left", "C-b"}
	case keyRight:
		return []string{"<right>", "right", "C-f"}
	case keyUp:
		return []string{"<up>", "up", "C-p"}
	case keyDown:
		return []string{"<down>", "down", "C-n"}
	case 3:
		return []string{"C-c"}
	default:
		if key >= 32 && key <= 126 {
			return []string{string(rune(key))}
		}
	}
	return nil
}

func (rt *runtimeState) dispatchViaCurrentKeymap(key int, env *golisp.SymbolTableFrame) bool {
	m := rt.currentBuffer().localMap
	if m == nil || !isKeymap(m) {
		return false
	}
	km := asKeymap(m)
	for _, k := range keyCandidates(key) {
		if binding, ok := km.bindings[k]; ok {
			_, target := resolveKeyBinding(binding, env)
			if golisp.FunctionOrPrimitiveP(target) {
				if err := rt.invokeBoundCommand(target, env); err == nil {
					return true
				}
				rt.warnf("keymap dispatch error for %s", k)
			}
		}
	}
	return false
}

func (rt *runtimeState) invokeBoundCommand(fn *golisp.Data, env *golisp.SymbolTableFrame) error {
	// Many interactive commands in games are defined as (_arg) and are
	// called by keymaps with a prefix argument in Emacs.
	_, err := golisp.ApplyWithoutEval(fn, golisp.EmptyCons(), env)
	if err == nil {
		return nil
	}
	if n, ok := parseExpectedArgCount(err.Error()); ok && n == 1 {
		one := golisp.ArrayToList([]*golisp.Data{golisp.IntegerWithValue(1)})
		if _, err2 := golisp.ApplyWithoutEval(fn, one, env); err2 == nil {
			return nil
		}
		nilArg := golisp.ArrayToList([]*golisp.Data{golisp.EmptyCons()})
		_, err3 := golisp.ApplyWithoutEval(fn, nilArg, env)
		if err3 == nil {
			return nil
		}
		rt.messages = append(rt.messages, err3.Error())
		return err3
	}
	rt.messages = append(rt.messages, err.Error())
	return err
}

func (rt *runtimeState) handleKey(key int, env *golisp.SymbolTableFrame) bool {
	if rt.dispatchViaCurrentKeymap(key, env) {
		return false
	}

	// Text-buffer games (like dunnet) should treat printable keys as input,
	// not as global game controls.
	if rt.gridWidth == 0 {
		switch key {
		case 3, 27:
			return true
		case int('q'):
			if rt.gameName == "life" {
				return true
			}
		case 10, 13:
			if rt.gameName == "dunnet" {
				if err := rt.handleDunnetEnter(env); err != nil {
					rt.messages = append(rt.messages, err.Error())
					rt.warnf("dunnet enter handler error: %v", err)
				}
				return false
			}
			for _, name := range []string{"dun-parse", "dun-unix-parse", "dun-dos-parse"} {
				if err := rt.invokeByName(name, env); err == nil {
					return false
				}
			}
			_, _ = insertImpl(golisp.ArrayToList([]*golisp.Data{golisp.IntegerWithValue('\n')}), nil)
			return false
		case 127, 8:
			buf := rt.currentBuffer()
			if buf != nil && buf.point > 0 && len(buf.text) > 0 {
				buf.text = append(buf.text[:buf.point-1], buf.text[buf.point:]...)
				buf.point--
			}
			return false
		case keyLeft:
			buf := rt.currentBuffer()
			if buf != nil && buf.point > 0 {
				buf.point--
			}
			return false
		case keyRight:
			buf := rt.currentBuffer()
			if buf != nil && buf.point < len(buf.text) {
				buf.point++
			}
			return false
		default:
			if key >= 32 && key <= 126 {
				_, _ = insertImpl(golisp.ArrayToList([]*golisp.Data{golisp.IntegerWithValue(int64(key))}), nil)
			}
			return false
		}
	}

	switch key {
	case int('q'), 3, 27:
		_ = rt.callFirst([]string{"tetris-end-game", "snake-end-game", "pong-quit"}, env)
		return true
	case int('n'):
		if err := rt.callFirst([]string{"tetris-start-game", "snake-start-game", "pong"}, env); err != nil {
			rt.messages = append(rt.messages, err.Error())
			rt.warnf("key n handler error: %v", err)
		}
		return false
	case int('p'):
		if err := rt.callFirst([]string{"tetris-pause-game", "snake-pause-game", "pong-pause", "pong-resume"}, env); err != nil {
			rt.messages = append(rt.messages, err.Error())
			rt.warnf("key p handler error: %v", err)
		}
		return false
	case int(' '):
		if err := rt.callFirst([]string{"tetris-move-bottom"}, env); err != nil {
			rt.messages = append(rt.messages, err.Error())
			rt.warnf("space handler error: %v", err)
		}
		return false
	case keyLeft:
		if err := rt.callFirst([]string{"tetris-move-left", "snake-move-left", "pong-move-left"}, env); err != nil {
			rt.messages = append(rt.messages, err.Error())
			rt.warnf("left handler error: %v", err)
		}
		return false
	case keyRight:
		if err := rt.callFirst([]string{"tetris-move-right", "snake-move-right", "pong-move-right"}, env); err != nil {
			rt.messages = append(rt.messages, err.Error())
			rt.warnf("right handler error: %v", err)
		}
		return false
	case keyDown:
		if err := rt.callFirst([]string{"tetris-move-down", "snake-move-down", "pong-move-down"}, env); err != nil {
			rt.messages = append(rt.messages, err.Error())
			rt.warnf("down handler error: %v", err)
		}
		return false
	case keyUp:
		if err := rt.callFirst([]string{"tetris-rotate-prev", "snake-move-up", "pong-move-up"}, env); err != nil {
			rt.messages = append(rt.messages, err.Error())
			rt.warnf("up handler error: %v", err)
		}
		return false
	case keyPgDn:
		if err := rt.callFirst([]string{"tetris-rotate-next"}, env); err != nil {
			rt.messages = append(rt.messages, err.Error())
			rt.warnf("pgdn handler error: %v", err)
		}
		return false
	case keyPgUp:
		if err := rt.callFirst([]string{"tetris-rotate-prev"}, env); err != nil {
			rt.messages = append(rt.messages, err.Error())
			rt.warnf("pgup handler error: %v", err)
		}
		return false
	default:
		return false
	}
}

func (rt *runtimeState) currentInputLine() string {
	buf := rt.currentBuffer()
	if buf == nil || len(buf.text) == 0 {
		return ""
	}
	p := min(max(buf.point, 0), len(buf.text))
	start := p
	for start > 0 && buf.text[start-1] != '\n' {
		start--
	}
	line := strings.TrimSpace(string(buf.text[start:p]))
	line = strings.TrimPrefix(line, ">")
	line = strings.TrimPrefix(line, "$")
	line = strings.TrimSpace(line)
	return line
}

func (rt *runtimeState) handleDunnetEnter(env *golisp.SymbolTableFrame) error {
	line := rt.currentInputLine()
	mode := featureName(env.ValueOf(golisp.Intern("dungeon-mode")))
	switch mode {
	case "unix":
		return rt.callDunnetParser("dun-parse2", env, golisp.EmptyCons(), env.ValueOf(golisp.Intern("dun-unix-verbs")), golisp.StringWithValue(strings.ToLower(line)))
	case "dos":
		return rt.callDunnetParser("dun-parse2", env, golisp.EmptyCons(), env.ValueOf(golisp.Intern("dun-dos-verbs")), golisp.StringWithValue(strings.ToLower(line)))
	default:
		if line == "" {
			return rt.invokeByName("dun-messages", env)
		}
		res, err := rt.callDunnetParserRaw("dun-vparse", env, env.ValueOf(golisp.Intern("dun-ignore")), env.ValueOf(golisp.Intern("dun-verblist")), golisp.StringWithValue(strings.ToLower(line)))
		if err != nil {
			return err
		}
		if golisp.IntegerP(res) && golisp.IntegerValue(res) == -1 {
			_ = rt.callDunnetParser("dun-mprincl", env, golisp.StringWithValue("I don't understand that."))
		}
		return rt.invokeByName("dun-messages", env)
	}
}

func (rt *runtimeState) callDunnetParser(name string, env *golisp.SymbolTableFrame, args ...*golisp.Data) error {
	_, err := rt.callDunnetParserRaw(name, env, args...)
	return err
}

func (rt *runtimeState) callDunnetParserRaw(name string, env *golisp.SymbolTableFrame, args ...*golisp.Data) (*golisp.Data, error) {
	fn := env.ValueOf(golisp.Intern(name))
	if !golisp.FunctionOrPrimitiveP(fn) {
		return nil, fmt.Errorf("function not found: %s", name)
	}
	return golisp.ApplyWithoutEval(fn, golisp.ArrayToList(args), env)
}

func (rt *runtimeState) defaultStatusLine() string {
	switch rt.gameName {
	case "tetris":
		return "q quit | n new | p pause | arrows move/rotate | space drop"
	case "snake":
		return "q quit | n new | p pause | arrows move"
	case "pong":
		return "q quit | p pause/resume | arrows move paddles"
	default:
		return "q quit | game keys come from current keymap"
	}
}

func resolveKeyBinding(binding *golisp.Data, env *golisp.SymbolTableFrame) (string, *golisp.Data) {
	if binding == nil {
		return "", nil
	}
	target := binding
	name := ""
	if golisp.PairP(target) && golisp.SymbolP(golisp.Car(target)) && golisp.StringValue(golisp.Car(target)) == "quote" {
		target = golisp.Cadr(target)
	}
	if golisp.SymbolP(target) {
		name = golisp.StringValue(target)
		target = env.ValueOf(target)
		return name, target
	}
	if golisp.FunctionP(target) {
		if f := golisp.FunctionValue(target); f != nil {
			name = f.Name
		}
		return name, target
	}
	if golisp.PrimitiveP(target) {
		return golisp.String(target), target
	}
	return name, target
}

func prettyKeyName(k string) string {
	switch k {
	case " ", "SPC":
		return "space"
	case "<left>":
		return "left"
	case "<right>":
		return "right"
	case "<up>":
		return "up"
	case "<down>":
		return "down"
	case "<prior>":
		return "pgup"
	case "<next>":
		return "pgdn"
	default:
		return k
	}
}

func prettyActionNameForGame(gameName, fnName string) string {
	// Pong's function names are historical and don't match movement direction.
	if gameName == "pong" {
		switch fnName {
		case "pong-move-left":
			return "p1 up"
		case "pong-move-right":
			return "p1 down"
		case "pong-move-up":
			return "p2 up"
		case "pong-move-down":
			return "p2 down"
		}
	}
	return prettyActionName(fnName)
}

func prettyActionName(fnName string) string {
	n := strings.ToLower(fnName)
	switch {
	case strings.Contains(n, "start-game"), strings.HasSuffix(n, "-start"):
		return "new"
	case strings.Contains(n, "pause"), strings.Contains(n, "resume"):
		return "pause"
	case strings.Contains(n, "quit"), strings.Contains(n, "end-game"), strings.HasSuffix(n, "-end"):
		return "quit"
	case strings.Contains(n, "move-bottom"), strings.Contains(n, "drop"):
		return "drop"
	case strings.Contains(n, "rotate-next"):
		return "rot cw"
	case strings.Contains(n, "rotate-prev"):
		return "rot ccw"
	case strings.Contains(n, "move-left"):
		return "left"
	case strings.Contains(n, "move-right"):
		return "right"
	case strings.Contains(n, "move-up"):
		return "up"
	case strings.Contains(n, "move-down"):
		return "down"
	case strings.Contains(n, "undo"):
		return "undo"
	case strings.Contains(n, "restart"):
		return "restart"
	default:
		if fnName == "" {
			return "action"
		}
		return strings.ReplaceAll(fnName, "-", " ")
	}
}

func (rt *runtimeState) statusFromCurrentKeymap() (string, bool) {
	m := rt.currentBuffer().localMap
	if m == nil || !isKeymap(m) {
		return "", false
	}
	km := asKeymap(m)
	if len(km.bindings) == 0 {
		return "", false
	}

	priority := []string{"q", "n", "p", " ", "<left>", "<right>", "<up>", "<down>", "<prior>", "<next>", "C-c"}
	seen := make(map[string]bool)
	tokens := make([]string, 0, 10)

	addBinding := func(key string) {
		b, ok := km.bindings[key]
		if !ok {
			return
		}
		fnName, _ := resolveKeyBinding(b, rt.env)
		label := fmt.Sprintf("%s %s", prettyKeyName(key), prettyActionNameForGame(rt.gameName, fnName))
		if !seen[label] {
			seen[label] = true
			tokens = append(tokens, label)
		}
	}

	for _, k := range priority {
		addBinding(k)
	}

	otherKeys := make([]string, 0, len(km.bindings))
	for k := range km.bindings {
		isPriority := slices.Contains(priority, k)
		if !isPriority {
			otherKeys = append(otherKeys, k)
		}
	}
	sort.Strings(otherKeys)
	for _, k := range otherKeys {
		if len(tokens) >= 8 {
			break
		}
		addBinding(k)
	}

	if len(tokens) == 0 {
		return "", false
	}
	return strings.Join(tokens, " | "), true
}

func (rt *runtimeState) draw(c *vt.Canvas) {
	c.Clear()
	w, h := c.Size()
	if rt.gridWidth == 0 || rt.gridHeight == 0 {
		rt.drawTextBuffer(c, w, h)
		c.Draw()
		return
	}
	gridH := min(uint(rt.gridHeight), h-1)
	gridW := min(uint(rt.gridWidth), w)
	for y := range gridH {
		for x := range gridW {
			v, ok := rt.grid[[2]int{int(x), int(y)}]
			if !ok {
				v = rt.gridDefault
			}
			r, fg, bg := rt.cellStyle(v)
			c.WriteRune(x, y, fg, bg, r)
		}
	}
	status := rt.defaultStatusLine()
	if kmStatus, ok := rt.statusFromCurrentKeymap(); ok {
		status = kmStatus
	}
	if len(rt.messages) > 0 {
		status = rt.messages[len(rt.messages)-1]
	}
	if len(status) > int(w) {
		status = status[:w]
	}
	if h > 0 {
		c.WriteString(0, h-1, vt.LightGray, vt.DefaultBackground, status)
	}
	c.Draw()
}

func (rt *runtimeState) drawTextBuffer(c *vt.Canvas, w, h uint) {
	if h == 0 {
		return
	}
	buf := rt.currentBuffer()
	text := ""
	if buf != nil {
		text = string(buf.text)
	}
	lines := strings.Split(text, "\n")
	visible := max(int(h-1), 0)
	start := 0
	if len(lines) > visible {
		start = len(lines) - visible
	}
	y := uint(0)
	for i := start; i < len(lines) && y < h-1; i++ {
		line := lines[i]
		if len(line) > int(w) {
			line = line[:w]
		}
		c.WriteString(0, y, vt.LightGray, vt.DefaultBackground, line)
		y++
	}
	status := rt.defaultStatusLine()
	if len(rt.messages) > 0 {
		status = rt.messages[len(rt.messages)-1]
	}
	if len(status) > int(w) {
		status = status[:w]
	}
	c.WriteString(0, h-1, vt.LightGray, vt.DefaultBackground, status)
}

func (rt *runtimeState) cellStyle(d *golisp.Data) (rune, vt.AttributeColor, vt.AttributeColor) {
	bg := vt.DefaultBackground
	fg := vt.White
	if golisp.IntegerP(d) {
		n := golisp.IntegerValue(d)
		switch rt.gameName {
		case "snake":
			switch n {
			case 0, 4:
				return ' ', fg, bg
			case 1:
				return '█', vt.LightGreen, bg
			case 2:
				return '●', vt.LightRed, bg
			case 3:
				return '▒', vt.LightGray, bg
			default:
				rt.warnOnce(fmt.Sprintf("snake-unknown-cell-%d", n), "unknown snake cell value: %d", n)
			}
		default:
			switch n {
			case 0, 1, 2, 3, 4, 5, 6:
				cols := []vt.AttributeColor{vt.Blue, vt.White, vt.Yellow, vt.Magenta, vt.Cyan, vt.Green, vt.Red}
				return '█', cols[n], bg
			case 7, 9:
				return ' ', fg, bg
			case 8:
				return '▒', vt.LightGray, bg
			default:
				rt.warnOnce(fmt.Sprintf("tetris-unknown-cell-%d", n), "unknown tetris cell value: %d", n)
			}
		}
		if n >= 32 && n <= 126 {
			return rune(n), vt.LightGray, bg
		}
	}
	if golisp.StringP(d) {
		s := golisp.StringValue(d)
		if s == "" {
			return ' ', fg, bg
		}
		return []rune(s)[0], vt.LightGray, bg
	}
	t := golisp.TypeName(golisp.TypeOf(d))
	rt.warnOnce("unknown-cell-type-"+t, "unknown cell data type: %s (%s)", t, golisp.String(d))
	return ' ', fg, bg
}
