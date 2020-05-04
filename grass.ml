
(* base *)
let true = w w
let car c = c true
let false x y = y
let cdr c = c false
let cons x y b = b x y

let tag = car
let val = cdr

(* insn *)
let tApp = w
let tAbs = Succ w
let isApp obj = tag obj tApp
let isAbs obj = tag obj tAbs

let makeApp m n = cons tApp (cons m n)
let App_fun app = car (val app)
let App_arg app = cdr (val app)

let cinc n f x = f (n f x)
let Abs_len abs = car (val abs)
let Abs_code abs = cdr (val abs)
let Abs_push abs insn =
  let l = cinc (Abs_len abs) in
  let c = cons insn (Abs_code abs) in
    cons tAbs (cons l c)


(* value *)
let tCh = w
let tPrim = Succ tCh
let tFn = Succ tPrim

let makeCh c = cons tCh c
let pSucc v = makeCh (Succ (val v))
let pOut v = makeCh (Out (val v))
let ignore2 x y z = z
let pIn v =
  let c = In ignore2 in
  let d = c c in
  let ret = makeCh c in
    d ret v
let makePrim p = cons tPrim p

let initialEnv _ =
  let vw = makeCh w in
  let vSucc = makePrim pSucc in
  let vOut = makePrim pOut in
  let vIn = makePrim pIn in
    cons vOut (cons vSucc (cons vw (cons vIn Succ)))

let makeFn abs e = cons tFn (cons abs e)
let Fn_abs f = car (val f)
let Fn_env f = cdr (val f)
let cn1 f x = f x
let cn2 f x = f (f x)
let nil x y = y
let blankabs = cons tAbs (cons nil nil)
let makeTrue a =
  let a1 = Abs_push a (makeApp cn2 cn1) in
  let a2 = Abs_push a a1 in
  let d = makeFn a nil in
    makeFn a2 d
let vTrue = makeTrue blankabs
let makeFalse a = makeFn (Abs_push a a) nil
let vFalse = makeFalse blankabs

let applyCh ch a = (val ch) (val a) vTrue vFalse
let applyPrim p a = (val p) a

let applyFn ee f a =
  let e = Fn_env f in
  let abs = Fn_abs f in
  let len = Abs_len abs in
  let code = Abs_code abs in
  let m = len ee (cons code (cons a e)) in
    car (cdr m)

let ref lst idx = car (idx cdr lst)
let apply ee app e =
  let refe = ref e in
  let f = refe (App_fun app) in
  let ft = tag f in
  let a = refe (App_arg app) in 
  let iffn = ft tFn (applyFn ee f) in
  let ifprim = ft tPrim (applyPrim f) in
  let t = iffn (ifprim (applyCh f)) in
    t a

let eval1 self machine =
  let recur = self self in
  let env = cdr machine in
  let code = car machine in
  let insn = car code in
  let b = isApp insn in
  let appt = apply recur in
  let v = b appt makeFn insn env in
    cons (cdr code) (cons v env)

let cn0 f x = x
let run prog =
  let e0 = initialEnv prog in
  let m = cons (Abs_code prog) e0 in
  let ee = eval1 eval1 in 
  let result = Abs_len prog ee m in
    ee (cons (cons (makeApp cn0 cn0) cn0) (cdr result))


(* make W,v,V  ref. http://golf.shinh.org/reveal.rb?Quine/kik_1221407798&grass *)
let f2s f x = Succ (f (f x))
let cn2 f x = f (f x)
let genvW c f =
  let t2 = cn2 f2s Succ in
  let t3 = f t2 in
  let t4 = cn2 f in
    t4 (t4 t3) c
let id x = x
let w = id w
let t = genvW w
let v = t f2s
let W = t cn2
let V = genvW W f2s

(* lexer *)
let true = V V
let false x y = y
let nil = false
let cn0 = false
let and x y = x y false
let or x y = x true y
let not x = x false true
let eof x y z = z
let iswWv c = or (c w) (or (c W) (c v))
let lex_makecont c n k acc = k (cons (cons c n) acc)
let lexf self cc n k tail = (* cc: current char; n: count; k: continuation *)
  let recur = self self in
  let c = In V in
  let iseof = V c (lex_makecont cc n k) in
  let iscc = cc c (recur cc (cinc n) k) in
  let issrc = iswWv c (recur c cn0 (lex_makecont cc n k)) in
  let skip = recur cc n k in
    iseof (iscc (issrc skip)) tail
let lex _ =
  let tail = cons (cons V cn0) nil in
    lexf lexf v cn0 id tail
(* ex.
  input: wWWwwww
  result: ((w . cn0) (W . cn1) (w . cn3) (V . cn0))
 *)


(* parser *)
let abort _ = Out Succ
let isnil x =
  let d _ _ _ x y = y in
    x d true

let skipvWf self pairs =
  let recur = self self in
  let e = isnil pairs abort in
  let errexit = e e e in
  let c = car (car pairs) in
  let b = c w in
    b (b pairs) recur (cdr pairs)
let skipvW = skipvWf skipvWf

let id x = x
let blankabs = id blankabs

let parse_app pairs =
  let f = cdr (car pairs) in
  let rest = cdr pairs in
  let next = car rest in
  let c = car next in
  let e = or (v c) (V c) abort in
  let errexit = e e e in
  let a = cdr next in
    cons (makeApp f a) (cdr rest)

let parse_makecont insn k acc = k (Abs_push acc insn)
let parse_absbody self pairs k _ _ =
  let recur = self self in
  let c = car (car pairs) in
  let isvV = or (c v) (c V) in
  let ir = isvV id parse_app pairs in
  let app = car ir in
  let nk = parse_makecont app k in
  let rest = cdr ir in
    isvV k (recur rest nk) blankabs pairs

let parse_abs pairs =
  let t = parse_absbody parse_absbody (cdr pairs) cons in
  let body_rest = t t t in
  let body = car body_rest in
  let rest = cdr body_rest in
  let arity = cdr (car pairs) in
  let f = Abs_push blankabs in
    cons (arity f body) rest

let parse_code self pairs k _ =
  let recur = self self in
  let c = car (car pairs) in
  let isw = c w parse_abs in
  let isW = c W parse_app in
  let ir = isw (isW id) pairs in
  let insn = car ir in
  let nk = parse_makecont insn k in
  let rest = cdr ir in
  let isv = c v in
  let isV = c V in
    isV k (recur rest (isv k nk)) blankabs

let parse pairs = 
  let src = skipvW pairs in
  let p = parse_code parse_code src id in
    p p

(* main *)
let main self =
  let tk = lex self in
  let code = parse tk in
    run code
