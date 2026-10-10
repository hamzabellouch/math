import OAI.ModelTheory.Choiceless.Stack

namespace OAI

namespace CPTSeparation.GaussMachine

open StackLang StackLang.Macros SerialGaussian

inductive Reg where
 | mat | back | scan | piv | pivBack | width | output
 deriving DecidableEq

instance : Fintype Reg where
 elems := {.mat, .back, .scan, .piv, .pivBack, .width, .output}
 complete := by intro k; cases k <;> simp

structure Control where
  pivot : Scalar := 0
  factor : Scalar := 0
  answer : Bool := true
 deriving DecidableEq, Fintype

abbrev Local := Option Scalar × Control

abbrev Prog := SProgram Reg Letter Local

structure Data where
  mat : List Letter := []
  back : List Letter := []
  scan : List Letter := []
  piv : List Letter := []
  pivBack : List Letter := []
  width : List Letter := []
  output : List Letter := []
 deriving DecidableEq

def Data.tapes (d : Data) : Reg → List Letter
 | .mat => d.mat
 | .back => d.back
 | .scan => d.scan
 | .piv => d.piv
 | .pivBack => d.pivBack
 | .width => d.width
 | .output => d.output

@[simp] lemma tapes_mat (d : Data) (xs : List Letter) : Function.update d.tapes .mat xs = ({d with mat := xs}).tapes := by funext k; cases k <;> simp [Data.tapes,Function.update]

@[simp] lemma tapes_back (d : Data) (xs : List Letter) : Function.update d.tapes .back xs = ({d with back := xs}).tapes := by funext k; cases k <;> simp [Data.tapes,Function.update]

@[simp] lemma tapes_scan (d : Data) (xs : List Letter) : Function.update d.tapes .scan xs = ({d with scan := xs}).tapes := by funext k; cases k <;> simp [Data.tapes,Function.update]

@[simp] lemma tapes_piv (d : Data) (xs : List Letter) : Function.update d.tapes .piv xs = ({d with piv := xs}).tapes := by funext k; cases k <;> simp [Data.tapes,Function.update]

@[simp] lemma tapes_pivBack (d : Data) (xs : List Letter) : Function.update d.tapes .pivBack xs = ({d with pivBack := xs}).tapes := by funext k; cases k <;> simp [Data.tapes,Function.update]

@[simp] lemma tapes_width (d : Data) (xs : List Letter) : Function.update d.tapes .width xs = ({d with width := xs}).tapes := by funext k; cases k <;> simp [Data.tapes,Function.update]

@[simp] lemma tapes_output (d : Data) (xs : List Letter) : Function.update d.tapes .output xs = ({d with output := xs}).tapes := by funext k; cases k <;> simp [Data.tapes,Function.update]

def st (c : Control) (buf : Option Letter) (d : Data) : SStore Reg Letter Local := state (none,c) buf d.tapes

def _root_.OAI.CPTSeparation.SerialGaussian.Row.entries {n} (r : SerialGaussian.Row n) : List Scalar := r.coeff ++ [r.rhs]

@[simp] lemma entries_length {n} (r : SerialGaussian.Row n) : r.entries.length = n+1 := by simp [SerialGaussian.Row.entries,r.length_eq]

lemma payload_cons {n} (r : SerialGaussian.Row n) (rs) :
 payload (r::rs) = r.entries.map some ++ none::payload rs := by
 simp [payload,SerialGaussian.Row.entries,List.map_append,List.append_assoc]

lemma entries_head_tail {n} (r : SerialGaussian.Row (n+1)) :
 r.entries = r.head :: r.tail.entries := by
 rcases r with ⟨coeff,hl,rhs⟩
 cases coeff with
 | nil => simp at hl
 | cons a coeff => rfl

def scanBody : Prog :=
 .seq (.atom (.pop .scan (fun c a => (none,(none,{c.2.2 with factor := (a.bind id).getD 0}))) .done))
 (.seq (.cond (fun c => c.2.2.pivot == 0 && c.2.2.factor != 0)
    (.seq (.atom (.load (fun c => (c.1,(none,{c.2.2 with pivot := c.2.2.factor}))) .done))
      (moveRow .scan .pivBack (fun _ a => a)))
    (skipRow .scan))
  (.atom (.peek .scan (fun c a => (a,(none,{c.2.2 with factor := 0}))) .done)))

def scanLoop : Prog := .loop (fun c => c.1.isSome) scanBody

def scanMatrix : Prog := .seq (peek .scan) scanLoop

lemma scanBody_skip {n} (c : Control) (buf : Option Letter) (d : Data)
    (r : SerialGaussian.Row (n+1)) (rs : List (SerialGaussian.Row (n+1)))
    (h : c.pivot ≠ 0 ∨ r.head = 0) :
 Runs scanBody (st c buf {d with scan := payload (r::rs)})
   (st {c with factor := 0} (payload rs).head? {d with scan := payload rs})
   (2*(n+1)+10) := by
 let c' : Control := {c with factor := r.head}
 have hp : Runs (.atom (.pop .scan (fun (c : Option Letter × Local) a =>
       (none,(none,{c.2.2 with factor := (a.bind id).getD 0}))) .done))
     (st c buf {d with scan := payload (r::rs)})
     (st c' none {d with scan := r.tail.entries.map some ++ none::payload rs}) 1 := by
   apply Runs.atom_of
   simp [Action.run,st,state,payload_cons,entries_head_tail,c',Data.tapes]
 have hs := skipRow_runs (σ := Local) Reg.scan (none,c') none d.tapes
   r.tail.entries (payload rs)
 have hs' : Runs (skipRow Reg.scan)
      (st c' none {d with scan := r.tail.entries.map some ++ none::payload rs})
      (st c' none {d with scan := payload rs}) (2*(n+1)+5) := by
   simpa [st] using hs
 have hc := Runs.cond_false (a := .seq
    (.atom (.load (fun c : Option Letter × Local =>
      (c.1,(none,{c.2.2 with pivot := c.2.2.factor}))) .done))
    (moveRow Reg.scan Reg.pivBack (fun (_ : Local) a => a)))
    (f := fun c : Option Letter × Local => c.2.2.pivot == 0 && c.2.2.factor != 0)
    (s := st c' none {d with scan := r.tail.entries.map some ++ none::payload rs})
    (by rcases h with h | h <;> simp_all [st,state,c']) hs'
 have hf : Runs (.atom (.peek .scan (fun (c : Option Letter × Local) a =>
       (a,(none,{c.2.2 with factor := 0}))) .done))
     (st c' none {d with scan := payload rs})
     (st {c with factor := 0} (payload rs).head? {d with scan := payload rs}) 1 := by
   apply Runs.atom_of
   simp [Action.run,st,state,c',Data.tapes]
 convert hp.seq (hc.seq hf) using 1 <;> first | rfl | omega

def ctrl (p : Scalar) (a : Bool) : Control := ⟨p,0,a⟩

lemma payload_head {n} (r : SerialGaussian.Row (n+1)) (rs) :
 (payload (r::rs)).head? = some (some r.head) := by
 rw [payload_cons,entries_head_tail]
 rfl

lemma scanLoop_nonzero {n} (p : Scalar) (hp : p ≠ 0) (a : Bool) (d : Data)
    (rs : List (SerialGaussian.Row (n+1))) :
 Runs scanLoop (st (ctrl p a) (payload rs).head? {d with scan := payload rs})
   (st (ctrl p a) none {d with scan := []}) ((2*(n+1)+13)*rs.length+1) := by
 induction rs with
 | nil => exact Runs.loop_false rfl
 | cons r rs ih =>
   have hb := scanBody_skip (ctrl p a) (payload (r::rs)).head? d r rs (Or.inl hp)
   have h := Runs.loop_true (f := fun c : Option Letter × Local => c.1.isSome)
     (by simp [st,state,payload_head]) hb ih
   exact h.mono (by simp only [List.length_cons,Nat.mul_add,Nat.mul_one]; omega)

lemma scanBody_pick {n} (a : Bool) (buf : Option Letter) (d : Data)
    (r : SerialGaussian.Row (n+1)) (rs : List (SerialGaussian.Row (n+1))) (hr : r.head ≠ 0) :
 Runs scanBody (st (ctrl 0 a) buf {d with scan := payload (r::rs), pivBack := []})
   (st (ctrl r.head a) (payload rs).head?
     {d with scan := payload rs, pivBack := (r.tail.entries.map some).reverse})
   (2*(n+1)+12) := by
 let c' : Control := ⟨0,r.head,a⟩
 let c'' : Control := ⟨r.head,r.head,a⟩
 have hp : Runs (.atom (.pop .scan (fun (c : Option Letter × Local) a =>
       (none,(none,{c.2.2 with factor := (a.bind id).getD 0}))) .done))
     (st (ctrl 0 a) buf {d with scan := payload (r::rs),pivBack := []})
     (st c' none {d with scan := r.tail.entries.map some ++ none::payload rs,pivBack := []}) 1 := by
   apply Runs.atom_of
   simp [Action.run,st,state,payload_cons,entries_head_tail,c',ctrl,Data.tapes]
 have hl : Runs (.atom (.load (fun c : Option Letter × Local =>
       (c.1,(none,{c.2.2 with pivot := c.2.2.factor}))) .done))
     (st c' none {d with scan := r.tail.entries.map some ++ none::payload rs,pivBack := []})
     (st c'' none {d with scan := r.tail.entries.map some ++ none::payload rs,pivBack := []}) 1 := by
   exact Runs.atom_of _ _ _ rfl
 have hm := moveRow_runs Reg.scan Reg.pivBack (by decide) (fun (_ : Local) a => a)
   (none,c'') none d.tapes r.tail.entries (payload rs) []
 have hm' : Runs (moveRow Reg.scan Reg.pivBack (fun (_ : Local) a => a))
      (st c'' none {d with scan := r.tail.entries.map some ++ none::payload rs,pivBack := []})
      (st c'' none {d with scan := payload rs,pivBack := (r.tail.entries.map some).reverse})
      (2*(n+1)+5) := by simpa [st] using hm
 have hc := Runs.cond_true (b := skipRow Reg.scan)
    (f := fun c : Option Letter × Local => c.2.2.pivot == 0 && c.2.2.factor != 0)
    (s := st c' none {d with scan := r.tail.entries.map some ++ none::payload rs,pivBack := []})
    (by simpa [st,state,c'] using hr) (hl.seq hm')
 have hf : Runs (.atom (.peek .scan (fun (c : Option Letter × Local) a =>
       (a,(none,{c.2.2 with factor := 0}))) .done))
     (st c'' none {d with scan := payload rs,pivBack := (r.tail.entries.map some).reverse})
     (st (ctrl r.head a) (payload rs).head?
       {d with scan := payload rs,pivBack := (r.tail.entries.map some).reverse}) 1 := by
   apply Runs.atom_of
   simp [Action.run,st,state,c'',ctrl,Data.tapes]
 convert hp.seq (hc.seq hf) using 1 <;> first | rfl | omega

def pivotHead {n} (p : Option (SerialGaussian.Row (n+1))) : Scalar := p.elim 0 Row.head

def pivotTail {n} (p : Option (SerialGaussian.Row (n+1))) : List Letter :=
 p.elim [] (fun r => r.tail.entries.map some)

lemma scanLoop_initial {n} (a : Bool) (d : Data) (rs : List (SerialGaussian.Row (n+1))) :
 Runs scanLoop (st (ctrl 0 a) (payload rs).head? {d with scan := payload rs,pivBack := []})
   (st (ctrl (pivotHead (pivot rs)) a) none
      {d with scan := [],pivBack := (pivotTail (pivot rs)).reverse})
   ((2*(n+1)+13)*rs.length+1) := by
 induction rs with
 | nil => exact Runs.loop_false rfl
 | cons r rs ih =>
   by_cases hr : r.head = 0
   · have hb := scanBody_skip (ctrl 0 a) (payload (r::rs)).head? {d with pivBack := []} r rs (Or.inr hr)
     have h := Runs.loop_true (f := fun c : Option Letter × Local => c.1.isSome)
       (by simp [st,state,payload_head]) hb ih
     simpa [scanLoop,pivot,List.find?_cons,hr,← Row.head_decode,List.length_cons,Nat.mul_add,
       Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
       h.mono (show 1+(2*(n+1)+10+((2*(n+1)+13)*rs.length+1)) ≤
         (2*(n+1)+13)*(rs.length+1)+1 by simp only [Nat.mul_add,Nat.mul_one]; omega)
   · have hb := scanBody_pick a (payload (r::rs)).head? d r rs hr
     have ht := scanLoop_nonzero r.head hr a
       {d with pivBack := (r.tail.entries.map some).reverse} rs
     have h := Runs.loop_true (f := fun c : Option Letter × Local => c.1.isSome)
       (by simp [st,state,payload_head]) hb ht
     convert h using 1 <;>
       simp [scanLoop,pivot,hr,-Row.head_decode,pivotHead,pivotTail,List.length_cons]; ring

def findPivot : Prog :=
 .seq (.atom (.load (fun c => (c.1,(none,ctrl 0 c.2.2.answer))) .done))
 (.seq (copy .mat .scan .back)
  (.seq scanMatrix (moveRev .pivBack .piv (fun _ a => a))))

lemma pivotTail_length {n} (p : Option (SerialGaussian.Row (n+1))) :
 (pivotTail p).length ≤ n+1 := by
 cases p <;> simp [pivotTail]

lemma findPivot_runs {n} (c : Control) (buf : Option Letter) (d : Data)
    (rs : List (SerialGaussian.Row (n+1))) :
 Runs findPivot
   (st c buf {d with mat := payload rs,back := [],scan := [],piv := [],pivBack := []})
   (st (ctrl (pivotHead (pivot rs)) c.answer) none
     {d with mat := payload rs,back := [],scan := [],piv := pivotTail (pivot rs),pivBack := []})
   (30*(rs.length+1)*(n+3)) := by
 let d' : Data := {d with mat := payload rs,back := [],scan := [],piv := [],pivBack := []}
 have hl : Runs (.atom (.load (fun c : Option Letter × Local =>
       (c.1,(none,ctrl 0 c.2.2.answer))) .done))
     (st c buf d') (st (ctrl 0 c.answer) buf d') 1 := Runs.atom_of _ _ _ rfl
 have hc := copy_runs (σ := Local) Reg.mat Reg.scan Reg.back (by decide) (by decide) (by decide)
   (none,ctrl 0 c.answer) buf d'.tapes (payload rs) []
 have hc' : Runs (copy Reg.mat Reg.scan Reg.back) (st (ctrl 0 c.answer) buf d')
   (st (ctrl 0 c.answer) none {d' with scan := payload rs}) (4*(payload rs).length+7) := by
   simpa [st,d'] using hc
 have hp : Runs (peek Reg.scan) (st (ctrl 0 c.answer) none {d' with scan := payload rs})
   (st (ctrl 0 c.answer) (payload rs).head? {d' with scan := payload rs}) 1 := by
   apply Runs.atom_of
   simp [Action.run,st,state,Data.tapes]
 have hs := scanLoop_initial c.answer d' rs
 have hs' : Runs scanMatrix (st (ctrl 0 c.answer) none {d' with scan := payload rs})
   (st (ctrl (pivotHead (pivot rs)) c.answer) none
     {d' with scan := [],pivBack := (pivotTail (pivot rs)).reverse})
   ((2*(n+1)+13)*rs.length+3) := by
   convert hp.seq hs using 1 <;> first | rfl | omega
 have hm := moveRev_runs Reg.pivBack Reg.piv (by decide) (fun (_ : Local) a => a)
   (none,ctrl (pivotHead (pivot rs)) c.answer) none d'.tapes (pivotTail (pivot rs)).reverse []
 have hm' : Runs (moveRev Reg.pivBack Reg.piv (fun (_ : Local) a => a))
    (st (ctrl (pivotHead (pivot rs)) c.answer) none
      {d' with scan := [],pivBack := (pivotTail (pivot rs)).reverse})
    (st (ctrl (pivotHead (pivot rs)) c.answer) none {d' with piv := pivotTail (pivot rs)})
    (2*(pivotTail (pivot rs)).length+3) := by simpa [st,d'] using hm
 have h := hl.seq (hc'.seq (hs'.seq hm'))
 apply h.mono
 rw [payload_length]
 have ht := pivotTail_length (pivot rs)
 nlinarith

lemma entries_reduce {n} (p r : SerialGaussian.Row (n+1)) :
 (p.reduce r).entries = List.zipWith (fun x y => x-(r.head/p.head)*y) r.tail.entries p.tail.entries := by
 simp only [SerialGaussian.Row.entries,Row.tail,Row.reduce]
 rw [List.zipWith_append (by simp [r.length_eq,p.length_eq])]
 rfl

def reduceInner : Prog :=
 .seq (.cond (fun c => c.2.2.pivot == 0)
    (moveRow .mat .back (fun _ a => a))
    (zipRow .mat .back .piv .pivBack (fun c x y => x-c.factor*y)))
   (moveRev .pivBack .piv (fun _ a => a))

def reduceBody : Prog :=
 .seq (.atom (.pop .mat (fun c a =>
   (none,(none,{c.2.2 with factor := (a.bind id).getD 0 / c.2.2.pivot}))) .done))
 (.seq reduceInner
   (.atom (.push .back (fun _ => none)
      (.peek .mat (fun c a => (a,(none,{c.2.2 with factor := 0}))) .done))))

def reduceLoop : Prog := .loop (fun c => c.1.isSome) reduceBody

def reduceMatrix : Prog := .seq (peek .mat) reduceLoop

def reducedRow {n} (p : Option (SerialGaussian.Row (n+1))) (r : SerialGaussian.Row (n+1)) : SerialGaussian.Row n :=
 p.elim r.tail (fun p => p.reduce r)

def reduceControl {n} (p : Option (SerialGaussian.Row (n+1))) (r : SerialGaussian.Row (n+1)) (a : Bool) : Control :=
 ⟨pivotHead p,r.head/pivotHead p,a⟩

lemma reduceInner_runs {n} (p : Option (SerialGaussian.Row (n+1)))
    (hp : ∀ q ∈ p, q.head ≠ 0) (r : SerialGaussian.Row (n+1)) (a : Bool)
    (d : Data) (xs bs : List Letter) :
 Runs reduceInner
   (st (reduceControl p r a) none
     {d with mat := r.tail.entries.map some ++ none::xs,back := bs,piv := pivotTail p,pivBack := []})
   (st (reduceControl p r a) none
     {d with mat := xs,back := ((reducedRow p r).entries.map some).reverse ++ bs,piv := pivotTail p,pivBack := []})
   (4*(n+1)+10) := by
 cases p with
 | none =>
   let c := reduceControl none r a
   have hm := moveRow_runs Reg.mat Reg.back (by decide) (fun (_ : Local) a => a)
     (none,c) none ({d with piv := [],pivBack := []}).tapes r.tail.entries xs bs
   have hm' : Runs (moveRow Reg.mat Reg.back (fun (_ : Local) a => a))
     (st c none {d with mat := r.tail.entries.map some ++ none::xs,back := bs,piv := [],pivBack := []})
     (st c none {d with mat := xs,back := (r.tail.entries.map some).reverse ++ bs,piv := [],pivBack := []})
     (2*(n+1)+5) := by simpa [st] using hm
   have hc := Runs.cond_true (f := fun c : Option Letter × Local => c.2.2.pivot == 0)
     (b := zipRow Reg.mat Reg.back Reg.piv Reg.pivBack (fun (c : Control) x y => x-c.factor*y))
     (by simp [st,state,c,reduceControl,pivotHead]) hm'
   have hr := moveRev_runs Reg.pivBack Reg.piv (by decide) (fun (_ : Local) a => a)
     (none,c) none ({d with mat := xs,back := (r.tail.entries.map some).reverse ++ bs}).tapes [] []
   have hr' : Runs (moveRev Reg.pivBack Reg.piv (fun (_ : Local) a => a))
     (st c none {d with mat := xs,back := (r.tail.entries.map some).reverse ++ bs,piv := [],pivBack := []})
     (st c none {d with mat := xs,back := (r.tail.entries.map some).reverse ++ bs,piv := [],pivBack := []}) 3 := by
     simpa [st,Function.comp_def] using hr
   exact (hc.seq hr').mono (by omega)
 | some p =>
   let c := reduceControl (some p) r a
   have hm := zipRow_runs Reg.mat Reg.back Reg.piv Reg.pivBack
     (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
     (fun (c : Control) x y => x-c.factor*y) c none d.tapes r.tail.entries p.tail.entries
     (by simp) xs bs []
   have hm' : Runs (zipRow Reg.mat Reg.back Reg.piv Reg.pivBack (fun (c : Control) x y => x-c.factor*y))
     (st c none {d with mat := r.tail.entries.map some ++ none::xs,back := bs,piv := p.tail.entries.map some,pivBack := []})
     (st c none {d with mat := xs,back := ((p.reduce r).entries.map some).reverse ++ bs,piv := [],pivBack := (p.tail.entries.map some).reverse}) (2*(n+1)+5) := by
     simpa [st,c,reduceControl,pivotHead,entries_reduce] using hm
   have hc := Runs.cond_false (f := fun c : Option Letter × Local => c.2.2.pivot == 0)
     (a := moveRow Reg.mat Reg.back (fun (_ : Local) a => a))
     (by simpa [st,state,c,reduceControl,pivotHead] using hp p (by simp)) hm'
   have hr := moveRev_runs Reg.pivBack Reg.piv (by decide) (fun (_ : Local) a => a)
     (none,c) none ({d with mat := xs,back := ((p.reduce r).entries.map some).reverse ++ bs}).tapes
     (p.tail.entries.map some).reverse []
   have hr' : Runs (moveRev Reg.pivBack Reg.piv (fun (_ : Local) a => a))
     (st c none {d with mat := xs,back := ((p.reduce r).entries.map some).reverse ++ bs,piv := [],pivBack := (p.tail.entries.map some).reverse})
     (st c none {d with mat := xs,back := ((p.reduce r).entries.map some).reverse ++ bs,piv := p.tail.entries.map some,pivBack := []}) (2*(n+1)+3) := by
     simpa [st,Function.comp_def] using hr
   convert hc.seq hr' using 1 <;> first | rfl | omega

lemma reduceBody_runs {n} (p : Option (SerialGaussian.Row (n+1)))
    (hp : ∀ q ∈ p, q.head ≠ 0) (r : SerialGaussian.Row (n+1)) (rs) (a : Bool)
    (buf : Option Letter) (d : Data) (bs : List Letter) :
 Runs reduceBody
   (st (ctrl (pivotHead p) a) buf
     {d with mat := payload (r::rs),back := bs,piv := pivotTail p,pivBack := []})
   (st (ctrl (pivotHead p) a) (payload rs).head?
     {d with mat := payload rs,back := (payload [reducedRow p r]).reverse ++ bs,piv := pivotTail p,pivBack := []})
   (4*(n+1)+14) := by
 have ho : Runs (.atom (.pop .mat (fun (c : Option Letter × Local) a =>
       (none,(none,{c.2.2 with factor := (a.bind id).getD 0/c.2.2.pivot}))) .done))
     (st (ctrl (pivotHead p) a) buf
       {d with mat := payload (r::rs),back := bs,piv := pivotTail p,pivBack := []})
     (st (reduceControl p r a) none
       {d with mat := r.tail.entries.map some ++ none::payload rs,back := bs,piv := pivotTail p,pivBack := []}) 1 := by
   apply Runs.atom_of
   simp [Action.run,st,state,Data.tapes,payload_cons,entries_head_tail,ctrl,reduceControl]
 have hi := reduceInner_runs p hp r a d (payload rs) bs
 have hf : Runs (.atom (.push .back (fun _ : Option Letter × Local => none)
       (.peek .mat (fun (c : Option Letter × Local) a => (a,(none,{c.2.2 with factor := 0}))) .done)))
     (st (reduceControl p r a) none
       {d with mat := payload rs,back := ((reducedRow p r).entries.map some).reverse ++ bs,piv := pivotTail p,pivBack := []})
     (st (ctrl (pivotHead p) a) (payload rs).head?
       {d with mat := payload rs,back := (payload [reducedRow p r]).reverse ++ bs,piv := pivotTail p,pivBack := []}) 1 := by
   apply Runs.atom_of
   simp [Action.run,st,state,Data.tapes,payload,SerialGaussian.Row.entries,ctrl,reduceControl,List.reverse_append]
 convert ho.seq (hi.seq hf) using 1 <;> first | rfl | omega

lemma payload_append {n} (xs ys : List (SerialGaussian.Row n)) :
 payload (xs++ys) = payload xs ++ payload ys := by simp [payload]

lemma reduceLoop_runs {n} (p : Option (SerialGaussian.Row (n+1)))
    (hp : ∀ q ∈ p, q.head ≠ 0) (a : Bool) (d : Data)
    (rs : List (SerialGaussian.Row (n+1))) (bs : List Letter) :
 Runs reduceLoop
   (st (ctrl (pivotHead p) a) (payload rs).head?
     {d with mat := payload rs,back := bs,piv := pivotTail p,pivBack := []})
   (st (ctrl (pivotHead p) a) none
     {d with mat := [],back := (payload (rs.map (reducedRow p))).reverse ++ bs,piv := pivotTail p,pivBack := []})
   ((4*(n+1)+15)*rs.length+1) := by
 induction rs generalizing bs with
 | nil => simpa [payload,reduceLoop] using
     (Runs.loop_false (b := reduceBody) (f := fun c : Option Letter × Local => c.1.isSome)
       (s := st (ctrl (pivotHead p) a) none {d with mat := [],back := bs,piv := pivotTail p,pivBack := []}) rfl)
 | cons r rs ih =>
   have hb := reduceBody_runs p hp r rs a (payload (r::rs)).head? d bs
   have ht := ih ((payload [reducedRow p r]).reverse ++ bs)
   have h := Runs.loop_true (f := fun c : Option Letter × Local => c.1.isSome)
     (by simp [st,state,payload_head]) hb ht
   convert h using 1 <;>
     simp [reduceLoop,payload,List.map_cons,List.reverse_append,List.append_assoc] ; ring

lemma reduceMatrix_runs {n} (p : Option (SerialGaussian.Row (n+1)))
    (hp : ∀ q ∈ p, q.head ≠ 0) (a : Bool) (buf : Option Letter) (d : Data)
    (rs : List (SerialGaussian.Row (n+1))) :
 Runs reduceMatrix
   (st (ctrl (pivotHead p) a) buf
     {d with mat := payload rs,back := [],piv := pivotTail p,pivBack := []})
   (st (ctrl (pivotHead p) a) none
     {d with mat := [],back := (payload (rs.map (reducedRow p))).reverse,piv := pivotTail p,pivBack := []})
   ((4*(n+1)+15)*rs.length+3) := by
 have hpeek : Runs (peek Reg.mat)
     (st (ctrl (pivotHead p) a) buf {d with mat := payload rs,back := [],piv := pivotTail p,pivBack := []})
     (st (ctrl (pivotHead p) a) (payload rs).head? {d with mat := payload rs,back := [],piv := pivotTail p,pivBack := []}) 1 := by
   apply Runs.atom_of
   simp [Action.run,st,state,Data.tapes]
 have h := hpeek.seq (reduceLoop_runs p hp a d rs [])
 have h' := h.mono (show 1+(1+((4*(n+1)+15)*rs.length+1)) ≤ (4*(n+1)+15)*rs.length+3 by omega)
 simpa only [List.append_nil,reduceMatrix] using h'

def eliminate : Prog :=
 .seq findPivot (.seq reduceMatrix
   (.seq (moveRev .back .mat (fun _ a => a))
      (.seq (clear .piv) (.atom (.load (fun c => (none,(none,ctrl 0 c.2.2.answer))) .done)))))

def nextRows {n} (rs : List (SerialGaussian.Row (n+1))) : List (SerialGaussian.Row n) :=
 rs.map (reducedRow (pivot rs))

@[simp] lemma nextRows_length {n} (rs : List (SerialGaussian.Row (n+1))) :
 (nextRows rs).length = rs.length := by simp [nextRows]

lemma pivot_nonzero {n} (rs : List (SerialGaussian.Row (n+1))) :
 ∀ q ∈ pivot rs, q.head ≠ 0 := by
 intro q hq
 have h := List.find?_some hq
 simpa [pivot,← Row.head_decode] using h

lemma solve_next {n} (rs : List (SerialGaussian.Row (n+1))) :
 solve rs = solve (nextRows rs) := by
 cases hp : pivot rs <;> simp only [solve,nextRows,hp] <;> rfl

lemma eliminate_runs {n} (c : Control) (buf : Option Letter) (d : Data)
    (rs : List (SerialGaussian.Row (n+1))) :
 Runs eliminate
   (st c buf {d with mat := payload rs,back := [],scan := [],piv := [],pivBack := []})
   (st (ctrl 0 c.answer) none
     {d with mat := payload (nextRows rs),back := [],scan := [],piv := [],pivBack := []})
   (100*(rs.length+1)*(n+3)) := by
 let d' : Data := {d with mat := payload rs,back := [],scan := [],piv := [],pivBack := []}
 let p := pivot rs
 have hf := findPivot_runs c buf d rs
 have hr := reduceMatrix_runs p (pivot_nonzero rs) c.answer none d' rs
 have hm := moveRev_runs Reg.back Reg.mat (by decide) (fun (_ : Local) a => a)
   (none,ctrl (pivotHead p) c.answer) none ({d' with piv := pivotTail p}).tapes
   (payload (nextRows rs)).reverse []
 have hm' : Runs (moveRev Reg.back Reg.mat (fun (_ : Local) a => a))
     (st (ctrl (pivotHead p) c.answer) none {d' with mat := [],back := (payload (nextRows rs)).reverse,piv := pivotTail p})
     (st (ctrl (pivotHead p) c.answer) none {d' with mat := payload (nextRows rs),piv := pivotTail p})
     (2*(payload (nextRows rs)).length+3) := by simpa [st,d',Function.comp_def] using hm
 have hc := clear_runs (σ := Local) Reg.piv (none,ctrl (pivotHead p) c.answer) none
   ({d' with mat := payload (nextRows rs)}).tapes (pivotTail p)
 have hc' : Runs (clear Reg.piv)
     (st (ctrl (pivotHead p) c.answer) none {d' with mat := payload (nextRows rs),piv := pivotTail p})
     (st (ctrl (pivotHead p) c.answer) none {d' with mat := payload (nextRows rs)})
     (2*(pivotTail p).length+3) := by simpa [st,d'] using hc
 have hl : Runs (.atom (.load (fun c : Option Letter × Local =>
       (none,(none,ctrl 0 c.2.2.answer))) .done))
     (st (ctrl (pivotHead p) c.answer) none {d' with mat := payload (nextRows rs)})
     (st (ctrl 0 c.answer) none {d' with mat := payload (nextRows rs)}) 1 := Runs.atom_of _ _ _ rfl
 have h := hf.seq (hr.seq (hm'.seq (hc'.seq hl)))
 apply h.mono
 rw [payload_length,nextRows_length]
 have ht := pivotTail_length p
 nlinarith

def normal : {n : ℕ} → List (SerialGaussian.Row n) → List (SerialGaussian.Row 0)
 | 0,rs => rs
 | _+1,rs => normal (nextRows rs)

@[simp] lemma normal_length {n} (rs : List (SerialGaussian.Row n)) :
 (normal rs).length = rs.length := by
 induction n with
 | zero => rfl
 | succ n ih => simpa [normal] using ih (nextRows rs)

lemma solve_normal {n} (rs : List (SerialGaussian.Row n)) : solve (normal rs) = solve rs := by
 induction n with
 | zero => rfl
 | succ n ih => rw [normal,ih,← solve_next]

def eliminationBody : Prog := .seq eliminate
 (.atom (.pop .width (fun c _ => c) (.peek .width (fun c a => (a,c.2)) .done)))

def eliminationLoop : Prog := .loop (fun c => c.1.isSome) eliminationBody

lemma eliminationBody_runs {n} (a : Bool) (buf : Option Letter) (d : Data)
    (rs : List (SerialGaussian.Row (n+1))) (ws : List Letter) :
 Runs eliminationBody
   (st (ctrl 0 a) buf {d with mat := payload rs,back := [],scan := [],piv := [],pivBack := [],width := none::ws})
   (st (ctrl 0 a) ws.head?
     {d with mat := payload (nextRows rs),back := [],scan := [],piv := [],pivBack := [],width := ws})
   (100*(rs.length+1)*(n+3)+2) := by
 have he := eliminate_runs (ctrl 0 a) buf {d with width := none::ws} rs
 have hp : Runs (.atom (.pop .width (fun c : Option Letter × Local => fun _ => c)
       (.peek .width (fun (c : Option Letter × Local) a => (a,c.2)) .done)))
     (st (ctrl 0 a) none {d with mat := payload (nextRows rs),back := [],scan := [],piv := [],pivBack := [],width := none::ws})
     (st (ctrl 0 a) ws.head? {d with mat := payload (nextRows rs),back := [],scan := [],piv := [],pivBack := [],width := ws}) 1 := by
   apply Runs.atom_of
   simp [Action.run,st,state,Data.tapes]
 convert he.seq hp using 1 <;> first | rfl | omega

lemma eliminationLoop_runs {n} (a : Bool) (d : Data) (rs : List (SerialGaussian.Row n)) :
 Runs eliminationLoop
   (st (ctrl 0 a) (List.replicate n (none : Letter)).head?
     {d with mat := payload rs,back := [],scan := [],piv := [],pivBack := [],width := List.replicate n none})
   (st (ctrl 0 a) none
     {d with mat := payload (normal rs),back := [],scan := [],piv := [],pivBack := [],width := []})
   (200*(rs.length+1)*(n+3)^2) := by
 induction n with
 | zero =>
   apply (Runs.loop_false rfl).mono
   norm_num
   omega
 | succ n ih =>
   have hb := eliminationBody_runs a (List.replicate (n+1) (none : Letter)).head? d rs
     (List.replicate n none)
   have ht := ih (nextRows rs)
   have h := Runs.loop_true (f := fun c : Option Letter × Local => c.1.isSome)
     (by simp [st,state,List.replicate_succ]) hb ht
   have h' : Runs eliminationLoop
       (st (ctrl 0 a) (List.replicate (n+1) (none : Letter)).head?
         {d with mat := payload rs,back := [],scan := [],piv := [],pivBack := [],width := List.replicate (n+1) none})
       (st (ctrl 0 a) none
         {d with mat := payload (normal rs),back := [],scan := [],piv := [],pivBack := [],width := []})
       (1+(100*(rs.length+1)*(n+3)+2+200*(rs.length+1)*(n+3)^2)) := by
     simpa only [eliminationLoop,List.replicate_succ,normal,nextRows_length] using h
   exact h'.mono (by nlinarith)

def zeroBody : Prog := .atom
 (.pop .mat (fun c a => (none,(none,{c.2.2 with answer := c.2.2.answer && ((a.bind id).getD 0 == 0)})))
  (.pop .mat (fun c _ => c) (.peek .mat (fun c a => (a,c.2)) .done)))

def zeroLoop : Prog := .loop (fun c => c.1.isSome) zeroBody

def checkZero : Prog :=
 .seq (.atom (.load (fun _ => (none,(none,ctrl 0 true)))
   (.peek .mat (fun c a => (a,c.2)) .done)))
 (.seq zeroLoop (.atom (.push .output (fun c => some (if c.2.2.answer then 1 else 0)) .done)))

lemma payload_zero_cons (r : SerialGaussian.Row 0) (rs) :
 payload (r::rs) = some r.rhs :: none :: payload rs := by
 have hc : r.coeff = [] := List.eq_nil_of_length_eq_zero r.length_eq
 simp [payload, hc]

lemma zeroLoop_runs (a : Bool) (d : Data) (rs : List (SerialGaussian.Row 0)) :
 Runs zeroLoop (st (ctrl 0 a) (payload rs).head? {d with mat := payload rs})
   (st (ctrl 0 (a && solve rs)) none {d with mat := []}) (2*rs.length+1) := by
 induction rs generalizing a with
 | nil => simpa [zeroLoop,solve,payload,ctrl] using
     (Runs.loop_false (b := zeroBody) (f := fun c : Option Letter × Local => c.1.isSome)
       (s := st (ctrl 0 a) none {d with mat := []}) rfl)
 | cons r rs ih =>
   have hb : Runs zeroBody (st (ctrl 0 a) (payload (r::rs)).head? {d with mat := payload (r::rs)})
       (st (ctrl 0 (a && (r.rhs == 0))) (payload rs).head? {d with mat := payload rs}) 1 := by
     apply Runs.atom_of
     simp [Action.run,st,state,ctrl,Data.tapes,payload_zero_cons]
   have h := Runs.loop_true (f := fun c : Option Letter × Local => c.1.isSome)
     (by simp [st,state,payload_zero_cons]) hb (ih (a && (r.rhs == 0)))
   convert h using 1 <;> simp [zeroLoop,solve,Bool.and_assoc] ; omega

lemma checkZero_runs (c : Control) (buf : Option Letter) (d : Data) (rs : List (SerialGaussian.Row 0)) :
 Runs checkZero (st c buf {d with mat := payload rs,output := []})
   (st (ctrl 0 (solve rs)) none {d with mat := [],output := boolCode (solve rs)}) (2*rs.length+5) := by
 have hi : Runs (.atom (.load (fun _ : Option Letter × Local => (none,(none,ctrl 0 true)))
       (.peek .mat (fun (c : Option Letter × Local) a => (a,c.2)) .done)))
     (st c buf {d with mat := payload rs,output := []})
     (st (ctrl 0 true) (payload rs).head? {d with mat := payload rs,output := []}) 1 := by
   apply Runs.atom_of
   simp [Action.run,st,state,Data.tapes]
 have hz := zeroLoop_runs true {d with output := []} rs
 have ho : Runs (.atom (.push .output (fun c : Option Letter × Local =>
       some (if c.2.2.answer then 1 else 0)) .done))
     (st (ctrl 0 (true && solve rs)) none {d with mat := [],output := []})
     (st (ctrl 0 (solve rs)) none {d with mat := [],output := boolCode (solve rs)}) 1 := by
   apply Runs.atom_of
   simp [Action.run,st,state,Data.tapes,ctrl,boolCode]
 convert hi.seq (hz.seq ho) using 1 <;> first | rfl | omega

def solver : Prog := .seq (peek .width) (.seq eliminationLoop checkZero)

lemma solver_runs {n} (d : Data) (rs : List (SerialGaussian.Row n)) :
 Runs solver
   (st (ctrl 0 true) none {d with mat := payload rs,back := [],scan := [],piv := [],pivBack := [], width := List.replicate n none,output := []})
   (st (ctrl 0 (solve rs)) none {d with mat := [],back := [],scan := [],piv := [],pivBack := [], width := [],output := boolCode (solve rs)})
   (300*(rs.length+1)*(n+3)^2) := by
 have hp : Runs (peek .width)
     (st (ctrl 0 true) none {d with mat := payload rs,back := [],scan := [],piv := [],pivBack := [], width := List.replicate n none,output := []})
     (st (ctrl 0 true) (List.replicate n (none : Letter)).head?
       {d with mat := payload rs,back := [],scan := [],piv := [],pivBack := [], width := List.replicate n none,output := []}) 1 := by
   apply Runs.atom_of
   rfl
 have he := eliminationLoop_runs true {d with output := []} rs
 have hz := checkZero_runs (ctrl 0 true) none
     {d with back := [],scan := [],piv := [],pivBack := [],width := []}
     (normal rs)
 have h := hp.seq (he.seq hz)
 have h' : Runs solver
   (st (ctrl 0 true) none {d with mat := payload rs,back := [],scan := [],piv := [],pivBack := [], width := List.replicate n none,output := []})
   (st (ctrl 0 (solve rs)) none {d with mat := [],back := [],scan := [],piv := [],pivBack := [], width := [],output := boolCode (solve rs)})
   (1+(1+(1+(200*(rs.length+1)*(n+3)^2+(2*rs.length+5))))) := by
   simpa only [solver,solve_normal,normal_length] using h
 exact h'.mono (by
   have hs : 1 ≤ (n+3)^2 := Nat.succ_le_iff.mpr (pow_pos (by omega) 2)
   have hm := Nat.mul_le_mul_left (rs.length+1) hs
   nlinarith)

end CPTSeparation.GaussMachine

end OAI
