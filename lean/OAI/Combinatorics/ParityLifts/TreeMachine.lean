import OAI.Combinatorics.ParityLifts.TreeRoutines

namespace OAI

namespace ParityWL.Complexity

structure FinStack (t a : ℕ) where
  State : Type
  finite : Fintype State
  program : StackMachine State t a

attribute [instance] FinStack.finite

def FinStack.of {Q : Type} [Fintype Q] {t a : ℕ} (P : StackMachine Q t a) : FinStack t a :=
  ⟨Q, inferInstance, P⟩

def dataReg {r : ℕ} (i : Fin r) : Fin (r + 3 + 1) := Fin.castAdd 4 i

def workReg (r : ℕ) (i : Fin 4) : Fin (r + 3 + 1) := Fin.natAdd r i

lemma dataReg_ne_workReg {r : ℕ} (i : Fin r) (j : Fin 4) : dataReg i ≠ workReg r j := by
  intro h
  have := congrArg Fin.val h
  dsimp [dataReg, workReg] at this
  omega

lemma workReg_injective (r : ℕ) : Function.Injective (workReg r) := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  dsimp [workReg] at this
  omega

def dataWords {r : ℕ} (d : Fin r → DataTree) : Words (r + 3) 0 :=
  Fin.append (m := r) (n := 4) (fun i => (d i).code) (fun _ : Fin 4 => [])

@[simp] lemma dataWords_data {r : ℕ} (d : Fin r → DataTree) (i : Fin r) :
    dataWords d (dataReg i) = (d i).code := by simp [dataWords, dataReg]

@[simp] lemma dataWords_work {r : ℕ} (d : Fin r → DataTree) (j : Fin 4) :
    dataWords d (workReg r j) = [] := by simp [dataWords, workReg]

lemma dataWords_update {r : ℕ} (d : Fin r → DataTree) (i : Fin r) (x : DataTree) :
    dataWords (Function.update d i x) = Function.update (dataWords d) (dataReg i) x.code := by
  funext j
  refine Fin.addCases (m := r) (n := 4) (fun j => ?_) (fun j => ?_) j
  · change dataWords (Function.update d i x) (dataReg j) = _
    change dataWords (Function.update d i x) (dataReg j) =
      Function.update (dataWords d) (dataReg i) x.code (dataReg j)
    by_cases he : j = i
    · subst j; simp
    · have hn : dataReg j ≠ dataReg i := by
        intro h
        apply he
        have hv := congrArg (fun x : Fin (r + 3 + 1) => x.val) h
        exact Fin.ext hv
      simp [he, hn]
  · change dataWords (Function.update d i x) (workReg r j) =
      Function.update (dataWords d) (dataReg i) x.code (workReg r j)
    simp [Ne.symm (dataReg_ne_workReg i j)]

def dataMass {r : ℕ} (d : Fin r → DataTree) : ℕ := ∑ i, (d i).size

lemma dataSize_le_mass {r : ℕ} (d : Fin r → DataTree) (i : Fin r) :
    (d i).size ≤ dataMass d := by
  exact Finset.single_le_sum (f := fun i => (d i).size) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

inductive TreeOp (r : ℕ) where
  | skip
  | nil (dst : Fin r)
  | node (dst left right : Fin r)
  | project (dst src : Fin r) (right : Bool)
  | test (src : Fin r)

def TreeOp.eval {r : ℕ} (op : TreeOp r) (d : Fin r → DataTree) : (Fin r → DataTree) × Bool :=
  match op with
  | .skip => (d, true)
  | .nil i => (Function.update d i .nil, true)
  | .node i j k => (Function.update d i (.node (d j) (d k)), true)
  | .project i j b => (Function.update d i ((d j).child b), true)
  | .test i => (d, decide (d i = .nil))

def testNil {t : ℕ} (src : Fin (t + 1)) :=
  primitive (a := 0) (fun _ _ => .keep) (fun x => decide (x src = some 0))

lemma testNil_run {r : ℕ} (i : Fin r) (d : Fin r → DataTree) :
    Runs (testNil (dataReg i)) (dataWords d) 1 (dataWords d) (decide (d i = .nil)) := by
  have he : (dataWords d (dataReg i)).head? = some 0 ↔ d i = .nil := by
    rw [dataWords_data]
    cases d i <;> simp [DataTree.code]
  have h := primitive_exec (fun (_ : Fin (r + 3 + 1) → Option (StackSymbol 0)) _ =>
    StackOp.keep) (fun x => decide (x (dataReg i) = some 0)) (dataWords d)
  have hh : (fun i => (dataWords d i).head?) (dataReg i) = some 0 ↔ d i = .nil := he
  simp only [hh] at h
  exact ⟨some (decide (d i = .nil)), h⟩

def TreeOp.routine {r : ℕ} : TreeOp r → FinStack (r + 3) 0
  | .skip => .of (.halt true)
  | .nil i => .of (nilWord (dataReg i))
  | .node i j k => .of (nodeWord (dataReg i) (dataReg j) (dataReg k)
      (workReg r 0) (workReg r 1))
  | .project i j b => .of (projectWord (dataReg i) (dataReg j)
      (workReg r 0) (workReg r 1) (workReg r 2) (workReg r 3) b)
  | .test i => .of (testNil (dataReg i))

lemma TreeOp.routine_run {r : ℕ} (op : TreeOp r) (d : Fin r → DataTree) :
    ∃ n, n ≤ 50 * (dataMass d + 1) ∧
      Runs op.routine.program (dataWords d) n (dataWords (op.eval d).1) (op.eval d).2 := by
  have hw (i j : Fin 4) (h : i ≠ j) : workReg r i ≠ workReg r j := fun he => h (workReg_injective r he)
  cases op with
  | skip => exact ⟨0, by omega, halt_run true (dataWords d)⟩
  | nil i =>
    have h := nilWord_run (dataReg i) (dataWords d)
    rw [dataWords_data, DataTree.length_code] at h
    refine ⟨2 * (d i).size + 3, ?_, ?_⟩
    · have hi := dataSize_le_mass d i; omega
    · simpa only [TreeOp.routine, FinStack.of, TreeOp.eval, dataWords_update, DataTree.code] using h
  | node i j k =>
    have h := nodeWord_run (dataReg i) (dataReg j) (dataReg k) (workReg r 0) (workReg r 1)
      (dataReg_ne_workReg i 0) (dataReg_ne_workReg i 1)
      (dataReg_ne_workReg j 0) (dataReg_ne_workReg j 1)
      (dataReg_ne_workReg k 0) (dataReg_ne_workReg k 1) (hw 0 1 (by decide))
      (dataWords d) (by simp) (by simp)
    simp only [dataWords_data, DataTree.length_code] at h
    refine ⟨10 * ((d j).size + (d k).size) + 2 * (d i).size + 23, ?_, ?_⟩
    · have hi := dataSize_le_mass d i
      have hj := dataSize_le_mass d j
      have hk := dataSize_le_mass d k
      omega
    · simpa only [TreeOp.routine, FinStack.of, TreeOp.eval, dataWords_update, DataTree.code] using h
  | project i j b =>
    obtain ⟨n, hn, h⟩ := projectWord_run (dataReg i) (dataReg j)
      (workReg r 0) (workReg r 1) (workReg r 2) (workReg r 3)
      (dataReg_ne_workReg i 0) (dataReg_ne_workReg i 1)
      (dataReg_ne_workReg j 0) (dataReg_ne_workReg j 1)
      (hw 0 1 (by decide)) (hw 0 2 (by decide)) (hw 0 3 (by decide)) (hw 2 3 (by decide))
      b (d j) (dataWords d) (by simp) (by simp) (by simp) (by simp) (by simp)
    simp only [dataWords_data, DataTree.length_code] at hn
    refine ⟨n, ?_, ?_⟩
    · have hi := dataSize_le_mass d i
      have hj := dataSize_le_mass d j
      omega
    · simpa only [TreeOp.routine, FinStack.of, TreeOp.eval, dataWords_update] using h
  | test i =>
    exact ⟨1, by omega, testNil_run i d⟩

/-- Finite code over unbounded but explicitly serialized binary trees. -/
structure TreeMachine (Q : Type) (r : ℕ) where
  initial : Q
  output : Q → Option Bool
  instruction : Q → TreeOp r
  next : Q → Bool → Q

def TreeMachine.lower {Q : Type} {r : ℕ} (P : TreeMachine Q r) : MacroMachine Q (r + 3) 0 where
  Control := fun q => (P.instruction q).routine.State
  initial := P.initial
  output := P.output
  routine := fun q => (P.instruction q).routine.program
  next := P.next

instance {Q : Type} {r : ℕ} (P : TreeMachine Q r) (q : Q) :
    Fintype (P.lower.Control q) := (P.instruction q).routine.finite

/-- Work is the sum of one plus the size of all live data before each step.
The compiler bound below is linear in this actual execution measure. -/
inductive TreeExec {Q : Type} {r : ℕ} (P : TreeMachine Q r) :
    Q → (Fin r → DataTree) → ℕ → (Fin r → DataTree) → Bool → Prop
  | halt (q d b) (h : P.output q = some b) : TreeExec P q d 0 d b
  | next (q d) {m z c} (h : P.output q = none)
      (tail : TreeExec P (P.next q ((P.instruction q).eval d).2)
        ((P.instruction q).eval d).1 m z c) :
      TreeExec P q d (dataMass d + 1 + m) z c

lemma TreeExec.lower {Q : Type} {r : ℕ} {P : TreeMachine Q r}
    {q : Q} {d e : Fin r → DataTree} {w : ℕ} {b : Bool} (h : TreeExec P q d w e b) :
    ∃ n, n ≤ 51 * w ∧ MacroExec P.lower q (dataWords d) n (dataWords e) b := by
  induction h with
  | halt q d b h => exact ⟨0, by omega, .halt q _ b h⟩
  | next q d ho _ ih =>
    obtain ⟨m, hm, ht⟩ := ih
    obtain ⟨n, hn, hr⟩ := (P.instruction q).routine_run d
    exact ⟨n + 1 + m, by omega, MacroExec.next q _ ho hr ht⟩

end ParityWL.Complexity

namespace ParityWL.Complexity

structure FinTree (r : ℕ) where
  State : Type
  finite : Fintype State
  program : TreeMachine State r

attribute [instance] FinTree.finite

def FinTree.of {Q : Type} [Fintype Q] {r : ℕ} (P : TreeMachine Q r) : FinTree r :=
  ⟨Q, inferInstance, P⟩

def TreeRuns {Q : Type} {r : ℕ} (P : TreeMachine Q r) (d : Fin r → DataTree)
    (w : ℕ) (e : Fin r → DataTree) (b : Bool) : Prop := TreeExec P P.initial d w e b

def TreeMachine.halt {r : ℕ} (b : Bool) : TreeMachine Unit r where
  initial := ()
  output := fun _ => some b
  instruction := fun _ => .skip
  next := fun _ _ => ()

lemma treeHalt_run {r : ℕ} (b : Bool) (d : Fin r → DataTree) :
    TreeRuns (.halt b) d 0 d b := .halt _ _ _ rfl

def TreeMachine.atomic {r : ℕ} (op : TreeOp r) : TreeMachine (Option Bool) r where
  initial := none
  output := id
  instruction := fun _ => op
  next := fun _ b => some b

lemma treeAtomic_run {r : ℕ} (op : TreeOp r) (d : Fin r → DataTree) :
    TreeRuns (.atomic op) d (dataMass d + 1) (op.eval d).1 (op.eval d).2 := by
  have h := TreeExec.next (P := .atomic op) none d (m := 0) rfl
    (.halt _ _ _ rfl)
  simpa [TreeRuns, TreeMachine.atomic] using h

lemma TreeExec.map {Q R : Type} {r : ℕ} {P : TreeMachine Q r} {T : TreeMachine R r}
    (f : Q → R) (ho : ∀ q, T.output (f q) = P.output q)
    (hi : ∀ q, P.output q = none → T.instruction (f q) = P.instruction q)
    (hn : ∀ q b, P.output q = none → T.next (f q) b = f (P.next q b))
    {q : Q} {d e : Fin r → DataTree} {n : ℕ} {b : Bool} (h : TreeExec P q d n e b) :
    TreeExec T (f q) d n e b := by
  induction h with
  | halt q d b h => exact .halt _ _ _ ((ho q).trans h)
  | next q d h _ ih =>
    apply TreeExec.next _ _ ((ho q).trans h)
    simpa only [hi q h, hn q _ h] using ih

def TreeMachine.andThen {Q R : Type} {r : ℕ} (P : TreeMachine Q r) (T : TreeMachine R r) :
    TreeMachine (Q ⊕ R) r where
  initial := .inl P.initial
  output := fun q => match q with | .inl _ => none | .inr q => T.output q
  instruction := fun q => match q with
    | .inl q => if P.output q = none then P.instruction q else .skip
    | .inr q => T.instruction q
  next := fun q b => match q with
    | .inl q => if P.output q = none then .inl (P.next q b) else .inr T.initial
    | .inr q => .inr (T.next q b)

lemma TreeExec.andThen_right {Q R : Type} {r : ℕ}
    (P : TreeMachine Q r) (T : TreeMachine R r)
    {q : R} {d e : Fin r → DataTree} {n : ℕ} {b : Bool} (h : TreeExec T q d n e b) :
    TreeExec (P.andThen T) (.inr q) d n e b := by
  exact h.map (T := P.andThen T) Sum.inr (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl)

lemma TreeExec.andThen {Q R : Type} {r : ℕ}
    {P : TreeMachine Q r} {T : TreeMachine R r}
    {q : Q} {d e z : Fin r → DataTree} {n m : ℕ} {b c : Bool}
    (h : TreeExec P q d n e b) (ht : TreeRuns T e m z c) :
    TreeExec (P.andThen T) (.inl q) d (n + dataMass e + 1 + m) z c := by
  induction h with
  | halt q d b ho =>
    have hh := ht.andThen_right P T
    have hi : (P.andThen T).instruction (.inl q) = .skip := by simp [TreeMachine.andThen, ho]
    have hn : (P.andThen T).next (.inl q) true = .inr T.initial := by simp [TreeMachine.andThen, ho]
    simp only [Nat.zero_add]
    apply TreeExec.next _ _ rfl
    simpa only [hi, TreeOp.eval, hn] using hh
  | next q d ho _ ih =>
    have hi : (P.andThen T).instruction (.inl q) = P.instruction q := by
      simp [TreeMachine.andThen, ho]
    have hn : ∀ b, (P.andThen T).next (.inl q) b = .inl (P.next q b) := by
      intro b; simp [TreeMachine.andThen, ho]
    have hh := TreeExec.next (P := P.andThen T) (.inl q) d rfl
      (by simpa only [hi, hn] using ih ht)
    convert hh using 1
    omega

lemma TreeRuns.andThen {Q R : Type} {r : ℕ}
    {P : TreeMachine Q r} {T : TreeMachine R r}
    {d e z : Fin r → DataTree} {n m : ℕ} {b c : Bool}
    (h : TreeRuns P d n e b) (ht : TreeRuns T e m z c) :
    TreeRuns (P.andThen T) d (n + dataMass e + 1 + m) z c := TreeExec.andThen h ht

def TreeMachine.branch {Q R : Type} {r : ℕ} (src : Fin r)
    (P : TreeMachine Q r) (T : TreeMachine R r) : TreeMachine (Unit ⊕ Q ⊕ R) r where
  initial := .inl ()
  output := fun q => match q with
    | .inl _ => none
    | .inr (.inl q) => P.output q
    | .inr (.inr q) => T.output q
  instruction := fun q => match q with
    | .inl _ => .test src
    | .inr (.inl q) => P.instruction q
    | .inr (.inr q) => T.instruction q
  next := fun q b => match q with
    | .inl _ => if b then .inr (.inl P.initial) else .inr (.inr T.initial)
    | .inr (.inl q) => .inr (.inl (P.next q b))
    | .inr (.inr q) => .inr (.inr (T.next q b))

lemma TreeRuns.branch_true {Q R : Type} {r : ℕ} (src : Fin r)
    (P : TreeMachine Q r) (T : TreeMachine R r)
    {d e : Fin r → DataTree} {n : ℕ} {b : Bool} (h : d src = .nil)
    (hr : TreeRuns P d n e b) :
    TreeRuns (TreeMachine.branch src P T) d (dataMass d + 1 + n) e b := by
  have hm := hr.map (T := TreeMachine.branch src P T) (fun q => .inr (.inl q))
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl)
  apply TreeExec.next _ _ rfl
  simpa [TreeMachine.branch, TreeOp.eval, h] using hm

lemma TreeRuns.branch_false {Q R : Type} {r : ℕ} (src : Fin r)
    (P : TreeMachine Q r) (T : TreeMachine R r)
    {d e : Fin r → DataTree} {n : ℕ} {b : Bool} (h : d src ≠ .nil)
    (hr : TreeRuns T d n e b) :
    TreeRuns (TreeMachine.branch src P T) d (dataMass d + 1 + n) e b := by
  have hm := hr.map (T := TreeMachine.branch src P T) (fun q => .inr (.inr q))
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl)
  apply TreeExec.next _ _ rfl
  simpa [TreeMachine.branch, TreeOp.eval, h] using hm

def TreeMachine.repeat {Q : Type} {r : ℕ} (P : TreeMachine Q r) : TreeMachine Q r where
  initial := P.initial
  output := fun q => if P.output q = some true then some true else none
  instruction := fun q => if P.output q = none then P.instruction q else .skip
  next := fun q b => if P.output q = none then P.next q b else P.initial

lemma TreeExec.repeat_true {Q : Type} {r : ℕ} {P : TreeMachine Q r}
    {q : Q} {d e : Fin r → DataTree} {n : ℕ} (h : TreeExec P q d n e true) :
    TreeExec P.repeat q d n e true := by
  generalize hb : true = b at h
  induction h with
  | halt q d b ho => subst b; exact .halt _ _ _ (by simp [TreeMachine.repeat, ho])
  | next q d ho _ ih =>
    apply TreeExec.next _ _ (by simp [TreeMachine.repeat, ho])
    simpa only [TreeMachine.repeat, ho, ↓reduceIte] using ih hb

lemma TreeExec.repeat_false {Q : Type} {r : ℕ} {P : TreeMachine Q r}
    {q : Q} {d e z : Fin r → DataTree} {n m : ℕ}
    (h : TreeExec P q d n e false) (ht : TreeRuns P.repeat e m z true) :
    TreeExec P.repeat q d (n + dataMass e + 1 + m) z true := by
  generalize hb : false = b at h
  induction h with
  | halt q d b ho =>
    subst b
    simp only [Nat.zero_add]
    apply TreeExec.next _ _ (by simp [TreeMachine.repeat, ho])
    simpa [TreeRuns, TreeMachine.repeat, ho, TreeOp.eval] using ht
  | next q d ho _ ih =>
    have hi : P.repeat.instruction q = P.instruction q := by simp [TreeMachine.repeat, ho]
    have hn : ∀ b, P.repeat.next q b = P.next q b := by intro b; simp [TreeMachine.repeat, ho]
    have hh := TreeExec.next (P := P.repeat) q d (by simp [TreeMachine.repeat, ho])
      (by simpa only [hi, hn] using ih ht hb)
    convert hh using 1
    omega

end ParityWL.Complexity

end OAI
