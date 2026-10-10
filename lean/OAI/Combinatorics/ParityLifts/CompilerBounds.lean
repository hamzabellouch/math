import OAI.Combinatorics.ParityLifts.Compiler

namespace OAI

namespace ParityWL.Complexity

def DataBound {r : ℕ} (d : Fin r → DataTree) (S : ℕ) : Prop := ∀ i, (d i).size ≤ S

lemma DataBound.mass {r S : ℕ} {d : Fin r → DataTree} (h : DataBound d S) :
    dataMass d ≤ r * S := by
  simpa [dataMass] using Finset.sum_le_sum (s := Finset.univ) (fun i _ => h i)

inductive BoundedExec {Q : Type} {r : ℕ} (P : TreeMachine Q r) (S : ℕ) :
    Q → (Fin r → DataTree) → ℕ → (Fin r → DataTree) → Bool → Prop
  | halt (q d b) (ho : P.output q = some b) (hb : DataBound d S) : BoundedExec P S q d 0 d b
  | next (q d) {n e b} (ho : P.output q = none) (hb : DataBound d S)
      (tail : BoundedExec P S (P.next q ((P.instruction q).eval d).2)
        ((P.instruction q).eval d).1 n e b) : BoundedExec P S q d (n + 1) e b

lemma BoundedExec.start_bound {Q : Type} {r S : ℕ} {P : TreeMachine Q r}
    {q d e n b} (h : BoundedExec P S q d n e b) : DataBound d S := by cases h <;> assumption

lemma BoundedExec.end_bound {Q : Type} {r S : ℕ} {P : TreeMachine Q r}
    {q d e n b} (h : BoundedExec P S q d n e b) : DataBound e S := by
  induction h with
  | halt _ _ _ _ h => exact h
  | next _ _ _ _ _ ih => exact ih

lemma BoundedExec.work {Q : Type} {r S : ℕ} {P : TreeMachine Q r}
    {q d e n b} (h : BoundedExec P S q d n e b) :
    ∃ w, w ≤ n * (r * S + 1) ∧ TreeExec P q d w e b := by
  induction h with
  | halt q d b ho hb => exact ⟨0, by simp, .halt q d b ho⟩
  | next q d ho hb _ ih =>
    obtain ⟨w, hw, he⟩ := ih
    refine ⟨dataMass d + 1 + w, ?_, .next q d ho he⟩
    have hm := hb.mass
    nlinarith

abbrev BoundedRuns {Q : Type} {r : ℕ} (P : TreeMachine Q r) (S : ℕ)
    (d : Fin r → DataTree) (n : ℕ) (e : Fin r → DataTree) (b : Bool) : Prop :=
  BoundedExec P S P.initial d n e b

lemma boundedHalt {r S : ℕ} (b : Bool) (d : Fin r → DataTree) (h : DataBound d S) :
    BoundedRuns (.halt b) S d 0 d b := .halt _ _ _ rfl h

lemma boundedAtomic {r S : ℕ} (op : TreeOp r) (d : Fin r → DataTree)
    (h : DataBound d S) (he : DataBound (op.eval d).1 S) :
    BoundedRuns (.atomic op) S d 1 (op.eval d).1 (op.eval d).2 :=
  .next _ _ rfl h (.halt _ _ _ rfl he)

lemma BoundedExec.map {Q R : Type} {r S : ℕ} {P : TreeMachine Q r} {T : TreeMachine R r}
    (f : Q → R) (ho : ∀ q, T.output (f q) = P.output q)
    (hi : ∀ q, P.output q = none → T.instruction (f q) = P.instruction q)
    (hn : ∀ q b, P.output q = none → T.next (f q) b = f (P.next q b))
    {q : Q} {d e : Fin r → DataTree} {n : ℕ} {b : Bool} (h : BoundedExec P S q d n e b) :
    BoundedExec T S (f q) d n e b := by
  induction h with
  | halt q d b h hb => exact .halt _ _ _ ((ho q).trans h) hb
  | next q d h hb _ ih =>
    apply BoundedExec.next _ _ ((ho q).trans h) hb
    simpa only [hi q h, hn q _ h] using ih

lemma BoundedExec.andThen_right {Q R : Type} {r S : ℕ}
    (P : TreeMachine Q r) (T : TreeMachine R r)
    {q : R} {d e : Fin r → DataTree} {n : ℕ} {b : Bool} (h : BoundedExec T S q d n e b) :
    BoundedExec (P.andThen T) S (.inr q) d n e b := by
  exact h.map (T := P.andThen T) Sum.inr (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl)

lemma BoundedExec.andThen {Q R : Type} {r S : ℕ}
    {P : TreeMachine Q r} {T : TreeMachine R r}
    {q : Q} {d e z : Fin r → DataTree} {n m : ℕ} {b c : Bool}
    (h : BoundedExec P S q d n e b) (ht : BoundedRuns T S e m z c) :
    BoundedExec (P.andThen T) S (.inl q) d (n + 1 + m) z c := by
  induction h with
  | halt q d b ho hb =>
    have hh := ht.andThen_right P T
    have hi : (P.andThen T).instruction (.inl q) = .skip := by simp [TreeMachine.andThen, ho]
    have hn : (P.andThen T).next (.inl q) true = .inr T.initial := by simp [TreeMachine.andThen, ho]
    have he := BoundedExec.next (P := P.andThen T) (.inl q) d rfl hb
      (by simpa only [hi, TreeOp.eval, hn] using hh)
    convert he using 1
    omega
  | next q d ho hb _ ih =>
    have hi : (P.andThen T).instruction (.inl q) = P.instruction q := by
      simp [TreeMachine.andThen, ho]
    have hn : ∀ b, (P.andThen T).next (.inl q) b = .inl (P.next q b) := by
      intro b; simp [TreeMachine.andThen, ho]
    have hh := BoundedExec.next (P := P.andThen T) (.inl q) d rfl hb
      (by simpa only [hi, hn] using ih ht)
    convert hh using 1
    omega

lemma BoundedRuns.andThen {Q R : Type} {r S : ℕ}
    {P : TreeMachine Q r} {T : TreeMachine R r}
    {d e z : Fin r → DataTree} {n m : ℕ} {b c : Bool}
    (h : BoundedRuns P S d n e b) (ht : BoundedRuns T S e m z c) :
    BoundedRuns (P.andThen T) S d (n + 1 + m) z c := BoundedExec.andThen h ht

lemma BoundedRuns.branch_true {Q R : Type} {r S : ℕ} (src : Fin r)
    (P : TreeMachine Q r) (T : TreeMachine R r)
    {d e : Fin r → DataTree} {n : ℕ} {b : Bool} (h : d src = .nil)
    (hr : BoundedRuns P S d n e b) :
    BoundedRuns (TreeMachine.branch src P T) S d (n + 1) e b := by
  have hm := hr.map (T := TreeMachine.branch src P T) (fun q => .inr (.inl q))
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl)
  apply BoundedExec.next _ _ rfl hr.start_bound
  simpa [TreeMachine.branch, TreeOp.eval, h] using hm

lemma BoundedRuns.branch_false {Q R : Type} {r S : ℕ} (src : Fin r)
    (P : TreeMachine Q r) (T : TreeMachine R r)
    {d e : Fin r → DataTree} {n : ℕ} {b : Bool} (h : d src ≠ .nil)
    (hr : BoundedRuns T S d n e b) :
    BoundedRuns (TreeMachine.branch src P T) S d (n + 1) e b := by
  have hm := hr.map (T := TreeMachine.branch src P T) (fun q => .inr (.inr q))
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl)
  apply BoundedExec.next _ _ rfl hr.start_bound
  simpa [TreeMachine.branch, TreeOp.eval, h] using hm

lemma BoundedExec.repeat_true {Q : Type} {r S : ℕ} {P : TreeMachine Q r}
    {q : Q} {d e : Fin r → DataTree} {n : ℕ} (h : BoundedExec P S q d n e true) :
    BoundedExec P.repeat S q d n e true := by
  generalize hb : true = b at h
  induction h with
  | halt q d b ho hd => subst b; exact .halt _ _ _ (by simp [TreeMachine.repeat, ho]) hd
  | next q d ho hd _ ih =>
    apply BoundedExec.next _ _ (by simp [TreeMachine.repeat, ho]) hd
    simpa only [TreeMachine.repeat, ho, ↓reduceIte] using ih hb

lemma BoundedExec.repeat_false {Q : Type} {r S : ℕ} {P : TreeMachine Q r}
    {q : Q} {d e z : Fin r → DataTree} {n m : ℕ}
    (h : BoundedExec P S q d n e false) (ht : BoundedRuns P.repeat S e m z true) :
    BoundedExec P.repeat S q d (n + 1 + m) z true := by
  generalize hb : false = b at h
  induction h with
  | halt q d b ho hd =>
    subst b
    have he := BoundedExec.next (P := P.repeat) q d (by simp [TreeMachine.repeat, ho]) hd
      (by simpa [BoundedRuns, TreeMachine.repeat, ho, TreeOp.eval] using ht)
    convert he using 1
    omega
  | next q d ho hd _ ih =>
    have hi : P.repeat.instruction q = P.instruction q := by simp [TreeMachine.repeat, ho]
    have hn : ∀ b, P.repeat.next q b = P.next q b := by intro b; simp [TreeMachine.repeat, ho]
    have hh := BoundedExec.next (P := P.repeat) q d (by simp [TreeMachine.repeat, ho]) hd
      (by simpa only [hi, hn] using ih ht hb)
    convert hh using 1
    omega

end ParityWL.Complexity

namespace ParityWL.Complexity

noncomputable def extendData {r s : ℕ} (f : Fin r ↪ Fin s)
    (d : Fin r → DataTree) (e : Fin s → DataTree) : Fin s → DataTree := Function.extend f d e

@[simp] lemma extendData_apply {r s : ℕ} (f : Fin r ↪ Fin s)
    (d : Fin r → DataTree) (e : Fin s → DataTree) (i : Fin r) : extendData f d e (f i) = d i :=
  f.injective.extend_apply d e i

lemma extendData_outside {r s : ℕ} (f : Fin r ↪ Fin s)
    (d : Fin r → DataTree) (e : Fin s → DataTree) (j : Fin s) (h : ¬∃ i, f i = j) :
    extendData f d e j = e j := Function.extend_apply' d e j h

lemma extendData_update {r s : ℕ} (f : Fin r ↪ Fin s)
    (d : Fin r → DataTree) (e : Fin s → DataTree) (i : Fin r) (x : DataTree) :
    extendData f (Function.update d i x) e = Function.update (extendData f d e) (f i) x := by
  funext j
  by_cases hj : ∃ k, f k = j
  · obtain ⟨k, rfl⟩ := hj
    by_cases hk : k = i
    · subst k; simp
    · simp [hk, show f k ≠ f i from fun h => hk (f.injective h)]
  · have hi : j ≠ f i := fun h => hj ⟨i, h.symm⟩
    simp [extendData_outside f _ _ j hj, hi]

lemma DataBound.extend {r s S : ℕ} (f : Fin r ↪ Fin s)
    {d : Fin r → DataTree} {e : Fin s → DataTree} (hd : DataBound d S) (he : DataBound e S) :
    DataBound (extendData f d e) S := by
  intro j
  by_cases hj : ∃ i, f i = j
  · obtain ⟨i, rfl⟩ := hj; simpa using hd i
  · simpa [extendData_outside f d e j hj] using he j

def TreeOp.rename {r s : ℕ} (f : Fin r ↪ Fin s) : TreeOp r → TreeOp s
  | .skip => .skip
  | .nil i => .nil (f i)
  | .node i j k => .node (f i) (f j) (f k)
  | .project i j b => .project (f i) (f j) b
  | .test i => .test (f i)

lemma TreeOp.rename_eval {r s : ℕ} (f : Fin r ↪ Fin s) (op : TreeOp r)
    (d : Fin r → DataTree) (e : Fin s → DataTree) :
    (op.rename f).eval (extendData f d e) = (extendData f (op.eval d).1 e, (op.eval d).2) := by
  cases op <;> simp [TreeOp.rename, TreeOp.eval, extendData_update]

def TreeMachine.rename {Q : Type} {r s : ℕ} (P : TreeMachine Q r) (f : Fin r ↪ Fin s) :
    TreeMachine Q s where
  initial := P.initial
  output := P.output
  instruction := fun q => (P.instruction q).rename f
  next := P.next

lemma BoundedExec.rename {Q : Type} {r s S : ℕ} {P : TreeMachine Q r}
    (f : Fin r ↪ Fin s) (e : Fin s → DataTree) (he : DataBound e S)
    {q d z n b} (h : BoundedExec P S q d n z b) :
    BoundedExec (P.rename f) S q (extendData f d e) n (extendData f z e) b := by
  induction h with
  | halt q d b ho hd => exact .halt q _ b ho (hd.extend f he)
  | next q d ho hd _ ih =>
    apply BoundedExec.next (P := P.rename f) q _ ho (hd.extend f he)
    simpa only [TreeMachine.rename, TreeOp.rename_eval] using ih

/-- A complete compiler from raw input bits, with explicit initialization and
all serialization work charged. -/
noncomputable def TreeMachine.compiled {Q : Type} [Fintype Q] {r : ℕ} (P : TreeMachine Q (r + 1)) : Machine :=
  ((initializeData r).andThen P.lower.lower).compiled

lemma TreeRuns.compiled {Q : Type} [Fintype Q] {r : ℕ} {P : TreeMachine Q (r + 1)}
    {bs : List Bool} {w : ℕ} {e : Fin (r + 1) → DataTree} {b : Bool}
    (h : TreeRuns P (inputData r bs) w e b) :
    ∃ s, s ≤ 102 * w + 44 * bs.length + 20 ∧ Emits P.compiled bs s b := by
  obtain ⟨m, hm, hr⟩ := h.lower
  obtain ⟨n, hn, hi⟩ := initializeData_run r bs
  have hh := hi.andThen hr.lower
  exact ⟨2 * (n + 1 + m), by omega, hh.compiled⟩

lemma BoundedRuns.compiled {Q : Type} [Fintype Q] {r S : ℕ} {P : TreeMachine Q (r + 1)}
    {bs : List Bool} {n : ℕ} {e : Fin (r + 1) → DataTree} {b : Bool}
    (h : BoundedRuns P S (inputData r bs) n e b) :
    ∃ s, s ≤ 102 * n * ((r + 1) * S + 1) + 44 * bs.length + 20 ∧
      Emits P.compiled bs s b := by
  obtain ⟨w, hw, hr⟩ := h.work
  obtain ⟨s, hs, he⟩ := TreeRuns.compiled hr
  refine ⟨s, ?_, he⟩
  nlinarith

end ParityWL.Complexity

namespace ParityWL.Complexity

lemma DataBound.update {r S : ℕ} {d : Fin r → DataTree} (h : DataBound d S)
    (i : Fin r) (x : DataTree) (hx : x.size ≤ S) : DataBound (Function.update d i x) S := by
  intro j
  by_cases hj : j = i
  · subst j; simpa using hx
  · simpa [hj] using h j

inductive BCodeExec {r : ℕ} (S : ℕ) :
    TreeCode r → (Fin r → DataTree) → ℕ → (Fin r → DataTree) → Prop
  | skip (d) (hb : DataBound d S) : BCodeExec S .skip d 0 d
  | op (op : TreeOp r) (d) (hb : DataBound d S) (he : DataBound (op.eval d).1 S) :
      BCodeExec S (.op op) d 2 (op.eval d).1
  | seq {p q d e z n m} : BCodeExec S p d n e → BCodeExec S q e m z →
      BCodeExec S (.seq p q) d (n + 1 + m) z
  | nil_cond {i p q d e n} : d i = .nil → BCodeExec S p d n e →
      BCodeExec S (.cond i p q) d (n + 1) e
  | node_cond {i p q d e n} : d i ≠ .nil → BCodeExec S q d n e →
      BCodeExec S (.cond i p q) d (n + 1) e
  | nil_loop {i p d} : d i = .nil → DataBound d S → BCodeExec S (.loop i p) d 1 d
  | node_loop {i p d e z n m} : d i ≠ .nil → BCodeExec S p d n e →
      BCodeExec S (.loop i p) e m z → BCodeExec S (.loop i p) d (n + m + 3) z

lemma BCodeExec.compile {r S : ℕ} {p : TreeCode r} {d e : Fin r → DataTree} {n : ℕ}
    (h : BCodeExec S p d n e) : BoundedRuns p.compile.program S d n e true := by
  induction h with
  | skip d hb => exact boundedHalt true d hb
  | op op d hb he =>
    have h := (boundedAtomic op d hb he).andThen (boundedHalt true (op.eval d).1 he)
    simpa [TreeCode.compile, FinTree.of] using h
  | seq _ _ ih₁ ih₂ => exact ih₁.andThen ih₂
  | nil_cond h _ ih => exact ih.branch_true _ _ _ h
  | node_cond h _ ih => exact ih.branch_false _ _ _ h
  | nil_loop h hb =>
    simpa [TreeCode.compile, FinTree.of, BoundedRuns, TreeMachine.repeat] using
      BoundedExec.repeat_true ((boundedHalt true _ hb).branch_true _ _ _ h)
  | node_loop h _ _ ih₁ ih₂ =>
    have hr := (ih₁.andThen (boundedHalt false _ ih₁.end_bound)).branch_false _ (.halt true) _ h
    have ht := BoundedExec.repeat_false hr (by simpa [TreeCode.compile, FinTree.of] using ih₂)
    dsimp only [BoundedRuns, TreeCode.compile, FinTree.of]
    convert ht using 1 <;> first | rfl | omega

lemma BCodeExec.start_bound {r S : ℕ} {p : TreeCode r} {d e : Fin r → DataTree} {n : ℕ}
    (h : BCodeExec S p d n e) : DataBound d S := h.compile.start_bound
lemma BCodeExec.end_bound {r S : ℕ} {p : TreeCode r} {d e : Fin r → DataTree} {n : ℕ}
    (h : BCodeExec S p d n e) : DataBound e S := h.compile.end_bound

lemma BCodeExec.nil {r S : ℕ} (i : Fin r) (d : Fin r → DataTree)
    (h : DataBound d S) :
    BCodeExec S (.op (.nil i)) d 2 (Function.update d i .nil) := by
  exact .op _ _ h (h.update i .nil (by have := DataTree.size_pos (d i); have := h i; simp [DataTree.size]; omega))

lemma BCodeExec.node {r S : ℕ} (i j k : Fin r) (d : Fin r → DataTree)
    (h : DataBound d S) (hx : (DataTree.node (d j) (d k)).size ≤ S) :
    BCodeExec S (.op (.node i j k)) d 2 (Function.update d i (.node (d j) (d k))) := by
  exact .op _ _ h (h.update i _ hx)

lemma DataTree.size_child (x : DataTree) (b : Bool) : (x.child b).size ≤ x.size := by
  cases x <;> cases b <;> simp [DataTree.child, DataTree.size]
  omega

lemma BCodeExec.project {r S : ℕ} (i j : Fin r) (b : Bool) (d : Fin r → DataTree)
    (h : DataBound d S) :
    BCodeExec S (.op (.project i j b)) d 2 (Function.update d i ((d j).child b)) := by
  exact .op _ _ h (h.update i _ ((DataTree.size_child _ _).trans (h j)))

/-- Copying is compiled, not a primitive constant-time operation of the tape model. -/
def TreeCode.copy {r : ℕ} (dst src : Fin r) : TreeCode r :=
  .seq (.op (.node dst src src)) (.op (.project dst dst false))

lemma BCodeExec.copy {r S : ℕ} (i j : Fin r) (d : Fin r → DataTree)
    (h : DataBound d (2 * S + 1)) (hx : (d j).size ≤ S) :
    BCodeExec (2 * S + 1) (.copy i j) d 5 (Function.update d i (d j)) := by
  have h₁ := BCodeExec.node i j j d h (by simp [DataTree.size]; omega)
  have h₂ := BCodeExec.project i i false _ h₁.end_bound
  simpa [TreeCode.copy, DataTree.child] using h₁.seq h₂

lemma BCodeExec.mono {r S T : ℕ} (hST : S ≤ T)
    {p : TreeCode r} {d e : Fin r → DataTree} {n : ℕ} (h : BCodeExec S p d n e) :
    BCodeExec T p d n e := by
  induction h with
  | skip d hb => exact .skip d (fun i => (hb i).trans hST)
  | op op d hb he => exact .op op d (fun i => (hb i).trans hST) (fun i => (he i).trans hST)
  | seq _ _ ih₁ ih₂ => exact ih₁.seq ih₂
  | nil_cond h _ ih => exact ih.nil_cond h
  | node_cond h _ ih => exact ih.node_cond h
  | nil_loop h hb => exact .nil_loop h (fun i => (hb i).trans hST)
  | node_loop h _ _ ih₁ ih₂ => exact .node_loop h ih₁ ih₂

end ParityWL.Complexity

end OAI
