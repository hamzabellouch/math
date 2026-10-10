import OAI.Combinatorics.ParityLifts.StackRoutines

namespace OAI

namespace ParityWL.Complexity

@[ext] lemma StackConfiguration.ext {Q : Type} {t a : ℕ}
    {x y : StackConfiguration Q t a} (hs : x.state = y.state) (hw : x.word = y.word) :
    x = y := by
  cases x; cases y; cases hs; cases hw; rfl

inductive StackTrace {Q : Type} {t a : ℕ} (P : StackMachine Q t a) :
    StackConfiguration Q t a → ℕ → StackConfiguration Q t a → Prop
  | refl (x) : StackTrace P x 0 x
  | next (x) {n y} (h : P.output x.state = none)
      (tail : StackTrace P (P.step x) n y) : StackTrace P x (n + 1) y

lemma StackTrace.exec {Q : Type} {t a : ℕ} {P : StackMachine Q t a}
    {x y z : StackConfiguration Q t a} {n m : ℕ} {b : Bool}
    (h : StackTrace P x n y) (he : StackExec P y m z b) :
    StackExec P x (n + m) z b := by
  induction h with
  | refl => simpa using he
  | next x h _ ih =>
    have hh := StackExec.next x h (ih he)
    convert hh using 1
    omega

lemma StackTrace.trans {Q : Type} {t a : ℕ} {P : StackMachine Q t a}
    {x y z : StackConfiguration Q t a} {n m : ℕ}
    (h : StackTrace P x n y) (he : StackTrace P y m z) :
    StackTrace P x (n + m) z := by
  induction h with
  | refl => simpa using he
  | next x h _ ih =>
    have hh := StackTrace.next x h (ih he)
    convert hh using 1
    omega

lemma StackTrace.one {Q : Type} {t a : ℕ} {P : StackMachine Q t a}
    (x : StackConfiguration Q t a) (h : P.output x.state = none) :
    StackTrace P x 1 (P.step x) := .next _ h (.refl _)

/-- Prepending a copy preserves the source and clears the temporary stack. -/
def copyWord {t a : ℕ} (src dst tmp : Fin (t + 1)) :=
  (transfer (a := a) src {tmp}).andThen (transfer tmp {src, dst})

lemma copyWord_run {t a : ℕ} (src dst tmp : Fin (t + 1))
    (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
    (w : Words t a) (ht : w tmp = []) :
    Runs (copyWord src dst tmp) w (4 * (w src).length + 3)
      (Function.update w dst (w src ++ w dst)) true := by
  have h1 := transfer_run src {tmp} w
  have h2 := transfer_run tmp {src, dst} (transferred src {tmp} w)
  have ht' : transferred src {tmp} w tmp = (w src).reverse := by
    simp [transferred, Ne.symm hst, ht]
  have hout : transferred tmp {src, dst} (transferred src {tmp} w) =
      Function.update w dst (w src ++ w dst) := by
    funext i
    by_cases hi : i = tmp
    · subst i
      simp [transferred, Function.update, Ne.symm hdt, ht]
    · by_cases hs : i = src
      · subst i
        simp [transferred, hst, Ne.symm hst, ht, Function.update, hsd]
      · by_cases hd : i = dst
        · subst i
          simp [transferred, hdt, Ne.symm hst, ht, Ne.symm hsd, Function.update]
        · simp [transferred, hi, hs, hd, Function.update]
  have h := h1.andThen h2
  rw [ht', List.length_reverse, hout] at h
  change Runs ((transfer src {tmp}).andThen (transfer tmp {src, dst})) _ _ _ _
  convert h using 1
  omega

/-- A fixed one-cell insertion. -/
def pushSymbol {t a : ℕ} (dst : Fin (t + 1)) (c : StackSymbol a) :=
  primitive (fun _ i => if i = dst then .push c else .keep) (fun _ => true)

lemma pushSymbol_run {t a : ℕ} (dst : Fin (t + 1)) (c : StackSymbol a) (w : Words t a) :
    Runs (pushSymbol dst c) w 1 (Function.update w dst (c :: w dst)) true := by
  refine ⟨some true, ?_⟩
  have h := primitive_exec (fun (_ : Fin (t + 1) → Option (StackSymbol a)) i =>
    if i = dst then StackOp.push c else .keep) (fun _ => true) w
  have he : applyOps (fun i => if i = dst then .push c else .keep) w =
      Function.update w dst (c :: w dst) := by
    funext i
    by_cases hi : i = dst <;> simp [applyOps, StackOp.apply, Function.update, hi]
  exact he ▸ h

/-- A prefix-encoded finite binary tree; every code is nonempty and uniquely
self-delimiting. Working trees need no infinite-alphabet cells. -/
inductive DataTree where
  | nil
  | node (left right : DataTree)
  deriving DecidableEq

def DataTree.code : DataTree → List (StackSymbol 0)
  | .nil => [0]
  | .node l r => 1 :: l.code ++ r.code

def DataTree.size : DataTree → ℕ
  | .nil => 1
  | .node l r => 1 + l.size + r.size

@[simp] lemma DataTree.length_code (d : DataTree) : d.code.length = d.size := by
  induction d with
  | nil => rfl
  | node l r hl hr => simp [DataTree.code, DataTree.size, hl, hr]; omega

lemma DataTree.size_pos (d : DataTree) : 0 < d.size := by cases d <;> simp [DataTree.size]

/-- Sweep one prefix tree into `dst` in reverse order, tracking unvisited child
slots on a unary stack. A null pending stack terminates; all transitions are
constant-size finite-table operations. -/
def treeScan {t : ℕ} (src dst pending : Fin (t + 1)) : StackMachine Bool t 0 where
  initial := false
  output := fun b => if b then some true else none
  transition := fun _ x =>
    if (x pending).isNone then (true, fun _ => .keep) else
      (false, fun i => if i = src then .pop else
        if i = dst then match x src with | none => .keep | some c => .push c else
        if i = pending then if x src = some 1 then .push 0 else .pop else .keep)

def scanUpdate {t : ℕ} (src dst pending : Fin (t + 1))
    (w : Words t 0) (chunk rest : List (StackSymbol 0)) (p : ℕ) : Words t 0 :=
  Function.update (Function.update (Function.update w src rest) dst
    (chunk.reverse ++ w dst)) pending (List.replicate p 0)

def scanResult {t : ℕ} (src dst pending : Fin (t + 1))
    (w : Words t 0) (d : DataTree) (rest : List (StackSymbol 0)) (p : ℕ) : Words t 0 :=
  scanUpdate src dst pending w d.code rest p

lemma treeScan_nil_step {t : ℕ} (src dst pending : Fin (t + 1))
    (hsd : src ≠ dst) (hsp : src ≠ pending) (hdp : dst ≠ pending)
    (w : Words t 0) (rest : List (StackSymbol 0)) (p : ℕ)
    (hs : w src = 0 :: rest) (hp : w pending = List.replicate (p + 1) 0) :
    (treeScan src dst pending).step ⟨false, w⟩ =
      ⟨false, scanResult src dst pending w .nil rest p⟩ := by
  apply StackConfiguration.ext
  · simp [StackMachine.step, treeScan, hp, List.replicate_succ]
  · funext i
    simp only [StackMachine.step, treeScan, Bool.false_eq_true, ↓reduceIte,
      hp, List.replicate_succ, List.head?_cons, Option.isNone_some]
    by_cases hi : i = src
    · subst i
      simp [scanResult, scanUpdate, hsp, hsd, Function.update, StackOp.apply, hs]
    · by_cases hd : i = dst
      · subst i
        simp [scanResult, scanUpdate, Ne.symm hsd, hdp, Function.update, StackOp.apply, hs,
          DataTree.code]
      · by_cases hpen : i = pending
        · subst i
          simp [scanResult, scanUpdate, Ne.symm hsp, Ne.symm hdp, Function.update, StackOp.apply,
            hs, hp, List.replicate_succ]
        · simp [scanResult, scanUpdate, hi, hd, hpen, Function.update, StackOp.apply]

end ParityWL.Complexity

namespace ParityWL.Complexity

lemma scanUpdate_comp {t : ℕ} (src dst pending : Fin (t + 1))
    (hsd : src ≠ dst) (hsp : src ≠ pending) (hdp : dst ≠ pending)
    (w : Words t 0) (u v rest mid : List (StackSymbol 0)) (p q : ℕ) :
    scanUpdate src dst pending (scanUpdate src dst pending w u mid p) v rest q =
      scanUpdate src dst pending w (u ++ v) rest q := by
  funext i
  by_cases hi : i = src
  · subst i; simp [scanUpdate, hsp, hsd]
  · by_cases hd : i = dst
    · subst i
      simp [scanUpdate, hdp, List.reverse_append, List.append_assoc]
    · by_cases hp : i = pending
      · subst i; simp [scanUpdate]
      · simp [scanUpdate, Function.update, hi, hd, hp]

lemma treeScan_node_step {t : ℕ} (src dst pending : Fin (t + 1))
    (hsd : src ≠ dst) (hsp : src ≠ pending) (hdp : dst ≠ pending)
    (w : Words t 0) (rest : List (StackSymbol 0)) (p : ℕ)
    (hs : w src = 1 :: rest) (hp : w pending = List.replicate (p + 1) 0) :
    (treeScan src dst pending).step ⟨false, w⟩ =
      ⟨false, scanUpdate src dst pending w [1] rest (p + 2)⟩ := by
  apply StackConfiguration.ext
  · simp [StackMachine.step, treeScan, hp, List.replicate_succ]
  · funext i
    simp only [StackMachine.step, treeScan, Bool.false_eq_true, ↓reduceIte,
      hp, List.replicate_succ, List.head?_cons, Option.isNone_some]
    by_cases hi : i = src
    · subst i
      simp [scanUpdate, hsp, hsd, Function.update, StackOp.apply, hs]
    · by_cases hd : i = dst
      · subst i
        simp [scanUpdate, Ne.symm hsd, hdp, Function.update, StackOp.apply, hs]
      · by_cases hpen : i = pending
        · subst i
          simp [scanUpdate, Ne.symm hsp, Ne.symm hdp, Function.update, StackOp.apply,
            hs, hp, List.replicate_succ]
        · simp [scanUpdate, hi, hd, hpen, Function.update, StackOp.apply]

lemma treeScan_trace {t : ℕ} (src dst pending : Fin (t + 1))
    (hsd : src ≠ dst) (hsp : src ≠ pending) (hdp : dst ≠ pending)
    (d : DataTree) (rest : List (StackSymbol 0)) (p : ℕ) (w : Words t 0)
    (hs : w src = d.code ++ rest) (hp : w pending = List.replicate (p + 1) 0) :
    StackTrace (treeScan src dst pending) ⟨false, w⟩ d.size
      ⟨false, scanResult src dst pending w d rest p⟩ := by
  induction d generalizing w rest p with
  | nil =>
    have h := StackTrace.one (P := treeScan src dst pending) ⟨false, w⟩ rfl
    rw [treeScan_nil_step src dst pending hsd hsp hdp w rest p hs hp] at h
    exact h
  | node l r hl hr =>
    let w₁ := scanUpdate src dst pending w [1] (l.code ++ r.code ++ rest) (p + 2)
    have h₁ : StackTrace (treeScan src dst pending) ⟨false, w⟩ 1 ⟨false, w₁⟩ := by
      have h := StackTrace.one (P := treeScan src dst pending) ⟨false, w⟩ rfl
      rw [treeScan_node_step src dst pending hsd hsp hdp w _ p
        (by simpa [DataTree.code, List.append_assoc] using hs) hp] at h
      simpa [w₁, List.append_assoc] using h
    have hls : w₁ src = l.code ++ (r.code ++ rest) := by
      simp [w₁, scanUpdate, hsp, hsd, List.append_assoc]
    have hlp : w₁ pending = List.replicate (p + 1 + 1) 0 := by
      simp [w₁, scanUpdate]
    have h₂ := hl (r.code ++ rest) (p + 1) w₁ hls hlp
    let w₂ := scanResult src dst pending w₁ l (r.code ++ rest) (p + 1)
    have hrs : w₂ src = r.code ++ rest := by simp [w₂, scanResult, scanUpdate, hsp, hsd]
    have hrp : w₂ pending = List.replicate (p + 1) 0 := by simp [w₂, scanResult, scanUpdate]
    have h₃ := hr rest p w₂ hrs hrp
    have hout : scanResult src dst pending w₂ r rest p =
        scanResult src dst pending w (.node l r) rest p := by
      dsimp only [w₂, w₁, scanResult]
      rw [scanUpdate_comp src dst pending hsd hsp hdp,
        scanUpdate_comp src dst pending hsd hsp hdp]
      simp [DataTree.code]
    rw [hout] at h₃
    simpa [DataTree.size, Nat.add_assoc] using h₁.trans (h₂.trans h₃)

lemma treeScan_run {t : ℕ} (src dst pending : Fin (t + 1))
    (hsd : src ≠ dst) (hsp : src ≠ pending) (hdp : dst ≠ pending)
    (d : DataTree) (rest : List (StackSymbol 0)) (w : Words t 0)
    (hs : w src = d.code ++ rest) (hp : w pending = [0]) :
    Runs (treeScan src dst pending) w (d.size + 1)
      (scanResult src dst pending w d rest 0) true := by
  have h := treeScan_trace src dst pending hsd hsp hdp d rest 0 w hs hp
  let v := scanResult src dst pending w d rest 0
  have hv : v pending = [] := by simp [v, scanResult, scanUpdate]
  have he : (treeScan src dst pending).step ⟨false, v⟩ = ⟨true, v⟩ := by
    simp [StackMachine.step, treeScan, hv, StackOp.apply]
  have halt : StackExec (treeScan src dst pending) ⟨false, v⟩ 1 ⟨true, v⟩ true := by
    apply StackExec.next _ rfl
    rw [he]
    exact .halt _ _ rfl
  exact ⟨true, h.exec halt⟩

def moveTree {t : ℕ} (src dst pending : Fin (t + 1)) :=
  (pushSymbol (a := 0) pending 0).andThen (treeScan src dst pending)

lemma moveTree_run {t : ℕ} (src dst pending : Fin (t + 1))
    (hsd : src ≠ dst) (hsp : src ≠ pending) (hdp : dst ≠ pending)
    (d : DataTree) (rest : List (StackSymbol 0)) (w : Words t 0)
    (hs : w src = d.code ++ rest) (hp : w pending = []) :
    Runs (moveTree src dst pending) w (d.size + 3)
      (scanResult src dst pending w d rest 0) true := by
  have h₁ := pushSymbol_run pending (0 : StackSymbol 0) w
  have h₂ := treeScan_run src dst pending hsd hsp hdp d rest
    (Function.update w pending (0 :: w pending)) (by simpa [hsp] using hs) (by simp [hp])
  have hout : scanResult src dst pending (Function.update w pending (0 :: w pending)) d rest 0 =
      scanResult src dst pending w d rest 0 := by
    funext i
    by_cases he : i = pending
    · subst i; simp [scanResult, scanUpdate]
    · simp [scanResult, scanUpdate, Function.update, he, hdp]
  have h := h₁.andThen h₂
  rw [hout] at h
  change Runs ((pushSymbol pending 0).andThen (treeScan src dst pending)) _ _ _ _
  convert h using 1
  omega

end ParityWL.Complexity

end OAI
