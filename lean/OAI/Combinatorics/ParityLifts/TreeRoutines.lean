import OAI.Combinatorics.ParityLifts.TreeWords

namespace OAI

namespace ParityWL.Complexity

def StackMachine.halt {t a : ℕ} (b : Bool) : StackMachine Unit t a where
  initial := ()
  output := fun _ => some b
  transition := fun _ _ => ((), fun _ => .keep)

lemma halt_run {t a : ℕ} (b : Bool) (w : Words t a) :
    Runs (.halt b) w 0 w b := ⟨(), .halt _ _ rfl⟩

/-- Branching tests only the finitely many currently scanned stack symbols. -/
def StackMachine.branch {Q R : Type} {t a : ℕ}
    (test : (Fin (t + 1) → Option (StackSymbol a)) → Bool)
    (P : StackMachine Q t a) (T : StackMachine R t a) :
    StackMachine (Unit ⊕ Q ⊕ R) t a where
  initial := .inl ()
  output := fun q => match q with
    | .inl _ => none
    | .inr (.inl q) => P.output q
    | .inr (.inr q) => T.output q
  transition := fun q x => match q with
    | .inl _ => (if test x then .inr (.inl P.initial) else .inr (.inr T.initial), fun _ => .keep)
    | .inr (.inl q) => let v := P.transition q x; (.inr (.inl v.1), v.2)
    | .inr (.inr q) => let v := T.transition q x; (.inr (.inr v.1), v.2)

lemma Runs.branch_true {Q R : Type} {t a : ℕ}
    (test : (Fin (t + 1) → Option (StackSymbol a)) → Bool)
    (P : StackMachine Q t a) (T : StackMachine R t a)
    {w v : Words t a} {n : ℕ} {b : Bool} (h : test (fun i => (w i).head?) = true)
    (hr : Runs P w n v b) : Runs (StackMachine.branch test P T) w (1 + n) v b := by
  obtain ⟨q, hq⟩ := hr
  let f : StackConfiguration Q t a → StackConfiguration (Unit ⊕ Q ⊕ R) t a :=
    fun x => ⟨.inr (.inl x.state), x.word⟩
  have hm := hq.map (T := StackMachine.branch test P T) f (fun _ => rfl) (by
    intro x hx
    simp only [f, StackMachine.step, StackMachine.branch, hx])
  have he : (StackMachine.branch test P T).step ⟨.inl (), w⟩ = f ⟨P.initial, w⟩ := by
    simp [f, StackMachine.step, StackMachine.branch, h, StackOp.apply]
  refine ⟨.inr (.inl q), ?_⟩
  have hh := StackExec.next ⟨.inl (), w⟩ (by rfl : (StackMachine.branch test P T).output _ = none)
    (he ▸ hm)
  simpa only [Nat.add_comm 1 n, f, StackMachine.branch] using hh

lemma Runs.branch_false {Q R : Type} {t a : ℕ}
    (test : (Fin (t + 1) → Option (StackSymbol a)) → Bool)
    (P : StackMachine Q t a) (T : StackMachine R t a)
    {w v : Words t a} {n : ℕ} {b : Bool} (h : test (fun i => (w i).head?) = false)
    (hr : Runs T w n v b) : Runs (StackMachine.branch test P T) w (1 + n) v b := by
  obtain ⟨q, hq⟩ := hr
  let f : StackConfiguration R t a → StackConfiguration (Unit ⊕ Q ⊕ R) t a :=
    fun x => ⟨.inr (.inr x.state), x.word⟩
  have hm := hq.map (T := StackMachine.branch test P T) f (fun _ => rfl) (by
    intro x hx
    simp only [f, StackMachine.step, StackMachine.branch, hx])
  have he : (StackMachine.branch test P T).step ⟨.inl (), w⟩ = f ⟨T.initial, w⟩ := by
    simp [f, StackMachine.step, StackMachine.branch, h, StackOp.apply]
  refine ⟨.inr (.inr q), ?_⟩
  have hh := StackExec.next ⟨.inl (), w⟩ (by rfl : (StackMachine.branch test P T).output _ = none)
    (he ▸ hm)
  simpa only [Nat.add_comm 1 n, f, StackMachine.branch] using hh

def popSymbol {t a : ℕ} (src : Fin (t + 1)) :=
  primitive (a := a) (fun _ i => if i = src then .pop else .keep) (fun _ => true)

lemma popSymbol_run {t a : ℕ} (src : Fin (t + 1)) (w : Words t a) :
    Runs (popSymbol src) w 1 (Function.update w src (w src).tail) true := by
  refine ⟨some true, ?_⟩
  have h := primitive_exec (fun (_ : Fin (t + 1) → Option (StackSymbol a)) i =>
    if i = src then StackOp.pop else .keep) (fun _ => true) w
  have he : applyOps (fun i => if i = src then .pop else .keep) w =
      Function.update w src (w src).tail := by
    funext i
    by_cases hi : i = src <;> simp [applyOps, StackOp.apply, Function.update, hi]
  exact he ▸ h

end ParityWL.Complexity

namespace ParityWL.Complexity

/-- Assemble a binary node without changing either operand, even if the
store destination aliases an operand. The buffer and temporary are cleared. -/
def nodeWord {t : ℕ} (dst left right buf tmp : Fin (t + 1)) :=
  (((((copyWord (a := 0) right buf tmp).andThen (copyWord left buf tmp)).andThen
    (pushSymbol buf 1)).andThen (transfer dst ∅)).andThen
    (copyWord buf dst tmp)).andThen (transfer buf ∅)

lemma nodeWord_run {t : ℕ} (dst left right buf tmp : Fin (t + 1))
    (hdb : dst ≠ buf) (hdt : dst ≠ tmp) (hlb : left ≠ buf) (hlt : left ≠ tmp)
    (hrb : right ≠ buf) (hrt : right ≠ tmp) (hbt : buf ≠ tmp)
    (w : Words t 0) (hb : w buf = []) (ht : w tmp = []) :
    Runs (nodeWord dst left right buf tmp) w
      (10 * ((w left).length + (w right).length) + 2 * (w dst).length + 23)
      (Function.update w dst (1 :: w left ++ w right)) true := by
  let u := w left
  let v := w right
  let z := w dst
  let c := 1 :: u ++ v
  let w₁ := Function.update w buf v
  let w₂ := Function.update w buf (u ++ v)
  let w₃ := Function.update w buf c
  let w₄ := Function.update w₃ dst []
  let w₅ := Function.update w₃ dst c
  let w₆ := Function.update w dst c
  have h₁ : Runs (copyWord right buf tmp) w (4 * v.length + 3) w₁ true := by
    simpa [w₁, v, hb] using copyWord_run right buf tmp hrb hrt hbt w ht
  have h₂ : Runs (copyWord left buf tmp) w₁ (4 * u.length + 3) w₂ true := by
    have h := copyWord_run left buf tmp hlb hlt hbt w₁ (by simp [w₁, Ne.symm hbt, ht])
    simpa [w₁, w₂, hlb, u] using h
  have h₃ : Runs (pushSymbol buf 1) w₂ 1 w₃ true := by
    simpa [w₂, w₃, c] using pushSymbol_run buf (1 : StackSymbol 0) w₂
  have h₄ : Runs (transfer dst ∅) w₃ (2 * z.length + 1) w₄ true := by
    simpa [w₄, z, w₃, hdb] using clear_run dst w₃
  have h₅ : Runs (copyWord buf dst tmp) w₄ (4 * c.length + 3) w₅ true := by
    have h := copyWord_run buf dst tmp (Ne.symm hdb) hbt hdt w₄
      (by simp [w₄, w₃, Ne.symm hdt, Ne.symm hbt, ht])
    simpa [w₄, w₅, w₃, Ne.symm hdb] using h
  have h₆ : Runs (transfer buf ∅) w₅ (2 * c.length + 1) w₆ true := by
    have h := clear_run buf w₅
    have he : Function.update w₅ buf [] = w₆ := by
      funext i
      by_cases hi : i = buf
      · subst i; simp [w₆, Ne.symm hdb, hb]
      · simp [w₅, w₃, w₆, Function.update, hi]
    rw [he] at h
    simpa [w₅, w₃, Ne.symm hdb] using h
  have hh := ((((h₁.andThen h₂).andThen h₃).andThen h₄).andThen h₅).andThen h₆
  unfold nodeWord
  have hc : c.length = 1 + u.length + v.length := by simp [c]; omega
  convert hh using 1
  dsimp only [u, v, z] at hc ⊢
  omega

def nilWord {t : ℕ} (dst : Fin (t + 1)) :=
  (transfer (a := 0) dst ∅).andThen (pushSymbol dst 0)

lemma nilWord_run {t : ℕ} (dst : Fin (t + 1)) (w : Words t 0) :
    Runs (nilWord dst) w (2 * (w dst).length + 3)
      (Function.update w dst [0]) true := by
  have h₁ := clear_run dst w
  have h₂ := pushSymbol_run dst (0 : StackSymbol 0) (Function.update w dst [])
  have h := h₁.andThen h₂
  have he : 2 * (w dst).length + 3 = 2 * (w dst).length + 1 + 1 + 1 := by omega
  simpa [nilWord, he] using h

end ParityWL.Complexity

namespace ParityWL.Complexity

def DataTree.child (right : Bool) : DataTree → DataTree
  | .nil => .nil
  | .node l r => if right then r else l

def selectChildTail {t : ℕ} (buf out : Fin (t + 1)) (right : Bool) :=
  StackMachine.branch (fun _ => right) (transfer (a := 0) out ∅)
    ((transfer buf ∅).andThen (transfer out {buf}))

def selectChild {t : ℕ} (buf out pending : Fin (t + 1)) (right : Bool) :=
  StackMachine.branch (fun x => decide (x buf = some 0)) (.halt true)
    (((popSymbol buf).andThen (moveTree buf out pending)).andThen
      (selectChildTail buf out right))

lemma selectChild_run {t : ℕ} (buf out pending : Fin (t + 1))
    (hbo : buf ≠ out) (hbp : buf ≠ pending) (hop : out ≠ pending)
    (right : Bool) (d : DataTree) (w : Words t 0)
    (hb : w buf = d.code) (ho : w out = []) (hp : w pending = []) :
    ∃ n, n ≤ 5 * d.size + 12 ∧ Runs (selectChild buf out pending right) w n
      (Function.update w buf (d.child right).code) true := by
  cases d with
  | nil =>
    have h := (halt_run true w).branch_true (fun x => decide (x buf = some 0))
      (.halt true) (((popSymbol buf).andThen (moveTree buf out pending)).andThen
      (selectChildTail buf out right)) (by simp [hb, DataTree.code])
    have he : Function.update w buf ((DataTree.nil).child right).code = w := by
      simp [DataTree.child, ← hb]
    refine ⟨1, by simp [DataTree.size], ?_⟩
    simpa only [he, Nat.add_zero, selectChild] using h
  | node l r =>
    let w₁ := Function.update w buf (l.code ++ r.code)
    let w₂ := Function.update (Function.update w buf r.code) out l.code.reverse
    have h₁ : Runs (popSymbol buf) w 1 w₁ true := by
      simpa [w₁, hb, DataTree.code] using popSymbol_run buf w
    have h₂ : Runs (moveTree buf out pending) w₁ (l.size + 3) w₂ true := by
      have h := moveTree_run buf out pending hbo hbp hop l r.code w₁
        (by simp [w₁]) (by simp [w₁, Ne.symm hbp, hp])
      have he : scanResult buf out pending w₁ l r.code 0 = w₂ := by
        funext i
        by_cases hi : i = pending
        · subst i
          simp [scanResult, scanUpdate, w₂, Ne.symm hop, Ne.symm hbp, hp]
        · by_cases he : i = buf
          · subst i; simp [scanResult, scanUpdate, w₁, w₂, hbp, hbo]
          · by_cases hd : i = out
            · subst i; simp [scanResult, scanUpdate, w₁, w₂, hop, Ne.symm hbo, ho]
            · simp [scanResult, scanUpdate, w₁, w₂, Function.update, hi, he, hd]
      exact he ▸ h
    have hpre := h₁.andThen h₂
    have htail : ∃ m, m ≤ 2 * l.size + 2 * r.size + 4 ∧
        Runs (selectChildTail buf out right) w₂ m
          (Function.update w buf ((DataTree.node l r).child right).code) true := by
      cases right with
      | false =>
        let z := Function.update w₂ buf []
        have hc : Runs (transfer buf ∅) w₂ (2 * r.size + 1) z true := by
          simpa [z, w₂, hbo] using clear_run buf w₂
        have ht := transfer_run out {buf} z
        have hzout : z out = l.code.reverse := by simp [z, w₂, Ne.symm hbo]
        have hz : transferred out {buf} z = Function.update w buf l.code := by
          funext i
          by_cases hi : i = out
          · subst i; simp [transferred, Function.update, Ne.symm hbo, ho]
          · by_cases he : i = buf
            · subst i; simp [transferred, hbo, hzout, z]
            · simp [transferred, hi, he, z, w₂, Function.update]
        rw [hzout, List.length_reverse, DataTree.length_code, hz] at ht
        have hh := (hc.andThen ht).branch_false (fun _ => false)
          (transfer out ∅) ((transfer buf ∅).andThen (transfer out {buf})) rfl
        refine ⟨_, ?_, hh⟩
        omega
      | true =>
        have hc := clear_run out w₂
        have hz : Function.update w₂ out [] = Function.update w buf r.code := by
          funext i
          by_cases hi : i = out
          · subst i; simp [Function.update, Ne.symm hbo, ho]
          · simp [w₂, Function.update, hi]
        have hout : w₂ out = l.code.reverse := by simp [w₂]
        rw [hout, List.length_reverse, DataTree.length_code, hz] at hc
        have hh := hc.branch_true (fun _ => true)
          (transfer out ∅) ((transfer buf ∅).andThen (transfer out {buf})) rfl
        exact ⟨_, by omega, hh⟩
    obtain ⟨m, hm, ht⟩ := htail
    have hn := (hpre.andThen ht).branch_false (fun x => decide (x buf = some 0))
      (.halt true) (((popSymbol buf).andThen (moveTree buf out pending)).andThen
      (selectChildTail buf out right)) (by simp [hb, DataTree.code])
    refine ⟨_, ?_, hn⟩
    simp only [DataTree.size]
    omega

/-- Tree projection with untouched operand and clean finite work stacks. -/
def projectWord {t : ℕ} (dst src buf tmp out pending : Fin (t + 1)) (right : Bool) :=
  ((((copyWord (a := 0) src buf tmp).andThen (selectChild buf out pending right)).andThen
    (transfer dst ∅)).andThen (copyWord buf dst tmp)).andThen (transfer buf ∅)

lemma projectWord_run {t : ℕ} (dst src buf tmp out pending : Fin (t + 1))
    (hdb : dst ≠ buf) (hdt : dst ≠ tmp)
    (hsb : src ≠ buf) (hst : src ≠ tmp)
    (hbt : buf ≠ tmp) (hbo : buf ≠ out) (hbp : buf ≠ pending)
    (hop : out ≠ pending)
    (right : Bool) (d : DataTree) (w : Words t 0)
    (hs : w src = d.code) (hb : w buf = []) (ht : w tmp = [])
    (ho : w out = []) (hp : w pending = []) :
    ∃ n, n ≤ 20 * (d.size + (w dst).length + 1) ∧
      Runs (projectWord dst src buf tmp out pending right) w n
        (Function.update w dst (d.child right).code) true := by
  let w₁ := Function.update w buf d.code
  let w₂ := Function.update w buf (d.child right).code
  let w₃ := Function.update w₂ dst []
  let w₄ := Function.update w₂ dst (d.child right).code
  have h₁ : Runs (copyWord src buf tmp) w (4 * d.size + 3) w₁ true := by
    simpa [w₁, hs, hb] using copyWord_run src buf tmp hsb hst hbt w ht
  obtain ⟨m, hm, h₂⟩ := selectChild_run buf out pending hbo hbp hop right d w₁
    (by simp [w₁]) (by simp [w₁, Ne.symm hbo, ho]) (by simp [w₁, Ne.symm hbp, hp])
  change Runs (selectChild buf out pending right) w₁ m
    (Function.update w₁ buf (d.child right).code) true at h₂
  have he : Function.update w₁ buf (d.child right).code = w₂ := by simp [w₁, w₂]
  rw [he] at h₂
  have h₃ : Runs (transfer dst ∅) w₂ (2 * (w dst).length + 1) w₃ true := by
    simpa [w₃, w₂, hdb] using clear_run dst w₂
  have h₄ : Runs (copyWord buf dst tmp) w₃ (4 * (d.child right).size + 3) w₄ true := by
    have h := copyWord_run buf dst tmp (Ne.symm hdb) hbt hdt w₃
      (by simp [w₃, w₂, Ne.symm hdt, Ne.symm hbt, ht])
    simpa [w₃, w₂, w₄, Ne.symm hdb] using h
  have h₅ : Runs (transfer buf ∅) w₄ (2 * (d.child right).size + 1)
      (Function.update w dst (d.child right).code) true := by
    have h := clear_run buf w₄
    have he : Function.update w₄ buf [] = Function.update w dst (d.child right).code := by
      funext i
      by_cases hi : i = buf
      · subst i; simp [Ne.symm hdb, hb]
      · simp [w₄, w₂, Function.update, hi]
    rw [he] at h
    simpa [w₄, w₂, Ne.symm hdb] using h
  have hh := (((h₁.andThen h₂).andThen h₃).andThen h₄).andThen h₅
  have hc : (d.child right).size ≤ d.size := by
    cases d with
    | nil => rfl
    | node l r => cases right <;> simp [DataTree.child, DataTree.size]; omega
  have hd := d.size_pos
  refine ⟨_, ?_, hh⟩
  omega

end ParityWL.Complexity

end OAI
