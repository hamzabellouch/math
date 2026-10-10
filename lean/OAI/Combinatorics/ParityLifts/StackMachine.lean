import OAI.Combinatorics.ParityLifts.Machines

namespace OAI

namespace ParityWL.Complexity

abbrev StackSymbol (a : ℕ) := Fin (a + 2)

def encodeTop {a : ℕ} : Option (StackSymbol a) → Fin (a + 3)
  | none => 0
  | some x => x.succ

def decodeTop {a : ℕ} (x : Fin (a + 3)) : Option (StackSymbol a) :=
  Fin.cases none some x

@[simp] lemma decode_encodeTop {a : ℕ} (x : Option (StackSymbol a)) :
    decodeTop (encodeTop x) = x := by cases x <;> simp [decodeTop, encodeTop]

@[simp] lemma encode_decodeTop {a : ℕ} (x : Fin (a + 3)) :
    encodeTop (decodeTop x) = x := by
  refine Fin.cases ?_ (fun x => ?_) x <;> simp [decodeTop, encodeTop]

@[simp] lemma encodeTop_zero_iff {a : ℕ} (x : Option (StackSymbol a)) :
    encodeTop x = 0 ↔ x = none := by
  cases x with
  | none => simp [encodeTop]
  | some x => simp only [encodeTop, Fin.succ_ne_zero, Option.some_ne_none]

def wordCell {a : ℕ} (w : List (StackSymbol a)) (z : ℤ) : Fin (a + 3) :=
  if 0 ≤ z then encodeTop w[z.toNat]? else 0

@[simp] lemma wordCell_zero {a : ℕ} (w : List (StackSymbol a)) :
    wordCell w 0 = encodeTop w.head? := by simp [wordCell, List.head?_eq_getElem?]

@[simp] lemma wordCell_nil {a : ℕ} (z : ℤ) : wordCell ([] : List (StackSymbol a)) z = 0 := by
  simp [wordCell, encodeTop]

lemma wordCell_neg {a : ℕ} (w : List (StackSymbol a)) {z : ℤ} (hz : z < 0) :
    wordCell w z = 0 := ite_eq_right (by omega)

lemma wordCell_cons {a : ℕ} (x : StackSymbol a) (w : List (StackSymbol a)) (z : ℤ) :
    wordCell (x :: w) z = if z = 0 then encodeTop (some x) else wordCell w (z - 1) := by
  by_cases hz : z = 0
  · subst z; simp
  by_cases hp : 0 < z
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ z - 1)
    have he : z = (n : ℤ) + 1 := by omega
    rw [he]
    simp [wordCell, Int.toNat_add, show 0 ≤ (n : ℤ) + 1 by omega,
      show ¬ (n : ℤ) + 1 = 0 by omega]
  · rw [wordCell_neg _ (by omega), ite_eq_right hz, wordCell_neg _ (by omega)]

lemma wordCell_pop {a : ℕ} (x : StackSymbol a) (w : List (StackSymbol a)) (z : ℤ) :
    (if z = 0 then 0 else wordCell (x :: w) z) = wordCell w (z - 1) := by
  rw [wordCell_cons]
  by_cases hz : z = 0
  · subst z; simp [wordCell]
  · simp [hz]

inductive StackOp (a : ℕ) where
  | keep
  | pop
  | push (symbol : StackSymbol a)
  deriving DecidableEq

def StackOp.apply {a : ℕ} : StackOp a → List (StackSymbol a) → List (StackSymbol a)
  | .keep, w => w
  | .pop, w => w.tail
  | .push x, w => x :: w

def StackOp.action {a : ℕ} : StackOp a → Fin (a + 3) → Fin (a + 3) × Move
  | .keep, z => (z, .stay)
  | .pop, z => if z = 0 then (0, .stay) else (0, .right)
  | .push _, z => (z, .left)

def StackOp.pending {a : ℕ} : StackOp a → Option (StackSymbol a)
  | .push x => some x
  | _ => none

def finishWrite {a : ℕ} (x : Option (StackSymbol a)) (z : Fin (a + 3)) : Fin (a + 3) :=
  match x with | none => z | some x => encodeTop (some x)

lemma tape_operation {a : ℕ} (op : StackOp a) (w : List (StackSymbol a))
    (h : ℤ) (f : ℤ → Fin (a + 3)) (hf : ∀ z, f z = wordCell w (z - h)) :
    let act := op.action (f h)
    let h' := h + act.2.offset
    let f' := fun z => if z = h then act.1 else f z
    ∀ z, (if z = h' then finishWrite op.pending (f' h') else f' z) =
      wordCell (op.apply w) (z - h') := by
  have hread : f h = encodeTop w.head? := by simpa using hf h
  cases op with
  | keep =>
    simp only [StackOp.action, Move.offset, add_zero, StackOp.pending, finishWrite, StackOp.apply]
    intro z
    by_cases hz : z = h
    · subst z; simp [hread]
    · simpa [hz] using hf z
  | pop =>
    cases w with
    | nil =>
      have hz : f h = 0 := by simpa [encodeTop] using hread
      simp only [StackOp.action, hz, ↓reduceIte, Move.offset, add_zero,
        StackOp.pending, finishWrite, StackOp.apply, List.tail_nil]
      intro z
      by_cases he : z = h
      · simp [he, encodeTop]
      · simpa [he] using hf z
    | cons x w =>
      have hz : f h ≠ 0 := by rw [hread]; simp
      simp only [StackOp.action, ite_eq_right hz, Move.offset, StackOp.pending,
        finishWrite, StackOp.apply, List.tail_cons]
      intro z
      have he : ¬ h + 1 = h := by omega
      by_cases hz' : z = h + 1
      · subst z
        simp only [↓reduceIte, ite_eq_right he]
        rw [hf, wordCell_cons]
        norm_num
      · simp only [ite_eq_right hz']
        rw [hf]
        have hc := wordCell_pop x w (z - h)
        have h0 : z - h = 0 ↔ z = h := sub_eq_zero
        have h1 : z - h - 1 = z - (h + 1) := by ring
        simpa only [h0, h1] using hc
  | push x =>
    dsimp only [StackOp.action, Move.offset, StackOp.pending, finishWrite, StackOp.apply]
    intro z
    by_cases hz : z = h + -1
    · subst z; simp
    · rw [ite_eq_right hz]
      rw [wordCell_cons]
      have h0 : ¬ z - (h + -1) = 0 := by omega
      have h1 : z - (h + -1) - 1 = z - h := by ring
      rw [ite_eq_right h0, h1]
      by_cases he : z = h
      · subst z; simp [hread]
      · simpa [he] using hf z

structure StackMachine (Q : Type) (t a : ℕ) where
  initial : Q
  output : Q → Option Bool
  transition : Q → (Fin (t + 1) → Option (StackSymbol a)) → Q × (Fin (t + 1) → StackOp a)

structure StackConfiguration (Q : Type) (t a : ℕ) where
  state : Q
  word : Fin (t + 1) → List (StackSymbol a)

def StackMachine.step {Q : Type} {t a : ℕ} (P : StackMachine Q t a)
    (x : StackConfiguration Q t a) : StackConfiguration Q t a :=
  match P.output x.state with
  | some _ => x
  | none =>
      let b := P.transition x.state (fun i => (x.word i).head?)
      { state := b.1, word := fun i => (b.2 i).apply (x.word i) }

abbrev StackControl (Q : Type) (t a : ℕ) := Q ⊕ (Q × (Fin (t + 1) → Option (StackSymbol a)))

def StackMachine.lower {Q : Type} {t a : ℕ} (P : StackMachine Q t a) :
    LocalMachine (StackControl Q t a) t a where
  initial := Sum.inl P.initial
  output := fun q => match q with | .inl q => P.output q | .inr _ => none
  transition := fun q x => match q with
    | .inl q =>
        let b := P.transition q (fun i => decodeTop (x i))
        (.inr (b.1, fun i => (b.2 i).pending), fun i => (b.2 i).action (x i))
    | .inr (q, p) => (.inl q, fun i => (finishWrite (p i) (x i), .stay))

def StackMachine.Represents {Q : Type} {t a : ℕ} (_P : StackMachine Q t a)
    (x : StackConfiguration Q t a) (y : LocalConfiguration (StackControl Q t a) t a) : Prop :=
  y.state = Sum.inl x.state ∧ ∀ i z, y.tape i z = wordCell (x.word i) (z - y.head i)

lemma StackMachine.lower_two_steps {Q : Type} {t a : ℕ} (P : StackMachine Q t a)
    (x : StackConfiguration Q t a) (y : LocalConfiguration (StackControl Q t a) t a)
    (h : P.Represents x y) : P.Represents (P.step x) (P.lower.step (P.lower.step y)) := by
  have hread : (fun i => decodeTop (y.tape i (y.head i))) = fun i => (x.word i).head? := by
    funext i
    rw [h.2 i, sub_self, wordCell_zero, decode_encodeTop]
  cases ho : P.output x.state with
  | some b =>
    have he : P.lower.step y = y := by
      simp only [LocalMachine.step, StackMachine.lower, h.1, ho]
    rw [he, he]
    simpa only [StackMachine.step, ho] using h
  | none =>
    simp only [StackMachine.Represents, StackMachine.step, LocalMachine.step,
      StackMachine.lower, h.1, ho, hread, Move.offset, add_zero]
    constructor
    · trivial
    · intro i z
      exact tape_operation _ _ _ _ (h.2 i) z

end ParityWL.Complexity

namespace ParityWL.Complexity

def stackInputSymbol (a : ℕ) (b : Bool) : StackSymbol a :=
  if b then ⟨1, by omega⟩ else 0

lemma encodeTop_input (a : ℕ) (b : Bool) :
    encodeTop (some (stackInputSymbol a b)) = localInputSymbol a b := by
  cases b <;> rfl

def StackMachine.initialConfiguration {Q : Type} {t a : ℕ}
    (P : StackMachine Q t a) (input : List Bool) : StackConfiguration Q t a where
  state := P.initial
  word := fun i => if i.val = 0 then input.map (stackInputSymbol a) else []

def StackMachine.run {Q : Type} {t a : ℕ} (P : StackMachine Q t a)
    (input : List Bool) (s : ℕ) : StackConfiguration Q t a :=
  P.step^[s] (P.initialConfiguration input)

lemma StackMachine.lower_initial {Q : Type} {t a : ℕ}
    (P : StackMachine Q t a) (input : List Bool) :
    P.Represents (P.initialConfiguration input) (P.lower.initialConfiguration input) := by
  constructor
  · rfl
  · intro i z
    change (if i.val = 0 ∧ 0 ≤ z then
      match input[z.toNat]? with
      | some b => localInputSymbol a b
      | none => 0
      else 0) = wordCell (if i.val = 0 then input.map (stackInputSymbol a) else []) (z - 0)
    rw [sub_zero]
    by_cases hi : i.val = 0
    · simp only [hi, true_and, ↓reduceIte, wordCell, List.getElem?_map]
      by_cases hz : 0 ≤ z
      · simp only [hz, ↓reduceIte]
        cases h : input[z.toNat]? with
        | none => rfl
        | some b => exact (encodeTop_input a b).symm
      · simp [hz]
    · simp [hi]

lemma StackMachine.lower_iterate {Q : Type} {t a : ℕ}
    (P : StackMachine Q t a) (x : StackConfiguration Q t a)
    (y : LocalConfiguration (StackControl Q t a) t a) (h : P.Represents x y) (s : ℕ) :
    P.Represents (P.step^[s] x) (P.lower.step^[2 * s] y) := by
  induction s with
  | zero => exact h
  | succ s ih =>
    have he : 2 * (s + 1) = 2 * s + 1 + 1 := by omega
    rw [he, Function.iterate_succ_apply', Function.iterate_succ_apply',
      Function.iterate_succ_apply']
    exact P.lower_two_steps _ _ ih

lemma StackMachine.lower_run {Q : Type} {t a : ℕ} (P : StackMachine Q t a)
    (input : List Bool) (s : ℕ) :
    P.Represents (P.run input s) (P.lower.run input (2 * s)) :=
  P.lower_iterate _ _ (P.lower_initial input) s

/-- Every machine with finite control and finitely many finite-alphabet stacks
is realized by the multitape `Machine`, at exactly two local steps per
stack step. This includes input preparation and halting semantics. -/
noncomputable def StackMachine.compiled {Q : Type} [Fintype Q] {t a : ℕ}
    (P : StackMachine Q t a) : Machine := P.lower.packed

lemma StackMachine.compiled_emits {Q : Type} [Fintype Q] {t a : ℕ}
    (P : StackMachine Q t a) (input : List Bool) (s : ℕ) (b : Bool) :
    Emits P.compiled input (2 * s) b ↔ P.output (P.run input s).state = some b := by
  rw [StackMachine.compiled, LocalMachine.packed_emits]
  rw [(P.lower_run input s).1]
  rfl

end ParityWL.Complexity

end OAI
