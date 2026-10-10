import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.FiniteStackArithmetic
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.ConfigurationTapes

namespace OAI

/-! Exact integer stack formulas for each recorder head move. A single
additional digit accommodates a step; a popped infinite blank tail stays zero. -/

namespace ForcedComputation.Lattice

def StackTailZero (d : ℕ) (a : ℕ → ℕ) : Prop := ∀ i, d ≤ i → a i = 0

theorem stackValue_pop_padding {b k : ℕ} (hb : 0 < b) {a : ℕ → ℕ}
    (ha : a 0 < b) (hz : StackTailZero (k + 1) a) (e : ℕ) :
    stackValue b (k + e) (fun i => a (i + 1)) = stackValue b (k + 1) a / b := by
  rw [stackValue_tail hb ha]
  apply stackValue_extend
  intro i hi
  exact hz (i + 1) (by omega)

def integerTapeCode (b d : ℕ) (T : Radix.Tape ℕ) : ℕ × ℕ :=
  (stackValue b d T.1, stackValue b d T.2)

theorem integerTapeCode_right {b k : ℕ} (hb : 0 < b) (s : ℕ) (T : Radix.Tape ℕ)
    (hR : T.2 0 < b) (hR0 : StackTailZero (k + 1) T.2) :
    integerTapeCode b (k + 2) (Radix.writeRight s T) =
      (s + b * (integerTapeCode b (k + 1) T).1,
        (integerTapeCode b (k + 1) T).2 / b) := by
  apply Prod.ext
  · rfl
  · exact stackValue_pop_padding hb hR hR0 2

theorem integerTapeCode_stay {b k : ℕ} (hb : 0 < b) (s : ℕ) (T : Radix.Tape ℕ)
    (hL0 : StackTailZero (k + 1) T.1)
    (hR : T.2 0 < b) (hR0 : StackTailZero (k + 1) T.2) :
    integerTapeCode b (k + 2) (Radix.writeStay s T) =
      ((integerTapeCode b (k + 1) T).1,
        s + b * ((integerTapeCode b (k + 1) T).2 / b)) := by
  apply Prod.ext
  · exact stackValue_extend b (k + 1) 1 T.1 hL0
  · change s + b * stackValue b (k + 1) (fun i => T.2 (i + 1)) = _
    rw [stackValue_pop_padding hb hR hR0 1]
    rfl

theorem integerTapeCode_left {b k : ℕ} (hb : 0 < b) (s : ℕ) (T : Radix.Tape ℕ)
    (hL : T.1 0 < b) (hL0 : StackTailZero (k + 1) T.1) (hR : T.2 0 < b) :
    integerTapeCode b (k + 2) (Radix.writeLeft s T) =
      ((integerTapeCode b (k + 1) T).1 / b,
        (integerTapeCode b (k + 1) T).1 % b +
          b * (s + b * ((integerTapeCode b (k + 1) T).2 / b))) := by
  apply Prod.ext
  · exact stackValue_pop_padding hb hL hL0 2
  · change T.1 0 + b * (s + b * stackValue b k (fun i => T.2 (i + 1))) = _
    simp only [integerTapeCode, stackValue_head hL, stackValue_tail hb hR]

theorem integerTapeCode_move {b d : ℕ} (hb : 0 < b) (hd : 0 < d)
    (s : ℕ) (T : Radix.Tape ℕ) (hL : T.1 0 < b) (hR : T.2 0 < b)
    (hL0 : StackTailZero d T.1) (hR0 : StackTailZero d T.2) (m : Fin 3) :
    integerTapeCode b (d + 1)
        (if m = 0 then Radix.writeLeft s T else
          if m = 1 then Radix.writeStay s T else Radix.writeRight s T) =
      (nextLeft b (integerTapeCode b d T).1 s m,
        nextRight b (integerTapeCode b d T).1 (integerTapeCode b d T).2 s m) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
  fin_cases m
  · simpa [nextLeft, nextRight, Nat.succ_eq_add_one] using
      integerTapeCode_left hb s T hL hL0 hR
  · simpa [nextLeft, nextRight, Nat.succ_eq_add_one] using
      integerTapeCode_stay hb s T hL0 hR hR0
  · simpa [nextLeft, nextRight, Nat.succ_eq_add_one] using
      integerTapeCode_right hb s T hR hR0

end ForcedComputation.Lattice

end OAI
