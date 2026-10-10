import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Rat.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace OAI

/-! Polynomial-time approximation of weighted matchings with singleton loops. -/

namespace LoopMatching.Accumulator
open scoped BigOperators

def Q (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => a 0
  | n + 1 => (n + 1) * Q a n + a (n + 1)

@[simp] theorem Q_zero (a : ℕ → ℕ) : Q a 0 = a 0 := rfl

@[simp] theorem Q_succ (a : ℕ → ℕ) (n : ℕ) :
    Q a (n + 1) = (n + 1) * Q a n + a (n + 1) := rfl

theorem denominator_pos (n : ℕ) : 0 < n.factorial := Nat.factorial_pos n

theorem quotient_eq_sum (a : ℕ → ℕ) (n : ℕ) :
    (Q a n : ℚ) / (n.factorial : ℚ) =
      ∑ j ∈ Finset.range (n + 1), (a j : ℚ) / (j.factorial : ℚ) := by
  induction n with
  | zero => simp [Q]
  | succ n ih =>
      rw [Finset.sum_range_succ, ← ih, Q_succ, Nat.factorial_succ]
      push_cast
      have hn : (n : ℚ) + 1 ≠ 0 := by positivity
      have hf : (n.factorial : ℚ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero n
      field_simp [hn, hf]

theorem Q_le_factorial_mul (a : ℕ → ℕ) (n B : ℕ)
    (ha : ∀ j ≤ n, a j ≤ B) :
    Q a n ≤ (n + 1).factorial * B := by
  induction n generalizing B with
  | zero => simpa using ha 0 (Nat.le_refl 0)
  | succ n ih =>
      have hprev : Q a n ≤ (n + 1).factorial * B :=
        ih B (fun j hj => ha j (Nat.le_trans hj (Nat.le_succ n)))
      have hlast : a (n + 1) ≤ B := ha (n + 1) (Nat.le_refl _)
      have hfac : 1 ≤ (n + 1).factorial := Nat.factorial_pos (n + 1)
      have hB : B ≤ (n + 1).factorial * B := by
        simpa only [one_mul] using Nat.mul_le_mul_right B hfac
      calc
        Q a (n + 1) = (n + 1) * Q a n + a (n + 1) := rfl
        _ ≤ (n + 1) * ((n + 1).factorial * B) + B :=
          Nat.add_le_add (Nat.mul_le_mul_left (n + 1) hprev) hlast
        _ ≤ (n + 1) * ((n + 1).factorial * B) +
              (n + 1).factorial * B := Nat.add_le_add_left hB _
        _ = (n + 1 + 1).factorial * B := by
          rw [Nat.factorial_succ (n + 1)]
          ring

end LoopMatching.Accumulator

end OAI
