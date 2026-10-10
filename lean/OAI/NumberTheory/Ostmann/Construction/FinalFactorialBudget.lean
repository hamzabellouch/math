import OAI.NumberTheory.Ostmann.Construction.FinalParityPaths
import OAI.NumberTheory.Ostmann.Construction.FactorialExponential

namespace OAI

/-! # The factorial gain from the actual final reassignment family -/

namespace Ostmann

open scoped BigOperators

theorem final_reassignment_card_exp_lower (n m : ℕ) :
    Real.exp ((2 ^ (n + 1) : ℝ) * m * ((n : ℝ) * Real.log 2 - 1)) ≤
      (Fintype.card (FinalParityReassignments n m) : ℝ) := by
  have hq : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by omega)
  have h := pow_le_pow_left₀ (Real.exp_nonneg _) (factorial_exp_lower hq) (2 * m)
  rw [← Real.exp_nat_mul] at h
  rw [card_finalParityReassignments]
  push_cast
  rw [← pow_mul]
  convert h using 1
  congr 1
  push_cast
  rw [Real.log_pow, pow_succ]
  ring

/-- At fixed depth, the diagonal exponential cost is beaten by the
factorial family as soon as its entropy margin is positive. -/
theorem final_diagonal_entropy_bound (n m : ℕ) (a C : ℝ)
    (ha : a ≤ (n : ℝ) * Real.log 2 - 1 - C) :
    Real.exp (C * (2 ^ (n + 1) : ℝ) * m) /
        (Fintype.card (FinalParityReassignments n m) : ℝ) ≤
      Real.exp (-a * (2 ^ (n + 1) : ℝ) * m) := by
  apply (div_le_iff₀ (by exact_mod_cast Fintype.card_pos (α := FinalParityReassignments n m))).mpr
  calc
    _ ≤ Real.exp (-a * (2 ^ (n + 1) : ℝ) * m) *
        Real.exp ((2 ^ (n + 1) : ℝ) * m * ((n : ℝ) * Real.log 2 - 1)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have ht : 0 ≤ (2 ^ (n + 1) : ℝ) * m := by positivity
      nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_left (final_reassignment_card_exp_lower n m) (Real.exp_nonneg _)

end Ostmann

end OAI
