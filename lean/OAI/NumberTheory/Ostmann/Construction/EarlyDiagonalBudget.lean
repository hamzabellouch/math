import OAI.NumberTheory.Ostmann.Construction.SelectedDiagonalBudget

namespace OAI

/-! # The two initial depths fit the same diagonal reserve -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem early_bad_multiplier_one_le (n : ℕ) (hn : n ≤ 1) (m : ℝ) (hm : 0 ≤ m) :
    1 ≤ (((2 ^ n + 1) * (2 ^ n) ^ (2 * 2 ^ n) : ℕ) : ℝ) *
      Real.exp ((2 ^ n : ℕ) * m * (-(3 / 4 : ℝ) * Real.log (2 ^ n : ℕ) + 5 / 4)) := by
  have hn' : n = 0 ∨ n = 1 := by omega
  rcases hn' with rfl | rfl
  · norm_num only [pow_zero, Nat.cast_one, Real.log_one, mul_zero, zero_add,
      Nat.reduceAdd, Nat.reduceMul, one_pow, Nat.cast_ofNat, one_mul]
    have he : 1 ≤ Real.exp (m * (5 / 4)) := Real.one_le_exp (by positivity)
    linarith
  · norm_num only [pow_one, Nat.reduceAdd, Nat.reduceMul, Nat.reducePow, Nat.cast_ofNat]
    have hlog : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    have he : 1 ≤ Real.exp (2 * m * (-(3 / 4 : ℝ) * Real.log 2 + 5 / 4)) :=
      Real.one_le_exp (mul_nonneg (by positivity) (by linarith))
    linarith

theorem early_diagonal_energy_le (n : ℕ) (hn : n ≤ 1) (m main err tail : ℝ)
    (hm : 0 ≤ m) (hmain : 0 ≤ main) (herr : 0 ≤ err) (htail : 0 ≤ tail) :
    4 * (main + 5 * err) ≤
      4 * ((((2 ^ n + 1) * (2 ^ n) ^ (2 * 2 ^ n) : ℕ) : ℝ) *
        Real.exp ((2 ^ n : ℕ) * m * (-(3 / 4 : ℝ) * Real.log (2 ^ n : ℕ) + 5 / 4)) *
          (main + 5 * err) + tail + 5 * err) := by
  have h := mul_le_mul_of_nonneg_right (early_bad_multiplier_one_le n hn m hm)
    (show 0 ≤ main + 5 * err by positivity)
  linarith

end Ostmann

end OAI
