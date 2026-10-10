import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace OAI

/-! Numerical consequences, to be used only after the geometric volume identities. -/

namespace ProjectionCounterexample

/-- Algebraic double-counting identity used after the visible-face measure sum.
The balance condition is later proved from the actual simplex facet vectors. -/
theorem sum_positive_eq_half_sum_abs {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ha : ∑ i, a i = 0) :
    (∑ i with 0 < a i, a i) = (∑ i, |a i|) / 2 := by
  classical
  have hi (i : ι) : 2 * (if 0 < a i then a i else 0) = |a i| + a i := by
    split_ifs with h
    · rw [abs_of_pos h]
      linarith
    · rw [abs_of_nonpos (le_of_not_gt h)]
      linarith
  have hs : 2 * (∑ i, if 0 < a i then a i else 0) = ∑ i, |a i| := by
    rw [Finset.mul_sum]
    simp_rw [hi]
    rw [Finset.sum_add_distrib, ha, add_zero]
  rw [Finset.sum_filter]
  linarith

theorem numerical_product_ratio :
    (((11 : ℝ) * 10 ^ 10 / (Nat.factorial 10 : ℝ)) ^ 2) /
        ((21 : ℝ) * 20 ^ 20 / (Nat.factorial 20 : ℝ)) =
      (22355476 : ℝ) / 22020096 := by
  norm_num [Nat.factorial]

theorem numerical_strict_excess :
    (1 : ℝ) < (22355476 : ℝ) / 22020096 := by
  norm_num

end ProjectionCounterexample

end OAI
