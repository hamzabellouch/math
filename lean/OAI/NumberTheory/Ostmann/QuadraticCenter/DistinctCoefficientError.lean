import OAI.NumberTheory.Ostmann.QuadraticCenter.DistinctCoefficientBounds

namespace OAI

namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem paired_series_error_bound {S m J k : ℕ}
    (hS : S ≤ J) (hm : m ≤ J) (hk : 2 ≤ k) :
    |(k.factorial : ℝ) *
        (∑ j ∈ Finset.range (m + 1),
          if 2 * j ≤ k then (-1 : ℝ) ^ j * (m.choose j : ℝ) * (S.choose (k - 2 * j) : ℝ)
          else 0) - (S : ℝ) ^ k| ≤
      (k : ℝ) ^ 2 * J * (S : ℝ) ^ (k - 2) +
        ∑ j ∈ (Finset.range (m + 1)).erase 0,
          if 2 * j ≤ k then ((k : ℝ) ^ 2 * J) ^ j * (S : ℝ) ^ (k - 2 * j) else 0 := by
  classical
  let F : ℕ → ℝ := fun j => if 2 * j ≤ k then
    (-1 : ℝ) ^ j * (m.choose j : ℝ) * (S.choose (k - 2 * j) : ℝ) else 0
  have hzero : 0 ∈ Finset.range (m + 1) := by simp
  have hs := Finset.sum_erase_add (Finset.range (m + 1)) F hzero
  have hlead : (k.factorial : ℝ) * F 0 = (S.descFactorial k : ℝ) := by
    have he : (k.factorial : ℝ) * (S.choose k : ℝ) = (S.descFactorial k : ℝ) := by
      exact_mod_cast (Nat.descFactorial_eq_factorial_mul_choose S k).symm
    simpa only [F, mul_zero, zero_le, ite_true, pow_zero, Nat.choose_zero_right,
      Nat.cast_one, one_mul, Nat.sub_zero] using he
  have hdecomp : (k.factorial : ℝ) * (∑ j ∈ Finset.range (m + 1), F j) =
      (S.descFactorial k : ℝ) + ∑ j ∈ (Finset.range (m + 1)).erase 0, (k.factorial : ℝ) * F j := by
    rw [← hs, mul_add, hlead, Finset.mul_sum]
    ring
  change |(k.factorial : ℝ) * (∑ j ∈ Finset.range (m + 1), F j) - (S : ℝ) ^ k| ≤ _
  rw [hdecomp]
  have hterm (j : ℕ) : |(k.factorial : ℝ) * F j| ≤
      if 2 * j ≤ k then ((k : ℝ) ^ 2 * J) ^ j * (S : ℝ) ^ (k - 2 * j) else 0 := by
    by_cases hj : 2 * j ≤ k
    · simp only [F, ite_eq_left hj, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
        one_mul]
      rw [abs_of_nonneg (Nat.cast_nonneg k.factorial : (0 : ℝ) ≤ k.factorial),
        abs_of_nonneg (Nat.cast_nonneg (m.choose j) : (0 : ℝ) ≤ m.choose j),
        abs_of_nonneg (Nat.cast_nonneg (S.choose (k - 2 * j)) : (0 : ℝ) ≤ S.choose (k - 2 * j))]
      simpa only [mul_assoc] using paired_binomial_coefficient_real_le (S := S) hj hm
    · simp only [F, ite_eq_right hj, mul_zero, abs_zero, le_refl]
  calc
    |(S.descFactorial k : ℝ) + (∑ j ∈ (Finset.range (m + 1)).erase 0,
        (k.factorial : ℝ) * F j) - (S : ℝ) ^ k| =
        |((S.descFactorial k : ℝ) - (S : ℝ) ^ k) +
          ∑ j ∈ (Finset.range (m + 1)).erase 0, (k.factorial : ℝ) * F j| := by
      congr 1
      ring
    _ ≤ |(S.descFactorial k : ℝ) - (S : ℝ) ^ k| +
        |∑ j ∈ (Finset.range (m + 1)).erase 0, (k.factorial : ℝ) * F j| := abs_add_le _ _
    _ ≤ (k : ℝ) ^ 2 * J * (S : ℝ) ^ (k - 2) +
        ∑ j ∈ (Finset.range (m + 1)).erase 0, |(k.factorial : ℝ) * F j| :=
      add_le_add (abs_descFactorial_sub_pow_le hS hk) (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ _ := add_le_add le_rfl (Finset.sum_le_sum (fun j hj => hterm j))

end Ostmann.QuadraticCenter

end OAI
