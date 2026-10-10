import OAI.NumberTheory.Ostmann.Preliminaries.SieveWeightTruncation

namespace OAI

/-! # The Euler-product lower bound for fixed-shift sieving -/

namespace Ostmann

open scoped Classical BigOperators

 theorem fixed_shift_euler_lower (P : Finset ℕ) (j : ℝ) (hj : 0 ≤ j)
    (hP : ∀ p ∈ P, j < (p : ℝ)) :
    Real.exp (j * ∑ p ∈ P, 1 / (p : ℝ)) ≤
      ∏ p ∈ P, (p : ℝ) / ((p : ℝ) - j) := by
  rw [Finset.mul_sum, Real.exp_sum]
  apply Finset.prod_le_prod₀
  · intro p _
    exact (Real.exp_pos _).le
  · intro p hp
    have hp0 : (0 : ℝ) < p := lt_of_le_of_lt hj (hP p hp)
    have hdiff : 0 < (p : ℝ) - j := sub_pos.mpr (hP p hp)
    have hratio : 0 < (p : ℝ) / ((p : ℝ) - j) := div_pos hp0 hdiff
    have hlog := Real.one_sub_inv_le_log_of_pos hratio
    have hid : 1 - ((p : ℝ) / ((p : ℝ) - j))⁻¹ = j * (1 / (p : ℝ)) := by
      field_simp
      ring
    rw [hid] at hlog
    exact (Real.exp_le_exp.mpr hlog).trans_eq (Real.exp_log hratio)

 theorem fixed_shift_euler_log_lower (P : Finset ℕ) (j : ℕ) (R C : ℝ)
    (hR : 1 < R) (hP : ∀ p ∈ P, (j : ℝ) < p)
    (hH : Real.log (Real.log R) - C ≤ ∑ p ∈ P, 1 / (p : ℝ)) :
    Real.exp (-(j : ℝ) * C) * Real.log R ^ j ≤
      ∏ p ∈ P, (p : ℝ) / ((p : ℝ) - j) := by
  have hp : Real.log R ^ j = Real.exp ((j : ℝ) * Real.log (Real.log R)) := by
    rw [Real.exp_nat_mul, Real.exp_log (Real.log_pos hR)]
  rw [hp, ← Real.exp_add]
  have hmul := mul_le_mul_of_nonneg_left hH (Nat.cast_nonneg (α := ℝ) j)
  have he : -(j : ℝ) * C + (j : ℝ) * Real.log (Real.log R) =
      (j : ℝ) * (Real.log (Real.log R) - C) := by ring
  rw [he]
  exact (Real.exp_le_exp.mpr hmul).trans
    (fixed_shift_euler_lower P j (Nat.cast_nonneg j) hP)

end Ostmann

end OAI
