import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import OAI.NumberTheory.Ostmann.Construction.WeightedRepeatRemoval

namespace OAI

/-! # Explicit numerical budgets for the relative repeat-removal error -/

namespace Ostmann

open Filter Asymptotics

/-- A shift of at most one quarter of the inverse moment order changes the
moment by a factor less than `3/2`. -/
theorem moment_small_shift (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (k : ℕ) (hk : 0 < k) (hsmall : 4 * k * B ≤ A) :
    (A + B) ^ k ≤ (3 / 2 : ℝ) * A ^ k := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  by_cases hA0 : A = 0
  · have hB0 : B = 0 := by nlinarith
    simp [hA0, hB0, hk.ne']
  have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hA0)
  have hkx : (k : ℝ) * (B / A) ≤ 1 / 4 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr
    rw [show ((k : ℝ) * (B / A)) * 4 = (4 * k * B) / A by ring]
    exact (div_le_one hApos).mpr hsmall
  have he : Real.exp (1 / 4 : ℝ) ≤ 3 / 2 := by
    have hh := Real.exp_bound_div_one_sub_of_interval
      (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num : (1 / 4 : ℝ) < 1)
    norm_num at hh ⊢
    linarith
  calc
    (A + B) ^ k = A ^ k * (1 + B / A) ^ k := by
      rw [← mul_pow]
      congr 1
      field_simp
    _ ≤ A ^ k * (Real.exp (B / A)) ^ k := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hA k)
      apply pow_le_pow_left₀ (by positivity)
      simpa only [add_comm] using Real.add_one_le_exp (B / A)
    _ = A ^ k * Real.exp (k * (B / A)) := by rw [Real.exp_nat_mul]
    _ ≤ A ^ k * Real.exp (1 / 4) := by gcongr
    _ ≤ _ := by nlinarith [pow_nonneg hA k]

/-- The squared form avoids logarithms of either moment and is convenient
when inserting `I≥sqrt(X)*exp(.016K)` and `I₀≤C*X`. -/
theorem repeat_shift_of_squared_budget (I I₀ : ℝ) (hI : 0 ≤ I) (hI₀ : 0 ≤ I₀)
    (J k : ℕ) (hJ : 0 < J) (hk : 0 < k)
    (hbudget : ((16 * (k : ℝ) ^ 3 / J) ^ k) * I₀ ^ 2 ≤ I ^ 2) :
    4 * k * ((Real.sqrt ((k : ℝ) * J) / J) * I₀ ^ (1 / (k : ℝ))) ≤
      I ^ (1 / (k : ℝ)) := by
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  have hKR : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hroot₀ : (I₀ ^ (1 / (k : ℝ))) ^ k = I₀ := by
    simpa only [one_div] using Real.rpow_inv_natCast_pow hI₀ hk.ne'
  have hroot : (I ^ (1 / (k : ℝ))) ^ k = I := by
    simpa only [one_div] using Real.rpow_inv_natCast_pow hI hk.ne'
  have hb : (4 * k * (Real.sqrt ((k : ℝ) * J) / J)) ^ 2 = 16 * (k : ℝ) ^ 3 / J := by
    rw [mul_pow, div_pow, Real.sq_sqrt (mul_nonneg hKR hJR.le)]
    field_simp
    ring
  have hh : ((4 * k * (Real.sqrt ((k : ℝ) * J) / J)) ^ k * I₀) ^ 2 ≤ I ^ 2 := by
    rw [mul_pow, ← pow_mul, mul_comm k 2, pow_mul, hb]
    exact hbudget
  have hh' : (4 * k * (Real.sqrt ((k : ℝ) * J) / J)) ^ k * I₀ ≤ I := by
    nlinarith [show 0 ≤ (4 * k * (Real.sqrt ((k : ℝ) * J) / J)) ^ k * I₀ by positivity]
  apply (pow_le_pow_iff_left₀ (by positivity) (Real.rpow_nonneg hI _) hk.ne').mp
  rw [show 4 * (k : ℝ) * ((Real.sqrt ((k : ℝ) * J) / J) * I₀ ^ (1 / (k : ℝ))) =
    (4 * k * (Real.sqrt ((k : ℝ) * J) / J)) * I₀ ^ (1 / (k : ℝ)) by ring,
    mul_pow, hroot₀, hroot]
  exact hh'

end Ostmann

end OAI
