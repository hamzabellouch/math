import OAI.NumberTheory.Ostmann.ZeroDensity.DensityTailBlock

namespace OAI

/-! # Numerical decay of the distant dyadic coefficient blocks -/

namespace Ostmann

open scoped BigOperators

 theorem density_dyadic_fraction_bound (B V A r L : ℝ)
    (hB : 0 ≤ B) (hBV : B ≤ V) (hV : 0 < V) (hA : 0 ≤ A) (hr : 1 ≤ r) (hL : 0 ≤ L) :
    B ^ 2 * (2 * r * V + A) * ((2 * r * V) * L ^ 3 / (r * V) ^ 3) ≤
      4 * (V + A) * L ^ 3 / r := by
  have hrp : 0 < r := by linarith
  have hsq : B ^ 2 ≤ V ^ 2 := pow_le_pow_left₀ hB hBV 2
  calc
    _ ≤ V ^ 2 * (2 * r * V + A) * ((2 * r * V) * L ^ 3 / (r * V) ^ 3) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right hsq (by positivity)
    _ = (4 * V / r + 2 * A / r ^ 2) * L ^ 3 := by field_simp; ring
    _ ≤ (4 * (V + A) / r) * L ^ 3 := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hL 3)
      apply (le_div_iff₀ hrp).mpr
      have hdiv : (2 * A / r ^ 2) * r = 2 * A / r := by field_simp
      rw [add_mul, div_mul_cancel₀ _ hrp.ne', hdiv]
      have hb : 2 * A / r ≤ 4 * A := by
        apply (div_le_iff₀ hrp).mpr
        nlinarith
      nlinarith
    _ = _ := by ring

 theorem density_dyadic_log_bound (N j : ℕ) (hN : 1 ≤ N) :
    1 + Real.log ((2 : ℝ) ^ (j + 1) * N) ≤
      (j + 2 : ℝ) * (1 + Real.log N) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNl : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  rw [Real.log_mul (by positivity) hNp.ne', Real.log_pow]
  have htwo : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  push_cast
  nlinarith

end Ostmann

end OAI
