import OAI.NumberTheory.EgyptianFractions.DescentRecurrence

namespace OAI
namespace Problem337

/-- A logarithmic estimate uniform over the moment orders used in the
exceptional-set descent. -/
theorem log_one_sub_reciprocal_lower (r : ℝ) (hr : 2 ≤ r) :
    -(2 / r) ≤ Real.log (1 - 1 / r) := by
  have hrpos : 0 < r := by linarith
  have hr1 : 0 < r - 1 := by linarith
  have hα : 0 < 1 - 1 / r := by
    have : 1 / r < (1 : ℝ) := (div_lt_one hrpos).mpr (by linarith)
    linarith
  have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr hα)
  rw [Real.log_inv] at hlog
  have hident : (1 - 1 / r)⁻¹ - 1 = 1 / (r - 1) := by
    field_simp
    ring
  have hfrac : 1 / (r - 1) ≤ 2 / r := by
    apply (div_le_div_iff₀ hr1 hrpos).mpr
    linarith
  rw [hident] at hlog
  linarith

/-- A moment order at least eight times the logarithmic depth constant
ensures that the repeated Hölder exponent loses at most a fourth power. -/
theorem descent_power_lower
    (r K S : ℝ) (d : ℕ) (hr : 2 ≤ r) (hKr : 8 * K ≤ r)
    (hS : 1 ≤ S) (hd : (d : ℝ) ≤ K * Real.log S) :
    S ^ (-(1 / 4 : ℝ)) ≤ (1 - 1 / r) ^ d := by
  have hrpos : 0 < r := by linarith
  have hSpos : 0 < S := lt_of_lt_of_le zero_lt_one hS
  have hlogS : 0 ≤ Real.log S := Real.log_nonneg hS
  have hα : 0 < 1 - 1 / r := by
    have : 1 / r < (1 : ℝ) := (div_lt_one hrpos).mpr (by linarith)
    linarith
  have hlog := log_one_sub_reciprocal_lower r hr
  have hlogmul := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
  have hdepth : 2 * (d : ℝ) / r ≤ Real.log S / 4 := by
    apply (div_le_div_iff₀ hrpos (by norm_num : (0 : ℝ) < 4)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hKr hlogS]
  rw [Real.rpow_def_of_pos hSpos]
  apply (Real.le_log_iff_exp_le (pow_pos hα d)).mp
  rw [Real.log_pow]
  simp only [div_eq_mul_inv] at hlogmul hdepth ⊢
  nlinarith

/-- The explicit finite density estimate, before the final asymptotic
comparison of the positive and negative terms in the exponent. -/
theorem descent_density_exp_bound
    (δ : ℕ → ℝ) (d : ℕ) (r K S c m : ℝ)
    (hr : 2 ≤ r) (hKr : 8 * K ≤ r) (hS : 1 ≤ S)
    (hc : 0 ≤ c) (hm : 0 ≤ m) (hd : (d : ℝ) ≤ K * Real.log S)
    (hδd : δ d = 0) (hδ : ∀ j ≤ d, 0 ≤ δ j)
    (hstep : ∀ j < d, δ j ≤ Real.exp (-c * m) +
      Real.exp (2 * S ^ (1 / 4 : ℝ)) * (δ (j + 1)) ^ (1 - 1 / r)) :
    δ 0 ≤ (d : ℝ) * Real.exp
      (2 * r * S ^ (1 / 4 : ℝ) - c * m * S ^ (-(1 / 4 : ℝ))) := by
  have hrpos : 0 < r := by linarith
  have hS0 : 0 ≤ S := le_trans zero_le_one hS
  have hα0 : 0 < 1 - 1 / r := by
    have : 1 / r < (1 : ℝ) := (div_lt_one hrpos).mpr (by linarith)
    linarith
  have hα1 : 1 - 1 / r < 1 := by
    have : 0 < 1 / r := div_pos zero_lt_one hrpos
    linarith
  have hrec := descent_recurrence_exp_bound δ d (2 * S ^ (1 / 4 : ℝ)) (c * m)
    (1 - 1 / r) (by positivity) (mul_nonneg hc hm) hα0 hα1 hδd hδ
    (by simpa only [neg_mul] using hstep)
  have hid : 2 * S ^ (1 / 4 : ℝ) / (1 - (1 - 1 / r)) =
      2 * r * S ^ (1 / 4 : ℝ) := by
    field_simp
    ring
  rw [hid] at hrec
  apply hrec.trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg d)
  apply Real.exp_le_exp.mpr
  have hpow := descent_power_lower r K S d hr hKr hS hd
  nlinarith [mul_le_mul_of_nonneg_left hpow (mul_nonneg hc hm)]

end Problem337

end OAI
