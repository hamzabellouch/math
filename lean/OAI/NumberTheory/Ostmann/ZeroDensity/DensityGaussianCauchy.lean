import OAI.NumberTheory.Ostmann.ZeroDensity.DensityWeightedCauchy

namespace OAI

/-! # Weighted square bounds for the Gaussian contour integral -/

namespace Ostmann

open MeasureTheory

noncomputable def densityHalfGaussian (u : ℝ) : ℝ := Real.exp (-(u ^ 2) / 2)

 theorem densityHalfGaussian_integrable : Integrable densityHalfGaussian := by
  convert integrable_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num) using 1
  funext u
  unfold densityHalfGaussian
  congr 1
  ring

 theorem densityHalfGaussian_pos (u : ℝ) : 0 < densityHalfGaussian u := Real.exp_pos _

 theorem densityHalfGaussian_continuous : Continuous densityHalfGaussian := by
  unfold densityHalfGaussian
  fun_prop

 theorem densityHalfGaussian_integral_pos : 0 < ∫ u, densityHalfGaussian u :=
  integral_exp_pos densityHalfGaussian_integrable

 theorem density_gaussian_integral_cauchy (f : ℝ → ℂ) (p : ℝ → ℝ) (M A : ℝ)
    (hp : Continuous p) (hp0 : ∀ u, 0 ≤ p u) (hpA : ∀ u, p u ≤ A)
    (hb : ∀ u, ‖f u‖ ≤ M * densityHalfGaussian u * p u) :
    ‖∫ u, f u‖ ^ 2 ≤ M ^ 2 * (∫ u, densityHalfGaussian u) *
      ∫ u, densityHalfGaussian u * (p u) ^ 2 := by
  have hg := densityHalfGaussian_integrable
  have hc := densityHalfGaussian_continuous
  have hA : 0 ≤ A := (hp0 0).trans (hpA 0)
  have hgp : Integrable (fun u => densityHalfGaussian u * p u) := by
    apply (hg.const_mul A).mono' (hc.mul hp).aestronglyMeasurable
    filter_upwards with u
    simp only [Pi.mul_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (densityHalfGaussian_pos u).le (hp0 u))]
    nlinarith [densityHalfGaussian_pos u, hpA u]
  have hgpp : Integrable (fun u => densityHalfGaussian u * (p u) ^ 2) := by
    apply (hg.const_mul (A ^ 2)).mono' (hc.mul (hp.pow 2)).aestronglyMeasurable
    filter_upwards with u
    simp only [Pi.mul_apply, Pi.pow_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (densityHalfGaussian_pos u).le (sq_nonneg _))]
    have hh := pow_le_pow_left₀ (hp0 u) (hpA u) 2
    nlinarith [densityHalfGaussian_pos u]
  have hn : ‖∫ u, f u‖ ≤ M * ∫ u, densityHalfGaussian u * p u := by
    rw [← integral_const_mul]
    apply norm_integral_le_of_norm_le (hgp.const_mul M)
    filter_upwards with u
    simpa only [mul_assoc] using hb u
  have hs := density_weighted_cauchy densityHalfGaussian p hg hgp hgpp
    (fun u => (densityHalfGaussian_pos u).le) densityHalfGaussian_integral_pos
  calc
    _ ≤ (M * ∫ u, densityHalfGaussian u * p u) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hn 2
    _ = M ^ 2 * (∫ u, densityHalfGaussian u * p u) ^ 2 := mul_pow _ _ _
    _ ≤ M ^ 2 * ((∫ u, densityHalfGaussian u) * ∫ u, densityHalfGaussian u * (p u) ^ 2) :=
      mul_le_mul_of_nonneg_left hs (sq_nonneg M)
    _ = _ := by ring

end Ostmann

end OAI
