import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import OAI.NumberTheory.Ostmann.ZeroDensity.DensitySquareGaussian
import OAI.NumberTheory.Ostmann.ZeroDensity.DensityCompletedStrip

namespace OAI

/-! # An integrable envelope for the completed-square contour -/

namespace Ostmann

open Complex Filter MeasureTheory
open scoped Topology

noncomputable def densityGaussianEnvelope (u : ℝ) : ℝ := (1 + u ^ 2) * Real.exp (-(u ^ 2))

 theorem densityGaussianEnvelope_nonneg (u : ℝ) : 0 ≤ densityGaussianEnvelope u := by
  unfold densityGaussianEnvelope
  positivity

 theorem densityGaussianEnvelope_integrable : Integrable densityGaussianEnvelope := by
  have h0 := integrable_exp_neg_mul_sq (b := (1 : ℝ)) (by norm_num)
  have h2 := integrable_rpow_mul_exp_neg_mul_sq (b := (1 : ℝ)) (by norm_num)
    (s := (2 : ℝ)) (by norm_num)
  convert h0.add h2 using 1
  funext u
  simp only [densityGaussianEnvelope, Real.rpow_two, neg_mul, one_mul, add_mul, Pi.add_apply]

 theorem densityGaussianEnvelope_tendsto :
    Tendsto densityGaussianEnvelope atTop (𝓝 0) := by
  have hp : Tendsto (fun t : ℝ => t ^ 2) atTop atTop :=
    tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)
  have h0 := Real.tendsto_exp_neg_atTop_nhds_zero.comp hp
  have h1 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hp
  convert h0.add h1 using 1
  · funext u
    simp only [densityGaussianEnvelope, Function.comp_apply, pow_one, add_mul, one_mul]
  · norm_num

 theorem densitySquareGaussian_band_bound (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hs : s.re = 1 / 2) : ∃ K : ℝ, 0 < K ∧ ∀ x u : ℝ, |x| ≤ 1 →
      ‖densitySquareGaussian χ s ((x : ℂ) + u * I)‖ ≤ K * densityGaussianEnvelope u := by
  obtain ⟨C, hC, hb⟩ := density_completed_square_strip_bound
  let a := |s.im| + 2
  let K := C * ((χ.modulus : ℝ) + 1) ^ 6 * 2 * a ^ 2 * Real.exp 1
  have ha : 2 ≤ a := by dsimp [a]; linarith [abs_nonneg s.im]
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro x u hx
  have hz : -(1 / 2 : ℝ) ≤ (s + ((x : ℂ) + u * I)).re ∧
      (s + ((x : ℂ) + u * I)).re ≤ 3 / 2 := by
    simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, mul_zero,
      zero_mul, sub_self, add_zero, hs]
    exact ⟨by linarith [(abs_le.mp hx).1], by linarith [(abs_le.mp hx).2]⟩
  have hi : |(s + ((x : ℂ) + u * I)).im| + 2 ≤ a + |u| := by
    simp only [add_im, ofReal_im, mul_im, I_re, I_im, ofReal_re, mul_one,
      zero_mul, add_zero, zero_add]
    dsimp [a]
    linarith [abs_add_le s.im u]
  have hpoly : (|(s + ((x : ℂ) + u * I)).im| + 2) ^ 2 ≤ 2 * a ^ 2 * (1 + u ^ 2) := by
    have h1 := pow_le_pow_left₀ (by positivity : 0 ≤ |(s + ((x : ℂ) + u * I)).im| + 2) hi 2
    have haa : 1 ≤ a ^ 2 := by nlinarith
    have h2 := mul_nonneg (sub_nonneg.mpr haa) (sq_nonneg u)
    nlinarith [sq_nonneg (a - |u|), sq_abs u]
  have hexp : ‖Complex.exp (((x : ℂ) + u * I) ^ 2)‖ ≤ Real.exp 1 * Real.exp (-(u ^ 2)) := by
    rw [Complex.norm_exp, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hxx : x ^ 2 ≤ 1 := by nlinarith [(abs_le.mp hx).1, (abs_le.mp hx).2]
    have hre : (((x : ℂ) + u * I) ^ 2).re = x ^ 2 - u ^ 2 := by
      simp [pow_two, mul_re, mul_im]
    rw [hre]
    linarith
  rw [densitySquareGaussian, norm_mul]
  calc
    _ ≤ (C * ((χ.modulus : ℝ) + 1) ^ 6 * (|(s + ((x : ℂ) + u * I)).im| + 2) ^ 2) *
        (Real.exp 1 * Real.exp (-(u ^ 2))) :=
      mul_le_mul (hb χ _ hz.1 hz.2) hexp (norm_nonneg _) (by positivity)
    _ ≤ (C * ((χ.modulus : ℝ) + 1) ^ 6 * (2 * a ^ 2 * (1 + u ^ 2))) *
        (Real.exp 1 * Real.exp (-(u ^ 2))) := by gcongr
    _ = K * densityGaussianEnvelope u := by dsimp [K, densityGaussianEnvelope]; ring

end Ostmann

end OAI
