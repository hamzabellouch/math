import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticLogFourierEnvelope

namespace OAI

/-! # The fixed half-reflection needed for square-root Poisson weights -/

namespace Ostmann

open MeasureTheory
open scoped SchwartzMap FourierTransform

noncomputable def quadraticHalfReflection (f : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 (-1 / 2 : ℝ) (by norm_num))) f

 theorem quadraticHalfReflection_apply (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    quadraticHalfReflection f x = f (-x / 2) := by
  change f (x * (-1 / 2 : ℝ)) = _
  congr 1
  ring

 theorem quadratic_half_reflection_fourier (f : 𝓢(ℝ, ℂ)) (u : ℝ) :
    𝓕 (quadraticHalfReflection f) u = 2 * 𝓕 f (-2 * u) := by
  let G := fun x : ℝ => realAdditivePhase (2 * x * u) * f x
  have ht := Measure.integral_comp_mul_right G (-1 / 2 : ℝ)
  norm_num at ht
  rw [quadratic_fourier_phase_integral, quadratic_fourier_phase_integral]
  calc
    _ = ∫ x : ℝ, G (x * (-1 / 2 : ℝ)) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [quadraticHalfReflection_apply]
      dsimp only [G]
      congr 2 <;> ring
    _ = (2 : ℝ) • ∫ x : ℝ, G x := by simpa only [neg_div, mul_neg, Complex.real_smul, Complex.ofReal_ofNat] using ht
    _ = _ := by
      rw [Complex.real_smul]
      push_cast
      congr 1
      apply integral_congr_ae
      filter_upwards with x
      dsimp only [G]
      congr 2
      ring

 theorem quadratic_half_reflection_fourier_norm (f : 𝓢(ℝ, ℂ)) (u : ℝ) :
    ‖𝓕 (quadraticHalfReflection f) u‖ = 2 * ‖𝓕 f (-2 * u)‖ := by
  rw [quadratic_half_reflection_fourier, norm_mul]
  norm_num

 theorem quadraticFourierEnvelope_half_reflection (u : ℝ) :
    quadraticFourierEnvelope (-2 * u) ≤ quadraticFourierEnvelope u := by
  apply Real.rpow_le_rpow_of_nonpos (by positivity)
  · rw [norm_mul]
    norm_num [Real.norm_eq_abs]
    linarith [abs_nonneg u]
  · norm_num

end Ostmann

end OAI
