import OAI.NumberTheory.Ostmann.Quadratic.QuadraticLogTranslation

namespace OAI

/-! # The second derivative controls the large Fourier frequencies -/

namespace Ostmann

open MeasureTheory LineDeriv
open scoped SchwartzMap FourierTransform

 theorem quadratic_fourier_line_derivative (f : 𝓢(ℝ, ℂ)) (u : ℝ) :
    𝓕 (∂_{(1 : ℝ)} f) u = (2 * Real.pi * Complex.I) * (u : ℂ) * 𝓕 f u := by
  have hh := congrArg (fun g : 𝓢(ℝ, ℂ) => g u)
    (SchwartzMap.fourier_lineDerivOp_eq f (1 : ℝ))
  have hg : (fun x : ℝ => inner ℝ x (1 : ℝ)).HasTemperateGrowth := by
    exact ((innerSL ℝ).flip (1 : ℝ)).hasTemperateGrowth
  change 𝓕 (∂_{(1 : ℝ)} f) u =
    (2 * Real.pi * Complex.I) *
      (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => inner ℝ x (1 : ℝ)) (𝓕 f)) u at hh
  rw [SchwartzMap.smulLeftCLM_apply_apply hg] at hh
  simpa [RCLike.inner_apply, Complex.real_smul, mul_assoc] using hh

 theorem quadratic_fourier_second_derivative (f : 𝓢(ℝ, ℂ)) (u : ℝ) :
    𝓕 (∂_{(1 : ℝ)} (∂_{(1 : ℝ)} f)) u =
      ((2 * Real.pi * Complex.I) * (u : ℂ)) ^ 2 * 𝓕 f u := by
  rw [quadratic_fourier_line_derivative, quadratic_fourier_line_derivative]
  ring

 theorem quadratic_fourier_second_derivative_norm (f : 𝓢(ℝ, ℂ)) (u : ℝ) :
    ‖𝓕 (∂_{(1 : ℝ)} (∂_{(1 : ℝ)} f)) u‖ =
      (2 * Real.pi) ^ 2 * u ^ 2 * ‖𝓕 f u‖ := by
  have hc : ‖(2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
    rw [norm_mul, Complex.norm_I, mul_one]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    norm_num
  rw [quadratic_fourier_second_derivative, norm_mul, norm_pow, norm_mul, hc,
    Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]

end Ostmann

end OAI
