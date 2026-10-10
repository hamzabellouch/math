import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningRescale
import Mathlib.Analysis.Complex.Basic

namespace OAI

/-! The actual complex Liouville coefficient converges to the Airy coefficient
on each fixed rescaled interval, with an explicit uniform error. -/

namespace DefocusingNLS

noncomputable def spectralTurningCoefficient
    (h b eta omega gamma r₀ d xi : ℝ) : ℂ :=
  (d^2 : ℝ)*(homogeneousSpectralLocalizationFrequency h b eta omega (r₀+d*xi)+
    Complex.I*(gamma : ℂ))

theorem spectralTurningCoefficient_bound (h b eta omega gamma r₀ d M xi : ℝ)
    (hr₀ : 0<r₀) (hd : 0≤d) (heta : 0≤eta) (hM : 0≤M)
    (hxi : |xi|≤M) (hsmall : d*M≤r₀/2)
    (hzero : homogeneousSpectralLocalizationFrequency h b eta omega r₀=0)
    (hscale : (r₀/8+2*(eta+99/4)/r₀^3)*d^3=1) :
    ‖spectralTurningCoefficient h b eta omega gamma r₀ d xi-(xi : ℂ)‖≤
      (17/2)*M^2*d/r₀+|gamma| * d^2 := by
  have hdelta : |d*xi|≤r₀/2 := by
    rw [abs_mul,abs_of_nonneg hd]
    exact (mul_le_mul_of_nonneg_left hxi hd).trans hsmall
  have hb := spectralTurning_rescaled_error h b eta omega r₀ d xi hr₀ heta hdelta hzero hscale
  have hc := spectralTurning_rescaled_coefficient eta r₀ d hr₀ hd heta hscale
  have hxi2 : xi^2≤M^2 := by nlinarith [sq_abs xi,abs_nonneg xi]
  have hre : |d^2*homogeneousSpectralLocalizationFrequency h b eta omega (r₀+d*xi)-xi|≤
      (17/2)*M^2*d/r₀ := by
    calc
      _ ≤ d^4*xi^2*(1/16+16*(eta+99/4)/r₀^4) := hb
      _ = (d^4*(1/16+16*(eta+99/4)/r₀^4))*xi^2 := by ring
      _ ≤ ((17/2)*d/r₀)*M^2 := mul_le_mul hc hxi2 (sq_nonneg xi) (by positivity)
      _ = _ := by ring
  have he : spectralTurningCoefficient h b eta omega gamma r₀ d xi-(xi : ℂ)=
      ((d^2*homogeneousSpectralLocalizationFrequency h b eta omega (r₀+d*xi)-xi : ℝ) : ℂ)+
        Complex.I*((gamma*d^2 : ℝ) : ℂ) := by
    dsimp only [spectralTurningCoefficient]
    push_cast
    ring
  rw [he]
  calc
    _ ≤ ‖((d^2*homogeneousSpectralLocalizationFrequency h b eta omega (r₀+d*xi)-xi : ℝ) : ℂ)‖+
        ‖Complex.I*((gamma*d^2 : ℝ) : ℂ)‖ := norm_add_le _ _
    _ = |d^2*homogeneousSpectralLocalizationFrequency h b eta omega (r₀+d*xi)-xi|+|gamma| * d^2 := by
      rw [norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,
        Real.norm_eq_abs,abs_mul,abs_of_nonneg (sq_nonneg d)]
    _ ≤ _ := add_le_add hre le_rfl

end DefocusingNLS

end OAI
