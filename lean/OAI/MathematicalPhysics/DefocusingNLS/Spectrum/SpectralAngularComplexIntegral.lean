import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralAngularMeasure
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRadialWeightedIntegral

namespace OAI

/-! The angular term uses r^9 dr while the radial terms use r^11 dr. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectral_angular_complex_integral (R : ℝ) (hR : 0 ≤ R) (f : ℝ → ℂ) :
    (∫ r, f r ∂spectralAngularMeasure R)=∫ r in (0 : ℝ)..R, (r : ℂ)^9*f r := by
  unfold spectralAngularMeasure
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)),
    intervalIntegral.integral_of_le hR]
  calc
    _ = ∫ r in Icc (0 : ℝ) R, (r : ℂ)^9*f r := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro r hr
      change (ENNReal.ofReal ((max r 0)^9)).toReal • f r=(r : ℂ)^9*f r
      rw [ENNReal.toReal_ofReal (by positivity),max_eq_left hr.1]
      simp only [Complex.real_smul,Complex.ofReal_pow]
    _ = _ := integral_Icc_eq_integral_Ioc

end DefocusingNLS

end OAI
