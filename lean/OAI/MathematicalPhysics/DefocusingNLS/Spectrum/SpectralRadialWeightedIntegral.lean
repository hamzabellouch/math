import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPressureMeasure

namespace OAI

/-! Complex-valued integration against the dimension-twelve radial measure. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectral_radial_complex_integral (R : ℝ) (hR : 0 ≤ R) (f : ℝ → ℂ) :
    (∫ r, f r ∂radialPressureMeasure R)=∫ r in (0 : ℝ)..R, (r : ℂ)^11*f r := by
  unfold radialPressureMeasure
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)),
    intervalIntegral.integral_of_le hR]
  calc
    _ = ∫ r in Icc (0 : ℝ) R, (r : ℂ)^11*f r := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro r hr
      change (ENNReal.ofReal ((max r 0)^11)).toReal • f r=(r : ℂ)^11*f r
      rw [ENNReal.toReal_ofReal (by positivity),max_eq_left hr.1]
      simp only [Complex.real_smul,Complex.ofReal_pow]
    _ = _ := integral_Icc_eq_integral_Ioc

end DefocusingNLS

end OAI
