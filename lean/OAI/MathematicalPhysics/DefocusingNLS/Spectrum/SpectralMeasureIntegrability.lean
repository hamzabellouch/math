import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralAngularComplexIntegral

namespace OAI

/-! Turn integrability in the radial measures into ordinary weighted integrability. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralRadial_integrableOn (R : ℝ) (f : ℝ → ℂ)
    (hf : Integrable f (radialPressureMeasure R)) :
    IntegrableOn (fun r : ℝ => (r : ℂ)^11*f r) (Icc 0 R) := by
  have h := (integrable_withDensity_iff_integrable_smul' (by fun_prop)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mp hf
  apply h.congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
  change (ENNReal.ofReal ((max r 0)^11)).toReal • f r=(r : ℂ)^11*f r
  rw [ENNReal.toReal_ofReal (by positivity),max_eq_left hr.1]
  simp only [Complex.real_smul,Complex.ofReal_pow]

theorem spectralAngular_integrableOn (R : ℝ) (f : ℝ → ℂ)
    (hf : Integrable f (spectralAngularMeasure R)) :
    IntegrableOn (fun r : ℝ => (r : ℂ)^9*f r) (Icc 0 R) := by
  have h := (integrable_withDensity_iff_integrable_smul' (by fun_prop)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mp hf
  apply h.congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
  change (ENNReal.ofReal ((max r 0)^9)).toReal • f r=(r : ℂ)^9*f r
  rw [ENNReal.toReal_ofReal (by positivity),max_eq_left hr.1]
  simp only [Complex.real_smul,Complex.ofReal_pow]

end DefocusingNLS

end OAI
