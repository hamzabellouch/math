import OAI.Analysis.CircleDomains.Rigidity.AxialCircleFlux

namespace OAI

/-! Zero extension of each axial circle increment to all transverse
lines. Its integral is exactly the corresponding circle flux. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 def axialBandIncrement (i : Fin 2) (F : ℂ → ℂ) (c : ℂ) (r : ℝ) : ℝ → ℝ :=
    (Icc (transverseCoordinate i c-r) (transverseCoordinate i c+r)).indicator
      (axialCircleIncrement i F c r)

 theorem axialCircleIncrement_measurable {F : ℂ → ℂ} (hF : Measurable F)
    (i : Fin 2) (c : ℂ) (r : ℝ) : Measurable (axialCircleIncrement i F c r) := by
  fin_cases i
  · change Measurable (fun y => axialCircleIncrement 0 F c r y)
    simp_rw [axialCircleIncrement_zero]
    exact (Complex.measurable_re.comp (hF.comp (continuous_horizontalCirclePoint true c r).measurable)).sub
      (Complex.measurable_re.comp (hF.comp (continuous_horizontalCirclePoint false c r).measurable))
  · change Measurable (fun y => axialCircleIncrement 1 F c r y)
    simp_rw [axialCircleIncrement_one]
    exact (Complex.measurable_im.comp (hF.comp (continuous_verticalCirclePoint true c r).measurable)).sub
      (Complex.measurable_im.comp (hF.comp (continuous_verticalCirclePoint false c r).measurable))

 theorem axialBandIncrement_integrable {F : ℂ → ℂ} (hF : Measurable F)
    (i : Fin 2) (c : ℂ) {r B : ℝ} (hr : 0 ≤ r) (hB : 0 ≤ B)
    (hb : ∀ z ∈ closedBall c r, ‖F z‖ ≤ B) : Integrable (axialBandIncrement i F c r) volume := by
  have hi : IntervalIntegrable (axialCircleIncrement i F c r) volume
      (transverseCoordinate i c-r) (transverseCoordinate i c+r) := by
    obtain ⟨hh,hv⟩ := circle_projection_integrable hF c hr hB hb
    fin_cases i
    · change IntervalIntegrable (fun y => axialCircleIncrement 0 F c r y) volume (c.im-r) (c.im+r)
      simpa only [axialCircleIncrement_zero,horizontalCircleIncrement] using hh
    · change IntervalIntegrable (fun y => axialCircleIncrement 1 F c r y) volume (c.re-r) (c.re+r)
      simpa only [axialCircleIncrement_one,verticalCircleIncrement] using hv
  rw [axialBandIncrement,integrable_indicator_iff measurableSet_Icc]
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith) (by finiteness)).mp hi

 theorem integral_axialBandIncrement (i : Fin 2) (F : ℂ → ℂ) (c : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    (∫ y, axialBandIncrement i F c r y) = axialCircleFlux i F c r := by
  rw [axialBandIncrement,integral_indicator measurableSet_Icc,axialCircleFlux,
    intervalIntegral.integral_of_le (by linarith),integral_Icc_eq_integral_Ioc]

end CircleDomainRigidity

end

end OAI
