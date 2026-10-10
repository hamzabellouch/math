import OAI.Geometry.RCD.Sobolev.UniformMetricMeasureTests
import OAI.Geometry.RCD.Coordinates.MeasuredCoordinateInput
import OAI.Geometry.RCD.Metric.LowerCurvatureVolume

namespace OAI

/-! # Measured coordinate estimates from the RCD structure -/

open Set Metric MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.measuredCoordinateInput_nonpos {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hK : K ≤ 0) : LocalMeasuredCoordinateInput hX := by
  intro hn S η hS hη
  obtain ⟨δ,hδ,hmeasure⟩ := hX.uniform_metric_measure_tests hn hK S η hS hη
  refine ⟨min δ (η/3),lt_min hδ (by positivity),?_⟩
  intro p r hr hcurv V hVm hV
  have hδcurv : -δ ≤ K*r^2 := (neg_le_neg (min_le_left _ _)).trans hcurv
  have hδV := hV.mono_error (min_le_left δ (η/3))
  refine ⟨?_,hVm,hmeasure p r hr hδcurv V hVm hδV⟩
  have hsmall := hV.restrict_radius hr hS.le (by linarith : S ≤ 2*S)
    (le_of_lt (lt_min hδ (by positivity)))
  exact hsmall.mono_error (by linarith [min_le_right δ (η/3)])

theorem NoncollapsedRCD.measuredCoordinateInput {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) : LocalMeasuredCoordinateInput hX := by
  intro hn
  by_cases hK : K ≤ 0
  · exact hX.measuredCoordinateInput_nonpos hK hn
  · let hX0 := hX.zero_of_nonneg_curvature hn (le_of_lt (lt_of_not_ge hK))
    intro S η hS hη
    obtain ⟨δ,hδ,hmeasure⟩ := hX0.measuredCoordinateInput_nonpos le_rfl hn S η hS hη
    refine ⟨δ,hδ,?_⟩
    intro p r hr _ V hVm hV
    exact hmeasure p r hr (by simpa only [zero_mul] using (neg_nonpos.mpr hδ.le)) V hVm hV

end RegularPointCoordinates

end

end OAI
