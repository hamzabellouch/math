import OAI.Geometry.RCD.Metric.MeasurablePointedApproximation

namespace OAI

/-! # Measured rescaling convergence from fixed-ball estimates

The quantitative measured-coordinate input already controls every
measurable pointed approximation. Measurable net replacement and the
vanishing rescaled curvature therefore give its sequential formulation.
-/

open Set Metric MeasureTheory Filter
open scoped Topology

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The fixed-ball measured-coordinate theorem supplies the separately
stated measured rescaling convergence, with no additional measure input. -/
theorem LocalMeasuredCoordinateInput.euclideanMeasuredRescalingConvergence
    {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X}
    (hinput : LocalMeasuredCoordinateInput hX) (hn : 2 ≤ n) (p : X) :
    EuclideanMeasuredRescalingConvergence (hausdorff n X) n p := by
  intro r hr hrzero hconv R ε hR hε
  obtain ⟨δ, hδ, happly⟩ := hinput hn R ε hR hε
  have hcurvzero : Tendsto (fun i => K*(r i)^2) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_pow (by norm_num : (2:ℕ) ≠ 0)] using
      hrzero.pow 2 |>.const_mul K
  filter_upwards [hconv (2*R) (by positivity) (δ/5) (by positivity),
    hcurvzero.eventually (lt_mem_nhds (neg_lt_zero.mpr hδ))] with i hi hcurv
  obtain ⟨f, hf⟩ := hi
  obtain ⟨g, hgm, hg⟩ := hf.exists_measurable (hr i) (by positivity) (by positivity)
  have hg' : IsPointedApproximation p 0 (r i) (2*R) δ g := by
    convert hg using 1; ring
  exact ⟨g, happly p (r i) (hr i) hcurv.le g hgm hg'⟩

end RegularPointCoordinates

end

end OAI
