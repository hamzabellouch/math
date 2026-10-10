import OAI.Geometry.RCD.Coordinates.RegularVolumeNonpositive
import OAI.Geometry.RCD.Metric.LowerCurvatureVolume
import OAI.Geometry.RCD.Coordinates.HausdorffMeasureRegularity

namespace OAI

/-! # Absolute volume convergence at every regular point, for every real curvature -/

noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.regular_volume_convergence {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2≤n) {p : X} (hp : IsRegular n p) :
    EuclideanRescalingVolumeConvergence (hausdorff n X) n p (euclideanUnitVolume n) := by
  let := hX.hausdorff_regular
  by_cases hK : K≤0
  · exact hX.regular_volume_convergence_nonpositive hn hK hp
  · exact (hX.zero_of_nonneg_curvature hn (le_of_not_ge hK)).regular_volume_convergence_nonpositive
      hn le_rfl hp

end RegularPointCoordinates

end

end OAI
