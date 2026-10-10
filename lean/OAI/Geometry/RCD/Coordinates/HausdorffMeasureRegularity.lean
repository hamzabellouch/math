import OAI.Geometry.RCD.Coordinates.Proper

namespace OAI

/-! # Regularity of the actual locally finite Hausdorff measure -/

noncomputable section
namespace RegularPointCoordinates
open MeasureTheory
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.hausdorff_regular {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [ProperSpace X] : (hausdorff n X).Regular := by
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
  infer_instance

end RegularPointCoordinates

end

end OAI
