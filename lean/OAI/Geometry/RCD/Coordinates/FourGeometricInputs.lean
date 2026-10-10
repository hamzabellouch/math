import OAI.Geometry.RCD.Coordinates.FiveGeometricInputs
import OAI.Geometry.RCD.Coordinates.Transformation

namespace OAI

/-! # Coordinates under almost splitting and local volume estimates -/

namespace RegularPointCoordinates
noncomputable section
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem regular_coordinates_of_four_geometric_inputs {K : ℝ} {n : ℕ}
    (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X) :
    let _ := hX.properSpace hn
    ∀ {p : X}, IsRegular n p →
      EuclideanRescalingVolumeConvergence (hausdorff n X) n p (euclideanUnitVolume n) →
      LocalAlmostSplittingInput hX → LocalVolumeRigidityInput hX →
      LocalMeasuredCoordinateInput hX → HasOpenBilipschitzChart n p := by
  let := hX.properSpace hn
  let := hX.hausdorff_regular
  dsimp only
  intro p hp hv hs hr hm
  exact regular_coordinates_of_five_geometric_inputs hn hX hp hv
    (hX.transformationInput_of_measured hm) hs.flatSplittingInput hr hm

end
end RegularPointCoordinates

end OAI
