import OAI.Geometry.RCD.Coordinates.FourGeometricInputs
import OAI.Geometry.RCD.Coordinates.FlatSplittingApproximation

namespace OAI

/-! # Coordinates under volume and measured-coordinate estimates -/

namespace RegularPointCoordinates
noncomputable section
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem regular_coordinates_of_three_geometric_inputs {K : ℝ} {n : ℕ}
    (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X) :
    let _ := hX.properSpace hn
    ∀ {p : X}, IsRegular n p →
      EuclideanRescalingVolumeConvergence (hausdorff n X) n p (euclideanUnitVolume n) →
      LocalVolumeRigidityInput hX → LocalMeasuredCoordinateInput hX →
      HasOpenBilipschitzChart n p := by
  let := hX.properSpace hn
  let := hX.hausdorff_regular
  dsimp only
  intro p hp hv hr hm
  exact regular_coordinates_of_five_geometric_inputs hn hX hp hv
    (hX.transformationInput_of_measured hm) (hX.flatSplittingInput_of_measured hm) hr hm

end
end RegularPointCoordinates

end OAI
