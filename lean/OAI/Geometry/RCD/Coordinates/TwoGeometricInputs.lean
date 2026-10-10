import OAI.Geometry.RCD.Coordinates.ThreeGeometricInputs
import OAI.Geometry.RCD.Coordinates.MeasuredCoordinates

namespace OAI

/-! # Coordinates under volume convergence and local volume rigidity -/

namespace RegularPointCoordinates
noncomputable section
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem regular_coordinates_of_two_geometric_inputs {K : ℝ} {n : ℕ}
    (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X) :
    let _ := hX.properSpace hn
    ∀ {p : X}, IsRegular n p →
      EuclideanRescalingVolumeConvergence (hausdorff n X) n p (euclideanUnitVolume n) →
      LocalVolumeRigidityInput hX → HasOpenBilipschitzChart n p := by
  let := hX.properSpace hn
  dsimp only
  intro p hp hv hr
  exact regular_coordinates_of_three_geometric_inputs hn hX hp hv hr hX.measuredCoordinateInput

end
end RegularPointCoordinates

end OAI
