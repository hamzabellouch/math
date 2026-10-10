import OAI.Geometry.RCD.Coordinates.SixGeometricInputs
import OAI.Geometry.RCD.Coordinates.InitialSplittingConstruction

namespace OAI

/-! # Coordinates under harmonic normalization and local volume estimates -/

namespace RegularPointCoordinates
noncomputable section
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem regular_coordinates_of_five_geometric_inputs {K : ℝ} {n : ℕ}
    (hn : 2≤n) (hX : NoncollapsedRCD K n X) :
    let _ := hX.properSpace hn
    ∀ {p : X}, IsRegular n p →
      EuclideanRescalingVolumeConvergence (hausdorff n X) n p (euclideanUnitVolume n) →
      LocalTransformationInput hX → LocalFlatSplittingInput hX →
      LocalVolumeRigidityInput hX → LocalMeasuredCoordinateInput hX → HasOpenBilipschitzChart n p := by
  let := hX.properSpace hn
  let := hX.hausdorff_regular
  dsimp only
  intro p hp hvol ht hs hr hm
  exact regular_coordinates_of_six_geometric_inputs hn hX hp hvol
    hX.initialSplittingInput ht hs hr hm

end
end RegularPointCoordinates

end OAI
