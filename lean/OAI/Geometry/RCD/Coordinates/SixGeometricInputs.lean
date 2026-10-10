import OAI.Geometry.RCD.Coordinates.SevenGeometricInputs
import OAI.Geometry.RCD.Sobolev.PoissonHarmonicCompactnessConstruction

namespace OAI

/-! # Coordinates under splitting and local volume estimates -/

namespace RegularPointCoordinates
noncomputable section
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem regular_coordinates_of_six_geometric_inputs {K : ℝ} {n : ℕ}
    (hn : 2≤n) (hX : NoncollapsedRCD K n X) :
    let _ := hX.properSpace hn
    ∀ {p : X}, IsRegular n p →
      EuclideanRescalingVolumeConvergence (hausdorff n X) n p (euclideanUnitVolume n) →
      LocalInitialSplittingInput hX → LocalTransformationInput hX →
      LocalFlatSplittingInput hX → LocalVolumeRigidityInput hX →
      LocalMeasuredCoordinateInput hX → HasOpenBilipschitzChart n p := by
  let := hX.properSpace hn
  let := hX.hausdorff_regular
  dsimp only
  intro p hp hvol hi ht hs hr hm
  exact regular_coordinates_of_seven_geometric_inputs hn hX hp hvol
    hX.poissonHarmonicCompactnessInput hi ht hs hr hm

end
end RegularPointCoordinates

end OAI
