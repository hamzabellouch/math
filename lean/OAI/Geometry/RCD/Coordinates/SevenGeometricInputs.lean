import OAI.Geometry.RCD.Coordinates.GeometricInputCoordinates
import OAI.Geometry.RCD.Harmonic.HarmonicMomentConstruction

namespace OAI

/-! # Coordinates under harmonic compactness and local geometric estimates -/

namespace RegularPointCoordinates
noncomputable section
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem regular_coordinates_of_seven_geometric_inputs {K : ℝ} {n : ℕ}
    (hn : 2≤n) (hX : NoncollapsedRCD K n X) :
    let _ := hX.properSpace hn
    ∀ {p : X}, IsRegular n p →
      EuclideanRescalingVolumeConvergence (hausdorff n X) n p (euclideanUnitVolume n) →
      LocalPoissonHarmonicCompactnessInput hX →
      LocalInitialSplittingInput hX → LocalTransformationInput hX →
      LocalFlatSplittingInput hX → LocalVolumeRigidityInput hX →
      LocalMeasuredCoordinateInput hX → HasOpenBilipschitzChart n p := by
  let := hX.properSpace hn
  let := hX.hausdorff_regular
  dsimp only
  intro p hp hvol hc hi ht hs hr hm
  exact regular_coordinates_of_geometric_inputs hn hX hp hvol hc hi ht hs hr
    (hX.harmonicMomentCompactnessInput hn) hm

end
end RegularPointCoordinates

end OAI
