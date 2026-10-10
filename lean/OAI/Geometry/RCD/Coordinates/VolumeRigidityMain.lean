import OAI.Geometry.RCD.Coordinates.RegularVolumeConvergence
import OAI.Geometry.RCD.Coordinates.TwoGeometricInputs

namespace OAI

/-! # Regular-point charts under local volume rigidity

Absolute regular-point volume convergence follows from first-order
coordinate maps and their image mass. The local volume rigidity
hypothesis is De Philippis--Gigli (2018), Theorem 1.6.
-/

noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem regular_coordinates_of_volume_rigidity {K : ℝ} {n : ℕ}
    (hn : 2≤n) (hX : NoncollapsedRCD K n X) :
    let _ := hX.properSpace hn
    ∀ {p : X}, IsRegular n p → LocalVolumeRigidityInput hX → HasOpenBilipschitzChart n p := by
  let := hX.properSpace hn
  dsimp only
  intro p hp hrigidity
  exact regular_coordinates_of_two_geometric_inputs hn hX hp
    (hX.regular_volume_convergence hn hp) hrigidity

end RegularPointCoordinates

end

end OAI
