import OAI.Geometry.RCD.Heat.NonpositiveBakryLedoux
import OAI.Geometry.RCD.Heat.BakryLedouxScalarBochner

namespace OAI

/-! # Scalar dimensional Bochner for nonpositive curvature

The estimate is derived from FullCD through the actual heat evolution,
with no Bakry--Ledoux or second-order input remaining.
-/

open MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.scalarBochner_nonpositive
    (K : ℝ) (n : ℕ) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    (hX : NoncollapsedRCD K n X) (hK : K ≤ 0) (p : X) :
    ScalarDimensionalBochner (hausdorff n X) hX.quadratic K n := by
  have hn0 : (0:ℝ)<n := by exact_mod_cast (lt_of_lt_of_le (by decide : 0<2) hn)
  exact (hX.bakryLedoux_nonpositive K n hn hK (N := n) le_rfl p).scalarBochner hX hn hn0 p

end RegularPointCoordinates

end

end OAI
