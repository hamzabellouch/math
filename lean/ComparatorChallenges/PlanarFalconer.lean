import Mathlib

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def distanceSet (E : Set Plane) : Set ℝ :=
  {r | ∃ x ∈ E, ∃ y ∈ E, dist x y = r}

def MainTarget : Prop :=
  ∀ E : Set Plane, IsCompact E → 1 < dimH E → 0 < volume (distanceSet E)

end PlanarFalconer

namespace PlanarFalconer

theorem mainTarget_proved : MainTarget := by
  sorry

end PlanarFalconer

end OAI
