import Mathlib

namespace OAI

namespace Falconer
open MeasureTheory
open scoped ENNReal

/-- A compact subset of Euclidean space with Hausdorff dimension greater than
half the ambient dimension determines a distance set of positive Lebesgue measure. -/
theorem falconer_distance_conjecture :
    ∀ (d : ℕ), 2 ≤ d → ∀ E : Set (EuclideanSpace ℝ (Fin d)), IsCompact E →
      (d : ℝ≥0∞) / 2 < dimH E →
        0 < volume {r : ℝ | ∃ x ∈ E, ∃ y ∈ E, dist x y = r} := by
  sorry

end Falconer

end OAI
