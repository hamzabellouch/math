import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Graphs.GraphJetMul

namespace OAI

/-! Measures and the conditional distance-set completion. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer
open Set MeasureTheory
open scoped ENNReal

abbrev Ambient (d : ℕ) := EuclideanSpace ℝ (Fin d)

def distanceSet {d : ℕ} (E : Set (Ambient d)) : Set ℝ :=
  {r | ∃ x ∈ E, ∃ y ∈ E, dist x y = r}

def MainTarget : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (E : Set (Ambient d)),
    IsCompact E → (d : ℝ≥0∞) / 2 < dimH E → 0 < volume (distanceSet E)

end CurrentFalconer
end GraphLiteralSupport
end
end

end OAI
