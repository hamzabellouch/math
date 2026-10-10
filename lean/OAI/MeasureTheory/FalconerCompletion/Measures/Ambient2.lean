import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Graphs.SuffixDescendants
import OAI.MeasureTheory.FalconerCompletion.Measures.Ambient

namespace OAI

/-! Measures and the conditional distance-set completion. -/

section
section
namespace CriticalFourierSupport
namespace CurrentFalconer
open Set MeasureTheory
open scoped ENNReal

abbrev Ambient (d : ℕ) := EuclideanSpace ℝ (Fin d)

def distanceSet {d : ℕ} (E : Set (Ambient d)) : Set ℝ :=
  {r | ∃ x ∈ E, ∃ y ∈ E, dist x y = r}

def MainTarget : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (E : Set (Ambient d)),
    IsCompact E → (d : ℝ≥0∞) / 2 < dimH E → 0 < volume (distanceSet E)

theorem distanceSet_eq_image {d : ℕ} (E : Set (Ambient d)) :
    distanceSet E = (fun p : Ambient d × Ambient d => dist p.1 p.2) '' (E ×ˢ E) := by
  ext r
  constructor
  · rintro ⟨x, hx, y, hy, hxy⟩
    exact ⟨(x, y), ⟨hx, hy⟩, hxy⟩
  · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, hxy⟩
    exact ⟨x, hx, y, hy, hxy⟩

theorem isCompact_distanceSet {d : ℕ} {E : Set (Ambient d)} (hE : IsCompact E) :
    IsCompact (distanceSet E) := by
  rw [distanceSet_eq_image]
  exact (hE.prod hE).image (by fun_prop)

theorem measurableSet_distanceSet {d : ℕ} {E : Set (Ambient d)} (hE : IsCompact E) :
    MeasurableSet (distanceSet E) := (isCompact_distanceSet hE).measurableSet

end CurrentFalconer
end CriticalFourierSupport
end
end

end OAI
