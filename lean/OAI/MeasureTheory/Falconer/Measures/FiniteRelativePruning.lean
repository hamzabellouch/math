import Mathlib.MeasureTheory.Constructions.Polish.Basic

namespace OAI

/-! # Finite pruning relative to the incoming measurable relation -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal BigOperators
variable {X : Type*} [MeasurableSpace X]

theorem finite_relative_pruning (μ : Measure X) (G : Set X) (hG : MeasurableSet G)
    (J : ℕ) (cost : ℕ → ℝ≥0∞) (P : ℕ → X → Prop)
    (hlocal : ∀ j < J, ∃ H : Set X, MeasurableSet H ∧ H ⊆ G ∧
      μ (G \ H) ≤ cost j ∧ ∀ x ∈ H, P j x) :
    ∃ H : Set X, MeasurableSet H ∧ H ⊆ G ∧
      μ (G \ H) ≤ ∑ j ∈ Finset.range J, cost j ∧ ∀ j < J, ∀ x ∈ H, P j x := by
  classical
  have hex : ∀ j : ℕ, ∃ H : Set X, MeasurableSet H ∧ H ⊆ G ∧
      (j < J → μ (G \ H) ≤ cost j ∧ ∀ x ∈ H, P j x) := by
    intro j
    by_cases hj : j < J
    · obtain ⟨H,hH,hHG,hcost,hP⟩ := hlocal j hj
      exact ⟨H,hH,hHG,fun _ => ⟨hcost,hP⟩⟩
    · exact ⟨G,hG,Subset.rfl,fun h => (hj h).elim⟩
  choose H hH hHG hrest using hex
  let B := ⋃ j ∈ Finset.range J, G \ H j
  have hB : MeasurableSet B := Finset.measurableSet_biUnion _ (fun j _ => hG.diff (hH j))
  refine ⟨G \ B,hG.diff hB,sdiff_subset,?_,?_⟩
  · have hsub : G \ (G \ B) ⊆ B := by
      intro x hx
      by_contra hn
      exact hx.2 ⟨hx.1,hn⟩
    apply (measure_mono hsub).trans
    apply (measure_biUnion_finset_le _ _).trans
    exact Finset.sum_le_sum (fun j hj => (hrest j (Finset.mem_range.mp hj)).1)
  · intro j hj x hx
    apply (hrest j hj).2 x
    by_contra hn
    exact hx.2 (mem_iUnion₂.mpr ⟨j,Finset.mem_range.mpr hj,⟨hx.1,hn⟩⟩)

end Falconer

end OAI
