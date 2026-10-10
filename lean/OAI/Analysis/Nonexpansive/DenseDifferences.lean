import OAI.Analysis.Nonexpansive.Basic
import Mathlib.Topology.Constructions.SumProd

namespace OAI

/-!
# Dense pairwise differences in the norm-closed difference span

All closures use the given norm topology. Density in the norm subtype of `K`
is transported through the continuous subtraction map on `K × K`.
No completeness, convexity, closedness or compactness assumption is needed.
-/

open scoped Pointwise

namespace ReflexiveFixedPoints

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {K : Set X}

theorem pairwiseDifferences_subset_sub {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] {K : Set X} (z : ℕ → K) :
    Set.range (fun ij : ℕ × ℕ => (z ij.1 : X) - (z ij.2 : X)) ⊆ K - K := by
  rintro _ ⟨ij, rfl⟩
  exact Set.sub_mem_sub (z ij.1).property (z ij.2).property

/-- Every actual difference is approximated by differences of the dense sequence. -/
theorem pairwiseDifferences_subset_closure {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] {K : Set X} (z : ℕ → K) (hz : DenseRange z) :
    K - K ⊆ closure (Set.range (fun ij : ℕ × ℕ => (z ij.1 : X) - (z ij.2 : X))) := by
  let q : K × K → X := fun p => (p.1 : X) - (p.2 : X)
  have hq : Continuous q :=
    (continuous_subtype_val.comp continuous_fst).sub
      (continuous_subtype_val.comp continuous_snd)
  have hmaps : Set.MapsTo q (Set.range (Prod.map z z))
      (Set.range (fun ij : ℕ × ℕ => (z ij.1 : X) - (z ij.2 : X))) := by
    rintro _ ⟨ij, rfl⟩
    exact ⟨ij, rfl⟩
  intro d hd
  obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_sub.mp hd
  exact hmaps.closure hq ((hz.prodMap hz) (⟨x, hx⟩, ⟨y, hy⟩))

/-- The sampled pairwise differences generate the entire norm-closed difference span. -/
theorem closure_span_pairwiseDifferences (z : ℕ → K) (hz : DenseRange z) :
    (Submodule.span ℝ
      (Set.range (fun ij : ℕ × ℕ => (z ij.1 : X) - (z ij.2 : X)))).topologicalClosure =
      (Submodule.span ℝ (K - K)).topologicalClosure := by
  apply le_antisymm
  · exact Submodule.topologicalClosure_mono
      (Submodule.span_mono (pairwiseDifferences_subset_sub z))
  · apply (Submodule.span ℝ (K - K)).topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      exact (pairwiseDifferences_subset_closure z hz).trans
        (Submodule.closure_subset_topologicalClosure_span _)
    · exact Submodule.isClosed_topologicalClosure _

/-- The same equality with the shared reduction carrier. -/
theorem closure_span_pairwiseDifferences_eq_differenceSpan
    (z : ℕ → K) (hz : DenseRange z) :
    (Submodule.span ℝ
      (Set.range (fun ij : ℕ × ℕ => (z ij.1 : X) - (z ij.2 : X)))).topologicalClosure =
      differenceSpan K :=
  closure_span_pairwiseDifferences z hz

end ReflexiveFixedPoints

end OAI
