import OAI.Analysis.KadisonSimilarity.Tracial.TracialExpectations
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace OAI

/-! Extending the two-dimensional expectation range from word vectors to
their tracial Hilbert closure. Orthogonal projection supplies continuity. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (A : StarSubalgebra ℂ P)

/-- The expectation of a Hilbert limit of word vectors still lies in the
span of the unit and the specified base element. -/
theorem expectation_span_of_word_closure (E : TracialExpectation G.trace A)
    (hfaithful : Function.Injective G.vector) (s : P) (words : Set P)
    (hword : ∀ x ∈ words, ∃ α β : ℂ, E.map x = α • (1 : P) + β • s)
    (x : P) (hx : G.vector x ∈
      (Submodule.span ℂ (G.vector '' words)).topologicalClosure) :
    ∃ α β : ℂ, E.map x = α • (1 : P) + β • s := by
  let F : H →L[ℂ] H := (G.baseInclusion A).toContinuousLinearMap.comp
    (G.baseInclusion A).toContinuousLinearMap.adjoint
  have hF (y : P) : F (G.vector y) = G.vector (E.map y) := by
    change (G.baseInclusion A)
      ((G.baseInclusion A).toContinuousLinearMap.adjoint (G.vector y)) = _
    rw [G.expectation_base_projection A E]
    rfl
  let B : Submodule ℂ H := Submodule.span ℂ {G.vector 1, G.vector s}
  have : FiniteDimensional ℂ B := FiniteDimensional.span_of_finite ℂ (Set.toFinite _)
  have hclosed : IsClosed (B : Set H) := B.closed_of_finiteDimensional
  have hspan : Submodule.span ℂ (G.vector '' words) ≤ B.comap F.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨y, hy, rfl⟩
    change F (G.vector y) ∈ B
    rw [hF]
    obtain ⟨α, β, h⟩ := hword y hy
    rw [h, map_add, map_smul, map_smul]
    exact B.add_mem (B.smul_mem α (Submodule.subset_span (by simp)))
      (B.smul_mem β (Submodule.subset_span (by simp)))
  have hmem := (Submodule.span ℂ (G.vector '' words)).topologicalClosure_minimal
    hspan (hclosed.preimage F.continuous) hx
  change F (G.vector x) ∈ B at hmem
  rw [hF] at hmem
  obtain ⟨α, β, h⟩ := Submodule.mem_span_pair.mp hmem
  refine ⟨α, β, ?_⟩
  apply hfaithful
  simpa only [map_add, map_smul] using h.symm

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
