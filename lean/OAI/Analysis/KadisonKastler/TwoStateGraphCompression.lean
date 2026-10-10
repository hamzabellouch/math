import OAI.Analysis.KadisonKastler.GraphCompressionVectors
import OAI.Analysis.KadisonKastler.TwoStateCornerCompression

namespace OAI

/-! # Each diagonal state's graph resolvent is a corner of the two-state resolvent -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (M : VonNeumannAlgebra H) (Ω ξ : H) (i : Fin 2)
  (J : H ≃ₗᵢ⋆[ℂ] H)
  (L : TwoStateMatrixHilbert H H ≃ₗᵢ⋆[ℂ] TwoStateMatrixHilbert H H)
  (c : ℝ)

theorem twoStateGraph_forward (a : Algebra M) :
    graphIsometry (twoStateCornerEmbedding i) J L
      (rescaledGraphVector J (twoStateVectorAt Ω ξ i) c a.val) ∈
        rescaledGraphSubspace (twoStateMatrixAlgebra M) L (twoStateMatrixVector Ω ξ) c := by
  have hs : (twoStateMatrixEquiv M (star (matrixSlot i i a))).val =
      star (twoStateMatrixEquiv M (matrixSlot i i a)).val :=
    congrArg Subtype.val (map_star (twoStateMatrixEquiv M) (matrixSlot i i a))
  have he := graphIsometry_vector (twoStateCornerEmbedding i) J L
    (twoStateVectorAt Ω ξ i) (twoStateMatrixVector Ω ξ) c a.val
    (twoStateMatrixEquiv M (matrixSlot i i a)).val
    (twoStateCornerEmbedding_vector M Ω ξ i a) (by
      have h := twoStateCornerEmbedding_vector M Ω ξ i (star a)
      rw [← matrixSlot_star, hs] at h
      exact h)
  rw [he]
  exact rescaledGraphVector_mem _ _ _ _ _

theorem twoStateGraph_backward (b : Algebra (twoStateMatrixAlgebra M)) :
    (graphIsometry (twoStateCornerEmbedding i) J L).toContinuousLinearMap.adjoint
      (rescaledGraphVector L (twoStateMatrixVector Ω ξ) c b.val) ∈
        rescaledGraphSubspace M J (twoStateVectorAt Ω ξ i) c := by
  obtain ⟨b, rfl⟩ := (twoStateMatrixEquiv M).surjective b
  have hs : (twoStateMatrixEquiv M (star b)).val =
      star (twoStateMatrixEquiv M b).val :=
    congrArg Subtype.val (map_star (twoStateMatrixEquiv M) b)
  have h1 : (twoStateCornerEmbedding i).toContinuousLinearMap.adjoint
      (star (twoStateMatrixEquiv M b).val (twoStateMatrixVector Ω ξ)) =
        star (b i i).val (twoStateVectorAt Ω ξ i) := by
    rw [← hs, twoStateCornerEmbedding_compress_vector]
    rfl
  change (graphIsometry (twoStateCornerEmbedding i) J L).toContinuousLinearMap.adjoint
    (rescaledGraphVector L (twoStateMatrixVector Ω ξ) c (twoStateMatrixEquiv M b).val) ∈
      rescaledGraphSubspace M J (twoStateVectorAt Ω ξ i) c
  rw [graphIsometry_adjoint_vector (twoStateCornerEmbedding i) J L
    (twoStateVectorAt Ω ξ i) (twoStateMatrixVector Ω ξ) c (b i i).val
    (twoStateMatrixEquiv M b).val
    (twoStateCornerEmbedding_compress_vector M Ω ξ i b) h1]
  exact rescaledGraphVector_mem _ _ _ _ _

theorem twoStateCorner_resolvent (x : H) :
    graphResolvent (twoStateMatrixAlgebra M) L (twoStateMatrixVector Ω ξ) c
        (twoStateCornerEmbedding i x) =
      twoStateCornerEmbedding i (graphResolvent M J (twoStateVectorAt Ω ξ i) c x) := by
  apply graphIsometry_resolvent (H := H) (K := TwoStateMatrixHilbert H H)
    (M := M) (N := twoStateMatrixAlgebra M) (twoStateCornerEmbedding i) J L
    (twoStateVectorAt Ω ξ i) (twoStateMatrixVector Ω ξ) c
  · intro a
    exact twoStateGraph_forward M Ω ξ i J L c a
  · intro b
    exact twoStateGraph_backward M Ω ξ i J L c b

end

end KadisonKastler

end OAI
