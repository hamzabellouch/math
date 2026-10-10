import OAI.Analysis.KadisonKastler.PolarIsometryTransport
import OAI.Analysis.KadisonKastler.TwoStateModularIdentification
import OAI.Analysis.KadisonKastler.PositiveConeSelfDual
import OAI.Analysis.KadisonKastler.CanonicalPositiveCone
import OAI.Analysis.KadisonKastler.StandardTypeIIIVector

namespace OAI

/-! # Positive vectors in the diagonal corners of the two-state representation -/

namespace KadisonKastler
open Generator
noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  (M : VonNeumannAlgebra H) (Ω ξ : H)
  (hΩc : DenseRange (algebraVectorMap M Ω)) (hξc : DenseRange (algebraVectorMap M ξ))
  (hΩs : Function.Injective (algebraVectorMap M Ω))
  (hξs : Function.Injective (algebraVectorMap M ξ))
  (J : H ≃ₗᵢ⋆[ℂ] H)
  (L : TwoStateMatrixHilbert H H ≃ₗᵢ⋆[ℂ] TwoStateMatrixHilbert H H)

local instance twoStatePositiveReal : InnerProductSpace ℝ H := InnerProductSpace.complexToReal
local instance twoStateBigPositiveReal : InnerProductSpace ℝ (TwoStateMatrixHilbert H H) :=
  InnerProductSpace.complexToReal

omit [TopologicalSpace.SeparableSpace H] in
theorem twoStateCorner_polar_conjugation (i : Fin 2) (x : H) :
    tomitaPolarConjugation L (twoStateMatrixVector Ω ξ)
      (twoStateMatrixAlgebra_separating M Ω ξ hΩs hξs)
      (twoStateMatrixAlgebra_cyclic M Ω ξ hΩc hξc) (twoStateCornerEmbedding i x) =
    twoStateCornerEmbedding i (tomitaPolarConjugation J (twoStateVectorAt Ω ξ i)
      (twoStateVectorAt_separating M Ω ξ hΩs hξs i)
      (twoStateVectorAt_cyclic M Ω ξ hΩc hξc i) x) :=
  tomitaPolarConjugation_isometry (M := M) (N := twoStateMatrixAlgebra M)
    (twoStateCornerEmbedding (H := H) i) J L
    (twoStateVectorAt Ω ξ i) (twoStateMatrixVector Ω ξ)
    (twoStateVectorAt_separating M Ω ξ hΩs hξs i)
    (twoStateVectorAt_cyclic M Ω ξ hΩc hξc i)
    (twoStateMatrixAlgebra_separating M Ω ξ hΩs hξs)
    (twoStateMatrixAlgebra_cyclic M Ω ξ hΩc hξc)
    (twoStateGraph_forward M Ω ξ i J L 1) (twoStateGraph_backward M Ω ξ i J L 1) x

omit [TopologicalSpace.SeparableSpace H] in
include hΩc hξc in
theorem twoStateCorner_slot (i : Fin 2) (a : Algebra M) (x : H) :
    (twoStateMatrixEquiv M (matrixSlot i i a)).val (twoStateCornerEmbedding i x) =
      twoStateCornerEmbedding i (a.val x) := by
  apply (twoStateVectorAt_cyclic M Ω ξ hΩc hξc i).induction_on
    (p := fun x => (twoStateMatrixEquiv M (matrixSlot i i a)).val
      (twoStateCornerEmbedding i x) = twoStateCornerEmbedding i (a.val x)) x
  · exact isClosed_eq (ContinuousLinearMap.continuous _ |>.comp
      (twoStateCornerEmbedding i).continuous)
      ((twoStateCornerEmbedding i).continuous.comp a.val.continuous)
  · intro b
    change (twoStateMatrixEquiv M (matrixSlot i i a)).val
      (twoStateCornerEmbedding i (b.val (twoStateVectorAt Ω ξ i))) = _
    rw [twoStateCornerEmbedding_vector]
    have he : (twoStateMatrixEquiv M (matrixSlot i i a)).val *
        (twoStateMatrixEquiv M (matrixSlot i i b)).val =
        (twoStateMatrixEquiv M (matrixSlot i i (a*b))).val := by
      exact (congrArg Subtype.val ((twoStateMatrixEquiv M).toStarAlgHom.map_mul'
        (matrixSlot i i a) (matrixSlot i i b))).symm.trans
        (congrArg (fun z => (twoStateMatrixEquiv M z).val) (matrixSlot_mul i i i a b))
    change ((twoStateMatrixEquiv M (matrixSlot i i a)).val *
      (twoStateMatrixEquiv M (matrixSlot i i b)).val) (twoStateMatrixVector Ω ξ) = _
    rw [he, ← twoStateCornerEmbedding_vector]
    rfl

omit [TopologicalSpace.SeparableSpace H] in
theorem twoStateCorner_quadratic (i : Fin 2) (a : Algebra M) :
    twoStateCornerEmbedding i
      (modularQuadratic (tomitaPolarConjugation J (twoStateVectorAt Ω ξ i)
        (twoStateVectorAt_separating M Ω ξ hΩs hξs i)
        (twoStateVectorAt_cyclic M Ω ξ hΩc hξc i)) a (twoStateVectorAt Ω ξ i)) =
    modularQuadratic (tomitaPolarConjugation L (twoStateMatrixVector Ω ξ)
      (twoStateMatrixAlgebra_separating M Ω ξ hΩs hξs)
      (twoStateMatrixAlgebra_cyclic M Ω ξ hΩc hξc))
      (twoStateMatrixEquiv M (matrixSlot i i a)) (twoStateMatrixVector Ω ξ) := by
  simp only [modularQuadratic, mul_apply_eq_comp, conjugationOperator_apply,
    tomitaPolarConjugation_fixes_vector]
  rw [← twoStateCornerEmbedding_vector M Ω ξ i a,
    twoStateCorner_polar_conjugation M Ω ξ hΩc hξc hΩs hξs J L,
    twoStateCorner_slot M Ω ξ hΩc hξc]


omit [TopologicalSpace.SeparableSpace H] in
theorem twoStateCorner_positive (i : Fin 2) {x : H}
    (hx : x ∈ canonicalModularPositiveCone J (twoStateVectorAt Ω ξ i)
      (twoStateVectorAt_separating M Ω ξ hΩs hξs i)
      (twoStateVectorAt_cyclic M Ω ξ hΩc hξc i)) :
    twoStateCornerEmbedding i x ∈ canonicalModularPositiveCone L (twoStateMatrixVector Ω ξ)
      (twoStateMatrixAlgebra_separating M Ω ξ hΩs hξs)
      (twoStateMatrixAlgebra_cyclic M Ω ξ hΩc hξc) := by
  let C := canonicalModularPositiveCone L (twoStateMatrixVector Ω ξ)
    (twoStateMatrixAlgebra_separating M Ω ξ hΩs hξs)
    (twoStateMatrixAlgebra_cyclic M Ω ξ hΩc hξc)
  let D := ConvexCone.hull ℝ (Set.range (fun a : Algebra M =>
    modularQuadratic (tomitaPolarConjugation J (twoStateVectorAt Ω ξ i)
      (twoStateVectorAt_separating M Ω ξ hΩs hξs i)
      (twoStateVectorAt_cyclic M Ω ξ hΩc hξc i)) a (twoStateVectorAt Ω ξ i)))
  have hD : D ≤ C.comap
      ((twoStateCornerEmbedding i).toContinuousLinearMap.restrictScalars ℝ).toLinearMap := by
    apply ConvexCone.hull_min
    rintro _ ⟨a,rfl⟩
    change twoStateCornerEmbedding i (_ : H) ∈ C
    rw [twoStateCorner_quadratic M Ω ξ hΩc hξc hΩs hξs J L]
    exact modularQuadratic_mem_positiveCone _ _ _
  have hC : IsClosed (C : Set (TwoStateMatrixHilbert H H)) :=
    modularPositiveCone_isClosed (M := twoStateMatrixAlgebra M) _ _
  exact closure_minimal (fun _ hz => hD hz)
    (hC.preimage (twoStateCornerEmbedding (H := H) i).continuous) hx

theorem twoStateCorner_positive_iff (i : Fin 2) (x : H) :
    twoStateCornerEmbedding i x ∈ canonicalModularPositiveCone L (twoStateMatrixVector Ω ξ)
      (twoStateMatrixAlgebra_separating M Ω ξ hΩs hξs)
      (twoStateMatrixAlgebra_cyclic M Ω ξ hΩc hξc) ↔
    x ∈ canonicalModularPositiveCone J (twoStateVectorAt Ω ξ i)
      (twoStateVectorAt_separating M Ω ξ hΩs hξs i)
      (twoStateVectorAt_cyclic M Ω ξ hΩc hξc i) := by
  constructor
  · intro hx
    let η := twoStateVectorAt Ω ξ i
    let hs := twoStateVectorAt_separating M Ω ξ hΩs hξs i
    let hc := twoStateVectorAt_cyclic M Ω ξ hΩc hξc i
    let d := constructedModularConjugationData J η hs hc
      (tomitaPolarConjugation_commutant_eq J η hs hc)
    apply modularPositiveCone_mem_of_dual d.conjugation d.involutive (d.right_mem le_rfl)
      d.left_mem η d.fixes_vector hc
    · apply (twoStateCornerEmbedding i).injective
      have hf := modularPositiveCone_fixed _
        (tomitaPolarConjugation_right_mem L (twoStateMatrixVector Ω ξ)
          (twoStateMatrixAlgebra_separating M Ω ξ hΩs hξs)
          (twoStateMatrixAlgebra_cyclic M Ω ξ hΩc hξc))
        (twoStateMatrixVector Ω ξ)
        (tomitaPolarConjugation_fixes_vector L (twoStateMatrixVector Ω ξ)
          (twoStateMatrixAlgebra_separating M Ω ξ hΩs hξs)
          (twoStateMatrixAlgebra_cyclic M Ω ξ hΩc hξc)) hx
      rw [twoStateCorner_polar_conjugation M Ω ξ hΩc hξc hΩs hξs J L] at hf
      exact hf
    · intro w hw
      have hp := canonicalModularPositiveCone_acute L (twoStateMatrixVector Ω ξ)
        (twoStateMatrixAlgebra_separating M Ω ξ hΩs hξs)
        (twoStateMatrixAlgebra_cyclic M Ω ξ hΩc hξc) hx
        (twoStateCorner_positive M Ω ξ hΩc hξc hΩs hξs J L i hw)
      have hi := congrArg Complex.re ((twoStateCornerEmbedding i).inner_map_map x w)
      change inner ℝ (twoStateCornerEmbedding i x) (twoStateCornerEmbedding i w) =
        inner ℝ x w at hi
      exact hi ▸ hp
  · exact twoStateCorner_positive M Ω ξ hΩc hξc hΩs hξs J L i

end
end KadisonKastler

end OAI
