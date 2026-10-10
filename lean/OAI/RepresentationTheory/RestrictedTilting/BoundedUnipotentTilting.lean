import OAI.RepresentationTheory.RestrictedTilting.TensorAssociatedIso
import OAI.RepresentationTheory.RestrictedTilting.TensorFormalComparison

namespace OAI

namespace FiberFunctorProof
open CategoryTheory CategoryTheory.MonoidalCategory Matrix
open scoped TensorProduct Kronecker
universe u
variable (k : Type u) [Field k] [Infinite k]
attribute [local instance 1100] HahnSeries.instAlgebra
variable (p : ℕ) [Fact p.Prime] [CharP k p]
variable (β ι : Type u) [Fintype β] [DecidableEq β] [Fintype ι] [DecidableEq ι]
variable (ρ : Representation k (Multiplicative k) (ι → k))
variable (P : Matrix ι ι (Polynomial k))
variable (hP : ∀ t : k, polynomialMatrixEval P t = LinearMap.toMatrix' (ρ (Multiplicative.ofAdd t)))
variable (d : ℕ) (hd : ∀ i j, (P i j).natDegree ≤ d)

include P hP hd in
 

theorem bounded_unipotent_tilting_coordinates (m : ℕ) (hm : d < p^(m+1))
    (e : steinberg k p m ≃ₗ[k] (β → k)) :
    ∃ T : FDRep k (SL2 k), IsTilting k T ∧
      ∃ E : T ≃ₗ[k] (β × ι → k), ∀ t : k, ∀ v : T,
        E (T.ρ (unipotent k t) v) =
          (LinearMap.toMatrix' (coordinateRepresentation k (steinberg k p m).ρ e (unipotent k t)) ⊗ₖ
            LinearMap.toMatrix' (ρ (Multiplicative.ofAdd t))) *ᵥ E v := by
  let N := associatedSectionsSubmodule k ι ρ
  let τ := coordinateRepresentation k (steinberg k p m).ρ e
  let σ := matrixTensorRepresentation τ (associatedSectionsRepresentation k ι ρ)
  have hσ : PlaneCompatible k σ := matrixTensor_planeCompatible k τ _ (associatedSections_planeCompatible k ι ρ)
  let := associated_planeJet_one_finite k ι ρ P hP d hd
  let := piPlaneOrigin_finite (β := β) (M := N) k
  let T := planeJetFD k σ hσ 1
  have hT : IsTilting k T := tensorAssociatedOrigin_tilting k ι ρ P hP d hd p m hm e
  have hτ : IsRational k τ := coordinateRepresentation_rational k _ e (steinberg_tilting k p m).1
  have hr : IsRational k σ := matrixTensor_rational k τ _ hτ (associatedSections_rational k ι ρ)
  have hx := pi_regular_x k (β := β) (And.left (associatedSections_regular k ι ρ P hP))
  have hy := pi_regular_y k (β := β) (And.right (associatedSections_regular k ι ρ P hP))
  obtain ⟨s,hs0,hs⟩ := compatible_planeJet_sections k σ hσ hr hx hy hT
  let F := tensorAssociatedFieldTrivialization k β ι ρ P hP d hd τ s hs0 hs
  obtain ⟨E,hE⟩ := tensor_linear_formal_comparison T.ρ hT.1 τ hτ P
    (formalLineParameter k) (formalLineParameter_ne_zero k) F
    (tensorAssociatedFieldTrivialization_unipotent_one k β ι ρ P hP d hd τ s hs0 hs)
  refine ⟨T,hT,E, fun t v => ?_⟩
  simpa only [hP] using hE t v
end FiberFunctorProof

end OAI
