import OAI.RepresentationTheory.RestrictedTilting.AssociatedBundle
import OAI.RepresentationTheory.RestrictedTilting.AssociatedFibre
import OAI.RepresentationTheory.RestrictedTilting.BoundedWeightsFactors
import OAI.RepresentationTheory.RestrictedTilting.FiniteSubgroupLift
import OAI.RepresentationTheory.RestrictedTilting.CoordinateTensor

namespace OAI

namespace FiberFunctorProof
universe u

 

theorem bounded_origin : BoundedOriginTheorem.{u} := by
  intro k _ _ p _ _ r hr l hl D
  classical
  let ι := ULift.{u} (Fin (Module.finrank k D))
  let f : D ≃ₗ[k] (ι → k) := ((Module.finBasis k D).reindex Equiv.ulift.symm).equivFun
  obtain ⟨ρ,P,hP,hd,hρ⟩ := finite_subgroup_polynomial_lift k l hl
    (coordinateRepresentation k D.ρ f)
  have hc : Fintype.card (Fin r → ZMod p) = p^r := by
    simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card]
  rw [hc] at hd
  let B := associatedPlaneBundle k ι ρ P hP (p^r-1) hd
  let E := associatedE1Equiv k ι ρ P hP (p^r-1) hd
  refine ⟨B, ⟨E.trans f.symm, ?_⟩, ?_⟩
  · intro g v
    apply f.injective
    change f (f.symm (E ((planeFibreRelations (k := k) _ ![1,0]).mkQ
      (associatedSectionsRepresentation k ι ρ (unipotent k (l g.toAdd)) v)))) =
      f (D.ρ g (f.symm (E ((planeFibreRelations (k := k) _ ![1,0]).mkQ v))))
    rw [f.apply_symm_apply]
    have h := associatedE1Equiv_unipotent k ι ρ P hP (p^r-1) hd (l g.toAdd) v
    change E _ = _ at h
    rw [h, hρ]
    rfl
  · have originData (R₀ : Submodule k (associatedSectionsSubmodule k ι ρ))
        (he : R₀ = associatedOriginRelations k ι ρ) :
        Module.Finite k ((associatedSectionsSubmodule k ι ρ) ⧸ R₀) ∧
        ∃ σ₀ : Representation k (SL2 k) ((associatedSectionsSubmodule k ι ρ) ⧸ R₀),
          (∀ g v, σ₀ g (R₀.mkQ v) =
            R₀.mkQ (associatedSectionsRepresentation k ι ρ g v)) ∧
          IsRational k σ₀ ∧ AllSimpleFactorsHighestBelow σ₀ (p^r) := by
      subst R₀
      refine ⟨associatedOrigin_finite k ι ρ P hP (p^r-1) hd,
        (associatedOriginRep k ι ρ).ρ, (fun _ _ => rfl), associatedOrigin_rational k ι ρ, ?_⟩
      exact allSimpleFactorsHighestBelow_of_weights k _ (associatedOrigin_rational k ι ρ)
        (p^r-1) (p^r) (Nat.sub_lt (Nat.pow_pos (Fact.out : p.Prime).pos) (by decide))
        (associatedOrigin_weights k ι ρ P hP (p^r-1) hd)
    exact originData _ (associatedPlaneBundle_originRelation k ι ρ P hP (p^r-1) hd)
end FiberFunctorProof

end OAI
