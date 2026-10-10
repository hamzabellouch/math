import OAI.RepresentationTheory.RestrictedTilting.AssociatedProjective
import OAI.RepresentationTheory.RestrictedTilting.AssociatedPlaneJet
import OAI.RepresentationTheory.RestrictedTilting.PlaneFibre

namespace OAI

namespace FiberFunctorProof
open scoped Pointwise
universe u
noncomputable section
variable (k : Type u) [Field k] [Infinite k]
variable (ι : Type u) [Fintype ι] [DecidableEq ι]
variable (ρ : Representation k (Multiplicative k) (ι → k))
variable (P : Matrix ι ι (Polynomial k))
variable (hP : ∀ t : k, polynomialMatrixEval P t = LinearMap.toMatrix' (ρ (Multiplicative.ofAdd t)))
variable (d : ℕ) (hd : ∀ i j, (P i j).natDegree ≤ d)
local notation "N" => associatedSectionsSubmodule k ι ρ
local notation "A" => MvPolynomial (Fin 2) k

 

def associatedPlaneBundle : EquivariantPlaneBundle k where
  Sections := N
  finite := associatedSections_finite k ι ρ P hP d hd
  projective := associatedSections_projective k ι ρ P hP d hd
  action := associatedSectionsRepresentation k ι ρ
  rational := associatedSections_rational k ι ρ
  compatible := associatedSections_planeCompatible k ι ρ

omit [Infinite k] in
lemma planeFibreRelations_origin (M : Type u) [AddCommGroup M] [Module k M] [Module A M]
    [IsScalarTower k A M] :
    planeFibreRelations M (0 : Fin 2 → k) = planeJetRelation (M := M) k 1 := by
  change (planePointIdeal 0 • (⊤ : Submodule A M)).restrictScalars k =
    (jetRelation (MvPolynomial.X 0 : A) (MvPolynomial.X 1) 1).restrictScalars k
  have he : planePointIdeal (0 : Fin 2 → k) = planeOriginIdeal k := by
    rw [planePointIdeal, MvPolynomial.eval_zero]; rfl
  rw [he, planeOriginIdeal_eq_span, Ideal.span_insert, Submodule.sup_smul,
    Submodule.ideal_span_singleton_smul, Submodule.ideal_span_singleton_smul,
    jetRelation_one]
  rfl

lemma associatedPlaneBundle_originRelation :
    (associatedPlaneBundle k ι ρ P hP d hd).fibreRelation 0 = associatedOriginRelations k ι ρ := by
  change planeFibreRelations N (0 : Fin 2 → k) = _
  rw [planeFibreRelations_origin, associated_planeJet_one]
end
end FiberFunctorProof

end OAI
