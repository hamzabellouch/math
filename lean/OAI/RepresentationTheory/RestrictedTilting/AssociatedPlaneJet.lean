import OAI.RepresentationTheory.RestrictedTilting.FormalSections
import OAI.RepresentationTheory.RestrictedTilting.AssociatedNumerator

namespace OAI

namespace FiberFunctorProof
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct Pointwise
universe u
variable (k : Type u) [Field k]
variable (ι : Type u) [Fintype ι] [DecidableEq ι]
variable (ρ : Representation k (Multiplicative k) (ι → k))
local notation "N" => associatedSectionsSubmodule k ι ρ
local notation "A" => MvPolynomial (Fin 2) k

omit [Fintype ι] [DecidableEq ι] in
lemma associatedSections_planeCompatible : PlaneCompatible k (associatedSectionsRepresentation k ι ρ) := by
  intro g P v
  induction P using MvPolynomial.induction_on generalizing v with
  | C c =>
    rw [linearChange_C, MvPolynomial.C_eq_algebraMap]
    simp only [algebraMap_smul, map_smul]
  | add P Q hP hQ => simp only [add_smul, map_add, hP, hQ]
  | mul_X P i hP =>
    rw [mul_smul, hP, associatedCoordinate_smul, associatedCoordinateMul_action,
      map_mul, mul_smul, linearChange_X]
    congr 1
    simp only [Finset.sum_smul, mul_smul, MvPolynomial.C_eq_algebraMap,
      algebraMap_smul, associatedCoordinate_smul]
    rfl

omit [Fintype ι] [DecidableEq ι] in
lemma associated_planeJet_one :
    planeJetRelation (M := N) k 1 = associatedOriginRelations k ι ρ := by
  change (jetRelation (M := N) (MvPolynomial.X 0 : A) (MvPolynomial.X 1) 1).restrictScalars k = _
  rw [jetRelation_one]
  ext v
  change v ∈ pairRelation (MvPolynomial.X 0 : A) (MvPolynomial.X 1) ↔ _
  rw [mem_pairRelation, associatedOriginRelations, Submodule.mem_sup]
  constructor
  · rintro ⟨a,b,rfl⟩
    exact ⟨_,⟨a,(associatedCoordinate_smul k ι ρ 0 a).symm⟩,
      _,⟨b,(associatedCoordinate_smul k ι ρ 1 b).symm⟩,rfl⟩
  · rintro ⟨_,⟨a,rfl⟩,_,⟨b,rfl⟩,rfl⟩
    exact ⟨a,b, by rw [associatedCoordinate_smul, associatedCoordinate_smul]⟩

variable [Infinite k]
variable (P : Matrix ι ι (Polynomial k))
variable (hP : ∀ t : k, polynomialMatrixEval P t = LinearMap.toMatrix' (ρ (Multiplicative.ofAdd t)))
variable (d : ℕ) (hd : ∀ i j, (P i j).natDegree ≤ d)

include hP hd in
lemma associated_planeJet_one_finite : Module.Finite k (N ⧸ planeJetRelation (M := N) k 1) := by
  rw [associated_planeJet_one]
  exact associatedOrigin_finite k ι ρ P hP d hd
end FiberFunctorProof

end OAI
