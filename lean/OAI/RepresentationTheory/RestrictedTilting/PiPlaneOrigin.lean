import OAI.RepresentationTheory.RestrictedTilting.PlaneMatrixTensor

namespace OAI

namespace FiberFunctorProof
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators TensorProduct
universe u
variable (k : Type u) [Field k]
variable {β : Type u} [Fintype β] [DecidableEq β]
variable {M : Type u} [AddCommGroup M] [Module k M]
  [Module (MvPolynomial (Fin 2) k) M] [IsScalarTower k (MvPolynomial (Fin 2) k) M]
local notation "A" => MvPolynomial (Fin 2) k
local notation "pM" => planeJetRelation (M := M) k 1
local notation "pPi" => planeJetRelation (M := β → M) k 1

noncomputable def piPlaneOriginMap : (β → M) →ₗ[k] (β → M ⧸ pM) :=
  LinearMap.pi fun i => (pM).mkQ.comp (LinearMap.proj i)

omit [Fintype β] [DecidableEq β] in
lemma piPlaneOriginMap_apply (v : β → M) (i : β) :
    piPlaneOriginMap k v i = (pM).mkQ (v i) := rfl

omit [Fintype β] [DecidableEq β] in
lemma piPlaneOriginMap_surjective : Function.Surjective (piPlaneOriginMap (β := β) (M := M) k) := by
  intro v
  choose w hw using fun i => (pM).mkQ_surjective (v i)
  exact ⟨w, funext hw⟩

lemma planeOrigin_mem_iff (v : M) : v ∈ pM ↔
    ∃ a b : M, v = (MvPolynomial.X 0 : A) • a + (MvPolynomial.X 1 : A) • b := by
  change v ∈ jetRelation (MvPolynomial.X 0 : A) (MvPolynomial.X 1) 1 ↔ _
  rw [jetRelation_one, mem_pairRelation]

omit [Fintype β] [DecidableEq β] in
lemma piPlaneOriginMap_ker : (piPlaneOriginMap (β := β) (M := M) k).ker = pPi := by
  ext v
  change piPlaneOriginMap k v = 0 ↔ v ∈ pPi
  rw [planeOrigin_mem_iff]
  constructor
  · intro h
    have hi (i : β) : v i ∈ pM := by
      exact (Submodule.Quotient.mk_eq_zero pM).mp (congrFun h i)
    choose a b hab using fun i => (planeOrigin_mem_iff k (v i)).mp (hi i)
    exact ⟨a,b,funext hab⟩
  · rintro ⟨a,b,rfl⟩
    funext i
    exact (Submodule.Quotient.mk_eq_zero pM).mpr
      ((planeOrigin_mem_iff k _).mpr ⟨a i,b i,rfl⟩)

noncomputable def piPlaneOriginEquiv : ((β → M) ⧸ pPi) ≃ₗ[k] (β → M ⧸ pM) := by
  let f : (β → M) →ₗ[k] (β → M ⧸ pM) := piPlaneOriginMap (β := β) (M := M) k
  let e : ((β → M) ⧸ f.ker) ≃ₗ[k] (β → M ⧸ pM) :=
    f.quotKerEquivOfSurjective (piPlaneOriginMap_surjective (β := β) (M := M) k)
  exact (Submodule.quotEquivOfEq pPi f.ker (piPlaneOriginMap_ker (β := β) (M := M) k).symm).trans e

omit [Fintype β] [DecidableEq β] in
lemma piPlaneOriginEquiv_mk (v : β → M) :
    piPlaneOriginEquiv k ((pPi).mkQ v) = fun i => (pM).mkQ (v i) := rfl

omit [DecidableEq β] in
lemma piPlaneOrigin_finite [Module.Finite k (M ⧸ pM)] :
    Module.Finite k ((β → M) ⧸ pPi) :=
  Module.Finite.of_surjective (piPlaneOriginEquiv (β := β) (M := M) k).symm.toLinearMap
    (piPlaneOriginEquiv k).symm.surjective

variable (τ : Representation k (SL2 k) (β → k)) (σ : Representation k (SL2 k) M)
  (hσ : PlaneCompatible k σ)

lemma piPlaneOriginEquiv_intertwines (g : SL2 k) (v : (β → M) ⧸ pPi) :
    piPlaneOriginEquiv k
      (planeJetRep k (matrixTensorRepresentation τ σ) (matrixTensor_planeCompatible k τ σ hσ) 1 g v) =
    matrixTensorRepresentation τ (planeJetRep k σ hσ 1) g (piPlaneOriginEquiv k v) := by
  obtain ⟨v,rfl⟩ := (pPi).mkQ_surjective v
  change piPlaneOriginEquiv k ((pPi).mkQ (matrixTensorRepresentation τ σ g v)) = _
  rw [piPlaneOriginEquiv_mk, piPlaneOriginEquiv_mk]
  funext i
  simp only [matrixTensorRepresentation_apply, map_sum, map_smul]
  rfl
end FiberFunctorProof

end OAI
