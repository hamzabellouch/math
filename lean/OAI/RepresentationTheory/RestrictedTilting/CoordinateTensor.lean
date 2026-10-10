import OAI.RepresentationTheory.RestrictedTilting.PlaneMatrixTensor

namespace OAI
namespace FiberFunctorProof
open CategoryTheory CategoryTheory.MonoidalCategory Matrix
open scoped TensorProduct BigOperators
universe u v
variable (k : Type u) [Field k]
variable {β : Type u} [Fintype β] [DecidableEq β]
variable {G : Type u} [Monoid G]
variable {M : Type u} [AddCommGroup M] [Module k M]

noncomputable def coordinateTensorEquiv : ((β → k) ⊗[k] M) ≃ₗ[k] (β → M) :=
  (TensorProduct.comm k (β → k) M).trans (TensorProduct.piScalarRight k k M β)

lemma coordinateTensorEquiv_tmul (v : β → k) (w : M) :
    coordinateTensorEquiv k (v ⊗ₜ[k] w) = fun i => v i • w := by
  simp [coordinateTensorEquiv, TensorProduct.piScalarRight_apply,
    TensorProduct.piScalarRightHom_tmul]

lemma coordinateTensorEquiv_intertwines
    (τ : Representation k G (β → k)) (σ : Representation k G M) (g : G)
    (v : (β → k) ⊗[k] M) :
    coordinateTensorEquiv k ((τ.tprod σ) g v) =
      matrixTensorRepresentation τ σ g (coordinateTensorEquiv k v) := by
  induction v using TensorProduct.inductionOn with
  | add v w hv hw => simp only [map_add, hv, hw]
  | tmul v w =>
    rw [Representation.tprod_apply, TensorProduct.map_tmul, coordinateTensorEquiv_tmul,
      coordinateTensorEquiv_tmul]
    funext i
    rw [matrixTensorRepresentation_apply]
    simp only [map_smul, smul_smul, ← Finset.sum_smul]
    congr 1
    exact (congrFun (LinearMap.toMatrix'_mulVec (τ g) v) i).symm

variable {V : Type u} [AddCommGroup V] [Module k V]
variable {H : Type v} [Monoid H]
noncomputable def coordinateRepresentation (ρ : Representation k H V) (e : V ≃ₗ[k] (β → k)) :
    Representation k H (β → k) := {
    toFun g := e.conj (ρ g)
    map_one' := by ext v; simp [LinearEquiv.conj_apply]
    map_mul' g h := by ext v; simp [LinearEquiv.conj_apply, Module.End.mul_apply]
  }

lemma coordinateRepresentation_equiv (ρ : Representation k H V) (e : V ≃ₗ[k] (β → k))
    (g : H) (v : V) : e (ρ g v) = coordinateRepresentation k ρ e g (e v) := by
  simp [coordinateRepresentation, LinearEquiv.conj_apply]

lemma coordinateRepresentation_rational (ρ : Representation k (SL2 k) V)
    (e : V ≃ₗ[k] (β → k)) (hρ : IsRational k ρ) :
    IsRational k (coordinateRepresentation k ρ e) :=
  IsRational.of_surjective k ρ _ e.toLinearMap e.surjective
    (coordinateRepresentation_equiv k ρ e) hρ

noncomputable def coordinateFDIso (S : FDRep k G) (e : S ≃ₗ[k] (β → k)) :
    S ≅ FDRep.of (coordinateRepresentation k S.ρ e) := by
  let f : S ⟶ FDRep.of (coordinateRepresentation k S.ρ e) := fdrepHom k e.toLinearMap (coordinateRepresentation_equiv k S.ρ e)
  letI : IsIso f := fdrepHom_isIso_of_bijective k f e.bijective
  exact asIso f
end FiberFunctorProof

end OAI
