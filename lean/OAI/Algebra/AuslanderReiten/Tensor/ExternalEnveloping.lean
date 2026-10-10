import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorProjective
import Mathlib.LinearAlgebra.TensorProduct.Opposite
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct

namespace ArExplicit.ExternalTensor

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]

abbrev ProductEnveloping := (A ⊗[k] Aᵐᵒᵖ) ⊗[k] (B ⊗[k] Bᵐᵒᵖ)
abbrev EnvelopingProduct := (A ⊗[k] B) ⊗[k] (A ⊗[k] B)ᵐᵒᵖ

def envelopingEquiv : ProductEnveloping k A B ≃ₐ[k] EnvelopingProduct k A B :=
  (Algebra.TensorProduct.tensorTensorTensorComm k k k k A Aᵐᵒᵖ B Bᵐᵒᵖ).trans
    (Algebra.TensorProduct.congr (AlgEquiv.refl : (A ⊗[k] B) ≃ₐ[k] (A ⊗[k] B))
      (Algebra.TensorProduct.opAlgEquiv k k A B))

@[simp] theorem envelopingEquiv_tmul (a c : A) (b d : B) :
    envelopingEquiv k A B ((a ⊗ₜ[k] MulOpposite.op c) ⊗ₜ[k] (b ⊗ₜ[k] MulOpposite.op d)) =
      (a ⊗ₜ[k] b) ⊗ₜ[k] MulOpposite.op (c ⊗ₜ[k] d) := by
  simp [envelopingEquiv]

@[simp] theorem envelopingEquiv_symm_tmul (a c : A) (b d : B) :
    (envelopingEquiv k A B).symm ((a ⊗ₜ[k] b) ⊗ₜ[k] MulOpposite.op (c ⊗ₜ[k] d)) =
      (a ⊗ₜ[k] MulOpposite.op c) ⊗ₜ[k] (b ⊗ₜ[k] MulOpposite.op d) := by
  apply (envelopingEquiv k A B).injective
  simp

abbrev envelopingFunctor : ModuleCat.{u} (ProductEnveloping k A B) ⥤
    ModuleCat.{u} (EnvelopingProduct k A B) :=
  ModuleCat.restrictScalars (envelopingEquiv k A B).symm.toRingHom

abbrev envelopingObject (M : ModuleCat.{u} (ProductEnveloping k A B)) :
    ModuleCat.{u} (EnvelopingProduct k A B) := (envelopingFunctor k A B).obj M

private instance forwardInverse : RingHomInvPair (envelopingEquiv k A B).toRingHom
    (envelopingEquiv k A B).symm.toRingHom where
  comp_eq := by apply RingHom.ext; intro x; exact (envelopingEquiv k A B).symm_apply_apply x
  comp_eq₂ := by apply RingHom.ext; intro x; exact (envelopingEquiv k A B).apply_symm_apply x

private instance backwardInverse : RingHomInvPair (envelopingEquiv k A B).symm.toRingHom
    (envelopingEquiv k A B).toRingHom where
  comp_eq := by apply RingHom.ext; intro x; exact (envelopingEquiv k A B).apply_symm_apply x
  comp_eq₂ := by apply RingHom.ext; intro x; exact (envelopingEquiv k A B).symm_apply_apply x

def envelopingSemilinear (M : ModuleCat.{u} (ProductEnveloping k A B)) :
    LinearEquiv (envelopingEquiv k A B).toRingHom
      (σ' := (envelopingEquiv k A B).symm.toRingHom) M (envelopingObject k A B M) where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a x := by
    change a • x = ((envelopingEquiv k A B).symm ((envelopingEquiv k A B) a)) • x
    rw [AlgEquiv.symm_apply_apply]

theorem enveloping_projective (M : ModuleCat.{u} (ProductEnveloping k A B))
    [Module.Projective (ProductEnveloping k A B) M] :
    Module.Projective (EnvelopingProduct k A B) (envelopingObject k A B M) :=
  Module.Projective.of_equiv (envelopingSemilinear k A B M)

instance envelopingBaseModule (M : ModuleCat.{u} (ProductEnveloping k A B)) [Module k M] :
    Module k (envelopingObject k A B M) := inferInstanceAs (Module k M)

instance envelopingTower (M : ModuleCat.{u} (ProductEnveloping k A B)) [Module k M]
    [IsScalarTower k (ProductEnveloping k A B) M] :
    IsScalarTower k (EnvelopingProduct k A B) (envelopingObject k A B M) :=
  IsScalarTower.of_algebraMap_smul (A := EnvelopingProduct k A B) fun a x => by
    change (envelopingEquiv k A B).symm (algebraMap k (EnvelopingProduct k A B) a) •
      (show M from x) = a • (show M from x)
    rw [AlgEquiv.commutes, algebraMap_smul]

instance envelopingFinite (M : ModuleCat.{u} (ProductEnveloping k A B)) [Module k M]
    [Module.Finite k M] : Module.Finite k (envelopingObject k A B M) :=
  inferInstanceAs (Module.Finite k M)

end ArExplicit.ExternalTensor

end

end OAI
