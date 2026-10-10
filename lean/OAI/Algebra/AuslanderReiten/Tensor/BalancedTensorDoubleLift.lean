import OAI.Algebra.AuslanderReiten.Tensor.BalancedTensorMap
import Mathlib.LinearAlgebra.TensorProduct.Associator

namespace OAI

noncomputable section
namespace ArExplicit.BalancedTensor
open scoped TensorProduct
universe u
variable {k A B F G X Y Z : Type u} [CommRing k] [Ring A] [Ring B]
  [AddCommGroup F] [AddCommGroup G] [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
  [Module k F] [Module k G] [Module k X] [Module k Y] [Module k Z]
  [Module Aᵐᵒᵖ F] [Module Bᵐᵒᵖ G] [Module A X] [Module B Y]

def doubleLift (b : F →ₗ[k] X →ₗ[k] G →ₗ[k] Y →ₗ[k] Z)
    (hA : ∀ (f : F) (a : A) (x : X) (g : G) (y : Y), b (MulOpposite.op a • f) x g y = b f (a • x) g y)
    (hB : ∀ (f : F) (x : X) (g : G) (a : B) (y : Y), b f x (MulOpposite.op a • g) y = b f x g (a • y)) :
    BalancedTensor k A F X →ₗ[k] BalancedTensor k B G Y →ₗ[k] Z :=
  lift
    { toFun f :=
        { toFun x := lift (b f x) (hB f x)
          map_add' x x' := by
            apply hom_ext
            intro g y
            simp only [lift_tmul, map_add, LinearMap.add_apply]
          map_smul' a x := by
            apply hom_ext
            intro g y
            simp only [lift_tmul, map_smul, LinearMap.smul_apply, RingHom.id_apply] }
      map_add' f f' := by
        apply LinearMap.ext
        intro x
        apply hom_ext
        intro g y
        simp only [LinearMap.coe_mk, AddHom.coe_mk, lift_tmul, map_add, LinearMap.add_apply]
      map_smul' a f := by
        apply LinearMap.ext
        intro x
        apply hom_ext
        intro g y
        simp only [LinearMap.coe_mk, AddHom.coe_mk, lift_tmul, map_smul,
          LinearMap.smul_apply, RingHom.id_apply] }
    (by
      intro f a x
      apply hom_ext
      intro g y
      exact hA f a x g y)

@[simp] theorem doubleLift_tmul (b : F →ₗ[k] X →ₗ[k] G →ₗ[k] Y →ₗ[k] Z)
    (hA : ∀ (f : F) (a : A) (x : X) (g : G) (y : Y), b (MulOpposite.op a • f) x g y = b f (a • x) g y)
    (hB : ∀ (f : F) (x : X) (g : G) (a : B) (y : Y), b f x (MulOpposite.op a • g) y = b f x g (a • y))
    (f : F) (x : X) (g : G) (y : Y) :
    doubleLift b hA hB (tmul f x) (tmul g y) = b f x g y := rfl

def curryFour (f : ((F ⊗[k] X) ⊗[k] (G ⊗[k] Y)) →ₗ[k] Z) :
    F →ₗ[k] X →ₗ[k] G →ₗ[k] Y →ₗ[k] Z :=
  TensorProduct.curry ((TensorProduct.lcurry (RingHom.id k) G Y Z).comp
    (TensorProduct.curry f))

@[simp] theorem curryFour_apply (h : ((F ⊗[k] X) ⊗[k] (G ⊗[k] Y)) →ₗ[k] Z)
    (f : F) (x : X) (g : G) (y : Y) :
    curryFour h f x g y = h ((f ⊗ₜ[k] x) ⊗ₜ[k] (g ⊗ₜ[k] y)) := rfl

end ArExplicit.BalancedTensor

end

end OAI
