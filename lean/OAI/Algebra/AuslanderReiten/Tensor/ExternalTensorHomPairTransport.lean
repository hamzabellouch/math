import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorHom

namespace OAI

noncomputable section
open scoped TensorProduct
namespace ArExplicit.ExternalTensor
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable {M N U V : Type u}
variable [AddCommGroup M] [AddCommGroup N] [AddCommGroup U] [AddCommGroup V]
variable [Module k M] [Module k N] [Module k U] [Module k V]
variable [Module A M] [Module B N] [Module A U] [Module B V]
variable [IsScalarTower k A M] [IsScalarTower k B N] [IsScalarTower k A U] [IsScalarTower k B V]
variable (a : M →ₗ[k] M) (b : N →ₗ[k] N) (e : U ≃ₗ[k] U) (f : V ≃ₗ[k] V)
variable (α : (M →ₗ[A] U) →ₗ[k] (M →ₗ[A] U))
variable (β : (N →ₗ[B] V) →ₗ[k] (N →ₗ[B] V))
variable (hα : ∀ c x, α c x = e.symm (c (a x)))
variable (hβ : ∀ d y, β d y = f.symm (d (b y)))
include hα hβ

theorem homMap_transport (c : (M →ₗ[A] U) ⊗[k] (N →ₗ[B] V))
    (z : moduleObject k A B M N) :
    homMap k A B (TensorProduct.map α β c) z =
      (TensorProduct.congr e f).symm (homMap k A B c (TensorProduct.map a b z)) := by
  induction c using TensorProduct.inductionOn with
  | add c d hc hd =>
    erw [map_add, map_add, LinearMap.add_apply, map_add, LinearMap.add_apply, map_add]
    rw [hc, hd]
    rfl
  | tmul c d =>
    induction z using TensorProduct.inductionOn with
    | add x y hx hy =>
      erw [map_add, map_add, map_add, map_add]
      rw [hx, hy]
      rfl
    | tmul x y =>
      simp only [TensorProduct.map_tmul, homMap_tmul, map_tmul,
        TensorProduct.congr_symm, TensorProduct.congr_tmul, hα, hβ]
      rfl

end ArExplicit.ExternalTensor

end

end OAI
