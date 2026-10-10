import Mathlib.LinearAlgebra.TensorProduct.Tower
import OAI.Algebra.Finitistic.Rectification.ExternalTensor

namespace OAI

noncomputable section
open scoped TensorProduct
namespace LittleFinitistic.TensorProjection
attribute [local instance] ExternalTensor.rightModule
variable {k B M M' N : Type*} [Field k] [Ring B] [Algebra k B]
  [AddCommGroup M] [Module k M] [AddCommGroup M'] [Module k M']
  [AddCommGroup N] [Module k N] [Module Bᵐᵒᵖ N] [IsScalarTower k Bᵐᵒᵖ N]

/-- Tensor a k-linear map with the identity while retaining the actual right B-action. -/
def rightMap (f : M →ₗ[k] M') : (M ⊗[k] N) →ₗ[Bᵐᵒᵖ] (M' ⊗[k] N) where
  __ := (TensorProduct.map f LinearMap.id).toAddMonoidHom
  map_smul' c x := by
    induction x using TensorProduct.inductionOn with
    | tmul m n => simp [ExternalTensor.right_smul_tmul]
    | add x y hx hy => simp_all [smul_add]

@[simp] theorem rightMap_tmul (f : M →ₗ[k] M') (m : M) (n : N) :
    rightMap (B := B) f (m ⊗ₜ[k] n) = f m ⊗ₜ[k] n := rfl

/-- Transport a first-factor vector-space equivalence as an actual right-module equivalence. -/
def rightCongr (e : M ≃ₗ[k] M') : (M ⊗[k] N) ≃ₗ[Bᵐᵒᵖ] (M' ⊗[k] N) where
  __ := rightMap (B := B) (N := N) e.toLinearMap
  invFun := rightMap (B := B) (N := N) e.symm.toLinearMap
  left_inv x := by
    induction x using TensorProduct.inductionOn with
    | tmul m n => simp
    | add x y hx hy => simp_all
  right_inv x := by
    induction x using TensorProduct.inductionOn with
    | tmul m n => simp
    | add x y hx hy => simp_all

variable (p : M →ₗ[k] M)

/-- The actual fixed submodule for a projector on the first tensor factor. -/
def fixed : Submodule Bᵐᵒᵖ (M ⊗[k] N) := (rightMap (B := B) p - LinearMap.id).ker

@[simp] theorem mem_fixed (x : M ⊗[k] N) : x ∈ fixed (B := B) p ↔ rightMap (B := B) p x = x := by
  simp [fixed,sub_eq_zero]

theorem range_fixed (hp : p.comp p = p) (x : p.range) : p x.val = x.val := by
  obtain ⟨m,hm⟩ := x.property
  have h := LinearMap.congr_fun hp m
  simpa only [LinearMap.comp_apply,hm] using h

/-- The eigenspace e(M tensor N) is exactly (eM) tensor N as a right module. -/
def imageTensorEquiv (hp : p.comp p = p) : (p.range ⊗[k] N) ≃ₗ[Bᵐᵒᵖ] fixed (B := B) (N := N) p where
  toFun x := ⟨rightMap (B := B) (N := N) p.range.subtype x,by
    rw [mem_fixed]
    induction x using TensorProduct.inductionOn with
    | tmul m n => simp [range_fixed p hp m]
    | add x y hx hy => simp_all⟩
  invFun x := rightMap (B := B) (N := N) p.rangeRestrict x.val
  left_inv x := by
    induction x using TensorProduct.inductionOn with
    | tmul m n =>
      simp only [rightMap_tmul]
      congr 1
      apply Subtype.ext
      exact range_fixed p hp m
    | add x y hx hy => simp_all
  right_inv x := by
    apply Subtype.ext
    have h : rightMap (B := B) p.range.subtype (rightMap (B := B) (N := N) p.rangeRestrict x.val) =
        rightMap (B := B) p x.val := by
      generalize x.val = y
      induction y using TensorProduct.inductionOn with
      | tmul m n => rfl
      | add a b ha hb => simp_all
    exact h.trans ((mem_fixed p x.val).1 x.property)
  map_add' x y := Subtype.ext (map_add _ x y)
  map_smul' c x := Subtype.ext (map_smul _ c x)
end LittleFinitistic.TensorProjection

end

end OAI
