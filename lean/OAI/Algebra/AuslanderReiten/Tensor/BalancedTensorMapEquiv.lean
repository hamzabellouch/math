import OAI.Algebra.AuslanderReiten.Tensor.BalancedTensorCategory

namespace OAI

noncomputable section
namespace ArExplicit.BalancedTensor
variable {k R S F L M : Type*} [Field k] [Ring R] [Ring S] [Algebra k R]
variable [AddCommGroup F] [Module k F] [Module Rᵐᵒᵖ F] [Module S F]
variable [SMulCommClass k S F] [SMulCommClass S Rᵐᵒᵖ F]
variable [AddCommGroup L] [Module k L] [Module R L] [IsScalarTower k R L]
variable [AddCommGroup M] [Module k M] [Module R M] [IsScalarTower k R M]

def mapRightEquiv (e : L ≃ₗ[R] M) : BalancedTensor k R F L ≃ₗ[S] BalancedTensor k R F M where
  __ := mapRight (k := k) (F := F) (S := S) e.toLinearMap
  invFun := mapRight (k := k) (F := F) (S := S) e.symm.toLinearMap
  left_inv x := by
    change mapRight (k := k) (F := F) (S := S) e.symm.toLinearMap
      (mapRight (k := k) (F := F) (S := S) e.toLinearMap x) = x
    have h := congrArg (fun t : BalancedTensor k R F L →ₗ[S] BalancedTensor k R F L => t x)
      (mapRight_comp (k := k) (F := F) (S := S) e.toLinearMap e.symm.toLinearMap)
    simpa only [e.symm_comp, mapRight_id, LinearMap.comp_apply, LinearMap.id_apply] using h.symm
  right_inv x := by
    change mapRight (k := k) (F := F) (S := S) e.toLinearMap
      (mapRight (k := k) (F := F) (S := S) e.symm.toLinearMap x) = x
    have h := congrArg (fun t : BalancedTensor k R F M →ₗ[S] BalancedTensor k R F M => t x)
      (mapRight_comp (k := k) (F := F) (S := S) e.symm.toLinearMap e.toLinearMap)
    simpa only [e.comp_symm, mapRight_id, LinearMap.comp_apply, LinearMap.id_apply] using h.symm

@[simp] theorem mapRightEquiv_tmul (e : L ≃ₗ[R] M) (f : F) (x : L) :
    mapRightEquiv (k := k) (F := F) (S := S) e (tmul f x) = tmul f (e x) := rfl

end ArExplicit.BalancedTensor

end

end OAI
