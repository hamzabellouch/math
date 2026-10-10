import OAI.Algebra.Finitistic.Ordinary.OrdinaryTensorBimap

namespace OAI
noncomputable section
namespace LittleFinitistic.BalancedTensor
universe u
variable {k A M M' N N' : Type u} [Field k] [Ring A] [Algebra k A]
variable [AddCommGroup M] [Module k M] [Module Aᵐᵒᵖ M] [IsScalarTower k Aᵐᵒᵖ M]
variable [AddCommGroup M'] [Module k M'] [Module Aᵐᵒᵖ M'] [IsScalarTower k Aᵐᵒᵖ M']
variable [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
variable [AddCommGroup N'] [Module k N'] [Module A N'] [IsScalarTower k A N']

/-- Actual balanced tensor congruence under module equivalences in both factors. -/
def congr (e : M ≃ₗ[Aᵐᵒᵖ] M') (f : N ≃ₗ[A] N') : Tensor k A M N ≃ₗ[k] Tensor k A M' N' where
  __ := bimap (k := k) e.toLinearMap f.toLinearMap
  invFun := bimap (k := k) e.symm.toLinearMap f.symm.toLinearMap
  left_inv x := by
    change bimap e.symm.toLinearMap f.symm.toLinearMap (bimap e.toLinearMap f.toLinearMap x) = x
    induction x using BalancedTensor.induction_on with
    | hz => simp only [map_zero]
    | ht m n => simp only [bimap_mk,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply]
    | ha x y hx hy => simp only [map_add,hx,hy]
  right_inv x := by
    change bimap e.toLinearMap f.toLinearMap (bimap e.symm.toLinearMap f.symm.toLinearMap x) = x
    induction x using BalancedTensor.induction_on with
    | hz => simp only [map_zero]
    | ht m n => simp only [bimap_mk,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply]
    | ha x y hx hy => simp only [map_add,hx,hy]
end LittleFinitistic.BalancedTensor

end

end OAI
