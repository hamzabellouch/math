import OAI.Algebra.AuslanderReiten.Tensor.BalancedTensorCompleteAction

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open scoped ModuleCat.Algebra
namespace ArExplicit.BalancedTensor
universe u
variable {k R F : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable [AddCommGroup F] [Module k F] [Module Rᵐᵒᵖ F] [Module R F]
variable [IsScalarTower k Rᵐᵒᵖ F]
variable [SMulCommClass k R F] [SMulCommClass R Rᵐᵒᵖ F]
variable [Module.Finite Rᵐᵒᵖ F] [Module.Projective Rᵐᵒᵖ F]
variable [Module.Finite R F] [Module.Projective R F]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable [PreservesFiniteLimits (functor (k := k) (R := R) (S := R) (F := F))]
variable [PreservesFiniteColimits (functor (k := k) (R := R) (S := R) (F := F))]
variable [(functor (k := k) (R := R) (S := R) (F := F)).PreservesProjectiveObjects]
variable (τ : FrobeniusTrace k R) (M : FiniteLeftModule k R)
variable (e : BalancedTensor k R F M.carrier ≃ₗ[R] M.carrier)

theorem completeActionIn_quotient :
    (HomotopyCategory.quotient _ _).map (completeActionIn τ M e) =
      (completeTensorIso τ M M e).inv := by
  apply (cancel_mono (completeTensorIso τ M M e).hom).1
  have h := completeAction_inverse τ M e
  rw [CategoryTheory.Functor.map_comp, completeActionOut_quotient] at h
  exact h.trans (completeTensorIso τ M M e).inv_hom_id.symm

end ArExplicit.BalancedTensor

end

end OAI
