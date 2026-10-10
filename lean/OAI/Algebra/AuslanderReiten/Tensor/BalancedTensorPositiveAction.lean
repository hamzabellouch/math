import OAI.Algebra.AuslanderReiten.Tensor.BalancedTensorCompleteAction

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits CochainComplex.HomComplex
open scoped ModuleCat.Algebra
namespace ArExplicit.BalancedTensor
universe u
variable {k R F : Type u} [Field k] [CharP k 2] [Ring R] [Algebra k R] [Module.Finite k R]
variable [AddCommGroup F] [Module k F] [Module Rᵐᵒᵖ F] [Module R F]
variable [IsScalarTower k Rᵐᵒᵖ F] [SMulCommClass k Rᵐᵒᵖ F]
variable [SMulCommClass k R F] [SMulCommClass R Rᵐᵒᵖ F]
variable [Module.Finite Rᵐᵒᵖ F] [Module.Projective Rᵐᵒᵖ F]
variable [Module.Finite R F] [Module.Projective R F]
variable [HasDerivedCategory (ModuleCat.{u} R)]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable [PreservesFiniteLimits (functor (k := k) (R := R) (S := R) (F := F))]
variable [PreservesFiniteColimits (functor (k := k) (R := R) (S := R) (F := F))]
variable [(functor (k := k) (R := R) (S := R) (F := F)).PreservesProjectiveObjects]
variable (τ : FrobeniusTrace k R) (M : FiniteLeftModule k R)
variable (e : BalancedTensor k R F M.carrier ≃ₗ[R] M.carrier)

omit [SMulCommClass k Rᵐᵒᵖ F] in
theorem completeAction_scalar_positive (d : ℕ) (hd : 0 < d) (c : k)
    (hs : ∀ z : Ext M.carrier M.carrier d,
      selfExtIso (k := k) (nativeEvaluationIso M e) d
        (z.mapExactFunctor (functor (k := k) (R := R) (S := R) (F := F))) = c • z)
    (x : CohomologyClass (M.completeCochain τ) (M.completeCochain τ) (d : ℤ)) :
    fullHomPostcomp (completeActionOut τ M e) _
      (fullHomPrecomp (completeActionIn τ M e) _
        (mapFullHom (functor (k := k) (R := R) (S := R) (F := F)) _ _ _ x)) = c • x := by
  cases d with
  | zero => exact False.elim (Nat.lt_irrefl 0 hd)
  | succ n => exact completeAction_scalar τ M e n c hs x

end ArExplicit.BalancedTensor

end

end OAI
