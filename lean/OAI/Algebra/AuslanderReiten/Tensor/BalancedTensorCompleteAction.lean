import OAI.Algebra.AuslanderReiten.Tensor.BalancedTensorResolution
import OAI.Algebra.AuslanderReiten.Tensor.BalancedTensorCanonicalEndpoint
import OAI.Algebra.AuslanderReiten.Complete.CompleteFunctorCokernelAction
import OAI.Algebra.AuslanderReiten.Tensor.BalancedTensorNative

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open CochainComplex.HomComplex
open scoped ModuleCat.Algebra
namespace ArExplicit.BalancedTensor
open CompleteComparison
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

def nativeEvaluationIso :
    (functor (k := k) (R := R) (S := R) (F := F)).obj M.carrier ≅ M.carrier :=
  nativeObjectIso (k := k) (R := R) (S := R) (F := F) M.carrier ≪≫ e.toModuleIso

def completeActionEndpoint : ModuleCat.of R (CochainCokernel (M.completeCochain τ)) ≅
    (functor (k := k) (R := R) (S := R) (F := F)).obj
      (ModuleCat.of R (CochainCokernel (M.completeCochain τ))) :=
  (M.completeCochainCokernelEquiv τ).toModuleIso ≪≫ (nativeEvaluationIso M e).symm ≪≫
    (functor (k := k) (R := R) (S := R) (F := F)).mapIso
      (M.completeCochainCokernelEquiv τ).symm.toModuleIso

def completeActionCokernelIso :
    ModuleCat.of R (CochainCokernel (completeTensor (F := F) τ M)) ≅
      ModuleCat.of R (CochainCokernel (M.completeCochain τ)) :=
  rawFunctorEndpointIso (functor (k := k) (R := R) (S := R) (F := F)) (M.completeCochain τ)
    (M.completeCochain_totallyAcyclic τ).to_chain
    (completeTensor_totallyAcyclic (F := F) τ M).to_chain ≪≫
      (completeActionEndpoint τ M e).symm

def completeActionIn : M.completeCochain τ ⟶ completeTensor (F := F) τ M :=
  cokernelCochainLift (M.completeCochain_totallyAcyclic τ)
    (completeTensor_totallyAcyclic (F := F) τ M)
    (completeActionCokernelIso τ M e).inv.hom

def completeActionOut : completeTensor (F := F) τ M ⟶ M.completeCochain τ :=
  cokernelCochainLift (completeTensor_totallyAcyclic (F := F) τ M)
    (M.completeCochain_totallyAcyclic τ) (completeActionCokernelIso τ M e).hom.hom

omit [CharP k 2] [SMulCommClass k Rᵐᵒᵖ F]
  [HasDerivedCategory (ModuleCat.{u} R)] in
theorem completeAction_inverse :
    (HomotopyCategory.quotient _ _).map
      (completeActionIn τ M e ≫ completeActionOut τ M e) = 𝟙 _ := by
  exact cokernelCochainLift_homotopy_inverse (M.completeCochain_totallyAcyclic τ)
    (completeTensor_totallyAcyclic (F := F) τ M)
    (completeActionCokernelIso τ M e).symm.toLinearEquiv

omit [CharP k 2] [SMulCommClass k Rᵐᵒᵖ F]
  [HasDerivedCategory (ModuleCat.{u} R)] in
theorem completeAction_inverse' :
    (HomotopyCategory.quotient _ _).map
      (completeActionOut τ M e ≫ completeActionIn τ M e) = 𝟙 _ := by
  exact cokernelCochainLift_homotopy_inverse (completeTensor_totallyAcyclic (F := F) τ M)
    (M.completeCochain_totallyAcyclic τ) (completeActionCokernelIso τ M e).toLinearEquiv

omit [SMulCommClass k Rᵐᵒᵖ F] in
theorem completeAction_scalar (n : ℕ) (c : k)
    (hs : ∀ z : Ext M.carrier M.carrier (n+1),
      selfExtIso (k := k) (nativeEvaluationIso M e) (n+1)
        (z.mapExactFunctor (functor (k := k) (R := R) (S := R) (F := F))) = c • z)
    (x : CohomologyClass (M.completeCochain τ) (M.completeCochain τ) ((n+1 : ℕ) : ℤ)) :
    fullHomPostcomp (completeActionOut τ M e) _
      (fullHomPrecomp (completeActionIn τ M e) _
        (mapFullHom (functor (k := k) (R := R) (S := R) (F := F)) _ _ _ x)) = c • x := by
  apply fullHom_rawFunctor_scalar (functor (k := k) (R := R) (S := R) (F := F))
    (M.completeCochain τ) (M.completeCochain_totallyAcyclic τ).to_chain
    (completeTensor_totallyAcyclic (F := F) τ M).to_chain
    (completeActionIn τ M e) (completeActionOut τ M e) (completeActionEndpoint τ M e)
  · exact cokernelCochainLift_map _ _ _
  · exact cokernelCochainLift_map _ _ _
  · exact exactFunctor_scalar_transport (functor (k := k) (R := R) (S := R) (F := F))
      (M.completeCochainCokernelEquiv τ).toModuleIso (nativeEvaluationIso M e).symm (n+1) c hs

omit [CharP k 2] [SMulCommClass k Rᵐᵒᵖ F]
  [HasDerivedCategory (ModuleCat.{u} R)] in
theorem completeActionCokernelIso_eq : completeActionCokernelIso τ M e =
    (((tensorCokernelEquiv (F := F) τ M).trans e).trans
      (M.completeCochainCokernelEquiv τ).symm).toModuleIso := by
  rw [completeActionCokernelIso, rawFunctorEndpointIso_eq]
  apply Iso.ext
  have ht := congrArg (fun f =>
    (cochainCokernelEquiv (k := k) (F := F) (S := R) (M.completeCochain τ)).toModuleIso.hom ≫
      f ≫ e.toModuleIso.hom ≫ (M.completeCochainCokernelEquiv τ).toModuleIso.inv)
    (nativeObjectIso_natural (k := k) (F := F) (S := R)
      (M.completeCochainCokernelEquiv τ).toLinearMap)
  exact ht

omit [CharP k 2] [SMulCommClass k Rᵐᵒᵖ F]
  [HasDerivedCategory (ModuleCat.{u} R)] in
theorem completeActionOut_quotient :
    (HomotopyCategory.quotient _ _).map (completeActionOut τ M e) =
      (completeTensorIso τ M M e).hom := by
  unfold completeActionOut
  rw [completeActionCokernelIso_eq]
  exact cokernelCochainLift_quotient _ _ _

end ArExplicit.BalancedTensor

end

end OAI
