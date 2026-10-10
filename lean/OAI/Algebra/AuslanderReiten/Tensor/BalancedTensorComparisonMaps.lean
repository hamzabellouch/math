import OAI.Algebra.AuslanderReiten.Tensor.BalancedTensorResolution
import OAI.Algebra.AuslanderReiten.Complete.CompleteCokernelLifts

namespace OAI

noncomputable section
open CategoryTheory CochainComplex.HomComplex
open scoped ModuleCat.Algebra
namespace ArExplicit.BalancedTensor
open CompleteComparison
universe u
variable {k R F : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable [AddCommGroup F] [Module k F] [Module Rᵐᵒᵖ F] [Module R F]
variable [IsScalarTower k Rᵐᵒᵖ F]
variable [SMulCommClass k R F] [SMulCommClass R Rᵐᵒᵖ F]
variable [Module.Finite Rᵐᵒᵖ F] [Module.Projective Rᵐᵒᵖ F]
variable [Module.Finite R F] [Module.Projective R F]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable (τ : FrobeniusTrace k R) (M N : FiniteLeftModule k R)
variable (e : BalancedTensor k R F M.carrier ≃ₗ[R] N.carrier)

def comparisonOut : completeTensor (F := F) τ M ⟶ N.completeCochain τ :=
  cokernelCochainLift (completeTensor_totallyAcyclic (F := F) τ M)
    (N.completeCochain_totallyAcyclic τ)
    (((tensorCokernelEquiv (F := F) τ M).trans e).trans
      (N.completeCochainCokernelEquiv τ).symm).toLinearMap

def comparisonIn : N.completeCochain τ ⟶ completeTensor (F := F) τ M :=
  cokernelCochainLift (N.completeCochain_totallyAcyclic τ)
    (completeTensor_totallyAcyclic (F := F) τ M)
    (((tensorCokernelEquiv (F := F) τ M).trans e).trans
      (N.completeCochainCokernelEquiv τ).symm).symm.toLinearMap

theorem comparisonOut_quotient :
    (HomotopyCategory.quotient _ _).map (comparisonOut τ M N e) =
      (completeTensorIso τ M N e).hom :=
  cokernelCochainLift_quotient _ _ _

theorem comparisonIn_quotient :
    (HomotopyCategory.quotient _ _).map (comparisonIn τ M N e) =
      (completeTensorIso τ M N e).inv :=
  cokernelCochainLift_quotient_inv _ _ _

theorem comparisonOut_bijective (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    Function.Bijective (fullHomPostcomp (K := K) (comparisonOut τ M N e) n) := by
  apply fullHomPostcomp_bijective k n (comparisonOut τ M N e) (comparisonIn τ M N e)
  · rw [CategoryTheory.Functor.map_comp, comparisonOut_quotient, comparisonIn_quotient,
      Iso.hom_inv_id]
  · rw [CategoryTheory.Functor.map_comp, comparisonOut_quotient, comparisonIn_quotient,
      Iso.inv_hom_id]

variable {G : Type u} [AddCommGroup G] [Module k G] [Module Rᵐᵒᵖ G] [Module R G]
variable [IsScalarTower k Rᵐᵒᵖ G]
variable [SMulCommClass k R G] [SMulCommClass R Rᵐᵒᵖ G]
variable [Module.Finite Rᵐᵒᵖ G] [Module.Projective Rᵐᵒᵖ G]
variable [Module.Finite R G] [Module.Projective R G]
variable (N' : FiniteLeftModule k R)

theorem comparisonOut_natural
    (a : F →ₗ[Rᵐᵒᵖ] G) (ha : ∀ (r : R) f, a (r • f) = r • a f)
    (e' : BalancedTensor k R G M.carrier ≃ₗ[R] N'.carrier)
    (b : N.carrier →ₗ[R] N'.carrier)
    (hab : ∀ x, e' (mapLeft (k := k) (M := M.carrier) a x) = b (e x)) :
    (HomotopyCategory.quotient _ _).map
      (complexMap (k := k) a ha (M.completeCochain τ) ≫ comparisonOut τ M N' e') =
    (HomotopyCategory.quotient _ _).map
      (comparisonOut τ M N e ≫ FiniteLeftModule.resolutionMap τ b) := by
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    comparisonOut_quotient, comparisonOut_quotient]
  exact completeTensorIso_natural τ M N N' a ha e e' b hab

theorem comparisonOut_fullHom_natural
    (a : F →ₗ[Rᵐᵒᵖ] G) (ha : ∀ (r : R) f, a (r • f) = r • a f)
    (e' : BalancedTensor k R G M.carrier ≃ₗ[R] N'.carrier)
    (b : N.carrier →ₗ[R] N'.carrier)
    (hab : ∀ x, e' (mapLeft (k := k) (M := M.carrier) a x) = b (e x))
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    (x : CohomologyClass K (completeTensor (F := F) τ M) n) :
    fullHomPostcomp (comparisonOut τ M N' e') n
      (fullHomPostcomp (complexMap (k := k) a ha (M.completeCochain τ)) n x) =
    fullHomPostcomp (FiniteLeftModule.resolutionMap τ b) n
      (fullHomPostcomp (comparisonOut τ M N e) n x) := by
  rw [fullHomPostcomp_comp, fullHomPostcomp_comp]
  exact fullHomPostcomp_congr k n (comparisonOut_natural τ M N e N' a ha e' b hab) x

end ArExplicit.BalancedTensor

end

end OAI
