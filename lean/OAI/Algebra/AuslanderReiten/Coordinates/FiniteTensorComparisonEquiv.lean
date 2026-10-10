import OAI.Algebra.AuslanderReiten.Coordinates.FiniteTensorComparison
import OAI.Algebra.AuslanderReiten.HomComplex.FullHomCompositionLinear

namespace OAI

noncomputable section
open CategoryTheory CochainComplex.HomComplex
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.FiniteLeftModule
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (τ : FrobeniusTrace k R) (X : FiniteLeftModule k R)
variable (M : FiniteLeftModule k (R ⊗[k] Rᵐᵒᵖ))
variable [Module.Finite R (EnvelopingBimodule k R M.carrier)]
  [Module.Projective R (EnvelopingBimodule k R M.carrier)]
  [Module.Finite Rᵐᵒᵖ (EnvelopingBimodule k R M.carrier)]
  [Module.Projective Rᵐᵒᵖ (EnvelopingBimodule k R M.carrier)]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower

def evaluatedResolutionFullEquiv (P : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    CohomologyClass P (BalancedTensor.completeTensor (F := EnvelopingBimodule k R M.carrier) τ X) n ≃ₗ[k]
      CohomologyClass P ((evaluated X M).completeCochain τ) n :=
  LinearEquiv.ofBijective (fullHomPostcompLinear k n (evaluatedResolutionOut τ X M))
    (BalancedTensor.comparisonOut_bijective τ X (evaluated X M) (LinearEquiv.refl _ _) P n)

@[simp] theorem evaluatedResolutionFullEquiv_apply (P : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    (x : CohomologyClass P (BalancedTensor.completeTensor (F := EnvelopingBimodule k R M.carrier) τ X) n) :
    evaluatedResolutionFullEquiv τ X M P n x = fullHomPostcomp (evaluatedResolutionOut τ X M) n x := rfl

end ArExplicit.FiniteLeftModule

end

end OAI
