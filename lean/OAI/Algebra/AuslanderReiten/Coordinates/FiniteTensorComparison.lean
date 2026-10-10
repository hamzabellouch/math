import OAI.Algebra.AuslanderReiten.Tensor.BalancedTensorComparisonMaps
import OAI.Algebra.AuslanderReiten.Modules.FiniteModuleEvaluation

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.FiniteLeftModule
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (τ : FrobeniusTrace k R) (X : FiniteLeftModule k R)
variable (M N : FiniteLeftModule k (R ⊗[k] Rᵐᵒᵖ))
variable [Module.Finite R (EnvelopingBimodule k R M.carrier)]
  [Module.Projective R (EnvelopingBimodule k R M.carrier)]
  [Module.Finite Rᵐᵒᵖ (EnvelopingBimodule k R M.carrier)]
  [Module.Projective Rᵐᵒᵖ (EnvelopingBimodule k R M.carrier)]
variable [Module.Finite R (EnvelopingBimodule k R N.carrier)]
  [Module.Projective R (EnvelopingBimodule k R N.carrier)]
  [Module.Finite Rᵐᵒᵖ (EnvelopingBimodule k R N.carrier)]
  [Module.Projective Rᵐᵒᵖ (EnvelopingBimodule k R N.carrier)]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower

def evaluatedResolutionOut :
    BalancedTensor.completeTensor (F := EnvelopingBimodule k R M.carrier) τ X ⟶
      (evaluated X M).completeCochain τ :=
  BalancedTensor.comparisonOut τ X (evaluated X M) (LinearEquiv.refl R _)

theorem evaluatedResolutionOut_natural (f : M.carrier ⟶ N.carrier)
    (L : FiniteLeftModule k R) (e : (evaluated X N).carrier ≃ₗ[R] L.carrier) :
    (HomotopyCategory.quotient _ _).map
      (BalancedTensor.complexMap (k := k) (EnvelopingBimodule.mapRight f)
        (EnvelopingBimodule.map_left_smul f) (X.completeCochain τ) ≫
          BalancedTensor.comparisonOut τ X L e) =
    (HomotopyCategory.quotient _ _).map
      (evaluatedResolutionOut τ X M ≫
        resolutionMap τ (e.toLinearMap.comp (evaluationMap X f.hom))) := by
  apply BalancedTensor.comparisonOut_natural τ X (evaluated X M)
    (LinearEquiv.refl R _) L (EnvelopingBimodule.mapRight f)
    (EnvelopingBimodule.map_left_smul f) e
    (e.toLinearMap.comp (evaluationMap X f.hom))
  intro x
  rfl

end ArExplicit.FiniteLeftModule

end

end OAI
