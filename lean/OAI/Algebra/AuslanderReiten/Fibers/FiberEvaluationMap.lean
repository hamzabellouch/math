import OAI.Algebra.AuslanderReiten.Fibers.FiniteEvaluatedFiber

namespace OAI

noncomputable section
namespace ArExplicit.FiniteLeftModule
open CategoryTheory
open scoped TensorProduct
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (X : FiniteLeftModule k R)
variable (U₁ U₂ Y : FiniteLeftModule k (R ⊗[k] Rᵐᵒᵖ))
variable (g₁ : U₁.carrier ⟶ Y.carrier) (g₂ : U₂.carrier ⟶ Y.carrier)

def fiberEvaluationInclusion : (evaluated X (fiber U₁ U₂ Y g₁ g₂)).carrier →ₗ[R]
    (evaluated X (fiberSource U₁ U₂ Y)).carrier :=
  evaluationMap X (M := fiber U₁ U₂ Y g₁ g₂) (N := fiberSource U₁ U₂ Y)
    (fiberInclusion U₁ U₂ Y g₁ g₂).hom

theorem middlePairMap_fiberEvaluationInclusion :
    (middlePairMap X U₁ U₂ Y).comp (fiberEvaluationInclusion X U₁ U₂ Y g₁ g₂) =
    (evaluationMap X (fiberProjection₁ U₁ U₂ Y g₁ g₂).hom).prod
      (evaluationMap X (fiberProjection₂ U₁ U₂ Y g₁ g₂).hom) :=
  middlePairMap_fiberInclusion X U₁ U₂ Y g₁ g₂

end ArExplicit.FiniteLeftModule

end

end OAI
