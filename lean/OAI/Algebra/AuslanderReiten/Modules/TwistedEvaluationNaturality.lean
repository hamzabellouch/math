import OAI.Algebra.AuslanderReiten.Modules.TwistedModuleEvaluation

namespace OAI

noncomputable section
namespace ArExplicit.FiniteLeftModule
open scoped TensorProduct
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (σ : R ≃ₐ[k] R) {X Y : FiniteLeftModule k R}

def twistedLeftMap (f : X.carrier →ₗ[R] Y.carrier) :
    TwistedLeftModule k R σ X.carrier →ₗ[R] TwistedLeftModule k R σ Y.carrier where
  toFun x := ⟨f x.value⟩
  map_add' x y := by
    apply TwistedLeftModule.ext
    exact f.map_add _ _
  map_smul' r x := by
    apply TwistedLeftModule.ext
    exact f.map_smul (σ.symm r) x.value

theorem twistedEvaluationEquiv_natural (f : X.carrier →ₗ[R] Y.carrier) :
    (twistedEvaluationEquiv σ Y).toLinearMap.comp
      (BalancedTensor.mapRight (k := k) (S := R)
        (F := EnvelopingBimodule k R (twistedFiniteModule σ).carrier) f) =
    (twistedLeftMap σ f).comp (twistedEvaluationEquiv σ X).toLinearMap := by
  apply BalancedTensor.leftHom_ext
  intro a x
  apply TwistedLeftModule.ext
  exact (f.map_smul (σ.symm a.value.value) x).symm

end ArExplicit.FiniteLeftModule

end

end OAI
