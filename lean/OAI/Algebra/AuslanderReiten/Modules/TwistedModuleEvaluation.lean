import OAI.Algebra.AuslanderReiten.Modules.FiniteModuleEvaluation
import OAI.Algebra.AuslanderReiten.Fibers.BimoduleFiber
import OAI.Algebra.AuslanderReiten.Tensor.BalancedTensorEquiv
import OAI.Algebra.AuslanderReiten.Tensor.TwistedTensor

namespace OAI

noncomputable section
namespace ArExplicit
open scoped TensorProduct
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (σ : R ≃ₐ[k] R)

def twistedEvaluationCoordinates :
    EnvelopingBimodule k R (twistedFiniteModule σ).carrier ≃ₗ[k] TwistedBimodule k R σ :=
  EnvelopingBimodule.scalarEquiv _

 theorem twistedEvaluationCoordinates_right (r : Rᵐᵒᵖ)
    (x : EnvelopingBimodule k R (twistedFiniteModule σ).carrier) :
    twistedEvaluationCoordinates σ (r • x) = r • twistedEvaluationCoordinates σ x := by
  change (1 : R) • (r • (show TwistedBimodule k R σ from x.value)) = r • (show TwistedBimodule k R σ from x.value)
  rw [one_smul]

 theorem twistedEvaluationCoordinates_left (r : R)
    (x : EnvelopingBimodule k R (twistedFiniteModule σ).carrier) :
    twistedEvaluationCoordinates σ (r • x) = r • twistedEvaluationCoordinates σ x := by
  change r • ((1 : Rᵐᵒᵖ) • (show TwistedBimodule k R σ from x.value)) = r • (show TwistedBimodule k R σ from x.value)
  rw [one_smul]

namespace FiniteLeftModule
variable (X : FiniteLeftModule k R)

def twistedEvaluationEquiv : (evaluated X (twistedFiniteModule σ)).carrier ≃ₗ[R]
    TwistedLeftModule k R σ X.carrier :=
  (BalancedTensor.congrLeft (twistedEvaluationCoordinates σ) (LinearEquiv.refl k X.carrier)
    (twistedEvaluationCoordinates_right σ) (fun _ _ => rfl)
    (twistedEvaluationCoordinates_left σ)).trans (TwistedBimodule.tensorUntwist σ)

@[simp] theorem twistedEvaluationEquiv_tmul
    (r : EnvelopingBimodule k R (twistedFiniteModule σ).carrier) (x : X.carrier) :
    twistedEvaluationEquiv σ X (BalancedTensor.tmul r x) =
      ⟨σ.symm r.value.value • x⟩ := rfl

end FiniteLeftModule
end ArExplicit

end

end OAI
