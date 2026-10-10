import OAI.Algebra.AuslanderReiten.Tensor.BalancedTensorCompleteAction
import OAI.Algebra.AuslanderReiten.Tensor.BalancedTensorNativeEvaluation

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit.BalancedTensor
universe u
variable {k R F : Type u} [Field k] [Ring R] [Algebra k R]
variable [AddCommGroup F] [Module k F] [Module Rᵐᵒᵖ F] [Module R F]
variable [SMulCommClass k R F] [SMulCommClass R Rᵐᵒᵖ F]
variable (M : FiniteLeftModule k R)
variable (e : BalancedTensor k R F M.carrier ≃ₗ[R] M.carrier)

theorem nativeEvaluationIso_tmul (f : F) (m : M.carrier) :
    (nativeEvaluationIso M e).hom.hom
      (letI := moduleCatBaseModule (k := k) (R := R) M.carrier; tmul f m) = e (tmul f m) :=
  tensorEvaluationIso_tmul M.carrier e f m

end ArExplicit.BalancedTensor

end

end OAI
