import OAI.Algebra.AuslanderReiten.Evaluation.TensorEvaluatedTop
import OAI.Algebra.AuslanderReiten.Fibers.ConcreteFiberComponentMaps

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H : kˣ)

def normalizedBranchTop : (A.simpleFiniteModule q).carrier →ₗ[A k q]
    (evaluatedBaseModule q 1).carrier :=
  (FiniteLeftModule.evaluationMap (A.simpleFiniteModule q)
    (M := twistedFiniteModule (sourceTwist q H))
    (N := TwoCone.baseCokernelModule (bimoduleTwoConeData q) (bimodule_term_finite_k q) 1)
    (normalizedSourceTop q H)).comp (evaluatedTwistEquiv q H).symm.toLinearMap

theorem branchHom_top :
    branchHom q H ≫ evaluatedFiniteTargetTop q =
      (HomotopyCategory.quotient _ _).map
        (FiniteLeftModule.resolutionMap (AFrobeniusTrace k q) (normalizedBranchTop q H)) := by
  unfold branchHom evaluatedBranchMap normalizedBranchTop
  rw [FiniteLeftModule.resolutionMap_comp, Category.assoc,
    normalizedLift_evaluated_top, ← FiniteLeftModule.resolutionMap_comp]

end ArExplicit.T

end

end OAI
