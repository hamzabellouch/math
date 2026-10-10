import OAI.Algebra.AuslanderReiten.Coordinates.TensorNormalizedTop
import OAI.Algebra.AuslanderReiten.Resolutions.FiniteResolutionEvaluation
import OAI.Algebra.AuslanderReiten.Cones.ConcreteTwoConeEvaluation

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H : kˣ)

def evaluatedFiniteTargetTop :
    (HomotopyCategory.quotient _ _).obj
      ((FiniteLeftModule.evaluated (A.simpleFiniteModule q) (fiberTarget q)).completeCochain
        (AFrobeniusTrace k q)) ⟶
    (HomotopyCategory.quotient _ _).obj
      ((FiniteLeftModule.evaluated (A.simpleFiniteModule q)
        (TwoCone.baseCokernelModule (bimoduleTwoConeData q) (bimodule_term_finite_k q) 1)).completeCochain
          (AFrobeniusTrace k q)) :=
  FiniteLeftModule.evaluationResolutionMap (A.simpleFiniteModule q)
    (AEnvelopingFrobeniusTrace k q) (AFrobeniusTrace k q) (finiteTargetTop q)

theorem normalizedLift_evaluated_top :
    (HomotopyCategory.quotient _ _).map
      (FiniteLeftModule.resolutionMap (AFrobeniusTrace k q)
        (FiniteLeftModule.evaluationMap (A.simpleFiniteModule q)
          (M := twistedFiniteModule (sourceTwist q H)) (N := fiberTarget q)
          (normalizedLift q H).hom)) ≫ evaluatedFiniteTargetTop q =
    (HomotopyCategory.quotient _ _).map
      (FiniteLeftModule.resolutionMap (AFrobeniusTrace k q)
        (FiniteLeftModule.evaluationMap (A.simpleFiniteModule q)
          (M := twistedFiniteModule (sourceTwist q H))
          (N := TwoCone.baseCokernelModule (bimoduleTwoConeData q) (bimodule_term_finite_k q) 1)
          (normalizedSourceTop q H))) := by
  exact FiniteLeftModule.evaluationResolutionMap_triangle (A.simpleFiniteModule q)
    (AEnvelopingFrobeniusTrace k q) (AFrobeniusTrace k q)
    (normalizedLift q H).hom (normalizedSourceTop q H) (finiteTargetTop q)
    (normalizedLift_top q H)

end ArExplicit.T

end

end OAI
