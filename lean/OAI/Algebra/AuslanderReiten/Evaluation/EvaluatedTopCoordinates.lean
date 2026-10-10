import OAI.Algebra.AuslanderReiten.Evaluation.EvaluatedMiddleCoordinates

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "R₀" => A k q
local notation "X₀" => A.simpleFiniteModule q
local notation "D₀" => bimoduleTwoConeData q
local notation "hf₀" => bimodule_term_finite_k q

theorem evaluatedTopAdjacent (n : ℕ) :
    (FiniteLeftModule.evaluationMap X₀
      (M := TwoCone.skeletonCokernelModule D₀ hf₀ n)
      (N := TwoCone.middleCokernelModule D₀ hf₀ n)
      (TwoCone.singletonCokernelProjection D₀ n)).comp
      (FiniteLeftModule.evaluationMap X₀
        (M := TwoCone.baseCokernelModule D₀ hf₀ (n+5))
        (N := TwoCone.skeletonCokernelModule D₀ hf₀ n)
        (-(TwoCone.topAttachingCokernel D₀ n))) =
    FiniteLeftModule.evaluationMap X₀
      (M := TwoCone.baseCokernelModule D₀ hf₀ (n+5))
      (N := TwoCone.middleCokernelModule D₀ hf₀ n)
      (-(TwoCone.columnCokernelMap D₀ n)) := by
  rw [← FiniteLeftModule.evaluationMap_comp, LinearMap.comp_neg,
    TwoCone.topAttachingCokernel_adjacent]

theorem evaluatedTopAdjacent_fst (n : ℕ) :
    ((evaluatedSingletonFst q n).comp
      (FiniteLeftModule.evaluationMap X₀
        (M := TwoCone.skeletonCokernelModule D₀ hf₀ n)
        (N := TwoCone.middleCokernelModule D₀ hf₀ n)
        (TwoCone.singletonCokernelProjection D₀ n))).comp
      (FiniteLeftModule.evaluationMap X₀
        (M := TwoCone.baseCokernelModule D₀ hf₀ (n+5))
        (N := TwoCone.skeletonCokernelModule D₀ hf₀ n)
        (-(TwoCone.topAttachingCokernel D₀ n))) =
    -(FiniteLeftModule.evaluationMap X₀
      (M := TwoCone.baseCokernelModule D₀ hf₀ (n+5))
      (N := TwoCone.baseCokernelModule D₀ hf₀ (n+2))
      (TwoCone.secondCokernelMap D₀ (n+2))) := by
  rw [LinearMap.comp_assoc, evaluatedTopAdjacent, evaluatedColumn_fst]

theorem evaluatedTopAdjacent_snd (n : ℕ) :
    ((evaluatedSingletonSnd q n).comp
      (FiniteLeftModule.evaluationMap X₀
        (M := TwoCone.skeletonCokernelModule D₀ hf₀ n)
        (N := TwoCone.middleCokernelModule D₀ hf₀ n)
        (TwoCone.singletonCokernelProjection D₀ n))).comp
      (FiniteLeftModule.evaluationMap X₀
        (M := TwoCone.baseCokernelModule D₀ hf₀ (n+5))
        (N := TwoCone.skeletonCokernelModule D₀ hf₀ n)
        (-(TwoCone.topAttachingCokernel D₀ n))) =
    FiniteLeftModule.evaluationMap X₀
      (M := TwoCone.baseCokernelModule D₀ hf₀ (n+5))
      (N := TwoCone.baseCokernelModule D₀ hf₀ (n+2))
      (TwoCone.firstCokernelMap D₀ (n+2)) := by
  rw [LinearMap.comp_assoc, evaluatedTopAdjacent, evaluatedColumn_snd]

end ArExplicit.T

end

end OAI
