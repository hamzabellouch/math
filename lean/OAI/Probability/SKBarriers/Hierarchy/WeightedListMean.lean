import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.WeightedListBridge
import OAI.Probability.SKBarriers.Replicas.TripleRetainedStats
import OAI.Probability.SKBarriers.Scalar.ScalarWeightedMean

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

def weightedMean (w : List (ℝ × (ℝ × ℝ))) : ℝ := (w.map (fun p => p.2.2*p.2.1*p.1)).sum

theorem weightedList_spin_mean (w : List (ℝ × (ℝ × ℝ))) (x : ℝ) :
    vectorIncrementAverage w (fun p : ℝ × ℝ => scalarSpinTerminal p.1) (fun p => p.2) (x,0)=
      weightedMean w*deriv (scalarIncrementChain (weightedUnderlying w) scalarSpinTerminal) x := by
  rw [vectorIncrementAverage_get]
  change vectorHierarchyAverage w.length (fun i => (w.get i).1)
    (fun i => ((w.get i).2.1,(w.get i).2.2)) _ _ _=_
  rw [scalarWeightedTest_integral _ _ _ _ scalarSpinTerminal_regular continuous_snd
    (HasExpGrowth.linear (ContinuousLinearMap.snd ℝ ℝ ℝ)),scalarPath_weighted_mean]
  rw [sum_get_map w (fun p => p.2.2*p.2.1*p.1)]
  congr 2
  have H := vectorIncrementChain_get w (fun p : ℝ × ℝ => scalarSpinTerminal p.1)
  rw [weightedBranch_value] at H
  have H' := congrArg (fun F : ℝ × ℝ → ℝ => fun y => F (y,0)) H
  have Hhier := congrArg (fun F : ℝ × ℝ → ℝ => fun y => F (y,0))
    (vectorHierarchy_pullback (ContinuousLinearMap.fst ℝ ℝ ℝ) w.length
      (fun i => (w.get i).1) (fun i => (w.get i).2) scalarSpinTerminal)
  rw [vectorHierarchy_real] at Hhier
  exact (H'.trans Hhier).symm

theorem zeroWeightChain_average_noise {f : ℝ → ℝ} (hf : BoundedDerivs f) (t : List (ℝ × ℝ)) (g : ℝ → ℝ) :
    vectorIncrementAverage (zeroWeightChain t) (fun p : ℝ × ℝ => f p.1) (fun p => g p.2)=fun p => g p.2 := by
  induction t with
  | nil => rfl
  | cons p t ih =>
    change vectorStepAverage p.1 (p.2,0) (vectorIncrementChain (zeroWeightChain t) (fun p : ℝ × ℝ => f p.1))
      (vectorIncrementAverage (zeroWeightChain t) (fun p : ℝ × ℝ => f p.1) (fun p => g p.2))=_
    rw [ih]
    apply vectorStepAverage_frozen (vectorIncrementChain_regular _ (hf.compCLM (ContinuousLinearMap.fst ℝ ℝ ℝ)))
    intro x s
    simp only [Prod.snd_add,Prod.smul_snd,smul_zero,add_zero]

@[simp] theorem weightedMean_append (v w : List (ℝ × (ℝ × ℝ))) : weightedMean (v++w)=weightedMean v+weightedMean w := by
  simp only [weightedMean,List.map_append,List.sum_append]

@[simp] theorem weightedMean_zeroWeight (t : List (ℝ × ℝ)) : weightedMean (zeroWeightChain t)=0 := by
  simp [weightedMean,zeroWeightChain,List.map_map,Function.comp_def]

theorem weightedList_tail_mean (w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ)) (x : ℝ) :
    vectorIncrementAverage w (fun p : ℝ × ℝ => scalarIncrementChain t scalarSpinTerminal p.1)
      (fun p => p.2) (x,0)=
      weightedMean w*deriv (scalarIncrementChain (weightedUnderlying w++t) scalarSpinTerminal) x := by
  have H := weightedList_spin_mean (w++zeroWeightChain t) x
  rw [vectorIncrementAverage_append,zeroWeightChain_average_noise scalarSpinTerminal_regular t (fun y => y),
    weightedBranch_value,weightedUnderlying_zeroWeight,weightedMean_append,weightedMean_zeroWeight,add_zero,
    weightedUnderlying_append,weightedUnderlying_zeroWeight] at H
  exact H

end SK.Analytic

end
end

end OAI
