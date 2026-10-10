import Mathlib
import OAI.Probability.SKBarriers.Locking.NarrowRetainedExpansion

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem narrowRetainedCommon_variance (c : List (ℝ × (ℝ × ℝ))) :
    ((narrowRetainedCommon c).map (fun p => (p.2.1.2+p.2.2.2)^2)).sum=weightedVariance c := by
  simp only [narrowRetainedCommon,List.map_map,Function.comp_def,zero_add,weightedVariance]

theorem narrowRetainedCommon_score (c : List (ℝ × (ℝ × ℝ))) :
    ((narrowRetainedCommon c).map (fun p => |p.2.1.2+p.2.2.2| * (|p.2.1.1|+2*|p.2.2.1|))).sum=
      3*weightedAbsCross c := by
  simp only [narrowRetainedCommon,List.map_map,Function.comp_def,zero_add,weightedAbsCross]
  rw [← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro p _
  ring

theorem narrowRetainedMiddle_variance (l : List NarrowMiddleIncrement) :
    ((narrowRetainedMiddle l).map (fun p => (p.2.1.2+p.2.2.2)^2)).sum=
      weightedVariance (productLeft l)+weightedVariance (productRight l) := by
  induction l with
  | nil => simp [narrowRetainedMiddle,productLeft,productRight,weightedVariance]
  | cons p l ih =>
    cases p <;> simp only [narrowRetainedMiddle,List.map_cons,List.map_map,Function.comp_def,List.sum_cons,
      productVector,Prod.snd_zero,productLeft,productRight,List.filterMap_cons,weightedVariance,List.map_cons,List.sum_cons,
      add_zero,zero_add] at ih ⊢ <;> rw [ih] <;> ring

theorem narrowRetainedMiddle_score (l : List NarrowMiddleIncrement) :
    ((narrowRetainedMiddle l).map (fun p => |p.2.1.2+p.2.2.2| * (|p.2.1.1|+2*|p.2.2.1|))).sum=
      weightedAbsCross (productLeft l)+2*weightedAbsCross (productRight l) := by
  induction l with
  | nil => simp [narrowRetainedMiddle,productLeft,productRight,weightedAbsCross]
  | cons p l ih =>
    cases p <;> simp only [narrowRetainedMiddle,List.map_cons,List.map_map,Function.comp_def,List.sum_cons,
      productVector,Prod.fst_zero,Prod.snd_zero,productLeft,productRight,List.filterMap_cons,weightedAbsCross,List.map_cons,List.sum_cons,
      abs_zero,mul_zero,add_zero,zero_add] at ih ⊢ <;> rw [ih] <;> ring

def narrowVariance (c v w : List (ℝ × (ℝ × ℝ))) := weightedVariance c+weightedVariance v+weightedVariance w
def narrowAbsCross (c v w : List (ℝ × (ℝ × ℝ))) := 3*weightedAbsCross c+weightedAbsCross v+2*weightedAbsCross w

theorem narrowRetainedPrefix_variance (c v w : List (ℝ × (ℝ × ℝ))) :
    ((narrowRetainedPrefix c v w).map (fun p => (p.2.1.2+p.2.2.2)^2)).sum=narrowVariance c v w := by
  simp only [narrowRetainedPrefix,List.map_append,List.sum_append,narrowRetainedCommon_variance,
    narrowRetainedMiddle_variance,mergedProductBranches_left,mergedProductBranches_right,narrowVariance,add_assoc]

theorem narrowRetainedPrefix_score (c v w : List (ℝ × (ℝ × ℝ))) :
    ((narrowRetainedPrefix c v w).map (fun p => |p.2.1.2+p.2.2.2| * (|p.2.1.1|+2*|p.2.2.1|))).sum=
      narrowAbsCross c v w := by
  simp only [narrowRetainedPrefix,List.map_append,List.sum_append,narrowRetainedCommon_score,
    narrowRetainedMiddle_score,mergedProductBranches_left,mergedProductBranches_right,narrowAbsCross,add_assoc]

end SK.Analytic

end
end

end OAI
