import Mathlib
import OAI.Probability.SKBarriers.Replicas.TripleScaleStats
import OAI.Probability.SKBarriers.Locking.NarrowRetainedStats

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix
namespace SK.Analytic

theorem narrowCommonSchedule_scale (β δ : ℝ) (c : List (ℝ × (ℝ × ℝ))) :
    scaleIncrementChain β (narrowCommonSchedule δ c)=narrowCommonSchedule δ (scaleIncrementChain β c) := by
  simp only [scaleIncrementChain,narrowCommonSchedule,List.map_map]
  apply List.map_congr_left
  intro p hp
  apply Prod.ext
  · rfl
  · ext i; fin_cases i <;> norm_num [Function.comp_def,smul_eq_mul] <;> ring

theorem narrowMiddleSchedule_scale (β δ : ℝ) (l : List NarrowMiddleIncrement) :
    scaleIncrementChain β (narrowMiddleSchedule δ l)=
      narrowMiddleSchedule δ (l.map (mapProductIncrement (fun x : ℝ × ℝ => β • x) (fun x : ℝ × ℝ => β • x))) := by
  simp only [scaleIncrementChain,narrowMiddleSchedule,List.map_map]
  apply List.map_congr_left
  intro p hp
  apply Prod.ext
  · simp only [Function.comp_def,productMass_map]
  · cases p <;> ext i <;> fin_cases i <;>
      norm_num [Function.comp_def,mapProductIncrement,narrowMiddleVector,smul_eq_mul] <;> ring

theorem narrowSchedule_scale (β δ : ℝ) (c v w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ)) :
    scaleIncrementChain β (narrowSchedule δ c v w t)=
      narrowSchedule δ (scaleIncrementChain β c) (scaleIncrementChain β v)
        (scaleIncrementChain β w) (scaleIncrementChain β t) := by
  simp only [narrowSchedule,scaleIncrementChain_append,narrowCommonSchedule_scale,narrowMiddleSchedule_scale,
    tripleTailSchedule_scale,mergedProductBranches_map]
  rfl

theorem narrowVariance_scale (β : ℝ) (c v w : List (ℝ × (ℝ × ℝ))) :
    narrowVariance (scaleIncrementChain β c) (scaleIncrementChain β v) (scaleIncrementChain β w)=β^2*narrowVariance c v w := by
  simp only [narrowVariance,weightedVariance_scale]
  ring

theorem narrowAbsCross_scale (β : ℝ) (c v w : List (ℝ × (ℝ × ℝ))) :
    narrowAbsCross (scaleIncrementChain β c) (scaleIncrementChain β v) (scaleIncrementChain β w)=β^2*narrowAbsCross c v w := by
  simp only [narrowAbsCross,weightedAbsCross_scale]
  ring

end SK.Analytic

end
end

end OAI
