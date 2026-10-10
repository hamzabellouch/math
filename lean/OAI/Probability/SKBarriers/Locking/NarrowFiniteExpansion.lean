import Mathlib
import OAI.Probability.SKBarriers.Locking.NarrowScheduleMass
import OAI.Probability.SKBarriers.Locking.NarrowRetainedStats
import OAI.Probability.SKBarriers.Locking.NarrowBaseFactor

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem narrowSchedule_value_expansion (c v w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ))
    (hv : weightedUnderlying v=weightedUnderlying w)
    (hm : ∀ p∈weightedUnderlying c++weightedUnderlying w++t,p.1∈Icc (0:ℝ) 1)
    (hs : (weightedUnderlying c++weightedUnderlying w++t).Pairwise (fun p q => p.1≤q.1))
    {a δ : ℝ} (ha : 0<a) (hδ : 4*δ^2≤a) (hδ1 : |δ|≤1)
    (hsmall : a*(4*narrowVariance c v w+(2*narrowAbsCross c v w)^2)≤1/2) :
    vectorIncrementChain (narrowSchedule δ c v w t) (fun x => ∑ u,scalarSpinTerminal (x u)) 0≤
      3*scalarIncrementChain (weightedUnderlying c++weightedUnderlying w++t) scalarSpinTerminal 0+
      δ^2*narrowBaseQuadratic c v w t+tripleExpansionConstant a*|δ|^3 := by
  have hm0 : ∀ p∈weightedUnderlying c++weightedUnderlying w,p.1∈Icc (0:ℝ) 1 :=
    fun p hp => hm p (List.mem_append_left _ hp)
  have hm1 := narrowRetainedPrefix_mass c v w hv hm0
  have hs1 := narrowRetainedPrefix_monotone c v w hv (fun p hp => (hm0 p hp).1) (List.pairwise_append.mp hs).1
  have hmt : ∀ p∈t,p.1∈Icc (0:ℝ) 1 := fun p hp => hm p (List.mem_append_right _ hp)
  have hst := (List.pairwise_append.mp hs).2.1
  have hsmall' : a*(4*((narrowRetainedPrefix c v w).map (fun p => (p.2.1.2+p.2.2.2)^2)).sum+
      (2*((narrowRetainedPrefix c v w).map (fun p => |p.2.1.2+p.2.2.2| * (|p.2.1.1|+2*|p.2.2.1|))).sum)^2)≤1/2 := by
    simpa only [narrowRetainedPrefix_variance,narrowRetainedPrefix_score] using hsmall
  have H := narrowRetained_expansion (narrowRetainedPrefix c v w) t hm1 hs1 hmt hst ha hδ hδ1 hsmall'
  dsimp only at H
  rw [narrowRetainedPrefix_value c v w hv (scalarIncrementChain_regular t scalarSpinTerminal_regular)] at H
  have hid : narrowSchedule δ c v w t=
      (narrowRetainedPrefix c v w).map (fun p => (p.1,narrowRetainedEmbedding δ p.2))++tripleTailSchedule t :=
    (narrowRetainedPrefix_image δ c v w).symm
  rw [hid,vectorIncrementChain_append]
  have he : (fun x : Fin 3 → ℝ => ∑ u,scalarSpinTerminal (x u))=
      fun x => scalarSpinTerminal (x 0)+scalarSpinTerminal (x 1)+scalarSpinTerminal (x 2) := by
    funext x; simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]; exact (add_assoc _ _ _).symm
  rw [he,tripleTailSchedule_value scalarSpinTerminal_regular scalarSpinTerminal_regular scalarSpinTerminal_regular]
  simpa only [scalarIncrementChain_append,narrowBaseQuadratic] using H

end SK.Analytic

end
end

end OAI
