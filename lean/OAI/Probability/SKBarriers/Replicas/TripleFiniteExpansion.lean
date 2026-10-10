import Mathlib
import OAI.Probability.SKBarriers.Replicas.TripleRetainedStats
import OAI.Probability.SKBarriers.Replicas.TripleRetainedExpansion

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

def tripleBaseQuadratic (c : List (ℝ × ℝ)) (w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ)) : ℝ :=
  let f := scalarIncrementChain t scalarSpinTerminal
  scalarIncrementAverage c (scalarIncrementChain (weightedUnderlying w) f)
    (fun x => vectorIncrementAverage w (fun q : ℝ × ℝ => f q.1) (fun q => q.2^2) (x,0)*
      scalarIncrementAverage (weightedUnderlying w) f (rootHessian 0 f) x) 0

def tripleExpansionConstant (a : ℝ) : ℝ :=
  ((2*(susceptibilityLipschitzConstant:ℝ)*(1+2/a^2)+32/a^2)*2)

theorem tripleSchedule_value_expansion (c : List (ℝ × ℝ)) (w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ))
    (hm : ∀ p∈c++weightedUnderlying w++t,p.1∈Icc (0:ℝ) 1)
    (hs : (c++weightedUnderlying w++t).Pairwise (fun p q => p.1≤q.1))
    {a δ : ℝ} (ha : 0<a) (hδ : 4*δ^2≤a) (hδ1 : |δ|≤1)
    (hsmall : a*(4*weightedVariance w+(2*weightedAbsCross w)^2)≤1/2) :
    vectorIncrementChain (tripleSchedule δ c w t) (fun x => ∑ u,scalarSpinTerminal (x u)) 0≤
      3*scalarIncrementChain (c++weightedUnderlying w++t) scalarSpinTerminal 0+
      δ^2*tripleBaseQuadratic c w t+tripleExpansionConstant a*|δ|^3 := by
  let l := tripleRetainedPrefix c w
  have hm0 : ∀ p∈c++weightedUnderlying w,p.1∈Icc (0:ℝ) 1 :=
    fun p hp => hm p (List.mem_append_left _ hp)
  have hm1 := tripleRetainedPrefix_mass c w hm0
  have hs1 := tripleRetainedPrefix_monotone c w (fun p hp => (hm0 p hp).1) (List.pairwise_append.mp hs).1
  have hmt : ∀ i : Fin t.length,(t.get i).1∈Icc (0:ℝ) 1 :=
    fun i => hm _ (List.mem_append_right _ (List.get_mem t i))
  have hst := mass_get_monotone (List.pairwise_append.mp hs).2.1
  have hsmall' : a*(4*(∑ i : Fin l.length,((l.get i).2.1.2)^2)+
      (2*∑ i : Fin l.length, |(l.get i).2.1.2| * (|(l.get i).2.1.1|+2*|(l.get i).2.2|))^2)≤1/2 := by
    rw [sum_get_map l (fun p => p.2.1.2^2),
      sum_get_map l (fun p => |p.2.1.2| * (|p.2.1.1|+2*|p.2.2|))]
    simpa only [l,tripleRetainedPrefix_variance,tripleRetainedPrefix_score] using hsmall
  have H := tripleRetained_expansion l.length t.length (fun i => (l.get i).1) (fun i => (l.get i).2)
    (fun i => (t.get i).1) (fun i => (t.get i).2) (fun i => hm1 _ (List.get_mem l i))
    (mass_get_monotone hs1) hmt hst ha hδ hδ1 hsmall'
  dsimp only at H
  rw [← scalarIncrementChain_get] at H
  have hmap : List.ofFn (fun i : Fin l.length => ((l.get i).1,tripleRetainedEmbedding δ (l.get i).2))=
      l.map (fun p => (p.1,tripleRetainedEmbedding δ p.2)) := by
    simpa only [List.ofFn_get,Function.comp_def] using
      (List.map_ofFn (f:=l.get) (g:=fun p => (p.1,tripleRetainedEmbedding δ p.2))).symm
  rw [← vectorIncrementChain_ofFn,hmap,← vectorIncrementChain_get,← vectorIncrementAverage_get] at H
  have hf := scalarIncrementChain_regular t scalarSpinTerminal_regular
  rw [tripleRetainedPrefix_value c w hf,tripleRetainedPrefix_average c w hf] at H
  have hid : tripleSchedule δ c w t=(l.map (fun p => (p.1,tripleRetainedEmbedding δ p.2)))++tripleTailSchedule t := by
    rw [tripleRetainedPrefix_image]
    simp only [tripleSchedule,tripleTailSchedule,List.flatMap_nil,List.append_nil]
  rw [hid,vectorIncrementChain_append]
  have he : (fun x : Fin 3 → ℝ => ∑ u,scalarSpinTerminal (x u))=
      fun x => scalarSpinTerminal (x 0)+scalarSpinTerminal (x 1)+scalarSpinTerminal (x 2) := by
    funext x; simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]; exact (add_assoc _ _ _).symm
  rw [he,tripleTailSchedule_value scalarSpinTerminal_regular scalarSpinTerminal_regular scalarSpinTerminal_regular]
  simpa only [scalarIncrementChain_append,tripleBaseQuadratic,tripleExpansionConstant] using H

end SK.Analytic

end
end

end OAI
