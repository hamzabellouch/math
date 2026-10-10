import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarResponseBounds
import OAI.Probability.SKBarriers.Scalar.ScalarWeightedVector
import OAI.Probability.SKBarriers.Replicas.TripleRetainedStats

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem finiteClockPenalty_eq_chain (n : ℕ) (m a : Fin n → ℝ) :
    finiteClockPenalty n m a=chainPotentialPenalty (fun x : ℝ => x^2) (List.ofFn (fun i => (m i,a i))) 0 := by
  rw [chainPotentialPenalty_ofFn]
  simp only [finiteClockPenalty,strictPrefix,zero_add,Finset.sum_sub_distrib,mul_sub]

theorem weightedCrossPenalty_get (w : List (ℝ × (ℝ × ℝ))) :
    weightedCrossPenalty w 0=finiteClockPenalty w.length (fun i => (w.get i).1)
      (fun i => (w.get i).2.1*(w.get i).2.2) := by
  rw [finiteClockPenalty_eq_chain]
  unfold weightedCrossPenalty
  congr 1
  simpa only [List.ofFn_get,Function.comp_def] using
    (List.map_ofFn (f:=w.get) (g:=fun p => (p.1,p.2.1*p.2.2)))

theorem weightedList_spin_response_le (w : List (ℝ × (ℝ × ℝ))) (k : Fin w.length → ℝ)
    (hm : ∀ p∈w,0≤p.1) (hk : ∀ i,0≤k i)
    (he : ∀ i,(w.get i).2.2=k i*(w.get i).2.1) (R : ℝ)
    (hR : ∀ i,k i≠0 → scalarFiniteResponse w.length (fun j => (w.get j).1)
      (fun j => (w.get j).2.1) i 0≤R) :
    vectorIncrementAverage w (fun p : ℝ × ℝ => scalarSpinTerminal p.1) (fun p => p.2^2) (0,0)≤
      weightedVariance w+R*weightedCrossPenalty w 0 := by
  rw [vectorIncrementAverage_get]
  have H := scalarWeightedAverage_spin_le w.length (fun i => (w.get i).1) (fun i => (w.get i).2.1) k
    (fun i => hm _ (List.get_mem w i)) hk 0 R hR
  have hev : (fun i : Fin w.length => ((w.get i).2.1,k i*(w.get i).2.1))=fun i => (w.get i).2 := by
    funext i; rw [← he i]
  have hs : (∑ i : Fin w.length,(k i)^2*((w.get i).2.1)^2)=weightedVariance w := by
    simp_rw [← mul_pow,← he]
    exact sum_get_map w (fun p => p.2.2^2)
  have hp : finiteClockPenalty w.length (fun i => (w.get i).1) (fun i => k i*((w.get i).2.1)^2)=
      weightedCrossPenalty w 0 := by
    rw [weightedCrossPenalty_get]
    congr 1
    funext i; rw [he i]; ring
  simpa only [scalarWeightedAverage,hev,hs,hp] using H

theorem weightedList_spin_early_le (w : List (ℝ × (ℝ × ℝ))) (k : Fin w.length → ℝ)
    (hm : ∀ p∈w,p.1∈Icc (0:ℝ) 1) (hs : w.Pairwise (fun p q => p.1≤q.1))
    (hk : ∀ i,0≤k i) (he : ∀ i,(w.get i).2.2=k i*(w.get i).2.1)
    {V : ℝ} (hV : 0≤V)
    (hactive : ∀ i,k i≠0 → scalarPrefixVariance w.length (fun j => (w.get j).2.1) i.castSucc≤V) :
    vectorIncrementAverage w (fun p : ℝ × ℝ => scalarSpinTerminal p.1) (fun p => p.2^2) (0,0)≤
      weightedVariance w+(rootHessian 0 (scalarIncrementChain (weightedUnderlying w) scalarSpinTerminal) 0+
        (2*V+4*V^2))*weightedCrossPenalty w 0 := by
  apply weightedList_spin_response_le w k (fun p hp => (hm p hp).1) hk he
  intro i hi
  have H := scalarFiniteResponse_origin_le w.length (fun j => (w.get j).1) (fun j => (w.get j).2.1)
    (fun j => hm _ (List.get_mem w j)) (mass_get_monotone hs) i
  have Hsq := (sq_le_sq₀ (scalarPrefixVariance_nonneg w.length (fun j => (w.get j).2.1) i.castSucc) hV).mpr (hactive i hi)
  have hchain : scalarHierarchy w.length (fun j => (w.get j).1) (fun j => (w.get j).2.1) scalarSpinTerminal=
      scalarIncrementChain (weightedUnderlying w) scalarSpinTerminal := by
    rw [← scalarIncrementChain_ofFn]
    congr 1
    simpa only [List.ofFn_get,Function.comp_def,weightedUnderlying] using
      (List.map_ofFn (f:=w.get) (g:=fun p => (p.1,p.2.1))).symm
  rw [hchain] at H
  nlinarith [hactive i hi]

end SK.Analytic

end
end

end OAI
