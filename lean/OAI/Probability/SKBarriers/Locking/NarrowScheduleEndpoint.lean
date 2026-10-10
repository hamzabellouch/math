import Mathlib
import OAI.Probability.SKBarriers.Replicas.TripleScheduleEndpoint
import OAI.Probability.SKBarriers.Locking.NarrowScheduleMass
import OAI.Probability.SKBarriers.Locking.NarrowRetainedStats

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

@[simp] theorem narrowClockPerturbed_zero (a b c r q δ : ℝ) :
    narrowClockPerturbed a b c r q δ 0 0 0=tripleClockMatrix a b c r q := by
  rw [narrowClockPerturbed_pair_zero,tripleClockPerturbed_zero]

def narrowCrossPenalty (c v w : List (ℝ × (ℝ × ℝ))) : ℝ :=
  weightedCrossPenalty c 0+weightedCrossPenalty v (weightedCross c)+weightedCrossPenalty w (weightedCross c)

def narrowQuarticPenalty (c v w : List (ℝ × (ℝ × ℝ))) : ℝ :=
  weightedVariancePenalty c 0/3+narrowNoisePenalty (mergedProductBranches v w) (weightedVariance c)

theorem narrowSchedule_covariance (δ : ℝ) (c v w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ))
    (hv : weightedUnderlying v=weightedUnderlying w) (hy : weightedCross c+weightedCross w=0) :
    matrixChainCovariance (narrowSchedule δ c v w t)=
      tripleClockPerturbed (rawVariance (weightedUnderlying c++weightedUnderlying w++t))
        (rawVariance (weightedUnderlying c++weightedUnderlying w++t))
        (rawVariance (weightedUnderlying c++weightedUnderlying w++t)) (rawVariance (weightedUnderlying c))
        (rawVariance (weightedUnderlying c++weightedUnderlying w)) δ
        (weightedCross c+weightedCross v) (narrowVariance c v w) := by
  have hc := narrowCommonSchedule_covariance δ c 0 0 0
  simp only [narrowClockPerturbed_zero,tripleClockMatrix_zero,zero_add] at hc
  have hm := narrowMiddleSchedule_covariance δ (mergedProductBranches v w)
    (rawVariance (weightedUnderlying c)) (rawVariance (weightedUnderlying c)) (rawVariance (weightedUnderlying c))
    (weightedCross c) (weightedCross c) (weightedVariance c)
  simp only [mergedProductBranches_left,mergedProductBranches_right,hv,hy,narrowClockPerturbed_pair_zero] at hm
  simp only [narrowSchedule,matrixChainCovariance_append,hc]
  rw [hm,tripleTailSchedule_covariance]
  simp only [rawVariance_append,narrowVariance]

theorem narrowSchedule_penalty (δ : ℝ) (c v w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ))
    (hv : weightedUnderlying v=weightedUnderlying w) (hy : weightedCross c+weightedCross w=0) :
    matrixChainPenalty (narrowSchedule δ c v w t) 0=
      3*rawPenalty (weightedUnderlying c++weightedUnderlying w++t) 0+
      4*δ^2*(narrowCrossPenalty c v w+narrowVariance c v w*rawArea t)+
      4*δ^4*narrowQuarticPenalty c v w := by
  have hc := narrowCommonSchedule_covariance δ c 0 0 0
  simp only [narrowClockPerturbed_zero,tripleClockMatrix_zero,zero_add] at hc
  have hpc := narrowCommonSchedule_penalty δ c 0 0 0
  simp only [narrowClockPerturbed_zero,tripleClockMatrix_zero] at hpc
  have hm := narrowMiddleSchedule_covariance δ (mergedProductBranches v w)
    (rawVariance (weightedUnderlying c)) (rawVariance (weightedUnderlying c)) (rawVariance (weightedUnderlying c))
    (weightedCross c) (weightedCross c) (weightedVariance c)
  simp only [mergedProductBranches_left,mergedProductBranches_right,hv,hy,narrowClockPerturbed_pair_zero] at hm
  have hpm := narrowMiddleSchedule_penalty δ (mergedProductBranches v w)
    (rawVariance (weightedUnderlying c)) (rawVariance (weightedUnderlying c)) (rawVariance (weightedUnderlying c))
    (weightedCross c) (weightedCross c) (weightedVariance c)
  simp only [mergedProductBranches_left,mergedProductBranches_right,hv] at hpm
  simp only [narrowSchedule,matrixChainPenalty_append,matrixChainCovariance_append,zero_add,hc,hpc,hm,hpm,
    tripleTailSchedule_penalty,rawPenalty_append,rawVariance_append,narrowCrossPenalty,narrowVariance,narrowQuarticPenalty]
  ring

theorem narrowNoisePenalty_nonneg (l : List NarrowMiddleIncrement)
    (hm : ∀ p∈l,0≤productMass p) {K : ℝ} (hK : 0≤K) : 0≤narrowNoisePenalty l K := by
  induction l generalizing K with
  | nil => rfl
  | cons p l ih =>
    change 0≤productMass p*((K+(narrowMiddleNoise p)^2)^2-K^2)+narrowNoisePenalty l (K+(narrowMiddleNoise p)^2)
    apply add_nonneg
    · apply mul_nonneg (hm p (List.mem_cons_self ..))
      nlinarith [sq_nonneg (narrowMiddleNoise p)]
    · exact ih (fun q hq => hm q (List.mem_cons_of_mem _ hq)) (by positivity)

theorem narrowQuarticPenalty_nonneg (c v w : List (ℝ × (ℝ × ℝ)))
    (hc : ∀ p∈c,0≤p.1) (hv : ∀ p∈v,0≤p.1) (hw : ∀ p∈w,0≤p.1) :
    0≤narrowQuarticPenalty c v w := by
  apply add_nonneg (div_nonneg (weightedVariancePenalty_nonneg c hc le_rfl) (by norm_num))
  apply narrowNoisePenalty_nonneg
  · intro p hp
    simp only [mergedProductBranches,List.mem_merge,List.mem_map] at hp
    rcases hp with ⟨q,hq,rfl⟩|⟨q,hq,rfl⟩
    · exact hv q hq
    · exact div_nonneg (hw q hq) (by norm_num)
  · unfold weightedVariance
    exact List.sum_nonneg (fun x hx => by obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hx; positivity)

theorem narrowConstrainedPressure_schedule {N : ℕ} (hN : 0<N) (β δ : ℝ)
    (c v w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ))
    (hv : weightedUnderlying v=weightedUnderlying w) (hy : weightedCross c+weightedCross w=0)
    (hm : ∀ p∈weightedUnderlying c++weightedUnderlying w++t,p.1∈Icc (0:ℝ) 1)
    (hs : (weightedUnderlying c++weightedUnderlying w++t).Pairwise (fun p q => p.1≤q.1))
    (ht : rawVariance (weightedUnderlying c++weightedUnderlying w++t)=1)
    (hg : weightedCross c+weightedCross v=1)
    (hD : Nonempty (MatrixStates N 3 (tripleGram (rawVariance (weightedUnderlying c)) δ
      (rawVariance (weightedUnderlying c++weightedUnderlying w))))) :
    matrixConstrainedPressure N 3 β (tripleGram (rawVariance (weightedUnderlying c)) δ
      (rawVariance (weightedUnderlying c++weightedUnderlying w))) ≤
      vectorIncrementChain ((narrowSchedule δ c v w t).map (fun p => (p.1,β • p.2)))
        (fun x => ∑ u,scalarSpinTerminal (x u)) 0-
      3*β^2/4*rawPenalty (weightedUnderlying c++weightedUnderlying w++t) 0-
      β^2*δ^2*(narrowCrossPenalty c v w+narrowVariance c v w*rawArea t)+
      β^2*δ^4*(narrowVariance c v w)^2 := by
  have H := matrixConstrainedPressure_chain hN β _ hD (narrowSchedule δ c v w t)
    (narrowSchedule_mass_bounds δ c v w t hv hm)
    (narrowSchedule_monotone δ c v w t hv (fun p hp => (hm p hp).1) hs)
  have hcw : ∀ p∈weightedUnderlying c++weightedUnderlying w,0≤p.1 :=
    fun p hp => (hm p (List.mem_append_left _ hp)).1
  have hc : ∀ p∈c,0≤p.1 := fun p hp => hcw (p.1,p.2.1)
    (List.mem_append_left _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  have hw : ∀ p∈w,0≤p.1 := fun p hp => hcw (p.1,p.2.1)
    (List.mem_append_right _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  have hv' : ∀ p∈v,0≤p.1 := by
    intro p hp
    have hp' : (p.1,p.2.1)∈weightedUnderlying w := hv ▸ List.mem_map.mpr ⟨p,hp,rfl⟩
    exact hcw _ (List.mem_append_right _ hp')
  have hq := narrowQuarticPenalty_nonneg c v w hc hv' hw
  simp only [narrowSchedule_covariance δ c v w t hv hy,ht,hg,tripleClockPerturbed_symmetric,
    triplePerturbedMatrix_mismatch,narrowSchedule_penalty δ c v w t hv hy] at H
  have hn : 0≤β^2*δ^4*narrowQuarticPenalty c v w := by positivity
  nlinarith

end SK.Analytic

end
end

end OAI
