import Mathlib
import OAI.Probability.SKBarriers.Replicas.TripleTailSchedule
import OAI.Probability.SKBarriers.Replicas.TripleScheduleMass

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

@[simp] theorem tripleClockMatrix_zero : tripleClockMatrix 0 0 0 0 0=0 := by
  funext i j; fin_cases i <;> fin_cases j <;> rfl

@[simp] theorem tripleClockPerturbed_zero (a b c r q δ : ℝ) :
    tripleClockPerturbed a b c r q δ 0 0=tripleClockMatrix a b c r q := by
  ext i j; simp [tripleClockPerturbed]

theorem rawVariance_append (l r : List (ℝ × ℝ)) : rawVariance (l++r)=rawVariance l+rawVariance r := by
  simp [rawVariance,List.sum_append]

theorem rawPenalty_append (l r : List (ℝ × ℝ)) (a : ℝ) :
    rawPenalty (l++r) a=rawPenalty l a+rawPenalty r (a+rawVariance l) := by
  simp only [rawPenalty,List.map_append,chainPotentialPenalty_append,chainSum,List.map_map,rawVariance,Function.comp_def]

theorem tripleSchedule_covariance (δ : ℝ) (c : List (ℝ × ℝ)) (w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ)) :
    matrixChainCovariance (tripleSchedule δ c w t)=
      tripleClockPerturbed (rawVariance (c++weightedUnderlying w++t)) (rawVariance (c++weightedUnderlying w++t))
        (rawVariance (c++weightedUnderlying w++t)) (rawVariance c) (rawVariance (c++weightedUnderlying w))
        δ (weightedCross w) (weightedVariance w) := by
  have hc := tripleCommonSchedule_covariance c 0
  simp only [tripleClockMatrix_zero,zero_add] at hc
  have hm := tripleMiddleSchedule_covariance δ (mergedProductBranches w (weightedUnderlying w))
    (rawVariance c) (rawVariance c) (rawVariance c) 0 0
  simp only [tripleClockPerturbed_zero,mergedProductBranches_left,mergedProductBranches_right,zero_add] at hm
  simp only [tripleSchedule,matrixChainCovariance_append,hc]
  rw [hm,tripleTailSchedule_covariance]
  simp only [rawVariance_append]

theorem tripleSchedule_penalty (δ : ℝ) (c : List (ℝ × ℝ)) (w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ)) :
    matrixChainPenalty (tripleSchedule δ c w t) 0=
      3*rawPenalty (c++weightedUnderlying w++t) 0+
      4*δ^2*(weightedCrossPenalty w 0+weightedVariance w*rawArea t)+
      4*δ^4*weightedVariancePenalty w 0 := by
  have hc := tripleCommonSchedule_covariance c 0
  simp only [tripleClockMatrix_zero,zero_add] at hc
  have hpc := tripleCommonSchedule_penalty c 0
  simp only [tripleClockMatrix_zero] at hpc
  have hm := tripleMiddleSchedule_covariance δ (mergedProductBranches w (weightedUnderlying w))
    (rawVariance c) (rawVariance c) (rawVariance c) 0 0
  simp only [tripleClockPerturbed_zero,mergedProductBranches_left,mergedProductBranches_right,zero_add] at hm
  have hpm := tripleMiddleSchedule_penalty δ (mergedProductBranches w (weightedUnderlying w))
    (rawVariance c) (rawVariance c) (rawVariance c) 0 0
  simp only [tripleClockPerturbed_zero,mergedProductBranches_left,mergedProductBranches_right] at hpm
  simp only [tripleSchedule,matrixChainPenalty_append,matrixChainCovariance_append,zero_add,hc,hpc,hm,hpm,
    tripleTailSchedule_penalty,rawPenalty_append,rawVariance_append]
  ring

theorem weightedVariancePenalty_nonneg (w : List (ℝ × (ℝ × ℝ)))
    (hm : ∀ p∈w,0≤p.1) {G : ℝ} (hG : 0≤G) : 0≤weightedVariancePenalty w G := by
  induction w generalizing G with
  | nil => rfl
  | cons p w ih =>
    change 0≤p.1*((G+p.2.2^2)^2-G^2)+weightedVariancePenalty w (G+p.2.2^2)
    apply add_nonneg
    · apply mul_nonneg (hm p (List.mem_cons_self ..))
      nlinarith [sq_nonneg p.2.2]
    · exact ih (fun q hq => hm q (List.mem_cons_of_mem _ hq)) (by positivity)

theorem tripleConstrainedPressure_schedule {N : ℕ} (hN : 0<N) (β δ : ℝ)
    (c : List (ℝ × ℝ)) (w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ))
    (hm : ∀ p∈c++weightedUnderlying w++t,p.1∈Icc (0:ℝ) 1)
    (hs : (c++weightedUnderlying w++t).Pairwise (fun p q => p.1≤q.1))
    (ht : rawVariance (c++weightedUnderlying w++t)=1) (hg : weightedCross w=1)
    (hD : Nonempty (MatrixStates N 3 (tripleGram (rawVariance c) δ (rawVariance (c++weightedUnderlying w))))) :
    matrixConstrainedPressure N 3 β (tripleGram (rawVariance c) δ (rawVariance (c++weightedUnderlying w))) ≤
      vectorIncrementChain ((tripleSchedule δ c w t).map (fun p => (p.1,β • p.2)))
        (fun x => ∑ u,scalarSpinTerminal (x u)) 0-
      3*β^2/4*rawPenalty (c++weightedUnderlying w++t) 0-
      β^2*δ^2*(weightedCrossPenalty w 0+weightedVariance w*rawArea t)+
      β^2*δ^4*(weightedVariance w)^2 := by
  have H := matrixConstrainedPressure_chain hN β _ hD (tripleSchedule δ c w t)
    (tripleSchedule_mass_bounds δ c w t hm)
    (tripleSchedule_monotone δ c w t (fun p hp => (hm p hp).1) hs)
  have hq : 0≤weightedVariancePenalty w 0 := weightedVariancePenalty_nonneg w (by
    intro p hp
    exact (hm (p.1,p.2.1) (by simp only [List.mem_append]; exact Or.inl (Or.inr (List.mem_map.mpr ⟨p,hp,rfl⟩)))).1) le_rfl
  simp only [tripleSchedule_covariance,ht,hg,tripleClockPerturbed_symmetric,
    triplePerturbedMatrix_mismatch,tripleSchedule_penalty] at H
  have hn : 0≤β^2*δ^4*weightedVariancePenalty w 0 := by positivity
  nlinarith

end SK.Analytic

end
end

end OAI
