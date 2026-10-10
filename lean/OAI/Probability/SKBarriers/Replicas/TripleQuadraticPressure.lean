import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.WeightedAugment
import OAI.Probability.SKBarriers.Replicas.TripleScaleStats
import OAI.Probability.SKBarriers.Replicas.TripleDecoupling
import OAI.Probability.SKBarriers.Replicas.TripleScheduleEndpoint

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem tripleSusceptibility_nonneg (c : List (ℝ × ℝ)) (w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ))
    (hm : ∀ p∈t,p.1∈Icc (0:ℝ) 1) : 0 ≤ tripleSusceptibility c w t := by
  have hf := scalarIncrementChain_regular t scalarSpinTerminal_regular
  have hc := scalarIncrementChain_spin_convex t hm
  exact scalarIncrementAverage_nonneg _ hf (hc.hessian_bounded hf) (fun x => (hc x).1) 0

def tripleQuadraticCoefficient (β V : ℝ) (c : List (ℝ × ℝ)) (w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ)) : ℝ :=
  let χ := tripleSusceptibility (scaleIncrementChain β c) (scaleIncrementChain β w) (scaleIncrementChain β t)
  let χ₀ := rootHessian 0 (scalarIncrementChain (scaleIncrementChain β (c++weightedUnderlying w++t)) scalarSpinTerminal) 0
  β^2*weightedVariance w*(χ-rawArea t)+
    β^2*weightedCrossPenalty w 0*(β^2*χ*(χ₀+2*V+4*V^2)-1)+
    tripleCommonError (scaleIncrementChain β c) (scaleIncrementChain β w)

theorem tripleConstrainedPressure_quadratic {N : ℕ} (hN : 0<N) (β δ : ℝ)
    (c : List (ℝ × ℝ)) (w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ))
    (hm : ∀ p∈c++weightedUnderlying w++t,p.1∈Icc (0:ℝ) 1)
    (hs : (c++weightedUnderlying w++t).Pairwise (fun p q => p.1≤q.1))
    (ht : rawVariance (c++weightedUnderlying w++t)=1) (hg : weightedCross w=1)
    (hD : Nonempty (MatrixStates N 3 (tripleGram (rawVariance c) δ (rawVariance (c++weightedUnderlying w)))))
    (k : Fin (zeroWeightChain (scaleIncrementChain β c)++scaleIncrementChain β w++zeroWeightChain (scaleIncrementChain β t)).length → ℝ)
    (hk : ∀ i,0≤k i)
    (he : ∀ i,((zeroWeightChain (scaleIncrementChain β c)++scaleIncrementChain β w++zeroWeightChain (scaleIncrementChain β t)).get i).2.2=
      k i*((zeroWeightChain (scaleIncrementChain β c)++scaleIncrementChain β w++zeroWeightChain (scaleIncrementChain β t)).get i).2.1)
    {V : ℝ} (hV : 0≤V)
    (hactive : ∀ i,k i≠0 → scalarPrefixVariance (zeroWeightChain (scaleIncrementChain β c)++scaleIncrementChain β w++zeroWeightChain (scaleIncrementChain β t)).length
      (fun j => ((zeroWeightChain (scaleIncrementChain β c)++scaleIncrementChain β w++zeroWeightChain (scaleIncrementChain β t)).get j).2.1) i.castSucc≤V)
    {a : ℝ} (ha : 0<a) (hδ : 4*δ^2≤a) (hδ1 : |δ|≤1)
    (hsmall : a*(4*β^2*weightedVariance w+(2*β^2*weightedAbsCross w)^2)≤1/2) :
    matrixConstrainedPressure N 3 β (tripleGram (rawVariance c) δ (rawVariance (c++weightedUnderlying w))) ≤
      3*(scalarIncrementChain (scaleIncrementChain β (c++weightedUnderlying w++t)) scalarSpinTerminal 0-
        β^2/4*rawPenalty (c++weightedUnderlying w++t) 0)+
      δ^2*tripleQuadraticCoefficient β V c w t+
      tripleExpansionConstant a*|δ|^3+β^2*δ^4*(weightedVariance w)^2 := by
  let c' := scaleIncrementChain β c
  let w' := scaleIncrementChain β w
  let t' := scaleIncrementChain β t
  have hall : c'++weightedUnderlying w'++t'=scaleIncrementChain β (c++weightedUnderlying w++t) := by
    simp only [c',w',t',scaleIncrementChain_append,weightedUnderlying_scale]
  have hm' : ∀ p∈c'++weightedUnderlying w'++t',p.1∈Icc (0:ℝ) 1 := by
    rw [hall]; exact scaleIncrementChain_mass β _ hm
  have hs' : (c'++weightedUnderlying w'++t').Pairwise (fun p q => p.1≤q.1) := by
    rw [hall]; exact scaleIncrementChain_sorted β _ hs
  have hmt : ∀ p∈t',p.1∈Icc (0:ℝ) 1 := fun p hp => hm' p (List.mem_append_right _ hp)
  have hχ := tripleSusceptibility_nonneg c' w' t' hmt
  have HB := weightedFull_spin_early_le c' w' t' hm' hs' k hk he hV hactive
  have HD := tripleBaseQuadratic_decoupling c' w' t' hm' hs'
  have HQ : tripleBaseQuadratic c' w' t' ≤
      tripleSusceptibility c' w' t'*(weightedVariance w'+
        (rootHessian 0 (scalarIncrementChain (c'++weightedUnderlying w'++t') scalarSpinTerminal) 0+
          (2*V+4*V^2))*weightedCrossPenalty w' 0)+tripleCommonError c' w' := by
    have H := (abs_le.mp HD).2
    have H' := mul_le_mul_of_nonneg_left HB hχ
    linarith
  have HE := tripleSchedule_value_expansion c' w' t' hm' hs' ha hδ hδ1 (by
    simpa only [w',weightedVariance_scale,weightedAbsCross_scale,mul_assoc] using hsmall)
  have HP := tripleConstrainedPressure_schedule hN β δ c w t hm hs ht hg hD
  change matrixConstrainedPressure N 3 β _ ≤ vectorIncrementChain (scaleIncrementChain β (tripleSchedule δ c w t)) _ 0-_-_+_ at HP
  rw [tripleSchedule_scale] at HP
  change matrixConstrainedPressure N 3 β _ ≤ vectorIncrementChain (tripleSchedule δ c' w' t') _ 0-_-_+_ at HP
  have HVE : vectorIncrementChain (tripleSchedule δ c' w' t') (fun x => ∑ u,scalarSpinTerminal (x u)) 0 ≤
      3*scalarIncrementChain (c'++weightedUnderlying w'++t') scalarSpinTerminal 0+
      δ^2*(tripleSusceptibility c' w' t'*(weightedVariance w'+
        (rootHessian 0 (scalarIncrementChain (c'++weightedUnderlying w'++t') scalarSpinTerminal) 0+
          (2*V+4*V^2))*weightedCrossPenalty w' 0)+tripleCommonError c' w')+
      tripleExpansionConstant a*|δ|^3 := HE.trans (by
    linarith [mul_le_mul_of_nonneg_left HQ (sq_nonneg δ)])
  rw [hall] at HVE
  have HA : vectorIncrementChain (tripleSchedule δ c' w' t') (fun x => ∑ u,scalarSpinTerminal (x u)) 0-
      3*β^2/4*rawPenalty (c++weightedUnderlying w++t) 0-
      β^2*δ^2*(weightedCrossPenalty w 0+weightedVariance w*rawArea t)+β^2*δ^4*(weightedVariance w)^2 ≤
      (3*scalarIncrementChain (scaleIncrementChain β (c++weightedUnderlying w++t)) scalarSpinTerminal 0+
      δ^2*(tripleSusceptibility c' w' t'*(weightedVariance w'+
        (rootHessian 0 (scalarIncrementChain (c'++weightedUnderlying w'++t') scalarSpinTerminal) 0+
          (2*V+4*V^2))*weightedCrossPenalty w' 0)+tripleCommonError c' w')+
      tripleExpansionConstant a*|δ|^3)-
      3*β^2/4*rawPenalty (c++weightedUnderlying w++t) 0-
      β^2*δ^2*(weightedCrossPenalty w 0+weightedVariance w*rawArea t)+β^2*δ^4*(weightedVariance w)^2 := by
    rw [hall]; linarith
  apply (HP.trans HA).trans
  apply le_of_eq
  simp only [hall,w',weightedVariance_scale,weightedCrossPenalty_scale_zero,tripleQuadraticCoefficient,c',t']
  ring

end SK.Analytic

end
end

end OAI
