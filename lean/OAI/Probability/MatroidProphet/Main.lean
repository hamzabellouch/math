import OAI.Probability.MatroidProphet.Algorithm.WeightedPayoff
import OAI.Probability.MatroidProphet.CompletePayoff
import OAI.Probability.MatroidProphet.Reduction

namespace OAI

namespace MatroidProphet

open MeasureTheory Finset MainAlgorithm

lemma main_branch_guarantee_small {n : ℕ} (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (w : Weights n)
    (hm : maximumRounded M w ≤ optimum M (fun e => roundedWeight weightBase (w e)) /
      (8 * densityThreshold)) :
    thinningRate * retainedFraction / (16 * densityThreshold) *
      optimum M (fun e => roundedWeight weightBase (w e)) ≤ mainPayoff M hE w := by
  apply main_branch_from_filter Finset.univ
    (analyzedComparisonMass M (fun e => roundedLevel weightBase (w e)))
    (comparisonMass M (fun e => roundedLevel weightBase (w e)))
    (fun H => ∑ e ∈ candidateLabels M (fun e => roundedLevel weightBase (w e)) H,
      roundedWeight weightBase (w e))
    (fun H => mainMean ⟨H, ∅, ∅, ∅, false⟩
      (fun d => mainWorstRounded M hE d (fun e => roundedLevel weightBase (w e))))
    (optimum M (fun e => roundedWeight weightBase (w e))) (maximumRounded M w)
    (optimum_nonneg M _) hm
  · exact expectation_positiveGreedy_survivors M hE w (by norm_num [weightBase])
  · exact expectation_candidateLabels_le_optimum M hE w weightBase
  · intro H _
    exact small_comparison_mass M hE w H
  · intro H _
    exact conditional_main_payoff M hE ⟨H, ∅, ∅, ∅, false⟩ _

theorem complete_hidden_guarantee {n : ℕ} (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (w : Weights n) (hw : ∀ e, 0 ≤ w e) :
    ((2 : ℝ) ^ 293)⁻¹ * optimum M w ≤
      ∫ r, hiddenWorstReward (completeHiddenRule M hE) w r ∂sourceSeedLaw n := by
  let W := optimum M (fun e => roundedWeight weightBase (w e))
  have hb := branch_mixture_lower W (maximumRounded M w) (mainPayoff M hE w) (maximumPayoff M w)
    (optimum_nonneg M _) (maximumRounded_nonneg M w) (mainPayoff_nonneg M hE w)
    (maximum_branch_guarantee M w hw) (main_branch_guarantee_small M hE w)
  have hi := integrated_branch_lower M hE w hw
  have hr := optimum_rounding_bound M weightBase (by norm_num [weightBase]) w hw
  have hc0 : 0 ≤ thinningRate * retainedFraction / (32 * densityThreshold * weightBase) :=
    div_nonneg (mul_nonneg constants_positive.2.2.1.le constants_positive.2.2.2.2.le)
      (mul_nonneg (mul_nonneg (by norm_num) constants_positive.2.1.le) constants_positive.1.le)
  have hscaled := mul_le_mul_of_nonneg_left hr hc0
  have hcancel : thinningRate * retainedFraction / (32 * densityThreshold * weightBase) *
      (weightBase * W) = thinningRate * retainedFraction / (32 * densityThreshold) * W := by
    field_simp [ne_of_gt constants_positive.1, ne_of_gt constants_positive.2.1]
  rw [hcancel] at hscaled
  rw [hidden_fraction_exact] at hscaled
  exact hscaled.trans (hb.trans hi)

theorem hidden_vector : HiddenVectorChallenge := by
  intro n M hE
  refine ⟨mainSeedBits n, sourceSeedLaw n, inferInstance, completeHiddenRule M hE, ?_, ?_⟩
  · exact completeHiddenRule_feasible M hE
  · exact complete_hidden_guarantee M hE

theorem one_sample.{u} : OneSampleChallenge.{u} :=
  hiddenVectorChallenge_implies_oneSampleChallenge hidden_vector

end MatroidProphet

end OAI
