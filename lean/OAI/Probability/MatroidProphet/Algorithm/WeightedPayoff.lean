import OAI.Probability.MatroidProphet.Algorithm.Worst
import OAI.Probability.MatroidProphet.GroupPayoff
import OAI.Probability.MatroidProphet.AnalyzedMass

namespace OAI

namespace MatroidProphet.MainAlgorithm
open Finset
variable {n : ℕ}

lemma higherTrueGroups_card_eq_sum (M : Matroid (Fin n)) (d : MainMasks n)
    (w : Fin n → Option ℤ) (i : ℤ) :
    ((higherTrueGroups M d w i).card : ℝ) =
      ∑ j ∈ trueLevels M w d.H with i < j, ((trueGroup M d w j).card : ℝ) := by
  simp only [trueGroup_eq_candidate_filter, higherTrueGroups]
  exact highGroup_card w (candidateLabels M w d.H) (trueLevels M w d.H) Subset.rfl i

theorem conditional_main_payoff (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) :
    thinningRate / (2 * densityThreshold) *
      (retainedFraction * analyzedComparisonMass M w d.H - ((2:ℝ)^21)⁻¹ *
        ∑ e ∈ candidateLabels M w d.H, levelWeight weightBase (w e)) ≤
      mainMean d (fun d' => mainWorstRounded M hE d' w) := by
  classical
  let J := positiveGreedy M w \ d.H
  let Y : ℤ → Finset (Fin n) := fun i => J.filter (fun e => w e = some i)
  have hY (i : ℤ) : (Y i : Set (Fin n)) ⊆ (trueGroup M d w i : Set (Fin n)) := by
    rw [trueGroup_eq_candidate_filter]
    intro e he
    obtain ⟨heJ, hew⟩ := mem_filter.mp he
    exact mem_filter.mpr ⟨positiveGreedy_survivors_subset M w d.H heJ, hew⟩
  have hI (i : ℤ) : M.Indep (Y i : Set (Fin n)) :=
    (positiveGreedy_survivors_indep M hE w d.H).subset (filter_subset _ _)
  have hgroup (i : ℤ) (hi : i ∈ analyzedLevels M w d.H) :
      thinningRate / densityThreshold *
        (retainedFraction * (Y i).card -
          (((2:ℝ)^23)⁻¹ + thinningRate * densityThreshold) * (trueGroup M d w i).card -
          (1 + thinningRate * densityThreshold) *
            ∑ l ∈ trueLevels M w d.H with i < l, ((trueGroup M d w l).card : ℝ)) ≤
        mainMean d (fun d' => (trueLambda M hE d' w i : ℝ)) := by
    have hn : densityThreshold ≤ ((trueGroup M d w i).card : ℝ) := by
      rw [trueGroup_eq_candidate_filter]
      exact (mem_filter.mp hi).2
    have hp := true_group_payoff M hE d w i (Y i : Set (Fin n)) (hY i) (hI i) hn
    simpa only [Set.ncard_coe_finset, higherTrueGroups_card_eq_sum] using hp
  have hpaid := source_weighted_group_payoff (trueLevels M w d.H) (analyzedLevels M w d.H)
    (filter_subset _ _) (fun i => ((trueGroup M d w i).card : ℝ))
    (fun i => ((Y i).card : ℝ)) (fun i => mainMean d (fun d' => (trueLambda M hE d' w i : ℝ)))
    (fun i hi => Nat.cast_nonneg _) hgroup
  have hmass : (∑ i ∈ trueLevels M w d.H, weightBase ^ i * ((trueGroup M d w i).card : ℝ)) =
      ∑ e ∈ candidateLabels M w d.H, levelWeight weightBase (w e) := by
    simp only [trueGroup_eq_candidate_filter]
    exact sum_weightGroups_mass w (candidateLabels M w d.H) (trueLevels M w d.H) Subset.rfl weightBase
  rw [hmass] at hpaid
  exact hpaid.trans (weighted_mean_trueLambda_le_mainWorstRounded M hE d w (analyzedLevels M w d.H))

end MatroidProphet.MainAlgorithm

end OAI
