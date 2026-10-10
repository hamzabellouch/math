import OAI.Probability.MatroidProphet.WeightGroups
import OAI.Probability.MatroidProphet.WeightedPayoff
import OAI.Probability.MatroidProphet.Maximum.Score

namespace OAI

namespace MatroidProphet.MainAlgorithm

open Finset

variable {n : ℕ}

noncomputable def trueLevels (M : Matroid (Fin n)) (a : Fin n → Option ℤ)
    (H : Finset (Fin n)) : Finset ℤ := weightLevels a (candidateLabels M a H)

noncomputable def analyzedLevels (M : Matroid (Fin n)) (a : Fin n → Option ℤ)
    (H : Finset (Fin n)) : Finset ℤ := by
  classical
  exact (trueLevels M a H).filter fun i =>
    densityThreshold ≤ ((candidateLabels M a H).filter (fun e => a e = some i)).card

noncomputable def comparisonMass (M : Matroid (Fin n)) (a : Fin n → Option ℤ)
    (H : Finset (Fin n)) : ℝ :=
  ∑ e ∈ positiveGreedy M a \ H, levelWeight weightBase (a e)

noncomputable def analyzedComparisonMass (M : Matroid (Fin n)) (a : Fin n → Option ℤ)
    (H : Finset (Fin n)) : ℝ := by
  classical
  exact ∑ i ∈ analyzedLevels M a H, weightBase ^ i *
    (((positiveGreedy M a \ H).filter (fun e => a e = some i)).card : ℝ)

lemma candidate_level_le_maximumRounded (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (w : Weights n) (H : Finset (Fin n)) (i : ℤ)
    (hi : i ∈ trueLevels M (fun e => roundedLevel weightBase (w e)) H) :
    weightBase ^ i ≤ maximumRounded M w := by
  classical
  obtain ⟨e, he, hei⟩ := (mem_weightLevels _ _ i).1 hi
  have hc : candidate M ⟨H, ∅, ∅, ∅, false⟩ (fun e => roundedLevel weightBase (w e)) e
      (roundedLevel weightBase (w e)) := (Finset.mem_filter.mp he).2
  have heI := candidate_singleton_indep M hE _ _ e _ hc
  have h := roundedWeight_le_maximumRounded M w e heI
  simpa only [roundedWeight, hei, levelWeight] using h

lemma comparisonMass_partition (M : Matroid (Fin n)) (a : Fin n → Option ℤ)
    (H : Finset (Fin n)) :
    comparisonMass M a H =
      ∑ i ∈ trueLevels M a H, weightBase ^ i *
        (((positiveGreedy M a \ H).filter (fun e => a e = some i)).card : ℝ) := by
  exact (sum_weightGroups_mass a _ _
    (weightLevels_mono a (positiveGreedy_survivors_subset M a H)) weightBase).symm

lemma small_comparison_mass (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (w : Weights n) (H : Finset (Fin n)) :
    comparisonMass M (fun e => roundedLevel weightBase (w e)) H ≤
      analyzedComparisonMass M (fun e => roundedLevel weightBase (w e)) H +
        2 * densityThreshold * maximumRounded M w := by
  classical
  let a : Fin n → Option ℤ := fun e => roundedLevel weightBase (w e)
  let Y := positiveGreedy M a \ H
  let U := candidateLabels M a H
  let L := trueLevels M a H
  let A := analyzedLevels M a H
  have hAU : A ⊆ L := Finset.filter_subset _ _
  have hsmall : ∀ i ∈ L \ A, ((Y.filter (fun e => a e = some i)).card : ℝ) ≤ densityThreshold := by
    intro i hi
    obtain ⟨hiL, hiA⟩ := Finset.mem_sdiff.mp hi
    have hn : ¬densityThreshold ≤ ((U.filter (fun e => a e = some i)).card : ℝ) := by
      intro hh
      exact hiA (Finset.mem_filter.mpr ⟨hiL, hh⟩)
    have hc : (Y.filter (fun e => a e = some i)).card ≤ (U.filter (fun e => a e = some i)).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ (positiveGreedy_survivors_subset M a H))
    have hcR : ((Y.filter (fun e => a e = some i)).card : ℝ) ≤
        ((U.filter (fun e => a e = some i)).card : ℝ) := by exact_mod_cast hc
    exact hcR.trans (le_of_lt (lt_of_not_ge hn))
  have hbound := small_group_mass_bound weightBase densityThreshold (maximumRounded M w)
    (by norm_num [weightBase]) constants_positive.2.1.le (maximumRounded_nonneg M w)
    (L \ A) (fun i => ((Y.filter (fun e => a e = some i)).card : ℝ)) hsmall
    (fun i hi => candidate_level_le_maximumRounded M hE w H i (Finset.mem_sdiff.mp hi).1)
  have hpartition := Finset.sum_sdiff hAU
    (f := fun i => weightBase ^ i * ((Y.filter (fun e => a e = some i)).card : ℝ))
  rw [comparisonMass_partition]
  change (∑ i ∈ L, weightBase ^ i * ((Y.filter (fun e => a e = some i)).card : ℝ)) ≤
    (∑ i ∈ A, weightBase ^ i * ((Y.filter (fun e => a e = some i)).card : ℝ)) + _
  linarith

end MatroidProphet.MainAlgorithm

end OAI
