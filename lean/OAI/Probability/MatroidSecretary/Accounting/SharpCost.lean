import OAI.Probability.MatroidSecretary.Accounting.ExpectedCost

namespace OAI

/-!
# Retaining the density-mask rate in the accounting budget

In accounting.tex immediately after `eq:expected-cost`, the manuscript notes
that the exact density-mask contribution is `1 / (4 * κ)`, although the proof
uses the more generous `1 / κ`.  This supplement proves that sharper inequality
for the actual zero-extended cost, without conditioning on random listing.
-/

namespace MatroidProphet.AccountingContracts
open Set Finset MainAlgorithm
variable {n : ℕ}

/-- Keep the sampled higher-group density count until after expectation. -/
theorem listedCost_le_sampled_true_counts (M : Matroid (Fin n)) (d : MainMasks n)
    (w : Fin n → Option ℤ) {h : ℕ} {i : ℤ}
    (hi : (groups M d w)[h]? = some i) :
    listedCost M d w h ≤
      (d.C ∩ trueGroup M d w i).card +
        (d.C ∩ higherTrueGroups M d w i).card +
          (d.D ∩ higherTrueGroups M d w i).card / densityThreshold := by
  classical
  let J := range ((groups M d w).length - (h + 1))
  have count (mask : Finset (Fin n)) :
      (∑ j ∈ J, (groupMask M d w mask (h + 1 + j)).ncard) ≤
        (mask ∩ higherTrueGroups M d w i).card := by
    apply sum_groupMask_card_le M d w J (fun j => h + 1 + j)
      (by intro a _ b _ hab; change h + 1 + a = h + 1 + b at hab; omega)
    intro j hj
    exact groupMask_later_subset M d w mask hi
      (by have := mem_range.mp hj; have := (List.getElem?_eq_some_iff.mp hi).1; omega)
      (by omega)
  have hc : (∑ j ∈ J, ((groupMask M d w d.C (h + 1 + j)).ncard : ℝ)) ≤
      (d.C ∩ higherTrueGroups M d w i).card := by exact_mod_cast count d.C
  have hd : (∑ j ∈ J, ((groupMask M d w d.D (h + 1 + j)).ncard : ℝ)) ≤
      (d.D ∩ higherTrueGroups M d w i).card := by exact_mod_cast count d.D
  have hf : (groupMask M d w d.C h).ncard = (d.C ∩ trueGroup M d w i).card := by
    rw [Set.ncard_eq_toFinset_card', groupMask_eq_focal M d w d.C hi,
      trueGroup_eq_candidate_filter]
  have hdiv := div_le_div_of_nonneg_right hd constants_positive.2.1.le
  unfold listedCost
  rw [hf, sum_add_distrib, ← sum_div]
  dsimp only [J] at hc hdiv
  linarith

/-- The density mask is averaged at its original rate, independently of `H`. -/
lemma mainMean_density_count (d : MainMasks n) (K : Finset (Fin n)) :
    mainMean d (fun d' => ((d'.D ∩ K).card : ℝ)) = (1 / 4 : ℝ) * K.card := by
  unfold mainMean tripleMaskExpectation MainAlgorithm.withMasks
  simp only [fairParityExpectation_const, bitsExpectation_const]
  simp_rw [Finset.inter_comm _ K]
  rw [bitsExpectation_card_inter _ univ K (subset_univ _)]
  simp [mul_comm]

lemma mainMean_div (d : MainMasks n) (f : MainMasks n → ℝ) (c : ℝ) :
    mainMean d (fun d' => f d' / c) = mainMean d f / c := by
  simpa only [div_eq_mul_inv, mul_comm] using mainMean_mul d c⁻¹ f

/-- Listing is not a conditioning event: unlisted true groups have cost zero. -/
theorem trueCost_le_sampled_true_counts (M : Matroid (Fin n)) (d : MainMasks n)
    (w : Fin n → Option ℤ) (i : ℤ) :
    trueCost M d w i ≤
      (d.C ∩ trueGroup M d w i).card +
        (d.C ∩ higherTrueGroups M d w i).card +
          (d.D ∩ higherTrueGroups M d w i).card / densityThreshold := by
  classical
  unfold trueCost
  split_ifs with hi
  · exact listedCost_le_sampled_true_counts M d w (groups_get?_idxOf M d w i hi)
  · have hk : 0 < densityThreshold := constants_positive.2.1
    positivity

/-- Source's sharper density contribution before relaxing `1/(4κ)` to `1/κ`. -/
theorem expected_cost_sharp (M : Matroid (Fin n)) (d : MainMasks n)
    (w : Fin n → Option ℤ) (i : ℤ) :
    mainMean d (fun d' => trueCost M d' w i) ≤
      thinningRate * (trueGroup M d w i).card +
        (thinningRate + 1 / (4 * densityThreshold)) * (higherTrueGroups M d w i).card := by
  have hm : mainMean d (fun d' => trueCost M d' w i) ≤
      mainMean d (fun d' => (d'.C ∩ trueGroup M d w i).card +
        (d'.C ∩ higherTrueGroups M d w i).card +
          (d'.D ∩ higherTrueGroups M d w i).card / densityThreshold) := by
    apply mainMean_mono
    intro d' hH
    have hc := trueCost_le_sampled_true_counts M d' w i
    rwa [trueGroup_eq_of_H_eq M d d' w i hH,
      higherTrueGroups_eq_of_H_eq M d d' w i hH] at hc
  simp only [mainMean_add, mainMean_div, mainMean_guard_count, mainMean_density_count] at hm
  convert hm using 1
  ring

/-- The equivalent finite sum over *all* higher true levels, listed or not. -/
theorem expected_cost_sharp_sum (M : Matroid (Fin n)) (d : MainMasks n)
    (w : Fin n → Option ℤ) (i : ℤ) :
    mainMean d (fun d' => trueCost M d' w i) ≤
      thinningRate * (trueGroup M d w i).card +
        (thinningRate + 1 / (4 * densityThreshold)) *
          ∑ j ∈ trueLevels M w d.H with i < j, ((trueGroup M d w j).card : ℝ) := by
  rw [← higherTrueGroups_card_eq_sum M d w i]
  exact expected_cost_sharp M d w i

end MatroidProphet.AccountingContracts

end OAI
