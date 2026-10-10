import OAI.Combinatorics.BalancedRyser.Candidates.CandidateGlobalLineMean
import OAI.Combinatorics.BalancedRyser.Incidence.CandidateIncidenceModel

namespace OAI

namespace Balanced.CandidateGlobalLine

noncomputable section
open scoped Classical BigOperators
open CandidateExposure PartialAlignment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem sum_targets_lineSuccess_stratum_le (L : Line F)
    (D : Finset (Direction F)) (a : MergedPairs F) (m j : ℕ)
    (hD : D.card ≤ m) (hj : j ≤ 4) (ha : L ∉ constituentLines a) :
    (∑ g : Direction F, ∑ T ∈ tuplesWithExposure g D j,
      conditionalProbability D a (lineSuccessEvent T g L)) ≤
      (32768 * (m + 1) ^ 4 : ℝ) *
        (if j = 0 then (Fintype.card F : ℝ) else 1) := by
  by_cases hlow : j = 0 ∨ j = 1
  · exact sum_targets_lineSuccess_zero_one_le L D a m j hD hlow ha
  have hdrop : (∑ g : Direction F, ∑ T ∈ tuplesWithExposure g D j,
      conditionalProbability D a (lineSuccessEvent T g L)) ≤
      ∑ g : Direction F, ∑ T ∈ tuplesWithExposure g D j,
        conditionalProbability D a (successfulInDirection T g) := by
    exact Finset.sum_le_sum (fun g _ => Finset.sum_le_sum
      (fun T _ => lineSuccessEvent_probability_le T g L D a))
  by_cases hmid : j = 2 ∨ j = 3
  · have h := hdrop.trans (sum_targets_success_two_three_le D a m j hD hmid)
    have hj0 : j ≠ 0 := by omega
    rw [ite_eq_right hj0, mul_one]
    exact h.trans (by gcongr; norm_num)
  · have hj4 : j = 4 := by omega
    subst j
    have h := hdrop.trans (sum_targets_success_four_le D a)
    norm_num only [show ¬ (4 : ℕ) = 0 by decide, ite_false, mul_one]
    apply h.trans
    have hm : (D.card : ℝ) ≤ (m : ℝ) + 1 := by exact_mod_cast (by omega : D.card ≤ m+1)
    have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ D.card) hm 4
    nlinarith [show (0 : ℝ) ≤ (m+1)^4 by positivity]

theorem sum_targets_lineSuccess_le (L : Line F)
    (D : Finset (Direction F)) (a : MergedPairs F) (m : ℕ)
    (hD : D.card ≤ m) (ha : L ∉ constituentLines a) :
    (∑ g : Direction F, ∑ T ∈ eligibleTuples g,
      conditionalProbability D a (lineSuccessEvent T g L)) ≤
      (163840 * (m + 1) ^ 4 : ℝ) * Fintype.card F := by
  have hpartition (g : Direction F) :
      (∑ T ∈ eligibleTuples g, conditionalProbability D a (lineSuccessEvent T g L)) =
      ∑ j ∈ Finset.range 5, ∑ T ∈ tuplesWithExposure g D j,
        conditionalProbability D a (lineSuccessEvent T g L) := by
    symm
    exact Finset.sum_fiberwise_of_maps_to
      (s := eligibleTuples g) (t := Finset.range 5)
      (g := fun T => (exposedTupleIndices T D).card)
      (fun T _ => Finset.mem_range.mpr (by
        have h := Finset.card_le_univ (exposedTupleIndices T D)
        simp only [Fintype.card_fin] at h
        omega)) _
  simp_rw [hpartition]
  rw [Finset.sum_comm]
  have hq : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos (α := F)
  calc
    _ ≤ ∑ _j ∈ Finset.range 5,
        (32768 * (m+1)^4 : ℝ) * Fintype.card F := by
      apply Finset.sum_le_sum
      intro j hj
      apply (sum_targets_lineSuccess_stratum_le L D a m j hD
        (by have := Finset.mem_range.mp hj; omega) ha).trans
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      split_ifs
      · exact le_rfl
      · exact hq
    _ = _ := by norm_num; ring

theorem sum_targets_overlapping_lineSuccess_le (L : Line F)
    (D : Finset (Direction F)) (a : MergedPairs F) (m : ℕ)
    (hD : D.card ≤ m) (ha : L ∉ constituentLines a) :
    (∑ g : Direction F,
      ∑ T ∈ (eligibleTuples g).filter (fun T => 0 < (exposedTupleIndices T D).card),
        conditionalProbability D a (lineSuccessEvent T g L)) ≤
      (163840 * (m + 1) ^ 4 : ℝ) := by
  have hpartition (g : Direction F) :
      (∑ T ∈ (eligibleTuples g).filter (fun T => 0 < (exposedTupleIndices T D).card),
        conditionalProbability D a (lineSuccessEvent T g L)) =
      ∑ j ∈ Finset.Icc 1 4, ∑ T ∈ tuplesWithExposure g D j,
        conditionalProbability D a (lineSuccessEvent T g L) := by
    have h := Finset.sum_fiberwise_eq_sum_filter (eligibleTuples g)
      (Finset.Icc 1 4) (fun T => (exposedTupleIndices T D).card)
      (fun T => conditionalProbability D a (lineSuccessEvent T g L))
    have heq : (eligibleTuples g).filter
        (fun T => (exposedTupleIndices T D).card ∈ Finset.Icc 1 4) =
        (eligibleTuples g).filter (fun T => 0 < (exposedTupleIndices T D).card) := by
      apply Finset.filter_congr
      intro T _
      have hc := Finset.card_le_univ (exposedTupleIndices T D)
      simp only [Fintype.card_fin] at hc
      simp only [Finset.mem_Icc]
      omega
    rw [heq] at h
    exact h.symm
  simp_rw [hpartition]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ _j ∈ Finset.Icc 1 4, (32768 * (m+1)^4 : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      obtain ⟨hj1, hj4⟩ := Finset.mem_Icc.mp hj
      simpa only [ite_eq_right (by omega : j ≠ 0), mul_one] using
        sum_targets_lineSuccess_stratum_le L D a m j hD hj4 ha
    _ ≤ _ := by norm_num; nlinarith [show (0 : ℝ) ≤ (m+1)^4 by positivity]

end
end Balanced.CandidateGlobalLine

end OAI
