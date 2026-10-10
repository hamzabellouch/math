import OAI.Probability.MatroidProphet.Main

namespace OAI

/-! The literal conditional cost inequality `eq:expected-cost`.  The cost is
zero on an unlisted true group; listing is never conditioned upon. -/

namespace MatroidProphet.AccountingContracts
open Set Finset MainAlgorithm

variable {n : ℕ}

/-- The single path-expansion budget of a listed group, with its real-valued
density contribution. -/
noncomputable def listedCost (M : Matroid (Fin n)) (d : MainMasks n)
    (w : Fin n → Option ℤ) (h : ℕ) : ℝ :=
  (groupMask M d w d.C h).ncard +
    ∑ j ∈ range ((groups M d w).length - (h + 1)),
      ((groupMask M d w d.C (h + 1 + j)).ncard +
        (groupMask M d w d.D (h + 1 + j)).ncard / densityThreshold)

/-- The source's `c_i`, extended by zero to unlisted true groups. -/
noncomputable def trueCost (M : Matroid (Fin n)) (d : MainMasks n)
    (w : Fin n → Option ℤ) (i : ℤ) : ℝ := by
  classical
  exact if i ∈ groups M d w then listedCost M d w ((groups M d w).idxOf i) else 0

theorem listedCost_le_true_counts (M : Matroid (Fin n)) (d : MainMasks n)
    (w : Fin n → Option ℤ) {h : ℕ} {i : ℤ}
    (hi : (groups M d w)[h]? = some i) :
    listedCost M d w h ≤
      (d.C ∩ trueGroup M d w i).card +
        (d.C ∩ higherTrueGroups M d w i).card +
          (higherTrueGroups M d w i).card / densityThreshold := by
  have hc := listed_cost_le_true_counts M d w hi (2^100)
  rw [← trueGroup_eq_candidate_filter M d w i] at hc
  have hr : densityThreshold * (groupMask M d w d.C h).ncard +
      ∑ j ∈ range ((groups M d w).length - (h + 1)),
        (densityThreshold * (groupMask M d w d.C (h + 1 + j)).ncard +
          (groupMask M d w d.D (h + 1 + j)).ncard) ≤
      densityThreshold * (d.C ∩ trueGroup M d w i).card +
        densityThreshold * (d.C ∩ higherTrueGroups M d w i).card +
          (higherTrueGroups M d w i).card := by
    simpa only [densityThreshold, higherTrueGroups, Nat.cast_add, Nat.cast_mul,
      Nat.cast_sum, Nat.cast_pow, Nat.cast_ofNat] using
      (Nat.cast_le.mpr hc : ( _ : ℝ) ≤ _)
  have hk : 0 < densityThreshold := constants_positive.2.1
  apply (mul_le_mul_iff_right₀ hk).mp
  have hs : densityThreshold * listedCost M d w h =
      densityThreshold * (groupMask M d w d.C h).ncard +
        ∑ j ∈ range ((groups M d w).length - (h + 1)),
          (densityThreshold * (groupMask M d w d.C (h + 1 + j)).ncard +
            (groupMask M d w d.D (h + 1 + j)).ncard) := by
    unfold listedCost
    rw [mul_add, mul_sum]
    congr 1
    apply sum_congr rfl
    intro j hj
    rw [mul_add]
    congr 1
    field_simp
  rw [hs, mul_add, mul_add]
  have he : densityThreshold *
      ((higherTrueGroups M d w i).card / densityThreshold) =
      (higherTrueGroups M d w i).card := by field_simp
  rw [he]
  exact hr

theorem trueCost_le_true_counts (M : Matroid (Fin n)) (d : MainMasks n)
    (w : Fin n → Option ℤ) (i : ℤ) :
    trueCost M d w i ≤
      (d.C ∩ trueGroup M d w i).card +
        (d.C ∩ higherTrueGroups M d w i).card +
          (higherTrueGroups M d w i).card / densityThreshold := by
  classical
  unfold trueCost
  split_ifs with hi
  · exact listedCost_le_true_counts M d w (groups_get?_idxOf M d w i hi)
  · have hk : 0 < densityThreshold := constants_positive.2.1
    positivity

/-- Conditional on `H`, the actual randomly listed cost is dominated before
averaging.  The higher-group cardinality is the sum over all higher true groups,
including those that the density mask did not list. -/
theorem expected_cost (M : Matroid (Fin n)) (d : MainMasks n)
    (w : Fin n → Option ℤ) (i : ℤ) :
    mainMean d (fun d' => trueCost M d' w i) ≤
      thinningRate * (trueGroup M d w i).card +
        (thinningRate + 1 / densityThreshold) * (higherTrueGroups M d w i).card := by
  have hm : mainMean d (fun d' => trueCost M d' w i) ≤
      mainMean d (fun d' => (d'.C ∩ trueGroup M d w i).card +
        (d'.C ∩ higherTrueGroups M d w i).card +
          (higherTrueGroups M d w i).card / densityThreshold) := by
    apply mainMean_mono
    intro d' hH
    have hc := trueCost_le_true_counts M d' w i
    rwa [trueGroup_eq_of_H_eq M d d' w i hH,
      higherTrueGroups_eq_of_H_eq M d d' w i hH] at hc
  simp only [mainMean_add, mainMean_guard_count, mainMean_const] at hm
  convert hm using 1
  ring

/-- Exact finite true-level sum presentation of `eq:expected-cost`. -/
theorem expected_cost_sum (M : Matroid (Fin n)) (d : MainMasks n)
    (w : Fin n → Option ℤ) (i : ℤ) :
    mainMean d (fun d' => trueCost M d' w i) ≤
      thinningRate * (trueGroup M d w i).card +
        (thinningRate + 1 / densityThreshold) *
          ∑ j ∈ trueLevels M w d.H with i < j, ((trueGroup M d w j).card : ℝ) := by
  rw [← higherTrueGroups_card_eq_sum M d w i]
  exact expected_cost M d w i

end MatroidProphet.AccountingContracts

end OAI
