import OAI.Analysis.CircleDomains.Probability.DelayedTupleMeasure

namespace OAI

/-! Positive weights of total mass at most one on the prescribed countable
point and tuple-type sets. Their squares have the same upper bound. -/

open Function
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem sum_slotWeight_succ : (∑' k, slotWeight (k + 1)) = 1 := by
  simp_rw [Nat.add_comm _ 1, slotWeight_add]
  rw [ENNReal.tsum_mul_left, tsum_slotWeight]
  simpa only [slotWeight, pow_one] using
    (ENNReal.inv_mul_cancel (a := 2) (by norm_num) (by norm_num))

theorem exists_positive_summable_weights (D : Type*) [Countable D] :
    ∃ c : D → ℝ≥0∞, (∀ s, 0 < c s) ∧ (∑' s, c s) ≤ 1 := by
  classical
  let := Encodable.ofCountable D
  refine ⟨fun s => slotWeight (Encodable.encode s + 1), fun s => slotWeight_pos _, ?_⟩
  exact (ENNReal.tsum_comp_le_tsum_of_injective Encodable.encode_injective
    (fun k => slotWeight (k + 1))).trans_eq sum_slotWeight_succ

theorem exists_positive_square_summable_weights (D : Type*) [Countable D] :
    ∃ c : D → ℝ≥0∞, (∀ s, 0 < c s) ∧ (∑' s, (c s) ^ 2) ≤ 1 := by
  obtain ⟨c, hc, hsum⟩ := exists_positive_summable_weights D
  refine ⟨c, hc, le_trans (ENNReal.tsum_le_tsum fun s => ?_) hsum⟩
  have hs : c s ≤ 1 := (ENNReal.le_tsum s).trans hsum
  simpa only [pow_two, mul_one] using mul_le_mul' (le_refl (c s)) hs

end CircleDomainRigidity

end

end OAI
