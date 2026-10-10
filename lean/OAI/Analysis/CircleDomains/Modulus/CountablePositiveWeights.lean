import OAI.Analysis.CircleDomains.Modulus.PositiveCountableWeights

namespace OAI

/-! Finite positive costs on countable mark sets, from geometric weights
of total mass at most one. -/

open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

theorem exists_positive_finite_square_weights (S : Type*) [Countable S] :
    ∃ w : S → ℝ≥0∞, (∀ s, w s ≠ 0) ∧ (∀ s, w s ≠ ∞) ∧
      (∑' s, w s) < ∞ ∧ (∑' s, w s ^ 2) < ∞ := by
  obtain ⟨w, hw, hsum⟩ := exists_positive_summable_weights S
  have hw1 : ∀ s, w s ≤ 1 := fun s => (ENNReal.le_tsum s).trans hsum
  refine ⟨w, fun s => (hw s).ne', fun s => ne_of_lt ((hw1 s).trans_lt (by simp)),
    hsum.trans_lt (by simp), ?_⟩
  apply lt_of_le_of_lt (ENNReal.tsum_le_tsum ?_) (hsum.trans_lt (by simp))
  intro s
  simpa only [pow_two, mul_one] using mul_le_mul' le_rfl (hw1 s)

end CircleDomainRigidity

end

end OAI
