import OAI.Combinatorics.EditApproximation.Coarse.CoarseSliceCopy
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation

/-- This guard uses interval endpoints before either input slice is copied. -/


theorem coarseInputGuardWithWork_value (sourceLo sourceHi targetLo targetHi : ℕ) :
    (coarseInputGuardWithWork sourceLo sourceHi targetLo targetHi).1 =
      decide (2 * (sourceHi - sourceLo) < targetHi - targetLo) := by
  apply Bool.eq_iff_iff.mpr
  simp only [coarseInputGuardWithWork, saturatingSubtractWithWork_value,
    binaryNaturalMulWithWork_value, decide_eq_true_eq, binaryNaturalCompareWithWork_lt]

theorem coarseInputGuardWithWork_cost (sourceLo sourceHi targetLo targetHi A : ℕ)
    (hslo : Nat.size sourceLo ≤ A) (hshi : Nat.size sourceHi ≤ A)
    (htlo : Nat.size targetLo ≤ A) (hthi : Nat.size targetHi ≤ A) :
    (coarseInputGuardWithWork sourceLo sourceHi targetLo targetHi).2 ≤ 1000 * (A + 1) := by
  have hs := saturatingSubtractWithWork_cost sourceHi sourceLo
  have ht := saturatingSubtractWithWork_cost targetHi targetLo
  have hsw : Nat.size (sourceHi - sourceLo) ≤ A :=
    (Nat.size_le_size (Nat.sub_le _ _)).trans hshi
  have htw : Nat.size (targetHi - targetLo) ≤ A :=
    (Nat.size_le_size (Nat.sub_le _ _)).trans hthi
  have hm := binaryNaturalMulWithWork_cost 2 (sourceHi - sourceLo)
  have hmw := natural_product_bit_length 2 (sourceHi - sourceLo)
  have hc := binaryNaturalCompareWithWork_cost (2 * (sourceHi - sourceLo)) (targetHi - targetLo)
  rw [show Nat.size 2 = 2 by decide] at hm hmw
  simp only [coarseInputGuardWithWork, saturatingSubtractWithWork_value, binaryNaturalMulWithWork_value]
  omega

/-- The optional copied pair is absent on the long-target branch. -/


theorem coarsePreparedSlicesWithWork_value (source target : List ℕ)
    (sourceLo sourceHi targetLo targetHi : ℕ)
    (hslo : sourceLo ≤ sourceHi) (hshi : sourceHi ≤ source.length)
    (htlo : targetLo ≤ targetHi) (hthi : targetHi ≤ target.length) :
    (coarsePreparedSlicesWithWork source target sourceLo sourceHi targetLo targetHi).1 =
      if 2 * (sourceHi - sourceLo) < targetHi - targetLo then none else
      some (substring source sourceLo sourceHi, substring target targetLo targetHi) := by
  simp only [coarsePreparedSlicesWithWork, coarseInputGuardWithWork_value, decide_eq_true_eq]
  split_ifs
  · rfl
  · simp only [coarseRangeCopyWithWork_slice source sourceLo sourceHi hslo hshi,
      coarseRangeCopyWithWork_slice target targetLo targetHi htlo hthi]

end EditApproximation

end OAI
