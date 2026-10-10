import OAI.Analysis.IrrationalRotation.Model.Analytic

namespace OAI

open scoped ENNReal

namespace Invariant233

theorem extendedExpNeg_eq_exp_toReal (a : ℝ≥0∞) (ha : a ≠ ∞) :
    (EReal.exp (-(a : EReal))).toReal = Real.exp (-a.toReal) := by
  rw [← EReal.coe_ennreal_toReal ha, ← EReal.coe_neg, EReal.exp_coe,
    ENNReal.toReal_ofReal (Real.exp_pos _).le]

theorem extendedExpNeg_eq_zero_iff (a : ℝ≥0∞) :
    (EReal.exp (-(a : EReal))).toReal = 0 ↔ a = ∞ := by
  by_cases ha : a = ∞
  · simp [ha]
  · rw [extendedExpNeg_eq_exp_toReal a ha]
    simp [Real.exp_ne_zero, ha]

theorem extendedExpNeg_mem_Icc (a : ℝ≥0∞) :
    (EReal.exp (-(a : EReal))).toReal ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases ha : a = ∞
  · simp [ha]
  · rw [extendedExpNeg_eq_exp_toReal a ha]
    exact ⟨(Real.exp_pos _).le,
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr ENNReal.toReal_nonneg)⟩

theorem negLogCost_extendedExpNeg (a : ℝ≥0∞) :
    negLogCost ((EReal.exp (-(a : EReal))).toReal) = a := by
  by_cases ha : a = ∞
  · simp [ha, negLogCost]
  · rw [extendedExpNeg_eq_exp_toReal a ha]
    simp only [negLogCost, Real.exp_ne_zero, ite_false,
      abs_of_pos (Real.exp_pos _), Real.log_exp, neg_neg]
    exact ENNReal.ofReal_toReal ha

end Invariant233

end OAI
