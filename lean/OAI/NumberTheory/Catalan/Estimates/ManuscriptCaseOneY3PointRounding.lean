import OAI.NumberTheory.Catalan.Estimates.ManuscriptCaseOneY0PointRounding

namespace OAI

section

noncomputable section

namespace InternalCatalan

def manuscriptCase1Y3RoundedSubstituteRat : ℚ :=
  manuscriptRoundedYFieldRat (barrierCase1YRat Case1PointData.Y3) (-1) (-3) (7966939383 / 5000000000) (2033060617 / 1250000000)

theorem manuscript_case1Y3_additional_rounding_error :
    |(manuscriptCase1Y3SubstituteRat : ℝ) - (manuscriptCase1Y3RoundedSubstituteRat : ℝ)| < (1 / 10 ^ 32 : ℝ) := by
  let a0 : ℚ := barrierCase1YApproxRat Case1PointData.Y3 (-1) (-3) (7966939383 / 5000000000) (2033060617 / 1250000000)
  let r0 : ℚ := manuscriptRoundedYFieldRat (barrierCase1YRat Case1PointData.Y3) (-1) (-3) (7966939383 / 5000000000) (2033060617 / 1250000000)
  let e0 : ℝ := ((7 / 48 : ℝ) + 1 / 12) * (3636 * manuscriptTermRoundStep)
  have h0 : |(a0 : ℝ) - (r0 : ℝ)| ≤ e0 := by
    exact manuscript_rounded_y_field_error_le (barrierCase1YRat Case1PointData.Y3) (-1) (-3) (7966939383 / 5000000000) (2033060617 / 1250000000) (by norm_num) (by norm_num)
  have hbudget : e0 < (1 / 10 ^ 32 : ℝ) := by
    norm_num [e0, manuscriptTermRoundStep]
  change |(manuscriptCase1Y3SubstituteRat : ℝ) - (manuscriptCase1Y3RoundedSubstituteRat : ℝ)| ≤ e0 at h0
  exact h0.trans_lt hbudget

end InternalCatalan

end

end

end OAI
