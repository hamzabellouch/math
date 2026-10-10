import OAI.NumberTheory.Catalan.Estimates.ManuscriptCaseOneY0PointRounding

namespace OAI

section

noncomputable section
namespace InternalCatalan

theorem manuscript_case1Y1_actual_substitution_error :
    |barrierCase1Y (Case1PointData.Y1 : ℝ) - (manuscriptCase1Y1SubstituteRat : ℝ)| < ((14 / 1000000000000000) : ℝ) := by
  have hw : manuscriptCase1Y1Interval.2 - manuscriptCase1Y1Interval.1 < ((14 / 1000000000000000) : ℚ) :=
    manuscript_case1Y1_interval_width.trans (by norm_num)
  simpa only [Rat.cast_div, Rat.cast_ofNat] using manuscript_interval_abs_sub_lt_of_width
    manuscriptCase1Y1Interval.1 manuscriptCase1Y1Interval.2 manuscriptCase1Y1SubstituteRat
    (barrierCase1Y (Case1PointData.Y1 : ℝ)) (14 / 1000000000000000)
    manuscript_case1Y1_interval manuscript_case1Y1_substitute_interval hw

end InternalCatalan

end

end

end OAI
