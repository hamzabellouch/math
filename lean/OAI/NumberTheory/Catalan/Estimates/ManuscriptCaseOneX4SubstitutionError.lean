import OAI.NumberTheory.Catalan.Estimates.ManuscriptCaseOneX4PointRounding

namespace OAI

section

noncomputable section
namespace InternalCatalan

theorem manuscript_case1X4_actual_substitution_error :
    |barrierCase1X (Case1PointData.X4 : ℝ) - (manuscriptCase1X4SubstituteRat : ℝ)| < ((35 / 1000000000000000) : ℝ) := by
  have hw : manuscriptCase1X4Interval.2 - manuscriptCase1X4Interval.1 < ((35 / 1000000000000000) : ℚ) :=
    manuscript_case1X4_interval_width.trans (by norm_num)
  simpa only [Rat.cast_div, Rat.cast_ofNat] using manuscript_interval_abs_sub_lt_of_width
    manuscriptCase1X4Interval.1 manuscriptCase1X4Interval.2 manuscriptCase1X4SubstituteRat
    (barrierCase1X (Case1PointData.X4 : ℝ)) (35 / 1000000000000000)
    manuscript_case1X4_interval manuscript_case1X4_substitute_interval hw

end InternalCatalan

end

end

end OAI
