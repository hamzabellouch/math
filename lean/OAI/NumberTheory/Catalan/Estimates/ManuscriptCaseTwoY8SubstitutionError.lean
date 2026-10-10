import OAI.NumberTheory.Catalan.Estimates.ManuscriptCaseTwoYAllPrecision

namespace OAI

section

noncomputable section
namespace InternalCatalan

theorem manuscript_case2Y8_actual_substitution_error :
    |barrierCase2Y (Case2PointData.Y8 : ℝ) - (manuscriptCase2Y8SubstituteRat : ℝ)| < ((14 / 1000000000000000) : ℝ) := by
  have hw : manuscriptCase2Y8Interval.2 - manuscriptCase2Y8Interval.1 < ((14 / 1000000000000000) : ℚ) :=
    manuscript_case2Y8_interval_width.trans (by norm_num)
  simpa only [Rat.cast_div, Rat.cast_ofNat] using manuscript_interval_abs_sub_lt_of_width
    manuscriptCase2Y8Interval.1 manuscriptCase2Y8Interval.2 manuscriptCase2Y8SubstituteRat
    (barrierCase2Y (Case2PointData.Y8 : ℝ)) (14 / 1000000000000000)
    manuscript_case2Y8_interval manuscript_case2Y8_substitute_interval hw

end InternalCatalan

end

end

end OAI
