import OAI.NumberTheory.Catalan.Estimates.ManuscriptCaseOneX4PointRounding

namespace OAI

section

noncomputable section

namespace InternalCatalan

def manuscriptCase1X5SubstituteRat : ℚ :=
  barrierCase1XApproxRat Case1PointData.X5 (0) (1) (1) (1 / 1) (1 / 1) (1 / 1)

theorem manuscript_case1X5_substitute_interval :
    manuscriptCase1X5SubstituteRat ∈ Set.Icc manuscriptCase1X5Interval.1 manuscriptCase1X5Interval.2 := by
  have hf := manuscript_x_substitute_interval (41 / 48) (barrierCase1XRat Case1PointData.X5) (0) (1) (1) (1 / 1) (1 / 1) (1 / 1) (by norm_num) (by norm_num) (by norm_num)
  change (barrierCase1XApproxRat Case1PointData.X5 (0) (1) (1) (1 / 1) (1 / 1) (1 / 1)) ∈ Set.Icc manuscriptCase1X5Interval.1 manuscriptCase1X5Interval.2 at hf
  exact hf

theorem manuscript_case1X5_substitute_cutoff :
    manuscriptCase1X5SubstituteRat < ((-66221 / 50000) : ℚ) := by
  have hp : Case1PointData.X5PrintedUpper < ((-66221 / 50000) : ℚ) := by norm_num [Case1PointData.X5PrintedUpper]
  exact manuscript_case1X5_substitute_interval.2.trans_lt (manuscript_case1X5_endpoint_lt_printed.trans hp)

end InternalCatalan

end

end

section

noncomputable section

namespace InternalCatalan

def manuscriptCase1X5RoundedSubstituteRat : ℚ :=
  manuscriptRoundedXFieldRat (41 / 48) (barrierCase1XRat Case1PointData.X5) (0) (1) (1) (1 / 1) (1 / 1) (1 / 1)

theorem manuscript_case1X5_additional_rounding_error :
    |(manuscriptCase1X5SubstituteRat : ℝ) - (manuscriptCase1X5RoundedSubstituteRat : ℝ)| < (1 / 10 ^ 32 : ℝ) := by
  let a0 : ℚ := barrierCase1XApproxRat Case1PointData.X5 (0) (1) (1) (1 / 1) (1 / 1) (1 / 1)
  let r0 : ℚ := manuscriptRoundedXFieldRat (41 / 48) (barrierCase1XRat Case1PointData.X5) (0) (1) (1) (1 / 1) (1 / 1) (1 / 1)
  let e0 : ℝ := ((19 / 48 : ℝ) + 1 / 12 + |(((41 / 48) : ℚ) : ℝ)|) * (3636 * manuscriptTermRoundStep)
  have h0 : |(a0 : ℝ) - (r0 : ℝ)| ≤ e0 := by
    exact manuscript_rounded_x_field_error_le (41 / 48) (barrierCase1XRat Case1PointData.X5) (0) (1) (1) (1 / 1) (1 / 1) (1 / 1) (by norm_num) (by norm_num) (by norm_num)
  have hbudget : e0 < (1 / 10 ^ 32 : ℝ) := by
    norm_num [e0, manuscriptTermRoundStep]
  change |(manuscriptCase1X5SubstituteRat : ℝ) - (manuscriptCase1X5RoundedSubstituteRat : ℝ)| ≤ e0 at h0
  exact h0.trans_lt hbudget

end InternalCatalan

end

end

section

noncomputable section
namespace InternalCatalan

theorem manuscript_case1X5_actual_substitution_error :
    |barrierCase1X (Case1PointData.X5 : ℝ) - (manuscriptCase1X5SubstituteRat : ℝ)| < ((35 / 1000000000000000) : ℝ) := by
  have hw : manuscriptCase1X5Interval.2 - manuscriptCase1X5Interval.1 < ((35 / 1000000000000000) : ℚ) :=
    manuscript_case1X5_interval_width.trans (by norm_num)
  simpa only [Rat.cast_div, Rat.cast_ofNat] using manuscript_interval_abs_sub_lt_of_width
    manuscriptCase1X5Interval.1 manuscriptCase1X5Interval.2 manuscriptCase1X5SubstituteRat
    (barrierCase1X (Case1PointData.X5 : ℝ)) (35 / 1000000000000000)
    manuscript_case1X5_interval manuscript_case1X5_substitute_interval hw

end InternalCatalan

end

end

end OAI
