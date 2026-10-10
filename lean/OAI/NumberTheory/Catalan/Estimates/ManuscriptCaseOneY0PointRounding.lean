import OAI.NumberTheory.Catalan.Estimates.ManuscriptCaseOneX4PointRounding

namespace OAI

section

noncomputable section
namespace InternalCatalan
open Case1PointData

def manuscriptCase1Y0Interval : ℚ × ℚ :=
  manuscriptYLogFieldInterval (barrierCase1YRat Y0) (-5) (-1) (266334893 / 156250000) (4733665107 / 2500000000)

theorem manuscript_case1Y0_interval :
    barrierCase1Y (Y0 : ℝ) ∈ Set.Icc (manuscriptCase1Y0Interval.1 : ℝ) (manuscriptCase1Y0Interval.2 : ℝ) :=
  manuscript_case1Y_interval Y0 (-5) (-1) (266334893 / 156250000) (4733665107 / 2500000000) Y0_normalizations.1 Y0_normalizations.2

theorem manuscript_case1Y0_endpoint_lt_printed :
    manuscriptCase1Y0Interval.2 < Y0PrintedUpper := by
  unfold manuscriptCase1Y0Interval manuscriptYLogFieldInterval barrierCase1YRat
  rw [barrierCase1TV_eq_explicit]
  simp only [manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, barrierLogHRat_two_eq]
  decide +kernel

theorem manuscript_case1Y0_interval_width :
    manuscriptCase1Y0Interval.2 - manuscriptCase1Y0Interval.1 < (216146856249281 / 1000000000000000000000000000000 : ℚ) := by
  unfold manuscriptCase1Y0Interval manuscriptYLogFieldInterval barrierCase1YRat
  rw [barrierCase1TV_eq_explicit]
  simp only [manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, barrierLogHRat_two_eq]
  decide +kernel

theorem manuscript_case1Y0_printed_upper :
    barrierCase1Y (Y0 : ℝ) < (Y0PrintedUpper : ℝ) :=
  manuscript_case1Y0_interval.2.trans_lt
    ((Rat.cast_lt (K := ℝ)).2 manuscript_case1Y0_endpoint_lt_printed)

end InternalCatalan

end

end

section

noncomputable section
namespace InternalCatalan
open Case1PointData

def manuscriptCase1Y1Interval : ℚ × ℚ :=
  manuscriptYLogFieldInterval (barrierCase1YRat Y1) (-2) (-1) (100169573 / 100000000) (299830427 / 200000000)

theorem manuscript_case1Y1_interval :
    barrierCase1Y (Y1 : ℝ) ∈ Set.Icc (manuscriptCase1Y1Interval.1 : ℝ) (manuscriptCase1Y1Interval.2 : ℝ) :=
  manuscript_case1Y_interval Y1 (-2) (-1) (100169573 / 100000000) (299830427 / 200000000) Y1_normalizations.1 Y1_normalizations.2

theorem manuscript_case1Y1_endpoint_lt_printed :
    manuscriptCase1Y1Interval.2 < Y1PrintedUpper := by
  unfold manuscriptCase1Y1Interval manuscriptYLogFieldInterval barrierCase1YRat
  rw [barrierCase1TV_eq_explicit]
  simp only [manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, barrierLogHRat_two_eq]
  decide +kernel

theorem manuscript_case1Y1_interval_width :
    manuscriptCase1Y1Interval.2 - manuscriptCase1Y1Interval.1 < (216146856249281 / 1000000000000000000000000000000 : ℚ) := by
  unfold manuscriptCase1Y1Interval manuscriptYLogFieldInterval barrierCase1YRat
  rw [barrierCase1TV_eq_explicit]
  simp only [manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, barrierLogHRat_two_eq]
  decide +kernel

theorem manuscript_case1Y1_printed_upper :
    barrierCase1Y (Y1 : ℝ) < (Y1PrintedUpper : ℝ) :=
  manuscript_case1Y1_interval.2.trans_lt
    ((Rat.cast_lt (K := ℝ)).2 manuscript_case1Y1_endpoint_lt_printed)

end InternalCatalan

end

end

section

noncomputable section
namespace InternalCatalan
open Case1PointData

def manuscriptCase1Y2Interval : ℚ × ℚ :=
  manuscriptYLogFieldInterval (barrierCase1YRat Y2) (-1) (-2) (2850869403 / 2500000000) (2149130597 / 1250000000)

theorem manuscript_case1Y2_interval :
    barrierCase1Y (Y2 : ℝ) ∈ Set.Icc (manuscriptCase1Y2Interval.1 : ℝ) (manuscriptCase1Y2Interval.2 : ℝ) :=
  manuscript_case1Y_interval Y2 (-1) (-2) (2850869403 / 2500000000) (2149130597 / 1250000000) Y2_normalizations.1 Y2_normalizations.2

theorem manuscript_case1Y2_endpoint_lt_printed :
    manuscriptCase1Y2Interval.2 < Y2PrintedUpper := by
  unfold manuscriptCase1Y2Interval manuscriptYLogFieldInterval barrierCase1YRat
  rw [barrierCase1TV_eq_explicit]
  simp only [manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, barrierLogHRat_two_eq]
  decide +kernel

theorem manuscript_case1Y2_interval_width :
    manuscriptCase1Y2Interval.2 - manuscriptCase1Y2Interval.1 < (216146856249281 / 1000000000000000000000000000000 : ℚ) := by
  unfold manuscriptCase1Y2Interval manuscriptYLogFieldInterval barrierCase1YRat
  rw [barrierCase1TV_eq_explicit]
  simp only [manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, barrierLogHRat_two_eq]
  decide +kernel

theorem manuscript_case1Y2_printed_upper :
    barrierCase1Y (Y2 : ℝ) < (Y2PrintedUpper : ℝ) :=
  manuscript_case1Y2_interval.2.trans_lt
    ((Rat.cast_lt (K := ℝ)).2 manuscript_case1Y2_endpoint_lt_printed)

end InternalCatalan

end

end

section

noncomputable section
namespace InternalCatalan
open Case1PointData

def manuscriptCase1Y3Interval : ℚ × ℚ :=
  manuscriptYLogFieldInterval (barrierCase1YRat Y3) (-1) (-3) (7966939383 / 5000000000) (2033060617 / 1250000000)

theorem manuscript_case1Y3_interval :
    barrierCase1Y (Y3 : ℝ) ∈ Set.Icc (manuscriptCase1Y3Interval.1 : ℝ) (manuscriptCase1Y3Interval.2 : ℝ) :=
  manuscript_case1Y_interval Y3 (-1) (-3) (7966939383 / 5000000000) (2033060617 / 1250000000) Y3_normalizations.1 Y3_normalizations.2

theorem manuscript_case1Y3_endpoint_lt_printed :
    manuscriptCase1Y3Interval.2 < Y3PrintedUpper := by
  unfold manuscriptCase1Y3Interval manuscriptYLogFieldInterval barrierCase1YRat
  rw [barrierCase1TV_eq_explicit]
  simp only [manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, barrierLogHRat_two_eq]
  decide +kernel

theorem manuscript_case1Y3_interval_width :
    manuscriptCase1Y3Interval.2 - manuscriptCase1Y3Interval.1 < (216146856249281 / 1000000000000000000000000000000 : ℚ) := by
  unfold manuscriptCase1Y3Interval manuscriptYLogFieldInterval barrierCase1YRat
  rw [barrierCase1TV_eq_explicit]
  simp only [manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, barrierLogHRat_two_eq]
  decide +kernel

theorem manuscript_case1Y3_printed_upper :
    barrierCase1Y (Y3 : ℝ) < (Y3PrintedUpper : ℝ) :=
  manuscript_case1Y3_interval.2.trans_lt
    ((Rat.cast_lt (K := ℝ)).2 manuscript_case1Y3_endpoint_lt_printed)

end InternalCatalan

end

end

section

noncomputable section
namespace InternalCatalan
open Case1PointData

def manuscriptCase1Y4Interval : ℚ × ℚ :=
  manuscriptYLogFieldInterval (barrierCase1YRat Y4) (-1) (-5) (4727245069 / 2500000000) (272754931 / 156250000)

theorem manuscript_case1Y4_interval :
    barrierCase1Y (Y4 : ℝ) ∈ Set.Icc (manuscriptCase1Y4Interval.1 : ℝ) (manuscriptCase1Y4Interval.2 : ℝ) :=
  manuscript_case1Y_interval Y4 (-1) (-5) (4727245069 / 2500000000) (272754931 / 156250000) Y4_normalizations.1 Y4_normalizations.2

theorem manuscript_case1Y4_endpoint_lt_printed :
    manuscriptCase1Y4Interval.2 < Y4PrintedUpper := by
  unfold manuscriptCase1Y4Interval manuscriptYLogFieldInterval barrierCase1YRat
  rw [barrierCase1TV_eq_explicit]
  simp only [manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, barrierLogHRat_two_eq]
  decide +kernel

theorem manuscript_case1Y4_interval_width :
    manuscriptCase1Y4Interval.2 - manuscriptCase1Y4Interval.1 < (216146856249281 / 1000000000000000000000000000000 : ℚ) := by
  unfold manuscriptCase1Y4Interval manuscriptYLogFieldInterval barrierCase1YRat
  rw [barrierCase1TV_eq_explicit]
  simp only [manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, barrierLogHRat_two_eq]
  decide +kernel

theorem manuscript_case1Y4_printed_upper :
    barrierCase1Y (Y4 : ℝ) < (Y4PrintedUpper : ℝ) :=
  manuscript_case1Y4_interval.2.trans_lt
    ((Rat.cast_lt (K := ℝ)).2 manuscript_case1Y4_endpoint_lt_printed)

end InternalCatalan

end

end

section

noncomputable section
namespace InternalCatalan

def manuscriptCase1YPrecisionClaims : Prop :=
  (barrierCase1Y (Case1PointData.Y0 : ℝ) ∈ Set.Icc (manuscriptCase1Y0Interval.1 : ℝ) (manuscriptCase1Y0Interval.2 : ℝ) ∧
    manuscriptCase1Y0Interval.2 < Case1PointData.Y0PrintedUpper ∧
    manuscriptCase1Y0Interval.2 - manuscriptCase1Y0Interval.1 < (216146856249281 / 1000000000000000000000000000000 : ℚ) ∧
    barrierCase1Y (Case1PointData.Y0 : ℝ) < (Case1PointData.Y0PrintedUpper : ℝ)) ∧
  (barrierCase1Y (Case1PointData.Y1 : ℝ) ∈ Set.Icc (manuscriptCase1Y1Interval.1 : ℝ) (manuscriptCase1Y1Interval.2 : ℝ) ∧
    manuscriptCase1Y1Interval.2 < Case1PointData.Y1PrintedUpper ∧
    manuscriptCase1Y1Interval.2 - manuscriptCase1Y1Interval.1 < (216146856249281 / 1000000000000000000000000000000 : ℚ) ∧
    barrierCase1Y (Case1PointData.Y1 : ℝ) < (Case1PointData.Y1PrintedUpper : ℝ)) ∧
  (barrierCase1Y (Case1PointData.Y2 : ℝ) ∈ Set.Icc (manuscriptCase1Y2Interval.1 : ℝ) (manuscriptCase1Y2Interval.2 : ℝ) ∧
    manuscriptCase1Y2Interval.2 < Case1PointData.Y2PrintedUpper ∧
    manuscriptCase1Y2Interval.2 - manuscriptCase1Y2Interval.1 < (216146856249281 / 1000000000000000000000000000000 : ℚ) ∧
    barrierCase1Y (Case1PointData.Y2 : ℝ) < (Case1PointData.Y2PrintedUpper : ℝ)) ∧
  (barrierCase1Y (Case1PointData.Y3 : ℝ) ∈ Set.Icc (manuscriptCase1Y3Interval.1 : ℝ) (manuscriptCase1Y3Interval.2 : ℝ) ∧
    manuscriptCase1Y3Interval.2 < Case1PointData.Y3PrintedUpper ∧
    manuscriptCase1Y3Interval.2 - manuscriptCase1Y3Interval.1 < (216146856249281 / 1000000000000000000000000000000 : ℚ) ∧
    barrierCase1Y (Case1PointData.Y3 : ℝ) < (Case1PointData.Y3PrintedUpper : ℝ)) ∧
  (barrierCase1Y (Case1PointData.Y4 : ℝ) ∈ Set.Icc (manuscriptCase1Y4Interval.1 : ℝ) (manuscriptCase1Y4Interval.2 : ℝ) ∧
    manuscriptCase1Y4Interval.2 < Case1PointData.Y4PrintedUpper ∧
    manuscriptCase1Y4Interval.2 - manuscriptCase1Y4Interval.1 < (216146856249281 / 1000000000000000000000000000000 : ℚ) ∧
    barrierCase1Y (Case1PointData.Y4 : ℝ) < (Case1PointData.Y4PrintedUpper : ℝ))

theorem manuscript_case1Y_all_precision : manuscriptCase1YPrecisionClaims := by
  exact ⟨⟨manuscript_case1Y0_interval, manuscript_case1Y0_endpoint_lt_printed, manuscript_case1Y0_interval_width, manuscript_case1Y0_printed_upper⟩,
    ⟨manuscript_case1Y1_interval, manuscript_case1Y1_endpoint_lt_printed, manuscript_case1Y1_interval_width, manuscript_case1Y1_printed_upper⟩,
    ⟨manuscript_case1Y2_interval, manuscript_case1Y2_endpoint_lt_printed, manuscript_case1Y2_interval_width, manuscript_case1Y2_printed_upper⟩,
    ⟨manuscript_case1Y3_interval, manuscript_case1Y3_endpoint_lt_printed, manuscript_case1Y3_interval_width, manuscript_case1Y3_printed_upper⟩,
    ⟨manuscript_case1Y4_interval, manuscript_case1Y4_endpoint_lt_printed, manuscript_case1Y4_interval_width, manuscript_case1Y4_printed_upper⟩⟩

end InternalCatalan

end

end

section

noncomputable section

namespace InternalCatalan

def manuscriptCase1Y0SubstituteRat : ℚ :=
  barrierCase1YApproxRat Case1PointData.Y0 (-5) (-1) (266334893 / 156250000) (4733665107 / 2500000000)

theorem manuscript_case1Y0_substitute_interval :
    manuscriptCase1Y0SubstituteRat ∈ Set.Icc manuscriptCase1Y0Interval.1 manuscriptCase1Y0Interval.2 := by
  have hf := manuscript_y_substitute_interval (barrierCase1YRat Case1PointData.Y0) (-5) (-1) (266334893 / 156250000) (4733665107 / 2500000000) (by norm_num) (by norm_num)
  change (barrierCase1YApproxRat Case1PointData.Y0 (-5) (-1) (266334893 / 156250000) (4733665107 / 2500000000)) ∈ Set.Icc manuscriptCase1Y0Interval.1 manuscriptCase1Y0Interval.2 at hf
  exact hf

theorem manuscript_case1Y0_substitute_cutoff :
    manuscriptCase1Y0SubstituteRat < ((-28561 / 20000) : ℚ) := by
  have hp : Case1PointData.Y0PrintedUpper < ((-28561 / 20000) : ℚ) := by norm_num [Case1PointData.Y0PrintedUpper]
  exact manuscript_case1Y0_substitute_interval.2.trans_lt (manuscript_case1Y0_endpoint_lt_printed.trans hp)

end InternalCatalan

end

end

section

noncomputable section

namespace InternalCatalan

def manuscriptCase1Y1SubstituteRat : ℚ :=
  barrierCase1YApproxRat Case1PointData.Y1 (-2) (-1) (100169573 / 100000000) (299830427 / 200000000)

theorem manuscript_case1Y1_substitute_interval :
    manuscriptCase1Y1SubstituteRat ∈ Set.Icc manuscriptCase1Y1Interval.1 manuscriptCase1Y1Interval.2 := by
  have hf := manuscript_y_substitute_interval (barrierCase1YRat Case1PointData.Y1) (-2) (-1) (100169573 / 100000000) (299830427 / 200000000) (by norm_num) (by norm_num)
  change (barrierCase1YApproxRat Case1PointData.Y1 (-2) (-1) (100169573 / 100000000) (299830427 / 200000000)) ∈ Set.Icc manuscriptCase1Y1Interval.1 manuscriptCase1Y1Interval.2 at hf
  exact hf

theorem manuscript_case1Y1_substitute_cutoff :
    manuscriptCase1Y1SubstituteRat < ((-28561 / 20000) : ℚ) := by
  have hp : Case1PointData.Y1PrintedUpper < ((-28561 / 20000) : ℚ) := by norm_num [Case1PointData.Y1PrintedUpper]
  exact manuscript_case1Y1_substitute_interval.2.trans_lt (manuscript_case1Y1_endpoint_lt_printed.trans hp)

end InternalCatalan

end

end

section

noncomputable section

namespace InternalCatalan

def manuscriptCase1Y2SubstituteRat : ℚ :=
  barrierCase1YApproxRat Case1PointData.Y2 (-1) (-2) (2850869403 / 2500000000) (2149130597 / 1250000000)

theorem manuscript_case1Y2_substitute_interval :
    manuscriptCase1Y2SubstituteRat ∈ Set.Icc manuscriptCase1Y2Interval.1 manuscriptCase1Y2Interval.2 := by
  have hf := manuscript_y_substitute_interval (barrierCase1YRat Case1PointData.Y2) (-1) (-2) (2850869403 / 2500000000) (2149130597 / 1250000000) (by norm_num) (by norm_num)
  change (barrierCase1YApproxRat Case1PointData.Y2 (-1) (-2) (2850869403 / 2500000000) (2149130597 / 1250000000)) ∈ Set.Icc manuscriptCase1Y2Interval.1 manuscriptCase1Y2Interval.2 at hf
  exact hf

theorem manuscript_case1Y2_substitute_cutoff :
    manuscriptCase1Y2SubstituteRat < ((-28561 / 20000) : ℚ) := by
  have hp : Case1PointData.Y2PrintedUpper < ((-28561 / 20000) : ℚ) := by norm_num [Case1PointData.Y2PrintedUpper]
  exact manuscript_case1Y2_substitute_interval.2.trans_lt (manuscript_case1Y2_endpoint_lt_printed.trans hp)

end InternalCatalan

end

end

section

noncomputable section

namespace InternalCatalan

def manuscriptCase1Y3SubstituteRat : ℚ :=
  barrierCase1YApproxRat Case1PointData.Y3 (-1) (-3) (7966939383 / 5000000000) (2033060617 / 1250000000)

theorem manuscript_case1Y3_substitute_interval :
    manuscriptCase1Y3SubstituteRat ∈ Set.Icc manuscriptCase1Y3Interval.1 manuscriptCase1Y3Interval.2 := by
  have hf := manuscript_y_substitute_interval (barrierCase1YRat Case1PointData.Y3) (-1) (-3) (7966939383 / 5000000000) (2033060617 / 1250000000) (by norm_num) (by norm_num)
  change (barrierCase1YApproxRat Case1PointData.Y3 (-1) (-3) (7966939383 / 5000000000) (2033060617 / 1250000000)) ∈ Set.Icc manuscriptCase1Y3Interval.1 manuscriptCase1Y3Interval.2 at hf
  exact hf

theorem manuscript_case1Y3_substitute_cutoff :
    manuscriptCase1Y3SubstituteRat < ((-28561 / 20000) : ℚ) := by
  have hp : Case1PointData.Y3PrintedUpper < ((-28561 / 20000) : ℚ) := by norm_num [Case1PointData.Y3PrintedUpper]
  exact manuscript_case1Y3_substitute_interval.2.trans_lt (manuscript_case1Y3_endpoint_lt_printed.trans hp)

end InternalCatalan

end

end

section

noncomputable section

namespace InternalCatalan

def manuscriptCase1Y4SubstituteRat : ℚ :=
  barrierCase1YApproxRat Case1PointData.Y4 (-1) (-5) (4727245069 / 2500000000) (272754931 / 156250000)

theorem manuscript_case1Y4_substitute_interval :
    manuscriptCase1Y4SubstituteRat ∈ Set.Icc manuscriptCase1Y4Interval.1 manuscriptCase1Y4Interval.2 := by
  have hf := manuscript_y_substitute_interval (barrierCase1YRat Case1PointData.Y4) (-1) (-5) (4727245069 / 2500000000) (272754931 / 156250000) (by norm_num) (by norm_num)
  change (barrierCase1YApproxRat Case1PointData.Y4 (-1) (-5) (4727245069 / 2500000000) (272754931 / 156250000)) ∈ Set.Icc manuscriptCase1Y4Interval.1 manuscriptCase1Y4Interval.2 at hf
  exact hf

theorem manuscript_case1Y4_substitute_cutoff :
    manuscriptCase1Y4SubstituteRat < ((-28561 / 20000) : ℚ) := by
  have hp : Case1PointData.Y4PrintedUpper < ((-28561 / 20000) : ℚ) := by norm_num [Case1PointData.Y4PrintedUpper]
  exact manuscript_case1Y4_substitute_interval.2.trans_lt (manuscript_case1Y4_endpoint_lt_printed.trans hp)

end InternalCatalan

end

end

section

noncomputable section

namespace InternalCatalan

def manuscriptCase1Y0RoundedSubstituteRat : ℚ :=
  manuscriptRoundedYFieldRat (barrierCase1YRat Case1PointData.Y0) (-5) (-1) (266334893 / 156250000) (4733665107 / 2500000000)

theorem manuscript_case1Y0_additional_rounding_error :
    |(manuscriptCase1Y0SubstituteRat : ℝ) - (manuscriptCase1Y0RoundedSubstituteRat : ℝ)| < (1 / 10 ^ 32 : ℝ) := by
  let a0 : ℚ := barrierCase1YApproxRat Case1PointData.Y0 (-5) (-1) (266334893 / 156250000) (4733665107 / 2500000000)
  let r0 : ℚ := manuscriptRoundedYFieldRat (barrierCase1YRat Case1PointData.Y0) (-5) (-1) (266334893 / 156250000) (4733665107 / 2500000000)
  let e0 : ℝ := ((7 / 48 : ℝ) + 1 / 12) * (3636 * manuscriptTermRoundStep)
  have h0 : |(a0 : ℝ) - (r0 : ℝ)| ≤ e0 := by
    exact manuscript_rounded_y_field_error_le (barrierCase1YRat Case1PointData.Y0) (-5) (-1) (266334893 / 156250000) (4733665107 / 2500000000) (by norm_num) (by norm_num)
  have hbudget : e0 < (1 / 10 ^ 32 : ℝ) := by
    norm_num [e0, manuscriptTermRoundStep]
  change |(manuscriptCase1Y0SubstituteRat : ℝ) - (manuscriptCase1Y0RoundedSubstituteRat : ℝ)| ≤ e0 at h0
  exact h0.trans_lt hbudget

end InternalCatalan

end

end

end OAI
