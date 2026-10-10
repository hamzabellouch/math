import OAI.NumberTheory.Catalan.Energy.ManuscriptBarrierFieldIntervals
import OAI.NumberTheory.Catalan.FirstBarrier.BarrierCaseOnePointY1

namespace OAI

section

noncomputable section
namespace InternalCatalan
open Case1PointData

def manuscriptCase1X0Interval : ℚ × ℚ :=
  manuscriptXLogFieldInterval (41 / 48) (barrierCase1XRat X0)
    (-1) 0 0 (1983459957 / 1000000000) (3983459957 / 2000000000)
      (7934113401022441849 / 4000000000000000000)

theorem manuscript_case1X0_interval :
    barrierCase1X (X0 : ℝ) ∈ Set.Icc (manuscriptCase1X0Interval.1 : ℝ)
      (manuscriptCase1X0Interval.2 : ℝ) :=
  manuscript_case1X_interval X0 (-1) 0 0 _ _ _
    X0_normalizations.1 X0_normalizations.2.1 X0_normalizations.2.2

theorem manuscript_case1X0_endpoint_lt_printed :
    manuscriptCase1X0Interval.2 < X0PrintedUpper := by
  unfold manuscriptCase1X0Interval manuscriptXLogFieldInterval barrierCase1XRat
  rw [barrierCase1TP_eq_explicit, barrierCase1SV_eq_explicit]
  simp only [manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, barrierLogHRat_two_eq]
  decide +kernel

theorem manuscript_case1X0_interval_width :
    manuscriptCase1X0Interval.2 - manuscriptCase1X0Interval.1 <
      (216146856249281 / 1000000000000000000000000000000 : ℚ) := by
  unfold manuscriptCase1X0Interval manuscriptXLogFieldInterval barrierCase1XRat
  rw [barrierCase1TP_eq_explicit, barrierCase1SV_eq_explicit]
  simp only [manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, barrierLogHRat_two_eq]
  decide +kernel

theorem manuscript_case1X0_printed_upper :
    barrierCase1X (X0 : ℝ) < (X0PrintedUpper : ℝ) :=
  manuscript_case1X0_interval.2.trans_lt
    ((Rat.cast_lt (K := ℝ)).2 manuscript_case1X0_endpoint_lt_printed)

end InternalCatalan

end

end

section

noncomputable section
namespace InternalCatalan
open Case1PointData

def manuscriptCase1X1Interval : ℚ × ℚ :=
  manuscriptXLogFieldInterval (41 / 48) (barrierCase1XRat X1) (-3) (0) (0) (2259572153 / 1250000000) (12259572153 / 10000000000) (105105666314613055409 / 100000000000000000000)

theorem manuscript_case1X1_interval :
    barrierCase1X (X1 : ℝ) ∈ Set.Icc (manuscriptCase1X1Interval.1 : ℝ) (manuscriptCase1X1Interval.2 : ℝ) :=
  manuscript_case1X_interval X1 (-3) (0) (0) (2259572153 / 1250000000) (12259572153 / 10000000000) (105105666314613055409 / 100000000000000000000) X1_normalizations.1 X1_normalizations.2.1 X1_normalizations.2.2

theorem manuscript_case1X1_endpoint_lt_printed :
    manuscriptCase1X1Interval.2 < X1PrintedUpper := by
  unfold manuscriptCase1X1Interval manuscriptXLogFieldInterval barrierCase1XRat
  rw [barrierCase1TP_eq_explicit, barrierCase1SV_eq_explicit]
  simp only [manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, barrierLogHRat_two_eq]
  decide +kernel

theorem manuscript_case1X1_interval_width :
    manuscriptCase1X1Interval.2 - manuscriptCase1X1Interval.1 < (216146856249281 / 1000000000000000000000000000000 : ℚ) := by
  unfold manuscriptCase1X1Interval manuscriptXLogFieldInterval barrierCase1XRat
  rw [barrierCase1TP_eq_explicit, barrierCase1SV_eq_explicit]
  simp only [manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, barrierLogHRat_two_eq]
  decide +kernel

theorem manuscript_case1X1_printed_upper :
    barrierCase1X (X1 : ℝ) < (X1PrintedUpper : ℝ) :=
  manuscript_case1X1_interval.2.trans_lt
    ((Rat.cast_lt (K := ℝ)).2 manuscript_case1X1_endpoint_lt_printed)

end InternalCatalan

end

end

section

noncomputable section
namespace InternalCatalan
open Case1PointData

def manuscriptCase1X2Interval : ℚ × ℚ :=
  manuscriptXLogFieldInterval (41 / 48) (barrierCase1XRat X2) (-2) (-1) (0) (1271904013 / 1250000000) (3728095987 / 2500000000) (26617739818285504169 / 25000000000000000000)

theorem manuscript_case1X2_interval :
    barrierCase1X (X2 : ℝ) ∈ Set.Icc (manuscriptCase1X2Interval.1 : ℝ) (manuscriptCase1X2Interval.2 : ℝ) :=
  manuscript_case1X_interval X2 (-2) (-1) (0) (1271904013 / 1250000000) (3728095987 / 2500000000) (26617739818285504169 / 25000000000000000000) X2_normalizations.1 X2_normalizations.2.1 X2_normalizations.2.2

theorem manuscript_case1X2_endpoint_lt_printed :
    manuscriptCase1X2Interval.2 < X2PrintedUpper := by
  unfold manuscriptCase1X2Interval manuscriptXLogFieldInterval barrierCase1XRat
  rw [barrierCase1TP_eq_explicit, barrierCase1SV_eq_explicit]
  simp only [manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, barrierLogHRat_two_eq]
  decide +kernel

theorem manuscript_case1X2_interval_width :
    manuscriptCase1X2Interval.2 - manuscriptCase1X2Interval.1 < (216146856249281 / 1000000000000000000000000000000 : ℚ) := by
  unfold manuscriptCase1X2Interval manuscriptXLogFieldInterval barrierCase1XRat
  rw [barrierCase1TP_eq_explicit, barrierCase1SV_eq_explicit]
  simp only [manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, barrierLogHRat_two_eq]
  decide +kernel

theorem manuscript_case1X2_printed_upper :
    barrierCase1X (X2 : ℝ) < (X2PrintedUpper : ℝ) :=
  manuscript_case1X2_interval.2.trans_lt
    ((Rat.cast_lt (K := ℝ)).2 manuscript_case1X2_endpoint_lt_printed)

end InternalCatalan

end

end

section

noncomputable section
namespace InternalCatalan
open Case1PointData

def manuscriptCase1X3Interval : ℚ × ℚ :=
  manuscriptXLogFieldInterval (41 / 48) (barrierCase1XRat X3) (-2) (-1) (0) (4437270259 / 2500000000) (5562729741 / 5000000000) (119689367351405927081 / 100000000000000000000)

theorem manuscript_case1X3_interval :
    barrierCase1X (X3 : ℝ) ∈ Set.Icc (manuscriptCase1X3Interval.1 : ℝ) (manuscriptCase1X3Interval.2 : ℝ) :=
  manuscript_case1X_interval X3 (-2) (-1) (0) (4437270259 / 2500000000) (5562729741 / 5000000000) (119689367351405927081 / 100000000000000000000) X3_normalizations.1 X3_normalizations.2.1 X3_normalizations.2.2

theorem manuscript_case1X3_endpoint_lt_printed :
    manuscriptCase1X3Interval.2 < X3PrintedUpper := by
  unfold manuscriptCase1X3Interval manuscriptXLogFieldInterval barrierCase1XRat
  rw [barrierCase1TP_eq_explicit, barrierCase1SV_eq_explicit]
  simp only [manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, barrierLogHRat_two_eq]
  decide +kernel

theorem manuscript_case1X3_interval_width :
    manuscriptCase1X3Interval.2 - manuscriptCase1X3Interval.1 < (216146856249281 / 1000000000000000000000000000000 : ℚ) := by
  unfold manuscriptCase1X3Interval manuscriptXLogFieldInterval barrierCase1XRat
  rw [barrierCase1TP_eq_explicit, barrierCase1SV_eq_explicit]
  simp only [manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, barrierLogHRat_two_eq]
  decide +kernel

theorem manuscript_case1X3_printed_upper :
    barrierCase1X (X3 : ℝ) < (X3PrintedUpper : ℝ) :=
  manuscript_case1X3_interval.2.trans_lt
    ((Rat.cast_lt (K := ℝ)).2 manuscript_case1X3_endpoint_lt_printed)

end InternalCatalan

end

end

section

noncomputable section
namespace InternalCatalan
open Case1PointData

def manuscriptCase1X4Interval : ℚ × ℚ :=
  manuscriptXLogFieldInterval (41 / 48) (barrierCase1XRat X4) (-1) (-2) (0) (634829897 / 500000000) (365170103 / 250000000) (1403008998125030609 / 1000000000000000000)

theorem manuscript_case1X4_interval :
    barrierCase1X (X4 : ℝ) ∈ Set.Icc (manuscriptCase1X4Interval.1 : ℝ) (manuscriptCase1X4Interval.2 : ℝ) :=
  manuscript_case1X_interval X4 (-1) (-2) (0) (634829897 / 500000000) (365170103 / 250000000) (1403008998125030609 / 1000000000000000000) X4_normalizations.1 X4_normalizations.2.1 X4_normalizations.2.2

theorem manuscript_case1X4_endpoint_lt_printed :
    manuscriptCase1X4Interval.2 < X4PrintedUpper := by
  unfold manuscriptCase1X4Interval manuscriptXLogFieldInterval barrierCase1XRat
  rw [barrierCase1TP_eq_explicit, barrierCase1SV_eq_explicit]
  simp only [manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, barrierLogHRat_two_eq]
  decide +kernel

theorem manuscript_case1X4_interval_width :
    manuscriptCase1X4Interval.2 - manuscriptCase1X4Interval.1 < (216146856249281 / 1000000000000000000000000000000 : ℚ) := by
  unfold manuscriptCase1X4Interval manuscriptXLogFieldInterval barrierCase1XRat
  rw [barrierCase1TP_eq_explicit, barrierCase1SV_eq_explicit]
  simp only [manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, barrierLogHRat_two_eq]
  decide +kernel

theorem manuscript_case1X4_printed_upper :
    barrierCase1X (X4 : ℝ) < (X4PrintedUpper : ℝ) :=
  manuscript_case1X4_interval.2.trans_lt
    ((Rat.cast_lt (K := ℝ)).2 manuscript_case1X4_endpoint_lt_printed)

end InternalCatalan

end

end

section

noncomputable section
namespace InternalCatalan
open Case1PointData

def manuscriptCase1X5Interval : ℚ × ℚ :=
  manuscriptXLogFieldInterval (41 / 48) (barrierCase1XRat X5) (0) (1) (1) (1 / 1) (1 / 1) (1 / 1)

theorem manuscript_case1X5_interval :
    barrierCase1X (X5 : ℝ) ∈ Set.Icc (manuscriptCase1X5Interval.1 : ℝ) (manuscriptCase1X5Interval.2 : ℝ) :=
  manuscript_case1X_interval X5 (0) (1) (1) (1 / 1) (1 / 1) (1 / 1) (by simpa only [div_one] using X5_normalizations.1) (by simpa only [div_one] using X5_normalizations.2.1) (by simpa only [div_one] using X5_normalizations.2.2)

theorem manuscript_case1X5_endpoint_lt_printed :
    manuscriptCase1X5Interval.2 < X5PrintedUpper := by
  unfold manuscriptCase1X5Interval manuscriptXLogFieldInterval barrierCase1XRat
  rw [barrierCase1TP_eq_explicit, barrierCase1SV_eq_explicit]
  simp only [manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, barrierLogHRat_two_eq]
  decide +kernel

theorem manuscript_case1X5_interval_width :
    manuscriptCase1X5Interval.2 - manuscriptCase1X5Interval.1 < (216146856249281 / 1000000000000000000000000000000 : ℚ) := by
  unfold manuscriptCase1X5Interval manuscriptXLogFieldInterval barrierCase1XRat
  rw [barrierCase1TP_eq_explicit, barrierCase1SV_eq_explicit]
  simp only [manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, barrierLogHRat_two_eq]
  decide +kernel

theorem manuscript_case1X5_printed_upper :
    barrierCase1X (X5 : ℝ) < (X5PrintedUpper : ℝ) :=
  manuscript_case1X5_interval.2.trans_lt
    ((Rat.cast_lt (K := ℝ)).2 manuscript_case1X5_endpoint_lt_printed)

end InternalCatalan

end

end

section

noncomputable section
namespace InternalCatalan
open Case1PointData

def manuscriptCase1X6Interval : ℚ × ℚ :=
  manuscriptXLogFieldInterval (41 / 48) (barrierCase1XRat X6) (-1) (0) (0) (1 / 1) (3 / 2) (5 / 4)

theorem manuscript_case1X6_interval :
    barrierCase1X (X6 : ℝ) ∈ Set.Icc (manuscriptCase1X6Interval.1 : ℝ) (manuscriptCase1X6Interval.2 : ℝ) :=
  manuscript_case1X_interval X6 (-1) (0) (0) (1 / 1) (3 / 2) (5 / 4) (by simpa only [div_one] using X6_normalizations.1) X6_normalizations.2.1 X6_normalizations.2.2

theorem manuscript_case1X6_endpoint_lt_printed :
    manuscriptCase1X6Interval.2 < X6PrintedUpper := by
  unfold manuscriptCase1X6Interval manuscriptXLogFieldInterval barrierCase1XRat
  rw [barrierCase1TP_eq_explicit, barrierCase1SV_eq_explicit]
  simp only [manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, barrierLogHRat_two_eq]
  decide +kernel

theorem manuscript_case1X6_interval_width :
    manuscriptCase1X6Interval.2 - manuscriptCase1X6Interval.1 < (216146856249281 / 1000000000000000000000000000000 : ℚ) := by
  unfold manuscriptCase1X6Interval manuscriptXLogFieldInterval barrierCase1XRat
  rw [barrierCase1TP_eq_explicit, barrierCase1SV_eq_explicit]
  simp only [manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, barrierLogHRat_two_eq]
  decide +kernel

theorem manuscript_case1X6_printed_upper :
    barrierCase1X (X6 : ℝ) < (X6PrintedUpper : ℝ) :=
  manuscript_case1X6_interval.2.trans_lt
    ((Rat.cast_lt (K := ℝ)).2 manuscript_case1X6_endpoint_lt_printed)

end InternalCatalan

end

end

section

noncomputable section
namespace InternalCatalan
open Case1PointData

def manuscriptCase1X7Interval : ℚ × ℚ :=
  manuscriptXLogFieldInterval (41 / 48) (barrierCase1XRat X7) (-1) (-1) (0) (1 / 1) (1 / 1) (5 / 4)

theorem manuscript_case1X7_interval :
    barrierCase1X (X7 : ℝ) ∈ Set.Icc (manuscriptCase1X7Interval.1 : ℝ) (manuscriptCase1X7Interval.2 : ℝ) :=
  manuscript_case1X_interval X7 (-1) (-1) (0) (1 / 1) (1 / 1) (5 / 4) (by simpa only [div_one] using X7_normalizations.1) (by simpa only [div_one] using X7_normalizations.2.1) X7_normalizations.2.2

theorem manuscript_case1X7_endpoint_lt_printed :
    manuscriptCase1X7Interval.2 < X7PrintedUpper := by
  unfold manuscriptCase1X7Interval manuscriptXLogFieldInterval barrierCase1XRat
  rw [barrierCase1TP_eq_explicit, barrierCase1SV_eq_explicit]
  simp only [manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, barrierLogHRat_two_eq]
  decide +kernel

theorem manuscript_case1X7_interval_width :
    manuscriptCase1X7Interval.2 - manuscriptCase1X7Interval.1 < (216146856249281 / 1000000000000000000000000000000 : ℚ) := by
  unfold manuscriptCase1X7Interval manuscriptXLogFieldInterval barrierCase1XRat
  rw [barrierCase1TP_eq_explicit, barrierCase1SV_eq_explicit]
  simp only [manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, barrierLogHRat_two_eq]
  decide +kernel

theorem manuscript_case1X7_printed_upper :
    barrierCase1X (X7 : ℝ) < (X7PrintedUpper : ℝ) :=
  manuscript_case1X7_interval.2.trans_lt
    ((Rat.cast_lt (K := ℝ)).2 manuscript_case1X7_endpoint_lt_printed)

end InternalCatalan

end

end

section

noncomputable section
namespace InternalCatalan

def manuscriptCase1XPrecisionClaims : Prop :=
  (barrierCase1X (Case1PointData.X0 : ℝ) ∈ Set.Icc (manuscriptCase1X0Interval.1 : ℝ) (manuscriptCase1X0Interval.2 : ℝ) ∧
    manuscriptCase1X0Interval.2 < Case1PointData.X0PrintedUpper ∧
    manuscriptCase1X0Interval.2 - manuscriptCase1X0Interval.1 < (216146856249281 / 1000000000000000000000000000000 : ℚ) ∧
    barrierCase1X (Case1PointData.X0 : ℝ) < (Case1PointData.X0PrintedUpper : ℝ)) ∧
  (barrierCase1X (Case1PointData.X1 : ℝ) ∈ Set.Icc (manuscriptCase1X1Interval.1 : ℝ) (manuscriptCase1X1Interval.2 : ℝ) ∧
    manuscriptCase1X1Interval.2 < Case1PointData.X1PrintedUpper ∧
    manuscriptCase1X1Interval.2 - manuscriptCase1X1Interval.1 < (216146856249281 / 1000000000000000000000000000000 : ℚ) ∧
    barrierCase1X (Case1PointData.X1 : ℝ) < (Case1PointData.X1PrintedUpper : ℝ)) ∧
  (barrierCase1X (Case1PointData.X2 : ℝ) ∈ Set.Icc (manuscriptCase1X2Interval.1 : ℝ) (manuscriptCase1X2Interval.2 : ℝ) ∧
    manuscriptCase1X2Interval.2 < Case1PointData.X2PrintedUpper ∧
    manuscriptCase1X2Interval.2 - manuscriptCase1X2Interval.1 < (216146856249281 / 1000000000000000000000000000000 : ℚ) ∧
    barrierCase1X (Case1PointData.X2 : ℝ) < (Case1PointData.X2PrintedUpper : ℝ)) ∧
  (barrierCase1X (Case1PointData.X3 : ℝ) ∈ Set.Icc (manuscriptCase1X3Interval.1 : ℝ) (manuscriptCase1X3Interval.2 : ℝ) ∧
    manuscriptCase1X3Interval.2 < Case1PointData.X3PrintedUpper ∧
    manuscriptCase1X3Interval.2 - manuscriptCase1X3Interval.1 < (216146856249281 / 1000000000000000000000000000000 : ℚ) ∧
    barrierCase1X (Case1PointData.X3 : ℝ) < (Case1PointData.X3PrintedUpper : ℝ)) ∧
  (barrierCase1X (Case1PointData.X4 : ℝ) ∈ Set.Icc (manuscriptCase1X4Interval.1 : ℝ) (manuscriptCase1X4Interval.2 : ℝ) ∧
    manuscriptCase1X4Interval.2 < Case1PointData.X4PrintedUpper ∧
    manuscriptCase1X4Interval.2 - manuscriptCase1X4Interval.1 < (216146856249281 / 1000000000000000000000000000000 : ℚ) ∧
    barrierCase1X (Case1PointData.X4 : ℝ) < (Case1PointData.X4PrintedUpper : ℝ)) ∧
  (barrierCase1X (Case1PointData.X5 : ℝ) ∈ Set.Icc (manuscriptCase1X5Interval.1 : ℝ) (manuscriptCase1X5Interval.2 : ℝ) ∧
    manuscriptCase1X5Interval.2 < Case1PointData.X5PrintedUpper ∧
    manuscriptCase1X5Interval.2 - manuscriptCase1X5Interval.1 < (216146856249281 / 1000000000000000000000000000000 : ℚ) ∧
    barrierCase1X (Case1PointData.X5 : ℝ) < (Case1PointData.X5PrintedUpper : ℝ)) ∧
  (barrierCase1X (Case1PointData.X6 : ℝ) ∈ Set.Icc (manuscriptCase1X6Interval.1 : ℝ) (manuscriptCase1X6Interval.2 : ℝ) ∧
    manuscriptCase1X6Interval.2 < Case1PointData.X6PrintedUpper ∧
    manuscriptCase1X6Interval.2 - manuscriptCase1X6Interval.1 < (216146856249281 / 1000000000000000000000000000000 : ℚ) ∧
    barrierCase1X (Case1PointData.X6 : ℝ) < (Case1PointData.X6PrintedUpper : ℝ)) ∧
  (barrierCase1X (Case1PointData.X7 : ℝ) ∈ Set.Icc (manuscriptCase1X7Interval.1 : ℝ) (manuscriptCase1X7Interval.2 : ℝ) ∧
    manuscriptCase1X7Interval.2 < Case1PointData.X7PrintedUpper ∧
    manuscriptCase1X7Interval.2 - manuscriptCase1X7Interval.1 < (216146856249281 / 1000000000000000000000000000000 : ℚ) ∧
    barrierCase1X (Case1PointData.X7 : ℝ) < (Case1PointData.X7PrintedUpper : ℝ))

theorem manuscript_case1X_all_precision : manuscriptCase1XPrecisionClaims := by
  exact ⟨⟨manuscript_case1X0_interval, manuscript_case1X0_endpoint_lt_printed, manuscript_case1X0_interval_width, manuscript_case1X0_printed_upper⟩,
    ⟨manuscript_case1X1_interval, manuscript_case1X1_endpoint_lt_printed, manuscript_case1X1_interval_width, manuscript_case1X1_printed_upper⟩,
    ⟨manuscript_case1X2_interval, manuscript_case1X2_endpoint_lt_printed, manuscript_case1X2_interval_width, manuscript_case1X2_printed_upper⟩,
    ⟨manuscript_case1X3_interval, manuscript_case1X3_endpoint_lt_printed, manuscript_case1X3_interval_width, manuscript_case1X3_printed_upper⟩,
    ⟨manuscript_case1X4_interval, manuscript_case1X4_endpoint_lt_printed, manuscript_case1X4_interval_width, manuscript_case1X4_printed_upper⟩,
    ⟨manuscript_case1X5_interval, manuscript_case1X5_endpoint_lt_printed, manuscript_case1X5_interval_width, manuscript_case1X5_printed_upper⟩,
    ⟨manuscript_case1X6_interval, manuscript_case1X6_endpoint_lt_printed, manuscript_case1X6_interval_width, manuscript_case1X6_printed_upper⟩,
    ⟨manuscript_case1X7_interval, manuscript_case1X7_endpoint_lt_printed, manuscript_case1X7_interval_width, manuscript_case1X7_printed_upper⟩⟩

end InternalCatalan

end

end

end OAI
