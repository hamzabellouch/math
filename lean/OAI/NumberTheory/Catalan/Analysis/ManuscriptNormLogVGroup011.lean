import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormV2_7Arg : ℂ :=
  1 - (barrierV2Tail.getD 2 (0, 0)).1 * (barrierV2Tail.getD 7 (0, 0)).1

def manuscriptNormV2_7Term : ℝ :=
  (-((barrierV2Tail.getD 2 (0, 0)).2 * (barrierV2Tail.getD 7 (0, 0)).2) *
    Complex.log manuscriptNormV2_7Arg).re

def manuscriptNormV2_7Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (9971941566429 / 2500000000000000) (-19210618876707 / 5000000000000000) (0) (-1) (25426 / 15625) (13 / 112)

private theorem manuscriptNormV2_7_arg_eq : manuscriptNormV2_7Arg = barrierComplex (1 / 1) (-99 / 125) := by
  apply Complex.ext <;> norm_num [manuscriptNormV2_7Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV2_7_weight_eq :
    -((barrierV2Tail.getD 2 (0, 0)).2 * (barrierV2Tail.getD 7 (0, 0)).2) =
      barrierComplex (9971941566429 / 2500000000000000) (-19210618876707 / 5000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV2_7_exact_interval :
    manuscriptNormV2_7Term ∈ Set.Icc (manuscriptNormV2_7Interval.1 : ℝ) (manuscriptNormV2_7Interval.2 : ℝ) := by
  unfold manuscriptNormV2_7Term
  rw [manuscriptNormV2_7_weight_eq]
  have h := manuscript_weighted_complex_log_interval (9971941566429 / 2500000000000000) (-19210618876707 / 5000000000000000)
    manuscriptNormV2_7Arg (0) (-1) (25426 / 15625) (224 / 125) (26 / 125)
  have hratio : ((26 / 125) / (224 / 125) : ℚ) = (13 / 112) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV2_7Interval
  apply h
  all_goals
    try rw [manuscriptNormV2_7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV2_7_rounded_endpoints :
    (-801277525046095019997984753 / 500000000000000000000000000000) ≤ manuscriptNormV2_7Interval.1 ∧ manuscriptNormV2_7Interval.2 ≤ (-400638762523047475177650967 / 250000000000000000000000000000) := by
  simp only [manuscriptNormV2_7Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV2_7_enclosure :
    manuscriptNormV2_7Term ∈ Set.Icc ((-801277525046095019997984753 / 500000000000000000000000000000) : ℝ) ((-400638762523047475177650967 / 250000000000000000000000000000) : ℝ) := by
  have hlo : ((-801277525046095019997984753 / 500000000000000000000000000000) : ℝ) ≤ (manuscriptNormV2_7Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV2_7_rounded_endpoints.1
  have hhi : (manuscriptNormV2_7Interval.2 : ℝ) ≤ ((-400638762523047475177650967 / 250000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV2_7_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV2_7_exact_interval.1, manuscriptNormV2_7_exact_interval.2.trans hhi⟩

def manuscriptNormV2_8Arg : ℂ :=
  1 - (barrierV2Tail.getD 2 (0, 0)).1 * (barrierV2Tail.getD 8 (0, 0)).1

def manuscriptNormV2_8Term : ℝ :=
  (-((barrierV2Tail.getD 2 (0, 0)).2 * (barrierV2Tail.getD 8 (0, 0)).2) *
    Complex.log manuscriptNormV2_8Arg).re

def manuscriptNormV2_8Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (9971941566429 / 2500000000000000) (19210618876707 / 5000000000000000) (0) (1) (25426 / 15625) (-13 / 112)

private theorem manuscriptNormV2_8_arg_eq : manuscriptNormV2_8Arg = barrierComplex (1 / 1) (99 / 125) := by
  apply Complex.ext <;> norm_num [manuscriptNormV2_8Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV2_8_weight_eq :
    -((barrierV2Tail.getD 2 (0, 0)).2 * (barrierV2Tail.getD 8 (0, 0)).2) =
      barrierComplex (9971941566429 / 2500000000000000) (19210618876707 / 5000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV2_8_exact_interval :
    manuscriptNormV2_8Term ∈ Set.Icc (manuscriptNormV2_8Interval.1 : ℝ) (manuscriptNormV2_8Interval.2 : ℝ) := by
  unfold manuscriptNormV2_8Term
  rw [manuscriptNormV2_8_weight_eq]
  have h := manuscript_weighted_complex_log_interval (9971941566429 / 2500000000000000) (19210618876707 / 5000000000000000)
    manuscriptNormV2_8Arg (0) (1) (25426 / 15625) (224 / 125) (-26 / 125)
  have hratio : ((-26 / 125) / (224 / 125) : ℚ) = (-13 / 112) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV2_8Interval
  apply h
  all_goals
    try rw [manuscriptNormV2_8_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV2_8_rounded_endpoints :
    (-801277525046095019997984753 / 500000000000000000000000000000) ≤ manuscriptNormV2_8Interval.1 ∧ manuscriptNormV2_8Interval.2 ≤ (-400638762523047475177650967 / 250000000000000000000000000000) := by
  simp only [manuscriptNormV2_8Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV2_8_enclosure :
    manuscriptNormV2_8Term ∈ Set.Icc ((-801277525046095019997984753 / 500000000000000000000000000000) : ℝ) ((-400638762523047475177650967 / 250000000000000000000000000000) : ℝ) := by
  have hlo : ((-801277525046095019997984753 / 500000000000000000000000000000) : ℝ) ≤ (manuscriptNormV2_8Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV2_8_rounded_endpoints.1
  have hhi : (manuscriptNormV2_8Interval.2 : ℝ) ≤ ((-400638762523047475177650967 / 250000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV2_8_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV2_8_exact_interval.1, manuscriptNormV2_8_exact_interval.2.trans hhi⟩

def manuscriptNormV2_9Arg : ℂ :=
  1 - (barrierV2Tail.getD 2 (0, 0)).1 * (barrierV2Tail.getD 9 (0, 0)).1

def manuscriptNormV2_9Term : ℝ :=
  (-((barrierV2Tail.getD 2 (0, 0)).2 * (barrierV2Tail.getD 9 (0, 0)).2) *
    Complex.log manuscriptNormV2_9Arg).re

def manuscriptNormV2_9Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (4259432104929 / 5000000000000000) (7580356876773 / 5000000000000000) (0) (-1) (10664201 / 6250000) (399 / 4601)

private theorem manuscriptNormV2_9_arg_eq : manuscriptNormV2_9Arg = barrierComplex (1 / 1) (-2101 / 2500) := by
  apply Complex.ext <;> norm_num [manuscriptNormV2_9Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV2_9_weight_eq :
    -((barrierV2Tail.getD 2 (0, 0)).2 * (barrierV2Tail.getD 9 (0, 0)).2) =
      barrierComplex (4259432104929 / 5000000000000000) (7580356876773 / 5000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV2_9_exact_interval :
    manuscriptNormV2_9Term ∈ Set.Icc (manuscriptNormV2_9Interval.1 : ℝ) (manuscriptNormV2_9Interval.2 : ℝ) := by
  unfold manuscriptNormV2_9Term
  rw [manuscriptNormV2_9_weight_eq]
  have h := manuscript_weighted_complex_log_interval (4259432104929 / 5000000000000000) (7580356876773 / 5000000000000000)
    manuscriptNormV2_9Arg (0) (-1) (10664201 / 6250000) (4601 / 2500) (399 / 2500)
  have hratio : ((399 / 2500) / (4601 / 2500) : ℚ) = (399 / 4601) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV2_9Interval
  apply h
  all_goals
    try rw [manuscriptNormV2_9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV2_9_rounded_endpoints :
    (128715977164432191110172169 / 100000000000000000000000000000) ≤ manuscriptNormV2_9Interval.1 ∧ manuscriptNormV2_9Interval.2 ≤ (643579885822160983031310613 / 500000000000000000000000000000) := by
  simp only [manuscriptNormV2_9Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV2_9_enclosure :
    manuscriptNormV2_9Term ∈ Set.Icc ((128715977164432191110172169 / 100000000000000000000000000000) : ℝ) ((643579885822160983031310613 / 500000000000000000000000000000) : ℝ) := by
  have hlo : ((128715977164432191110172169 / 100000000000000000000000000000) : ℝ) ≤ (manuscriptNormV2_9Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV2_9_rounded_endpoints.1
  have hhi : (manuscriptNormV2_9Interval.2 : ℝ) ≤ ((643579885822160983031310613 / 500000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV2_9_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV2_9_exact_interval.1, manuscriptNormV2_9_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
