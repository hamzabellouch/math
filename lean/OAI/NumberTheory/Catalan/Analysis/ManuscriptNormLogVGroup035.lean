import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormV8_1Arg : ℂ :=
  1 - (barrierV2Tail.getD 8 (0, 0)).1 * (barrierV2Tail.getD 1 (0, 0)).1

def manuscriptNormV8_1Term : ℝ :=
  (-((barrierV2Tail.getD 8 (0, 0)).2 * (barrierV2Tail.getD 1 (0, 0)).2) *
    Complex.log manuscriptNormV8_1Arg).re

def manuscriptNormV8_1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (17439989085201 / 2500000000000000) (33597567865583 / 5000000000000000) (0) (-1) (27289 / 15625) (17 / 233)

private theorem manuscriptNormV8_1_arg_eq : manuscriptNormV8_1Arg = barrierComplex (1 / 1) (-108 / 125) := by
  apply Complex.ext <;> norm_num [manuscriptNormV8_1Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV8_1_weight_eq :
    -((barrierV2Tail.getD 8 (0, 0)).2 * (barrierV2Tail.getD 1 (0, 0)).2) =
      barrierComplex (17439989085201 / 2500000000000000) (33597567865583 / 5000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV8_1_exact_interval :
    manuscriptNormV8_1Term ∈ Set.Icc (manuscriptNormV8_1Interval.1 : ℝ) (manuscriptNormV8_1Interval.2 : ℝ) := by
  unfold manuscriptNormV8_1Term
  rw [manuscriptNormV8_1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (17439989085201 / 2500000000000000) (33597567865583 / 5000000000000000)
    manuscriptNormV8_1Arg (0) (-1) (27289 / 15625) (233 / 125) (17 / 125)
  have hratio : ((17 / 125) / (233 / 125) : ℚ) = (17 / 233) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV8_1Interval
  apply h
  all_goals
    try rw [manuscriptNormV8_1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV8_1_rounded_endpoints :
    (3366521771051272355351880559 / 500000000000000000000000000000) ≤ manuscriptNormV8_1Interval.1 ∧ manuscriptNormV8_1Interval.2 ≤ (1683260885525636238575254391 / 250000000000000000000000000000) := by
  simp only [manuscriptNormV8_1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV8_1_enclosure :
    manuscriptNormV8_1Term ∈ Set.Icc ((3366521771051272355351880559 / 500000000000000000000000000000) : ℝ) ((1683260885525636238575254391 / 250000000000000000000000000000) : ℝ) := by
  have hlo : ((3366521771051272355351880559 / 500000000000000000000000000000) : ℝ) ≤ (manuscriptNormV8_1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV8_1_rounded_endpoints.1
  have hhi : (manuscriptNormV8_1Interval.2 : ℝ) ≤ ((1683260885525636238575254391 / 250000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV8_1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV8_1_exact_interval.1, manuscriptNormV8_1_exact_interval.2.trans hhi⟩

def manuscriptNormV8_2Arg : ℂ :=
  1 - (barrierV2Tail.getD 8 (0, 0)).1 * (barrierV2Tail.getD 2 (0, 0)).1

def manuscriptNormV8_2Term : ℝ :=
  (-((barrierV2Tail.getD 8 (0, 0)).2 * (barrierV2Tail.getD 2 (0, 0)).2) *
    Complex.log manuscriptNormV8_2Arg).re

def manuscriptNormV8_2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (9971941566429 / 2500000000000000) (19210618876707 / 5000000000000000) (0) (1) (25426 / 15625) (-13 / 112)

private theorem manuscriptNormV8_2_arg_eq : manuscriptNormV8_2Arg = barrierComplex (1 / 1) (99 / 125) := by
  apply Complex.ext <;> norm_num [manuscriptNormV8_2Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV8_2_weight_eq :
    -((barrierV2Tail.getD 8 (0, 0)).2 * (barrierV2Tail.getD 2 (0, 0)).2) =
      barrierComplex (9971941566429 / 2500000000000000) (19210618876707 / 5000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV8_2_exact_interval :
    manuscriptNormV8_2Term ∈ Set.Icc (manuscriptNormV8_2Interval.1 : ℝ) (manuscriptNormV8_2Interval.2 : ℝ) := by
  unfold manuscriptNormV8_2Term
  rw [manuscriptNormV8_2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (9971941566429 / 2500000000000000) (19210618876707 / 5000000000000000)
    manuscriptNormV8_2Arg (0) (1) (25426 / 15625) (224 / 125) (-26 / 125)
  have hratio : ((-26 / 125) / (224 / 125) : ℚ) = (-13 / 112) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV8_2Interval
  apply h
  all_goals
    try rw [manuscriptNormV8_2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV8_2_rounded_endpoints :
    (-801277525046095019997984753 / 500000000000000000000000000000) ≤ manuscriptNormV8_2Interval.1 ∧ manuscriptNormV8_2Interval.2 ≤ (-400638762523047475177650967 / 250000000000000000000000000000) := by
  simp only [manuscriptNormV8_2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV8_2_enclosure :
    manuscriptNormV8_2Term ∈ Set.Icc ((-801277525046095019997984753 / 500000000000000000000000000000) : ℝ) ((-400638762523047475177650967 / 250000000000000000000000000000) : ℝ) := by
  have hlo : ((-801277525046095019997984753 / 500000000000000000000000000000) : ℝ) ≤ (manuscriptNormV8_2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV8_2_rounded_endpoints.1
  have hhi : (manuscriptNormV8_2Interval.2 : ℝ) ≤ ((-400638762523047475177650967 / 250000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV8_2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV8_2_exact_interval.1, manuscriptNormV8_2_exact_interval.2.trans hhi⟩

def manuscriptNormV8_3Arg : ℂ :=
  1 - (barrierV2Tail.getD 8 (0, 0)).1 * (barrierV2Tail.getD 3 (0, 0)).1

def manuscriptNormV8_3Term : ℝ :=
  (-((barrierV2Tail.getD 8 (0, 0)).2 * (barrierV2Tail.getD 3 (0, 0)).2) *
    Complex.log manuscriptNormV8_3Arg).re

def manuscriptNormV8_3Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-19324262066907 / 2500000000000000) (-37227558060581 / 5000000000000000) (0) (1) (69241 / 40000) (-29 / 371)

private theorem manuscriptNormV8_3_arg_eq : manuscriptNormV8_3Arg = barrierComplex (1 / 1) (171 / 200) := by
  apply Complex.ext <;> norm_num [manuscriptNormV8_3Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV8_3_weight_eq :
    -((barrierV2Tail.getD 8 (0, 0)).2 * (barrierV2Tail.getD 3 (0, 0)).2) =
      barrierComplex (-19324262066907 / 2500000000000000) (-37227558060581 / 5000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV8_3_exact_interval :
    manuscriptNormV8_3Term ∈ Set.Icc (manuscriptNormV8_3Interval.1 : ℝ) (manuscriptNormV8_3Interval.2 : ℝ) := by
  unfold manuscriptNormV8_3Term
  rw [manuscriptNormV8_3_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-19324262066907 / 2500000000000000) (-37227558060581 / 5000000000000000)
    manuscriptNormV8_3Arg (0) (1) (69241 / 40000) (371 / 200) (-29 / 200)
  have hratio : ((-29 / 200) / (371 / 200) : ℚ) = (-29 / 371) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV8_3Interval
  apply h
  all_goals
    try rw [manuscriptNormV8_3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV8_3_rounded_endpoints :
    (3146180457411023770175562599 / 1000000000000000000000000000000) ≤ manuscriptNormV8_3Interval.1 ∧ manuscriptNormV8_3Interval.2 ≤ (3146180457411024040091742511 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV8_3Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV8_3_enclosure :
    manuscriptNormV8_3Term ∈ Set.Icc ((3146180457411023770175562599 / 1000000000000000000000000000000) : ℝ) ((3146180457411024040091742511 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((3146180457411023770175562599 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormV8_3Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV8_3_rounded_endpoints.1
  have hhi : (manuscriptNormV8_3Interval.2 : ℝ) ≤ ((3146180457411024040091742511 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV8_3_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV8_3_exact_interval.1, manuscriptNormV8_3_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
