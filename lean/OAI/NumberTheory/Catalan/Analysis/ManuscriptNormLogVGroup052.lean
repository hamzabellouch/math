import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormV12_0Arg : ℂ :=
  1 - (barrierV2Tail.getD 12 (0, 0)).1 * (barrierV2Tail.getD 0 (0, 0)).1

def manuscriptNormV12_0Term : ℝ :=
  (-((barrierV2Tail.getD 12 (0, 0)).2 * (barrierV2Tail.getD 0 (0, 0)).2) *
    Complex.log manuscriptNormV12_0Arg).re

def manuscriptNormV12_0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-31237616036943 / 20000000000000000) (330063770995139 / 20000000000000000) (0) (-1) (632689 / 390625) (133 / 1117)

private theorem manuscriptNormV12_0_arg_eq : manuscriptNormV12_0Arg = barrierComplex (1 / 1) (-492 / 625) := by
  apply Complex.ext <;> norm_num [manuscriptNormV12_0Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV12_0_weight_eq :
    -((barrierV2Tail.getD 12 (0, 0)).2 * (barrierV2Tail.getD 0 (0, 0)).2) =
      barrierComplex (-31237616036943 / 20000000000000000) (330063770995139 / 20000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV12_0_exact_interval :
    manuscriptNormV12_0Term ∈ Set.Icc (manuscriptNormV12_0Interval.1 : ℝ) (manuscriptNormV12_0Interval.2 : ℝ) := by
  unfold manuscriptNormV12_0Term
  rw [manuscriptNormV12_0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-31237616036943 / 20000000000000000) (330063770995139 / 20000000000000000)
    manuscriptNormV12_0Arg (0) (-1) (632689 / 390625) (1117 / 625) (133 / 625)
  have hratio : ((133 / 625) / (1117 / 625) : ℚ) = (133 / 1117) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV12_0Interval
  apply h
  all_goals
    try rw [manuscriptNormV12_0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV12_0_rounded_endpoints :
    (10629171334454979986482737241 / 1000000000000000000000000000000) ≤ manuscriptNormV12_0Interval.1 ∧ manuscriptNormV12_0Interval.2 ≤ (10629171334454980584759307369 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV12_0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV12_0_enclosure :
    manuscriptNormV12_0Term ∈ Set.Icc ((10629171334454979986482737241 / 1000000000000000000000000000000) : ℝ) ((10629171334454980584759307369 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((10629171334454979986482737241 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormV12_0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV12_0_rounded_endpoints.1
  have hhi : (manuscriptNormV12_0Interval.2 : ℝ) ≤ ((10629171334454980584759307369 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV12_0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV12_0_exact_interval.1, manuscriptNormV12_0_exact_interval.2.trans hhi⟩

def manuscriptNormV12_1Arg : ℂ :=
  1 - (barrierV2Tail.getD 12 (0, 0)).1 * (barrierV2Tail.getD 1 (0, 0)).1

def manuscriptNormV12_1Term : ℝ :=
  (-((barrierV2Tail.getD 12 (0, 0)).2 * (barrierV2Tail.getD 1 (0, 0)).2) *
    Complex.log manuscriptNormV12_1Arg).re

def manuscriptNormV12_1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-4574556807003 / 10000000000000000) (48335809895519 / 10000000000000000) (0) (-1) (18479929 / 9765625) (173 / 6077)

private theorem manuscriptNormV12_1_arg_eq : manuscriptNormV12_1Arg = barrierComplex (1 / 1) (-2952 / 3125) := by
  apply Complex.ext <;> norm_num [manuscriptNormV12_1Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV12_1_weight_eq :
    -((barrierV2Tail.getD 12 (0, 0)).2 * (barrierV2Tail.getD 1 (0, 0)).2) =
      barrierComplex (-4574556807003 / 10000000000000000) (48335809895519 / 10000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV12_1_exact_interval :
    manuscriptNormV12_1Term ∈ Set.Icc (manuscriptNormV12_1Interval.1 : ℝ) (manuscriptNormV12_1Interval.2 : ℝ) := by
  unfold manuscriptNormV12_1Term
  rw [manuscriptNormV12_1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-4574556807003 / 10000000000000000) (48335809895519 / 10000000000000000)
    manuscriptNormV12_1Arg (0) (-1) (18479929 / 9765625) (6077 / 3125) (173 / 3125)
  have hratio : ((173 / 3125) / (6077 / 3125) : ℚ) = (173 / 6077) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV12_1Interval
  apply h
  all_goals
    try rw [manuscriptNormV12_1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV12_1_rounded_endpoints :
    (878208501076450742714674087 / 250000000000000000000000000000) ≤ manuscriptNormV12_1Interval.1 ∧ manuscriptNormV12_1Interval.2 ≤ (3512834004305803146088280731 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV12_1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV12_1_enclosure :
    manuscriptNormV12_1Term ∈ Set.Icc ((878208501076450742714674087 / 250000000000000000000000000000) : ℝ) ((3512834004305803146088280731 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((878208501076450742714674087 / 250000000000000000000000000000) : ℝ) ≤ (manuscriptNormV12_1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV12_1_rounded_endpoints.1
  have hhi : (manuscriptNormV12_1Interval.2 : ℝ) ≤ ((3512834004305803146088280731 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV12_1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV12_1_exact_interval.1, manuscriptNormV12_1_exact_interval.2.trans hhi⟩

def manuscriptNormV12_2Arg : ℂ :=
  1 - (barrierV2Tail.getD 12 (0, 0)).1 * (barrierV2Tail.getD 2 (0, 0)).1

def manuscriptNormV12_2Term : ℝ :=
  (-((barrierV2Tail.getD 12 (0, 0)).2 * (barrierV2Tail.getD 2 (0, 0)).2) *
    Complex.log manuscriptNormV12_2Arg).re

def manuscriptNormV12_2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2615667529887 / 10000000000000000) (27637739306451 / 10000000000000000) (0) (1) (17088061 / 9765625) (-419 / 5831)

private theorem manuscriptNormV12_2_arg_eq : manuscriptNormV12_2Arg = barrierComplex (1 / 1) (2706 / 3125) := by
  apply Complex.ext <;> norm_num [manuscriptNormV12_2Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV12_2_weight_eq :
    -((barrierV2Tail.getD 12 (0, 0)).2 * (barrierV2Tail.getD 2 (0, 0)).2) =
      barrierComplex (-2615667529887 / 10000000000000000) (27637739306451 / 10000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV12_2_exact_interval :
    manuscriptNormV12_2Term ∈ Set.Icc (manuscriptNormV12_2Interval.1 : ℝ) (manuscriptNormV12_2Interval.2 : ℝ) := by
  unfold manuscriptNormV12_2Term
  rw [manuscriptNormV12_2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2615667529887 / 10000000000000000) (27637739306451 / 10000000000000000)
    manuscriptNormV12_2Arg (0) (1) (17088061 / 9765625) (5831 / 3125) (-419 / 3125)
  have hratio : ((-419 / 3125) / (5831 / 3125) : ℚ) = (-419 / 5831) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV12_2Interval
  apply h
  all_goals
    try rw [manuscriptNormV12_2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV12_2_rounded_endpoints :
    (-2045581158108370136473370921 / 1000000000000000000000000000000) ≤ manuscriptNormV12_2Interval.1 ∧ manuscriptNormV12_2Interval.2 ≤ (-2045581158108370036280529529 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV12_2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV12_2_enclosure :
    manuscriptNormV12_2Term ∈ Set.Icc ((-2045581158108370136473370921 / 1000000000000000000000000000000) : ℝ) ((-2045581158108370036280529529 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((-2045581158108370136473370921 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormV12_2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV12_2_rounded_endpoints.1
  have hhi : (manuscriptNormV12_2Interval.2 : ℝ) ≤ ((-2045581158108370036280529529 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV12_2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV12_2_exact_interval.1, manuscriptNormV12_2_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
