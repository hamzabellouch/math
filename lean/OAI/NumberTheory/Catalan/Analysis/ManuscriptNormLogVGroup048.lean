import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormV11_1Arg : ℂ :=
  1 - (barrierV2Tail.getD 11 (0, 0)).1 * (barrierV2Tail.getD 1 (0, 0)).1

def manuscriptNormV11_1Term : ℝ :=
  (-((barrierV2Tail.getD 11 (0, 0)).2 * (barrierV2Tail.getD 1 (0, 0)).2) *
    Complex.log manuscriptNormV11_1Arg).re

def manuscriptNormV11_1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-4574556807003 / 10000000000000000) (-48335809895519 / 10000000000000000) (0) (1) (18479929 / 9765625) (-173 / 6077)

private theorem manuscriptNormV11_1_arg_eq : manuscriptNormV11_1Arg = barrierComplex (1 / 1) (2952 / 3125) := by
  apply Complex.ext <;> norm_num [manuscriptNormV11_1Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV11_1_weight_eq :
    -((barrierV2Tail.getD 11 (0, 0)).2 * (barrierV2Tail.getD 1 (0, 0)).2) =
      barrierComplex (-4574556807003 / 10000000000000000) (-48335809895519 / 10000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV11_1_exact_interval :
    manuscriptNormV11_1Term ∈ Set.Icc (manuscriptNormV11_1Interval.1 : ℝ) (manuscriptNormV11_1Interval.2 : ℝ) := by
  unfold manuscriptNormV11_1Term
  rw [manuscriptNormV11_1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-4574556807003 / 10000000000000000) (-48335809895519 / 10000000000000000)
    manuscriptNormV11_1Arg (0) (1) (18479929 / 9765625) (6077 / 3125) (-173 / 3125)
  have hratio : ((-173 / 3125) / (6077 / 3125) : ℚ) = (-173 / 6077) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV11_1Interval
  apply h
  all_goals
    try rw [manuscriptNormV11_1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV11_1_rounded_endpoints :
    (878208501076450742714674087 / 250000000000000000000000000000) ≤ manuscriptNormV11_1Interval.1 ∧ manuscriptNormV11_1Interval.2 ≤ (3512834004305803146088280731 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV11_1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV11_1_enclosure :
    manuscriptNormV11_1Term ∈ Set.Icc ((878208501076450742714674087 / 250000000000000000000000000000) : ℝ) ((3512834004305803146088280731 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((878208501076450742714674087 / 250000000000000000000000000000) : ℝ) ≤ (manuscriptNormV11_1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV11_1_rounded_endpoints.1
  have hhi : (manuscriptNormV11_1Interval.2 : ℝ) ≤ ((3512834004305803146088280731 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV11_1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV11_1_exact_interval.1, manuscriptNormV11_1_exact_interval.2.trans hhi⟩

def manuscriptNormV11_2Arg : ℂ :=
  1 - (barrierV2Tail.getD 11 (0, 0)).1 * (barrierV2Tail.getD 2 (0, 0)).1

def manuscriptNormV11_2Term : ℝ :=
  (-((barrierV2Tail.getD 11 (0, 0)).2 * (barrierV2Tail.getD 2 (0, 0)).2) *
    Complex.log manuscriptNormV11_2Arg).re

def manuscriptNormV11_2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2615667529887 / 10000000000000000) (-27637739306451 / 10000000000000000) (0) (-1) (17088061 / 9765625) (419 / 5831)

private theorem manuscriptNormV11_2_arg_eq : manuscriptNormV11_2Arg = barrierComplex (1 / 1) (-2706 / 3125) := by
  apply Complex.ext <;> norm_num [manuscriptNormV11_2Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV11_2_weight_eq :
    -((barrierV2Tail.getD 11 (0, 0)).2 * (barrierV2Tail.getD 2 (0, 0)).2) =
      barrierComplex (-2615667529887 / 10000000000000000) (-27637739306451 / 10000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV11_2_exact_interval :
    manuscriptNormV11_2Term ∈ Set.Icc (manuscriptNormV11_2Interval.1 : ℝ) (manuscriptNormV11_2Interval.2 : ℝ) := by
  unfold manuscriptNormV11_2Term
  rw [manuscriptNormV11_2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2615667529887 / 10000000000000000) (-27637739306451 / 10000000000000000)
    manuscriptNormV11_2Arg (0) (-1) (17088061 / 9765625) (5831 / 3125) (419 / 3125)
  have hratio : ((419 / 3125) / (5831 / 3125) : ℚ) = (419 / 5831) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV11_2Interval
  apply h
  all_goals
    try rw [manuscriptNormV11_2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV11_2_rounded_endpoints :
    (-2045581158108370136473370921 / 1000000000000000000000000000000) ≤ manuscriptNormV11_2Interval.1 ∧ manuscriptNormV11_2Interval.2 ≤ (-2045581158108370036280529529 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV11_2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV11_2_enclosure :
    manuscriptNormV11_2Term ∈ Set.Icc ((-2045581158108370136473370921 / 1000000000000000000000000000000) : ℝ) ((-2045581158108370036280529529 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((-2045581158108370136473370921 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormV11_2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV11_2_rounded_endpoints.1
  have hhi : (manuscriptNormV11_2Interval.2 : ℝ) ≤ ((-2045581158108370036280529529 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV11_2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV11_2_exact_interval.1, manuscriptNormV11_2_exact_interval.2.trans hhi⟩

def manuscriptNormV11_3Arg : ℂ :=
  1 - (barrierV2Tail.getD 11 (0, 0)).1 * (barrierV2Tail.getD 3 (0, 0)).1

def manuscriptNormV11_3Term : ℝ :=
  (-((barrierV2Tail.getD 11 (0, 0)).2 * (barrierV2Tail.getD 3 (0, 0)).2) *
    Complex.log manuscriptNormV11_3Arg).re

def manuscriptNormV11_3Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (5068806760521 / 10000000000000000) (53558167558133 / 10000000000000000) (0) (-1) (11711569 / 6250000) (163 / 4837)

private theorem manuscriptNormV11_3_arg_eq : manuscriptNormV11_3Arg = barrierComplex (1 / 1) (-2337 / 2500) := by
  apply Complex.ext <;> norm_num [manuscriptNormV11_3Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV11_3_weight_eq :
    -((barrierV2Tail.getD 11 (0, 0)).2 * (barrierV2Tail.getD 3 (0, 0)).2) =
      barrierComplex (5068806760521 / 10000000000000000) (53558167558133 / 10000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV11_3_exact_interval :
    manuscriptNormV11_3Term ∈ Set.Icc (manuscriptNormV11_3Interval.1 : ℝ) (manuscriptNormV11_3Interval.2 : ℝ) := by
  unfold manuscriptNormV11_3Term
  rw [manuscriptNormV11_3_weight_eq]
  have h := manuscript_weighted_complex_log_interval (5068806760521 / 10000000000000000) (53558167558133 / 10000000000000000)
    manuscriptNormV11_3Arg (0) (-1) (11711569 / 6250000) (4837 / 2500) (163 / 2500)
  have hratio : ((163 / 2500) / (4837 / 2500) : ℚ) = (163 / 4837) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV11_3Interval
  apply h
  all_goals
    try rw [manuscriptNormV11_3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV11_3_rounded_endpoints :
    (4185192971723380656657287637 / 1000000000000000000000000000000) ≤ manuscriptNormV11_3Interval.1 ∧ manuscriptNormV11_3Interval.2 ≤ (418519297172338085081844233 / 100000000000000000000000000000) := by
  simp only [manuscriptNormV11_3Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV11_3_enclosure :
    manuscriptNormV11_3Term ∈ Set.Icc ((4185192971723380656657287637 / 1000000000000000000000000000000) : ℝ) ((418519297172338085081844233 / 100000000000000000000000000000) : ℝ) := by
  have hlo : ((4185192971723380656657287637 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormV11_3Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV11_3_rounded_endpoints.1
  have hhi : (manuscriptNormV11_3Interval.2 : ℝ) ≤ ((418519297172338085081844233 / 100000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV11_3_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV11_3_exact_interval.1, manuscriptNormV11_3_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
