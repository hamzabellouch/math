import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormV0_12Arg : ℂ :=
  1 - (barrierV2Tail.getD 0 (0, 0)).1 * (barrierV2Tail.getD 12 (0, 0)).1

def manuscriptNormV0_12Term : ℝ :=
  (-((barrierV2Tail.getD 0 (0, 0)).2 * (barrierV2Tail.getD 12 (0, 0)).2) *
    Complex.log manuscriptNormV0_12Arg).re

def manuscriptNormV0_12Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-31237616036943 / 20000000000000000) (330063770995139 / 20000000000000000) (0) (-1) (632689 / 390625) (133 / 1117)

private theorem manuscriptNormV0_12_arg_eq : manuscriptNormV0_12Arg = barrierComplex (1 / 1) (-492 / 625) := by
  apply Complex.ext <;> norm_num [manuscriptNormV0_12Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV0_12_weight_eq :
    -((barrierV2Tail.getD 0 (0, 0)).2 * (barrierV2Tail.getD 12 (0, 0)).2) =
      barrierComplex (-31237616036943 / 20000000000000000) (330063770995139 / 20000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV0_12_exact_interval :
    manuscriptNormV0_12Term ∈ Set.Icc (manuscriptNormV0_12Interval.1 : ℝ) (manuscriptNormV0_12Interval.2 : ℝ) := by
  unfold manuscriptNormV0_12Term
  rw [manuscriptNormV0_12_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-31237616036943 / 20000000000000000) (330063770995139 / 20000000000000000)
    manuscriptNormV0_12Arg (0) (-1) (632689 / 390625) (1117 / 625) (133 / 625)
  have hratio : ((133 / 625) / (1117 / 625) : ℚ) = (133 / 1117) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV0_12Interval
  apply h
  all_goals
    try rw [manuscriptNormV0_12_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV0_12_rounded_endpoints :
    (10629171334454979986482737241 / 1000000000000000000000000000000) ≤ manuscriptNormV0_12Interval.1 ∧ manuscriptNormV0_12Interval.2 ≤ (10629171334454980584759307369 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV0_12Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV0_12_enclosure :
    manuscriptNormV0_12Term ∈ Set.Icc ((10629171334454979986482737241 / 1000000000000000000000000000000) : ℝ) ((10629171334454980584759307369 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((10629171334454979986482737241 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormV0_12Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV0_12_rounded_endpoints.1
  have hhi : (manuscriptNormV0_12Interval.2 : ℝ) ≤ ((10629171334454980584759307369 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV0_12_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV0_12_exact_interval.1, manuscriptNormV0_12_exact_interval.2.trans hhi⟩

def manuscriptNormV1_0Arg : ℂ :=
  1 - (barrierV2Tail.getD 1 (0, 0)).1 * (barrierV2Tail.getD 0 (0, 0)).1

def manuscriptNormV1_0Term : ℝ :=
  (-((barrierV2Tail.getD 1 (0, 0)).2 * (barrierV2Tail.getD 0 (0, 0)).2) *
    Complex.log manuscriptNormV1_0Arg).re

def manuscriptNormV1_0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-33830875019341 / 5000000000000000) (0 / 1) (-5) (0) (26912 / 15625) (0 / 1)

private theorem manuscriptNormV1_0_arg_eq : manuscriptNormV1_0Arg = barrierComplex (29 / 125) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV1_0Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV1_0_weight_eq :
    -((barrierV2Tail.getD 1 (0, 0)).2 * (barrierV2Tail.getD 0 (0, 0)).2) =
      barrierComplex (-33830875019341 / 5000000000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV1_0_exact_interval :
    manuscriptNormV1_0Term ∈ Set.Icc (manuscriptNormV1_0Interval.1 : ℝ) (manuscriptNormV1_0Interval.2 : ℝ) := by
  unfold manuscriptNormV1_0Term
  rw [manuscriptNormV1_0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-33830875019341 / 5000000000000000) (0 / 1)
    manuscriptNormV1_0Arg (-5) (0) (26912 / 15625) (29 / 125) (0 / 1)
  have hratio : ((0 / 1) / (29 / 125) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV1_0Interval
  apply h
  all_goals
    try rw [manuscriptNormV1_0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV1_0_rounded_endpoints :
    (9885502844684175872275224267 / 1000000000000000000000000000000) ≤ manuscriptNormV1_0Interval.1 ∧ manuscriptNormV1_0Interval.2 ≤ (9885502844684175874559747331 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV1_0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV1_0_enclosure :
    manuscriptNormV1_0Term ∈ Set.Icc ((9885502844684175872275224267 / 1000000000000000000000000000000) : ℝ) ((9885502844684175874559747331 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((9885502844684175872275224267 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormV1_0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV1_0_rounded_endpoints.1
  have hhi : (manuscriptNormV1_0Interval.2 : ℝ) ≤ ((9885502844684175874559747331 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV1_0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV1_0_exact_interval.1, manuscriptNormV1_0_exact_interval.2.trans hhi⟩

def manuscriptNormV1_1Arg : ℂ :=
  1 - (barrierV2Tail.getD 1 (0, 0)).1 * (barrierV2Tail.getD 1 (0, 0)).1

def manuscriptNormV1_1Term : ℝ :=
  (-((barrierV2Tail.getD 1 (0, 0)).2 * (barrierV2Tail.getD 1 (0, 0)).2) *
    Complex.log manuscriptNormV1_1Arg).re

def manuscriptNormV1_1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-4954323640561 / 2500000000000000) (0 / 1) (-8) (0) (614656 / 390625) (0 / 1)

private theorem manuscriptNormV1_1_arg_eq : manuscriptNormV1_1Arg = barrierComplex (49 / 625) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV1_1Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV1_1_weight_eq :
    -((barrierV2Tail.getD 1 (0, 0)).2 * (barrierV2Tail.getD 1 (0, 0)).2) =
      barrierComplex (-4954323640561 / 2500000000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV1_1_exact_interval :
    manuscriptNormV1_1Term ∈ Set.Icc (manuscriptNormV1_1Interval.1 : ℝ) (manuscriptNormV1_1Interval.2 : ℝ) := by
  unfold manuscriptNormV1_1Term
  rw [manuscriptNormV1_1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-4954323640561 / 2500000000000000) (0 / 1)
    manuscriptNormV1_1Arg (-8) (0) (614656 / 390625) (49 / 625) (0 / 1)
  have hratio : ((0 / 1) / (49 / 625) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV1_1Interval
  apply h
  all_goals
    try rw [manuscriptNormV1_1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV1_1_rounded_endpoints :
    (1009069430608399715799384979 / 200000000000000000000000000000) ≤ manuscriptNormV1_1Interval.1 ∧ manuscriptNormV1_1Interval.2 ≤ (5045347153041998580067454651 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV1_1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV1_1_enclosure :
    manuscriptNormV1_1Term ∈ Set.Icc ((1009069430608399715799384979 / 200000000000000000000000000000) : ℝ) ((5045347153041998580067454651 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((1009069430608399715799384979 / 200000000000000000000000000000) : ℝ) ≤ (manuscriptNormV1_1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV1_1_rounded_endpoints.1
  have hhi : (manuscriptNormV1_1Interval.2 : ℝ) ≤ ((5045347153041998580067454651 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV1_1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV1_1_exact_interval.1, manuscriptNormV1_1_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
