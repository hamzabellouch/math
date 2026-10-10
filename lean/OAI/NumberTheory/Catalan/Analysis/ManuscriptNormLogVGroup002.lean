import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormV0_6Arg : ℂ :=
  1 - (barrierV2Tail.getD 0 (0, 0)).1 * (barrierV2Tail.getD 6 (0, 0)).1

def manuscriptNormV0_6Term : ℝ :=
  (-((barrierV2Tail.getD 0 (0, 0)).2 * (barrierV2Tail.getD 6 (0, 0)).2) *
    Complex.log manuscriptNormV0_6Arg).re

def manuscriptNormV0_6Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-207003480727327 / 10000000000000000) (9130910809039 / 312500000000000) (0) (-1) (21709 / 15625) (47 / 203)

private theorem manuscriptNormV0_6_arg_eq : manuscriptNormV0_6Arg = barrierComplex (1 / 1) (-78 / 125) := by
  apply Complex.ext <;> norm_num [manuscriptNormV0_6Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV0_6_weight_eq :
    -((barrierV2Tail.getD 0 (0, 0)).2 * (barrierV2Tail.getD 6 (0, 0)).2) =
      barrierComplex (-207003480727327 / 10000000000000000) (9130910809039 / 312500000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV0_6_exact_interval :
    manuscriptNormV0_6Term ∈ Set.Icc (manuscriptNormV0_6Interval.1 : ℝ) (manuscriptNormV0_6Interval.2 : ℝ) := by
  unfold manuscriptNormV0_6Term
  rw [manuscriptNormV0_6_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-207003480727327 / 10000000000000000) (9130910809039 / 312500000000000)
    manuscriptNormV0_6Arg (0) (-1) (21709 / 15625) (203 / 125) (47 / 125)
  have hratio : ((47 / 125) / (203 / 125) : ℚ) = (47 / 203) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV0_6Interval
  apply h
  all_goals
    try rw [manuscriptNormV0_6_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV0_6_rounded_endpoints :
    (12896941244777008109092538609 / 1000000000000000000000000000000) ≤ manuscriptNormV0_6Interval.1 ∧ manuscriptNormV0_6Interval.2 ≤ (1612117655597126146042737969 / 125000000000000000000000000000) := by
  simp only [manuscriptNormV0_6Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV0_6_enclosure :
    manuscriptNormV0_6Term ∈ Set.Icc ((12896941244777008109092538609 / 1000000000000000000000000000000) : ℝ) ((1612117655597126146042737969 / 125000000000000000000000000000) : ℝ) := by
  have hlo : ((12896941244777008109092538609 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormV0_6Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV0_6_rounded_endpoints.1
  have hhi : (manuscriptNormV0_6Interval.2 : ℝ) ≤ ((1612117655597126146042737969 / 125000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV0_6_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV0_6_exact_interval.1, manuscriptNormV0_6_exact_interval.2.trans hhi⟩

def manuscriptNormV0_7Arg : ℂ :=
  1 - (barrierV2Tail.getD 0 (0, 0)).1 * (barrierV2Tail.getD 7 (0, 0)).1

def manuscriptNormV0_7Term : ℝ :=
  (-((barrierV2Tail.getD 0 (0, 0)).2 * (barrierV2Tail.getD 7 (0, 0)).2) *
    Complex.log manuscriptNormV0_7Arg).re

def manuscriptNormV0_7Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (119089937171181 / 5000000000000000) (-229422864123923 / 10000000000000000) (0) (1) (949 / 625) (-7 / 43)

private theorem manuscriptNormV0_7_arg_eq : manuscriptNormV0_7Arg = barrierComplex (1 / 1) (18 / 25) := by
  apply Complex.ext <;> norm_num [manuscriptNormV0_7Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV0_7_weight_eq :
    -((barrierV2Tail.getD 0 (0, 0)).2 * (barrierV2Tail.getD 7 (0, 0)).2) =
      barrierComplex (119089937171181 / 5000000000000000) (-229422864123923 / 10000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV0_7_exact_interval :
    manuscriptNormV0_7Term ∈ Set.Icc (manuscriptNormV0_7Interval.1 : ℝ) (manuscriptNormV0_7Interval.2 : ℝ) := by
  unfold manuscriptNormV0_7Term
  rw [manuscriptNormV0_7_weight_eq]
  have h := manuscript_weighted_complex_log_interval (119089937171181 / 5000000000000000) (-229422864123923 / 10000000000000000)
    manuscriptNormV0_7Arg (0) (1) (949 / 625) (43 / 25) (-7 / 25)
  have hratio : ((-7 / 25) / (43 / 25) : ℚ) = (-7 / 43) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV0_7Interval
  apply h
  all_goals
    try rw [manuscriptNormV0_7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV0_7_rounded_endpoints :
    (9645195985586246393878749607 / 500000000000000000000000000000) ≤ manuscriptNormV0_7Interval.1 ∧ manuscriptNormV0_7Interval.2 ≤ (3858078394234498723893081383 / 200000000000000000000000000000) := by
  simp only [manuscriptNormV0_7Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV0_7_enclosure :
    manuscriptNormV0_7Term ∈ Set.Icc ((9645195985586246393878749607 / 500000000000000000000000000000) : ℝ) ((3858078394234498723893081383 / 200000000000000000000000000000) : ℝ) := by
  have hlo : ((9645195985586246393878749607 / 500000000000000000000000000000) : ℝ) ≤ (manuscriptNormV0_7Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV0_7_rounded_endpoints.1
  have hhi : (manuscriptNormV0_7Interval.2 : ℝ) ≤ ((3858078394234498723893081383 / 200000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV0_7_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV0_7_exact_interval.1, manuscriptNormV0_7_exact_interval.2.trans hhi⟩

def manuscriptNormV0_8Arg : ℂ :=
  1 - (barrierV2Tail.getD 0 (0, 0)).1 * (barrierV2Tail.getD 8 (0, 0)).1

def manuscriptNormV0_8Term : ℝ :=
  (-((barrierV2Tail.getD 0 (0, 0)).2 * (barrierV2Tail.getD 8 (0, 0)).2) *
    Complex.log manuscriptNormV0_8Arg).re

def manuscriptNormV0_8Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (119089937171181 / 5000000000000000) (229422864123923 / 10000000000000000) (0) (-1) (949 / 625) (7 / 43)

private theorem manuscriptNormV0_8_arg_eq : manuscriptNormV0_8Arg = barrierComplex (1 / 1) (-18 / 25) := by
  apply Complex.ext <;> norm_num [manuscriptNormV0_8Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV0_8_weight_eq :
    -((barrierV2Tail.getD 0 (0, 0)).2 * (barrierV2Tail.getD 8 (0, 0)).2) =
      barrierComplex (119089937171181 / 5000000000000000) (229422864123923 / 10000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV0_8_exact_interval :
    manuscriptNormV0_8Term ∈ Set.Icc (manuscriptNormV0_8Interval.1 : ℝ) (manuscriptNormV0_8Interval.2 : ℝ) := by
  unfold manuscriptNormV0_8Term
  rw [manuscriptNormV0_8_weight_eq]
  have h := manuscript_weighted_complex_log_interval (119089937171181 / 5000000000000000) (229422864123923 / 10000000000000000)
    manuscriptNormV0_8Arg (0) (-1) (949 / 625) (43 / 25) (7 / 25)
  have hratio : ((7 / 25) / (43 / 25) : ℚ) = (7 / 43) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV0_8Interval
  apply h
  all_goals
    try rw [manuscriptNormV0_8_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV0_8_rounded_endpoints :
    (9645195985586246393878749607 / 500000000000000000000000000000) ≤ manuscriptNormV0_8Interval.1 ∧ manuscriptNormV0_8Interval.2 ≤ (3858078394234498723893081383 / 200000000000000000000000000000) := by
  simp only [manuscriptNormV0_8Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV0_8_enclosure :
    manuscriptNormV0_8Term ∈ Set.Icc ((9645195985586246393878749607 / 500000000000000000000000000000) : ℝ) ((3858078394234498723893081383 / 200000000000000000000000000000) : ℝ) := by
  have hlo : ((9645195985586246393878749607 / 500000000000000000000000000000) : ℝ) ≤ (manuscriptNormV0_8Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV0_8_rounded_endpoints.1
  have hhi : (manuscriptNormV0_8Interval.2 : ℝ) ≤ ((3858078394234498723893081383 / 200000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV0_8_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV0_8_exact_interval.1, manuscriptNormV0_8_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
