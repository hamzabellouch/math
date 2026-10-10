import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormV6_12Arg : ℂ :=
  1 - (barrierV2Tail.getD 6 (0, 0)).1 * (barrierV2Tail.getD 12 (0, 0)).1

def manuscriptNormV6_12Term : ℝ :=
  (-((barrierV2Tail.getD 6 (0, 0)).2 * (barrierV2Tail.getD 12 (0, 0)).2) *
    Complex.log manuscriptNormV6_12Arg).re

def manuscriptNormV6_12Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (389474106710791 / 20000000000000000) (335265249034277 / 20000000000000000) (1) (0) (122036209 / 78125000) (0 / 1)

private theorem manuscriptNormV6_12_arg_eq : manuscriptNormV6_12Arg = barrierComplex (11047 / 6250) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV6_12Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV6_12_weight_eq :
    -((barrierV2Tail.getD 6 (0, 0)).2 * (barrierV2Tail.getD 12 (0, 0)).2) =
      barrierComplex (389474106710791 / 20000000000000000) (335265249034277 / 20000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV6_12_exact_interval :
    manuscriptNormV6_12Term ∈ Set.Icc (manuscriptNormV6_12Interval.1 : ℝ) (manuscriptNormV6_12Interval.2 : ℝ) := by
  unfold manuscriptNormV6_12Term
  rw [manuscriptNormV6_12_weight_eq]
  have h := manuscript_weighted_complex_log_interval (389474106710791 / 20000000000000000) (335265249034277 / 20000000000000000)
    manuscriptNormV6_12Arg (1) (0) (122036209 / 78125000) (11047 / 6250) (0 / 1)
  have hratio : ((0 / 1) / (11047 / 6250) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV6_12Interval
  apply h
  all_goals
    try rw [manuscriptNormV6_12_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV6_12_rounded_endpoints :
    (2218356623650128240239486083 / 200000000000000000000000000000) ≤ manuscriptNormV6_12Interval.1 ∧ manuscriptNormV6_12Interval.2 ≤ (5545891559125320601256195969 / 500000000000000000000000000000) := by
  simp only [manuscriptNormV6_12Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV6_12_enclosure :
    manuscriptNormV6_12Term ∈ Set.Icc ((2218356623650128240239486083 / 200000000000000000000000000000) : ℝ) ((5545891559125320601256195969 / 500000000000000000000000000000) : ℝ) := by
  have hlo : ((2218356623650128240239486083 / 200000000000000000000000000000) : ℝ) ≤ (manuscriptNormV6_12Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV6_12_rounded_endpoints.1
  have hhi : (manuscriptNormV6_12Interval.2 : ℝ) ≤ ((5545891559125320601256195969 / 500000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV6_12_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV6_12_exact_interval.1, manuscriptNormV6_12_exact_interval.2.trans hhi⟩

def manuscriptNormV7_0Arg : ℂ :=
  1 - (barrierV2Tail.getD 7 (0, 0)).1 * (barrierV2Tail.getD 0 (0, 0)).1

def manuscriptNormV7_0Term : ℝ :=
  (-((barrierV2Tail.getD 7 (0, 0)).2 * (barrierV2Tail.getD 0 (0, 0)).2) *
    Complex.log manuscriptNormV7_0Arg).re

def manuscriptNormV7_0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (119089937171181 / 5000000000000000) (-229422864123923 / 10000000000000000) (0) (1) (949 / 625) (-7 / 43)

private theorem manuscriptNormV7_0_arg_eq : manuscriptNormV7_0Arg = barrierComplex (1 / 1) (18 / 25) := by
  apply Complex.ext <;> norm_num [manuscriptNormV7_0Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV7_0_weight_eq :
    -((barrierV2Tail.getD 7 (0, 0)).2 * (barrierV2Tail.getD 0 (0, 0)).2) =
      barrierComplex (119089937171181 / 5000000000000000) (-229422864123923 / 10000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV7_0_exact_interval :
    manuscriptNormV7_0Term ∈ Set.Icc (manuscriptNormV7_0Interval.1 : ℝ) (manuscriptNormV7_0Interval.2 : ℝ) := by
  unfold manuscriptNormV7_0Term
  rw [manuscriptNormV7_0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (119089937171181 / 5000000000000000) (-229422864123923 / 10000000000000000)
    manuscriptNormV7_0Arg (0) (1) (949 / 625) (43 / 25) (-7 / 25)
  have hratio : ((-7 / 25) / (43 / 25) : ℚ) = (-7 / 43) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV7_0Interval
  apply h
  all_goals
    try rw [manuscriptNormV7_0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV7_0_rounded_endpoints :
    (9645195985586246393878749607 / 500000000000000000000000000000) ≤ manuscriptNormV7_0Interval.1 ∧ manuscriptNormV7_0Interval.2 ≤ (3858078394234498723893081383 / 200000000000000000000000000000) := by
  simp only [manuscriptNormV7_0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV7_0_enclosure :
    manuscriptNormV7_0Term ∈ Set.Icc ((9645195985586246393878749607 / 500000000000000000000000000000) : ℝ) ((3858078394234498723893081383 / 200000000000000000000000000000) : ℝ) := by
  have hlo : ((9645195985586246393878749607 / 500000000000000000000000000000) : ℝ) ≤ (manuscriptNormV7_0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV7_0_rounded_endpoints.1
  have hhi : (manuscriptNormV7_0Interval.2 : ℝ) ≤ ((3858078394234498723893081383 / 200000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV7_0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV7_0_exact_interval.1, manuscriptNormV7_0_exact_interval.2.trans hhi⟩

def manuscriptNormV7_1Arg : ℂ :=
  1 - (barrierV2Tail.getD 7 (0, 0)).1 * (barrierV2Tail.getD 1 (0, 0)).1

def manuscriptNormV7_1Term : ℝ :=
  (-((barrierV2Tail.getD 7 (0, 0)).2 * (barrierV2Tail.getD 1 (0, 0)).2) *
    Complex.log manuscriptNormV7_1Arg).re

def manuscriptNormV7_1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (17439989085201 / 2500000000000000) (-33597567865583 / 5000000000000000) (0) (1) (27289 / 15625) (-17 / 233)

private theorem manuscriptNormV7_1_arg_eq : manuscriptNormV7_1Arg = barrierComplex (1 / 1) (108 / 125) := by
  apply Complex.ext <;> norm_num [manuscriptNormV7_1Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV7_1_weight_eq :
    -((barrierV2Tail.getD 7 (0, 0)).2 * (barrierV2Tail.getD 1 (0, 0)).2) =
      barrierComplex (17439989085201 / 2500000000000000) (-33597567865583 / 5000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV7_1_exact_interval :
    manuscriptNormV7_1Term ∈ Set.Icc (manuscriptNormV7_1Interval.1 : ℝ) (manuscriptNormV7_1Interval.2 : ℝ) := by
  unfold manuscriptNormV7_1Term
  rw [manuscriptNormV7_1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (17439989085201 / 2500000000000000) (-33597567865583 / 5000000000000000)
    manuscriptNormV7_1Arg (0) (1) (27289 / 15625) (233 / 125) (-17 / 125)
  have hratio : ((-17 / 125) / (233 / 125) : ℚ) = (-17 / 233) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV7_1Interval
  apply h
  all_goals
    try rw [manuscriptNormV7_1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV7_1_rounded_endpoints :
    (3366521771051272355351880559 / 500000000000000000000000000000) ≤ manuscriptNormV7_1Interval.1 ∧ manuscriptNormV7_1Interval.2 ≤ (1683260885525636238575254391 / 250000000000000000000000000000) := by
  simp only [manuscriptNormV7_1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV7_1_enclosure :
    manuscriptNormV7_1Term ∈ Set.Icc ((3366521771051272355351880559 / 500000000000000000000000000000) : ℝ) ((1683260885525636238575254391 / 250000000000000000000000000000) : ℝ) := by
  have hlo : ((3366521771051272355351880559 / 500000000000000000000000000000) : ℝ) ≤ (manuscriptNormV7_1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV7_1_rounded_endpoints.1
  have hhi : (manuscriptNormV7_1Interval.2 : ℝ) ≤ ((1683260885525636238575254391 / 250000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV7_1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV7_1_exact_interval.1, manuscriptNormV7_1_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
