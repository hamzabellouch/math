import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormV7_11Arg : ℂ :=
  1 - (barrierV2Tail.getD 7 (0, 0)).1 * (barrierV2Tail.getD 11 (0, 0)).1

def manuscriptNormV7_11Term : ℝ :=
  (-((barrierV2Tail.getD 7 (0, 0)).2 * (barrierV2Tail.getD 11 (0, 0)).2) *
    Complex.log manuscriptNormV7_11Arg).re

def manuscriptNormV7_11Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (359993860770103 / 20000000000000000) (309276931099449 / 20000000000000000) (1) (0) (5555449 / 3125000) (0 / 1)

private theorem manuscriptNormV7_11_arg_eq : manuscriptNormV7_11Arg = barrierComplex (2357 / 1250) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV7_11Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV7_11_weight_eq :
    -((barrierV2Tail.getD 7 (0, 0)).2 * (barrierV2Tail.getD 11 (0, 0)).2) =
      barrierComplex (359993860770103 / 20000000000000000) (309276931099449 / 20000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV7_11_exact_interval :
    manuscriptNormV7_11Term ∈ Set.Icc (manuscriptNormV7_11Interval.1 : ℝ) (manuscriptNormV7_11Interval.2 : ℝ) := by
  unfold manuscriptNormV7_11Term
  rw [manuscriptNormV7_11_weight_eq]
  have h := manuscript_weighted_complex_log_interval (359993860770103 / 20000000000000000) (309276931099449 / 20000000000000000)
    manuscriptNormV7_11Arg (1) (0) (5555449 / 3125000) (2357 / 1250) (0 / 1)
  have hratio : ((0 / 1) / (2357 / 1250) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV7_11Interval
  apply h
  all_goals
    try rw [manuscriptNormV7_11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV7_11_rounded_endpoints :
    (71351466364959732874330401 / 6250000000000000000000000000) ≤ manuscriptNormV7_11Interval.1 ∧ manuscriptNormV7_11Interval.2 ≤ (11416234618393557261110141487 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV7_11Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV7_11_enclosure :
    manuscriptNormV7_11Term ∈ Set.Icc ((71351466364959732874330401 / 6250000000000000000000000000) : ℝ) ((11416234618393557261110141487 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((71351466364959732874330401 / 6250000000000000000000000000) : ℝ) ≤ (manuscriptNormV7_11Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV7_11_rounded_endpoints.1
  have hhi : (manuscriptNormV7_11Interval.2 : ℝ) ≤ ((11416234618393557261110141487 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV7_11_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV7_11_exact_interval.1, manuscriptNormV7_11_exact_interval.2.trans hhi⟩

def manuscriptNormV7_12Arg : ℂ :=
  1 - (barrierV2Tail.getD 7 (0, 0)).1 * (barrierV2Tail.getD 12 (0, 0)).1

def manuscriptNormV7_12Term : ℝ :=
  (-((barrierV2Tail.getD 7 (0, 0)).2 * (barrierV2Tail.getD 12 (0, 0)).2) *
    Complex.log manuscriptNormV7_12Arg).re

def manuscriptNormV7_12Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-295581257499211 / 20000000000000000) (-371321316540867 / 20000000000000000) (-7) (0) (654368 / 390625) (0 / 1)

private theorem manuscriptNormV7_12_arg_eq : manuscriptNormV7_12Arg = barrierComplex (143 / 1250) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV7_12Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV7_12_weight_eq :
    -((barrierV2Tail.getD 7 (0, 0)).2 * (barrierV2Tail.getD 12 (0, 0)).2) =
      barrierComplex (-295581257499211 / 20000000000000000) (-371321316540867 / 20000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV7_12_exact_interval :
    manuscriptNormV7_12Term ∈ Set.Icc (manuscriptNormV7_12Interval.1 : ℝ) (manuscriptNormV7_12Interval.2 : ℝ) := by
  unfold manuscriptNormV7_12Term
  rw [manuscriptNormV7_12_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-295581257499211 / 20000000000000000) (-371321316540867 / 20000000000000000)
    manuscriptNormV7_12Arg (-7) (0) (654368 / 390625) (143 / 1250) (0 / 1)
  have hratio : ((0 / 1) / (143 / 1250) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV7_12Interval
  apply h
  all_goals
    try rw [manuscriptNormV7_12_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV7_12_rounded_endpoints :
    (8010452334665209331488056821 / 250000000000000000000000000000) ≤ manuscriptNormV7_12Interval.1 ∧ manuscriptNormV7_12Interval.2 ≤ (16020904669330418666468974703 / 500000000000000000000000000000) := by
  simp only [manuscriptNormV7_12Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV7_12_enclosure :
    manuscriptNormV7_12Term ∈ Set.Icc ((8010452334665209331488056821 / 250000000000000000000000000000) : ℝ) ((16020904669330418666468974703 / 500000000000000000000000000000) : ℝ) := by
  have hlo : ((8010452334665209331488056821 / 250000000000000000000000000000) : ℝ) ≤ (manuscriptNormV7_12Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV7_12_rounded_endpoints.1
  have hhi : (manuscriptNormV7_12Interval.2 : ℝ) ≤ ((16020904669330418666468974703 / 500000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV7_12_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV7_12_exact_interval.1, manuscriptNormV7_12_exact_interval.2.trans hhi⟩

def manuscriptNormV8_0Arg : ℂ :=
  1 - (barrierV2Tail.getD 8 (0, 0)).1 * (barrierV2Tail.getD 0 (0, 0)).1

def manuscriptNormV8_0Term : ℝ :=
  (-((barrierV2Tail.getD 8 (0, 0)).2 * (barrierV2Tail.getD 0 (0, 0)).2) *
    Complex.log manuscriptNormV8_0Arg).re

def manuscriptNormV8_0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (119089937171181 / 5000000000000000) (229422864123923 / 10000000000000000) (0) (-1) (949 / 625) (7 / 43)

private theorem manuscriptNormV8_0_arg_eq : manuscriptNormV8_0Arg = barrierComplex (1 / 1) (-18 / 25) := by
  apply Complex.ext <;> norm_num [manuscriptNormV8_0Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV8_0_weight_eq :
    -((barrierV2Tail.getD 8 (0, 0)).2 * (barrierV2Tail.getD 0 (0, 0)).2) =
      barrierComplex (119089937171181 / 5000000000000000) (229422864123923 / 10000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV8_0_exact_interval :
    manuscriptNormV8_0Term ∈ Set.Icc (manuscriptNormV8_0Interval.1 : ℝ) (manuscriptNormV8_0Interval.2 : ℝ) := by
  unfold manuscriptNormV8_0Term
  rw [manuscriptNormV8_0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (119089937171181 / 5000000000000000) (229422864123923 / 10000000000000000)
    manuscriptNormV8_0Arg (0) (-1) (949 / 625) (43 / 25) (7 / 25)
  have hratio : ((7 / 25) / (43 / 25) : ℚ) = (7 / 43) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV8_0Interval
  apply h
  all_goals
    try rw [manuscriptNormV8_0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV8_0_rounded_endpoints :
    (9645195985586246393878749607 / 500000000000000000000000000000) ≤ manuscriptNormV8_0Interval.1 ∧ manuscriptNormV8_0Interval.2 ≤ (3858078394234498723893081383 / 200000000000000000000000000000) := by
  simp only [manuscriptNormV8_0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV8_0_enclosure :
    manuscriptNormV8_0Term ∈ Set.Icc ((9645195985586246393878749607 / 500000000000000000000000000000) : ℝ) ((3858078394234498723893081383 / 200000000000000000000000000000) : ℝ) := by
  have hlo : ((9645195985586246393878749607 / 500000000000000000000000000000) : ℝ) ≤ (manuscriptNormV8_0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV8_0_rounded_endpoints.1
  have hhi : (manuscriptNormV8_0Interval.2 : ℝ) ≤ ((3858078394234498723893081383 / 200000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV8_0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV8_0_exact_interval.1, manuscriptNormV8_0_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
