import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormV8_10Arg : ℂ :=
  1 - (barrierV2Tail.getD 8 (0, 0)).1 * (barrierV2Tail.getD 10 (0, 0)).1

def manuscriptNormV8_10Term : ℝ :=
  (-((barrierV2Tail.getD 8 (0, 0)).2 * (barrierV2Tail.getD 10 (0, 0)).2) *
    Complex.log manuscriptNormV8_10Arg).re

def manuscriptNormV8_10Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-142349837215793 / 10000000000000000) (42818261555831 / 10000000000000000) (1) (0) (13830961 / 8000000) (0 / 1)

private theorem manuscriptNormV8_10_arg_eq : manuscriptNormV8_10Arg = barrierComplex (3719 / 2000) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV8_10Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV8_10_weight_eq :
    -((barrierV2Tail.getD 8 (0, 0)).2 * (barrierV2Tail.getD 10 (0, 0)).2) =
      barrierComplex (-142349837215793 / 10000000000000000) (42818261555831 / 10000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV8_10_exact_interval :
    manuscriptNormV8_10Term ∈ Set.Icc (manuscriptNormV8_10Interval.1 : ℝ) (manuscriptNormV8_10Interval.2 : ℝ) := by
  unfold manuscriptNormV8_10Term
  rw [manuscriptNormV8_10_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-142349837215793 / 10000000000000000) (42818261555831 / 10000000000000000)
    manuscriptNormV8_10Arg (1) (0) (13830961 / 8000000) (3719 / 2000) (0 / 1)
  have hratio : ((0 / 1) / (3719 / 2000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV8_10Interval
  apply h
  all_goals
    try rw [manuscriptNormV8_10_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV8_10_rounded_endpoints :
    (-2207517269453298436964373209 / 250000000000000000000000000000) ≤ manuscriptNormV8_10Interval.1 ∧ manuscriptNormV8_10Interval.2 ≤ (-4415034538906596873448011269 / 500000000000000000000000000000) := by
  simp only [manuscriptNormV8_10Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV8_10_enclosure :
    manuscriptNormV8_10Term ∈ Set.Icc ((-2207517269453298436964373209 / 250000000000000000000000000000) : ℝ) ((-4415034538906596873448011269 / 500000000000000000000000000000) : ℝ) := by
  have hlo : ((-2207517269453298436964373209 / 250000000000000000000000000000) : ℝ) ≤ (manuscriptNormV8_10Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV8_10_rounded_endpoints.1
  have hhi : (manuscriptNormV8_10Interval.2 : ℝ) ≤ ((-4415034538906596873448011269 / 500000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV8_10_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV8_10_exact_interval.1, manuscriptNormV8_10_exact_interval.2.trans hhi⟩

def manuscriptNormV8_11Arg : ℂ :=
  1 - (barrierV2Tail.getD 8 (0, 0)).1 * (barrierV2Tail.getD 11 (0, 0)).1

def manuscriptNormV8_11Term : ℝ :=
  (-((barrierV2Tail.getD 8 (0, 0)).2 * (barrierV2Tail.getD 11 (0, 0)).2) *
    Complex.log manuscriptNormV8_11Arg).re

def manuscriptNormV8_11Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-295581257499211 / 20000000000000000) (371321316540867 / 20000000000000000) (-7) (0) (654368 / 390625) (0 / 1)

private theorem manuscriptNormV8_11_arg_eq : manuscriptNormV8_11Arg = barrierComplex (143 / 1250) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV8_11Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV8_11_weight_eq :
    -((barrierV2Tail.getD 8 (0, 0)).2 * (barrierV2Tail.getD 11 (0, 0)).2) =
      barrierComplex (-295581257499211 / 20000000000000000) (371321316540867 / 20000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV8_11_exact_interval :
    manuscriptNormV8_11Term ∈ Set.Icc (manuscriptNormV8_11Interval.1 : ℝ) (manuscriptNormV8_11Interval.2 : ℝ) := by
  unfold manuscriptNormV8_11Term
  rw [manuscriptNormV8_11_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-295581257499211 / 20000000000000000) (371321316540867 / 20000000000000000)
    manuscriptNormV8_11Arg (-7) (0) (654368 / 390625) (143 / 1250) (0 / 1)
  have hratio : ((0 / 1) / (143 / 1250) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV8_11Interval
  apply h
  all_goals
    try rw [manuscriptNormV8_11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV8_11_rounded_endpoints :
    (8010452334665209331488056821 / 250000000000000000000000000000) ≤ manuscriptNormV8_11Interval.1 ∧ manuscriptNormV8_11Interval.2 ≤ (16020904669330418666468974703 / 500000000000000000000000000000) := by
  simp only [manuscriptNormV8_11Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV8_11_enclosure :
    manuscriptNormV8_11Term ∈ Set.Icc ((8010452334665209331488056821 / 250000000000000000000000000000) : ℝ) ((16020904669330418666468974703 / 500000000000000000000000000000) : ℝ) := by
  have hlo : ((8010452334665209331488056821 / 250000000000000000000000000000) : ℝ) ≤ (manuscriptNormV8_11Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV8_11_rounded_endpoints.1
  have hhi : (manuscriptNormV8_11Interval.2 : ℝ) ≤ ((16020904669330418666468974703 / 500000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV8_11_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV8_11_exact_interval.1, manuscriptNormV8_11_exact_interval.2.trans hhi⟩

def manuscriptNormV8_12Arg : ℂ :=
  1 - (barrierV2Tail.getD 8 (0, 0)).1 * (barrierV2Tail.getD 12 (0, 0)).1

def manuscriptNormV8_12Term : ℝ :=
  (-((barrierV2Tail.getD 8 (0, 0)).2 * (barrierV2Tail.getD 12 (0, 0)).2) *
    Complex.log manuscriptNormV8_12Arg).re

def manuscriptNormV8_12Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (359993860770103 / 20000000000000000) (-309276931099449 / 20000000000000000) (1) (0) (5555449 / 3125000) (0 / 1)

private theorem manuscriptNormV8_12_arg_eq : manuscriptNormV8_12Arg = barrierComplex (2357 / 1250) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV8_12Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV8_12_weight_eq :
    -((barrierV2Tail.getD 8 (0, 0)).2 * (barrierV2Tail.getD 12 (0, 0)).2) =
      barrierComplex (359993860770103 / 20000000000000000) (-309276931099449 / 20000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV8_12_exact_interval :
    manuscriptNormV8_12Term ∈ Set.Icc (manuscriptNormV8_12Interval.1 : ℝ) (manuscriptNormV8_12Interval.2 : ℝ) := by
  unfold manuscriptNormV8_12Term
  rw [manuscriptNormV8_12_weight_eq]
  have h := manuscript_weighted_complex_log_interval (359993860770103 / 20000000000000000) (-309276931099449 / 20000000000000000)
    manuscriptNormV8_12Arg (1) (0) (5555449 / 3125000) (2357 / 1250) (0 / 1)
  have hratio : ((0 / 1) / (2357 / 1250) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV8_12Interval
  apply h
  all_goals
    try rw [manuscriptNormV8_12_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV8_12_rounded_endpoints :
    (71351466364959732874330401 / 6250000000000000000000000000) ≤ manuscriptNormV8_12Interval.1 ∧ manuscriptNormV8_12Interval.2 ≤ (11416234618393557261110141487 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV8_12Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV8_12_enclosure :
    manuscriptNormV8_12Term ∈ Set.Icc ((71351466364959732874330401 / 6250000000000000000000000000) : ℝ) ((11416234618393557261110141487 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((71351466364959732874330401 / 6250000000000000000000000000) : ℝ) ≤ (manuscriptNormV8_12Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV8_12_rounded_endpoints.1
  have hhi : (manuscriptNormV8_12Interval.2 : ℝ) ≤ ((11416234618393557261110141487 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV8_12_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV8_12_exact_interval.1, manuscriptNormV8_12_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
