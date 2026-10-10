import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormV5_10Arg : ℂ :=
  1 - (barrierV2Tail.getD 5 (0, 0)).1 * (barrierV2Tail.getD 10 (0, 0)).1

def manuscriptNormV5_10Term : ℝ :=
  (-((barrierV2Tail.getD 5 (0, 0)).2 * (barrierV2Tail.getD 10 (0, 0)).2) *
    Complex.log manuscriptNormV5_10Arg).re

def manuscriptNormV5_10Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (160081263898183 / 10000000000000000) (-16780401343011 / 10000000000000000) (-4) (0) (6507601 / 6250000) (0 / 1)

private theorem manuscriptNormV5_10_arg_eq : manuscriptNormV5_10Arg = barrierComplex (2551 / 10000) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV5_10Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV5_10_weight_eq :
    -((barrierV2Tail.getD 5 (0, 0)).2 * (barrierV2Tail.getD 10 (0, 0)).2) =
      barrierComplex (160081263898183 / 10000000000000000) (-16780401343011 / 10000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV5_10_exact_interval :
    manuscriptNormV5_10Term ∈ Set.Icc (manuscriptNormV5_10Interval.1 : ℝ) (manuscriptNormV5_10Interval.2 : ℝ) := by
  unfold manuscriptNormV5_10Term
  rw [manuscriptNormV5_10_weight_eq]
  have h := manuscript_weighted_complex_log_interval (160081263898183 / 10000000000000000) (-16780401343011 / 10000000000000000)
    manuscriptNormV5_10Arg (-4) (0) (6507601 / 6250000) (2551 / 10000) (0 / 1)
  have hratio : ((0 / 1) / (2551 / 10000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV5_10Interval
  apply h
  all_goals
    try rw [manuscriptNormV5_10_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV5_10_rounded_endpoints :
    (-2733586989958455530919248339 / 125000000000000000000000000000) ≤ manuscriptNormV5_10Interval.1 ∧ manuscriptNormV5_10Interval.2 ≤ (-10934347959833822121515096977 / 500000000000000000000000000000) := by
  simp only [manuscriptNormV5_10Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV5_10_enclosure :
    manuscriptNormV5_10Term ∈ Set.Icc ((-2733586989958455530919248339 / 125000000000000000000000000000) : ℝ) ((-10934347959833822121515096977 / 500000000000000000000000000000) : ℝ) := by
  have hlo : ((-2733586989958455530919248339 / 125000000000000000000000000000) : ℝ) ≤ (manuscriptNormV5_10Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV5_10_rounded_endpoints.1
  have hhi : (manuscriptNormV5_10Interval.2 : ℝ) ≤ ((-10934347959833822121515096977 / 500000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV5_10_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV5_10_exact_interval.1, manuscriptNormV5_10_exact_interval.2.trans hhi⟩

def manuscriptNormV5_11Arg : ℂ :=
  1 - (barrierV2Tail.getD 5 (0, 0)).1 * (barrierV2Tail.getD 11 (0, 0)).1

def manuscriptNormV5_11Term : ℝ :=
  (-((barrierV2Tail.getD 5 (0, 0)).2 * (barrierV2Tail.getD 11 (0, 0)).2) *
    Complex.log manuscriptNormV5_11Arg).re

def manuscriptNormV5_11Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (389474106710791 / 20000000000000000) (-335265249034277 / 20000000000000000) (1) (0) (122036209 / 78125000) (0 / 1)

private theorem manuscriptNormV5_11_arg_eq : manuscriptNormV5_11Arg = barrierComplex (11047 / 6250) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV5_11Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV5_11_weight_eq :
    -((barrierV2Tail.getD 5 (0, 0)).2 * (barrierV2Tail.getD 11 (0, 0)).2) =
      barrierComplex (389474106710791 / 20000000000000000) (-335265249034277 / 20000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV5_11_exact_interval :
    manuscriptNormV5_11Term ∈ Set.Icc (manuscriptNormV5_11Interval.1 : ℝ) (manuscriptNormV5_11Interval.2 : ℝ) := by
  unfold manuscriptNormV5_11Term
  rw [manuscriptNormV5_11_weight_eq]
  have h := manuscript_weighted_complex_log_interval (389474106710791 / 20000000000000000) (-335265249034277 / 20000000000000000)
    manuscriptNormV5_11Arg (1) (0) (122036209 / 78125000) (11047 / 6250) (0 / 1)
  have hratio : ((0 / 1) / (11047 / 6250) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV5_11Interval
  apply h
  all_goals
    try rw [manuscriptNormV5_11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV5_11_rounded_endpoints :
    (2218356623650128240239486083 / 200000000000000000000000000000) ≤ manuscriptNormV5_11Interval.1 ∧ manuscriptNormV5_11Interval.2 ≤ (5545891559125320601256195969 / 500000000000000000000000000000) := by
  simp only [manuscriptNormV5_11Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV5_11_enclosure :
    manuscriptNormV5_11Term ∈ Set.Icc ((2218356623650128240239486083 / 200000000000000000000000000000) : ℝ) ((5545891559125320601256195969 / 500000000000000000000000000000) : ℝ) := by
  have hlo : ((2218356623650128240239486083 / 200000000000000000000000000000) : ℝ) ≤ (manuscriptNormV5_11Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV5_11_rounded_endpoints.1
  have hhi : (manuscriptNormV5_11Interval.2 : ℝ) ≤ ((5545891559125320601256195969 / 500000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV5_11_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV5_11_exact_interval.1, manuscriptNormV5_11_exact_interval.2.trans hhi⟩

def manuscriptNormV5_12Arg : ℂ :=
  1 - (barrierV2Tail.getD 5 (0, 0)).1 * (barrierV2Tail.getD 12 (0, 0)).1

def manuscriptNormV5_12Term : ℝ :=
  (-((barrierV2Tail.getD 5 (0, 0)).2 * (barrierV2Tail.getD 12 (0, 0)).2) *
    Complex.log manuscriptNormV5_12Arg).re

def manuscriptNormV5_12Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-445455465826873 / 20000000000000000) (256246551143909 / 20000000000000000) (-5) (0) (16889672 / 9765625) (0 / 1)

private theorem manuscriptNormV5_12_arg_eq : manuscriptNormV5_12Arg = barrierComplex (1453 / 6250) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV5_12Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV5_12_weight_eq :
    -((barrierV2Tail.getD 5 (0, 0)).2 * (barrierV2Tail.getD 12 (0, 0)).2) =
      barrierComplex (-445455465826873 / 20000000000000000) (256246551143909 / 20000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV5_12_exact_interval :
    manuscriptNormV5_12Term ∈ Set.Icc (manuscriptNormV5_12Interval.1 : ℝ) (manuscriptNormV5_12Interval.2 : ℝ) := by
  unfold manuscriptNormV5_12Term
  rw [manuscriptNormV5_12_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-445455465826873 / 20000000000000000) (256246551143909 / 20000000000000000)
    manuscriptNormV5_12Arg (-5) (0) (16889672 / 9765625) (1453 / 6250) (0 / 1)
  have hratio : ((0 / 1) / (1453 / 6250) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV5_12Interval
  apply h
  all_goals
    try rw [manuscriptNormV5_12_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV5_12_rounded_endpoints :
    (4061860828661937773552758353 / 125000000000000000000000000000) ≤ manuscriptNormV5_12Interval.1 ∧ manuscriptNormV5_12Interval.2 ≤ (32494886629295502195942314237 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV5_12Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV5_12_enclosure :
    manuscriptNormV5_12Term ∈ Set.Icc ((4061860828661937773552758353 / 125000000000000000000000000000) : ℝ) ((32494886629295502195942314237 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((4061860828661937773552758353 / 125000000000000000000000000000) : ℝ) ≤ (manuscriptNormV5_12Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV5_12_rounded_endpoints.1
  have hhi : (manuscriptNormV5_12Interval.2 : ℝ) ≤ ((32494886629295502195942314237 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV5_12_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV5_12_exact_interval.1, manuscriptNormV5_12_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
