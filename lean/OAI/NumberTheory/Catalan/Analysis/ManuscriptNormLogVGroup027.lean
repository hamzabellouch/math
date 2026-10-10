import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormV6_3Arg : ℂ :=
  1 - (barrierV2Tail.getD 6 (0, 0)).1 * (barrierV2Tail.getD 3 (0, 0)).1

def manuscriptNormV6_3Term : ℝ :=
  (-((barrierV2Tail.getD 6 (0, 0)).2 * (barrierV2Tail.getD 3 (0, 0)).2) *
    Complex.log manuscriptNormV6_3Arg).re

def manuscriptNormV6_3Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (33589651698169 / 5000000000000000) (-1481637471433 / 156250000000000) (0) (1) (1549081 / 1000000) (-259 / 1741)

private theorem manuscriptNormV6_3_arg_eq : manuscriptNormV6_3Arg = barrierComplex (1 / 1) (741 / 1000) := by
  apply Complex.ext <;> norm_num [manuscriptNormV6_3Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV6_3_weight_eq :
    -((barrierV2Tail.getD 6 (0, 0)).2 * (barrierV2Tail.getD 3 (0, 0)).2) =
      barrierComplex (33589651698169 / 5000000000000000) (-1481637471433 / 156250000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV6_3_exact_interval :
    manuscriptNormV6_3Term ∈ Set.Icc (manuscriptNormV6_3Interval.1 : ℝ) (manuscriptNormV6_3Interval.2 : ℝ) := by
  unfold manuscriptNormV6_3Term
  rw [manuscriptNormV6_3_weight_eq]
  have h := manuscript_weighted_complex_log_interval (33589651698169 / 5000000000000000) (-1481637471433 / 156250000000000)
    manuscriptNormV6_3Arg (0) (1) (1549081 / 1000000) (1741 / 1000) (-259 / 1000)
  have hratio : ((-259 / 1000) / (1741 / 1000) : ℚ) = (-259 / 1741) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV6_3Interval
  apply h
  all_goals
    try rw [manuscriptNormV6_3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV6_3_rounded_endpoints :
    (7517221743037368858959427589 / 1000000000000000000000000000000) ≤ manuscriptNormV6_3Interval.1 ∧ manuscriptNormV6_3Interval.2 ≤ (1879305435759342300679999343 / 250000000000000000000000000000) := by
  simp only [manuscriptNormV6_3Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV6_3_enclosure :
    manuscriptNormV6_3Term ∈ Set.Icc ((7517221743037368858959427589 / 1000000000000000000000000000000) : ℝ) ((1879305435759342300679999343 / 250000000000000000000000000000) : ℝ) := by
  have hlo : ((7517221743037368858959427589 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormV6_3Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV6_3_rounded_endpoints.1
  have hhi : (manuscriptNormV6_3Interval.2 : ℝ) ≤ ((1879305435759342300679999343 / 250000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV6_3_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV6_3_exact_interval.1, manuscriptNormV6_3_exact_interval.2.trans hhi⟩

def manuscriptNormV6_4Arg : ℂ :=
  1 - (barrierV2Tail.getD 6 (0, 0)).1 * (barrierV2Tail.getD 4 (0, 0)).1

def manuscriptNormV6_4Term : ℝ :=
  (-((barrierV2Tail.getD 6 (0, 0)).2 * (barrierV2Tail.getD 4 (0, 0)).2) *
    Complex.log manuscriptNormV6_4Arg).re

def manuscriptNormV6_4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-158231827865049 / 10000000000000000) (6979596199593 / 312500000000000) (0) (1) (62073709 / 39062500) (-1453 / 11047)

private theorem manuscriptNormV6_4_arg_eq : manuscriptNormV6_4Arg = barrierComplex (1 / 1) (4797 / 6250) := by
  apply Complex.ext <;> norm_num [manuscriptNormV6_4Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV6_4_weight_eq :
    -((barrierV2Tail.getD 6 (0, 0)).2 * (barrierV2Tail.getD 4 (0, 0)).2) =
      barrierComplex (-158231827865049 / 10000000000000000) (6979596199593 / 312500000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV6_4_exact_interval :
    manuscriptNormV6_4Term ∈ Set.Icc (manuscriptNormV6_4Interval.1 : ℝ) (manuscriptNormV6_4Interval.2 : ℝ) := by
  unfold manuscriptNormV6_4Term
  rw [manuscriptNormV6_4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-158231827865049 / 10000000000000000) (6979596199593 / 312500000000000)
    manuscriptNormV6_4Arg (0) (1) (62073709 / 39062500) (11047 / 6250) (-1453 / 6250)
  have hratio : ((-1453 / 6250) / (11047 / 6250) : ℚ) = (-1453 / 11047) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV6_4Interval
  apply h
  all_goals
    try rw [manuscriptNormV6_4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV6_4_rounded_endpoints :
    (-18285074699575041905754917947 / 1000000000000000000000000000000) ≤ manuscriptNormV6_4Interval.1 ∧ manuscriptNormV6_4Interval.2 ≤ (-18285074699575041096073057651 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV6_4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV6_4_enclosure :
    manuscriptNormV6_4Term ∈ Set.Icc ((-18285074699575041905754917947 / 1000000000000000000000000000000) : ℝ) ((-18285074699575041096073057651 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((-18285074699575041905754917947 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormV6_4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV6_4_rounded_endpoints.1
  have hhi : (manuscriptNormV6_4Interval.2 : ℝ) ≤ ((-18285074699575041096073057651 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV6_4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV6_4_exact_interval.1, manuscriptNormV6_4_exact_interval.2.trans hhi⟩

def manuscriptNormV6_5Arg : ℂ :=
  1 - (barrierV2Tail.getD 6 (0, 0)).1 * (barrierV2Tail.getD 5 (0, 0)).1

def manuscriptNormV6_5Term : ℝ :=
  (-((barrierV2Tail.getD 6 (0, 0)).2 * (barrierV2Tail.getD 5 (0, 0)).2) *
    Complex.log manuscriptNormV6_5Arg).re

def manuscriptNormV6_5Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-555047830758473 / 10000000000000000) (0 / 1) (-3) (0) (958441 / 781250) (0 / 1)

private theorem manuscriptNormV6_5_arg_eq : manuscriptNormV6_5Arg = barrierComplex (979 / 2500) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV6_5Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV6_5_weight_eq :
    -((barrierV2Tail.getD 6 (0, 0)).2 * (barrierV2Tail.getD 5 (0, 0)).2) =
      barrierComplex (-555047830758473 / 10000000000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV6_5_exact_interval :
    manuscriptNormV6_5Term ∈ Set.Icc (manuscriptNormV6_5Interval.1 : ℝ) (manuscriptNormV6_5Interval.2 : ℝ) := by
  unfold manuscriptNormV6_5Term
  rw [manuscriptNormV6_5_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-555047830758473 / 10000000000000000) (0 / 1)
    manuscriptNormV6_5Arg (-3) (0) (958441 / 781250) (979 / 2500) (0 / 1)
  have hratio : ((0 / 1) / (979 / 2500) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV6_5Interval
  apply h
  all_goals
    try rw [manuscriptNormV6_5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV6_5_rounded_endpoints :
    (52036531644412522036185932323 / 1000000000000000000000000000000) ≤ manuscriptNormV6_5Interval.1 ∧ manuscriptNormV6_5Interval.2 ≤ (52036531644412522047429808083 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV6_5Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV6_5_enclosure :
    manuscriptNormV6_5Term ∈ Set.Icc ((52036531644412522036185932323 / 1000000000000000000000000000000) : ℝ) ((52036531644412522047429808083 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((52036531644412522036185932323 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormV6_5Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV6_5_rounded_endpoints.1
  have hhi : (manuscriptNormV6_5Interval.2 : ℝ) ≤ ((52036531644412522047429808083 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV6_5_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV6_5_exact_interval.1, manuscriptNormV6_5_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
