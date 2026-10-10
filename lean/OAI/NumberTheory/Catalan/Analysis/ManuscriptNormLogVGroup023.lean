import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormV5_4Arg : ℂ :=
  1 - (barrierV2Tail.getD 5 (0, 0)).1 * (barrierV2Tail.getD 4 (0, 0)).1

def manuscriptNormV5_4Term : ℝ :=
  (-((barrierV2Tail.getD 5 (0, 0)).2 * (barrierV2Tail.getD 4 (0, 0)).2) *
    Complex.log manuscriptNormV5_4Arg).re

def manuscriptNormV5_4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-158231827865049 / 10000000000000000) (-6979596199593 / 312500000000000) (0) (-1) (62073709 / 39062500) (1453 / 11047)

private theorem manuscriptNormV5_4_arg_eq : manuscriptNormV5_4Arg = barrierComplex (1 / 1) (-4797 / 6250) := by
  apply Complex.ext <;> norm_num [manuscriptNormV5_4Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV5_4_weight_eq :
    -((barrierV2Tail.getD 5 (0, 0)).2 * (barrierV2Tail.getD 4 (0, 0)).2) =
      barrierComplex (-158231827865049 / 10000000000000000) (-6979596199593 / 312500000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV5_4_exact_interval :
    manuscriptNormV5_4Term ∈ Set.Icc (manuscriptNormV5_4Interval.1 : ℝ) (manuscriptNormV5_4Interval.2 : ℝ) := by
  unfold manuscriptNormV5_4Term
  rw [manuscriptNormV5_4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-158231827865049 / 10000000000000000) (-6979596199593 / 312500000000000)
    manuscriptNormV5_4Arg (0) (-1) (62073709 / 39062500) (11047 / 6250) (1453 / 6250)
  have hratio : ((1453 / 6250) / (11047 / 6250) : ℚ) = (1453 / 11047) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV5_4Interval
  apply h
  all_goals
    try rw [manuscriptNormV5_4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV5_4_rounded_endpoints :
    (-18285074699575041905754917947 / 1000000000000000000000000000000) ≤ manuscriptNormV5_4Interval.1 ∧ manuscriptNormV5_4Interval.2 ≤ (-18285074699575041096073057651 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV5_4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV5_4_enclosure :
    manuscriptNormV5_4Term ∈ Set.Icc ((-18285074699575041905754917947 / 1000000000000000000000000000000) : ℝ) ((-18285074699575041096073057651 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((-18285074699575041905754917947 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormV5_4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV5_4_rounded_endpoints.1
  have hhi : (manuscriptNormV5_4Interval.2 : ℝ) ≤ ((-18285074699575041096073057651 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV5_4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV5_4_exact_interval.1, manuscriptNormV5_4_exact_interval.2.trans hhi⟩

def manuscriptNormV5_5Arg : ℂ :=
  1 - (barrierV2Tail.getD 5 (0, 0)).1 * (barrierV2Tail.getD 5 (0, 0)).1

def manuscriptNormV5_5Term : ℝ :=
  (-((barrierV2Tail.getD 5 (0, 0)).2 * (barrierV2Tail.getD 5 (0, 0)).2) *
    Complex.log manuscriptNormV5_5Arg).re

def manuscriptNormV5_5Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (7362962422863 / 400000000000000) (-8181815098393 / 156250000000000) (1) (0) (16168441 / 12500000) (0 / 1)

private theorem manuscriptNormV5_5_arg_eq : manuscriptNormV5_5Arg = barrierComplex (4021 / 2500) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV5_5Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV5_5_weight_eq :
    -((barrierV2Tail.getD 5 (0, 0)).2 * (barrierV2Tail.getD 5 (0, 0)).2) =
      barrierComplex (7362962422863 / 400000000000000) (-8181815098393 / 156250000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV5_5_exact_interval :
    manuscriptNormV5_5Term ∈ Set.Icc (manuscriptNormV5_5Interval.1 : ℝ) (manuscriptNormV5_5Interval.2 : ℝ) := by
  unfold manuscriptNormV5_5Term
  rw [manuscriptNormV5_5_weight_eq]
  have h := manuscript_weighted_complex_log_interval (7362962422863 / 400000000000000) (-8181815098393 / 156250000000000)
    manuscriptNormV5_5Arg (1) (0) (16168441 / 12500000) (4021 / 2500) (0 / 1)
  have hratio : ((0 / 1) / (4021 / 2500) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV5_5Interval
  apply h
  all_goals
    try rw [manuscriptNormV5_5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV5_5_rounded_endpoints :
    (1093491717623458862478015627 / 125000000000000000000000000000) ≤ manuscriptNormV5_5Interval.1 ∧ manuscriptNormV5_5Interval.2 ≤ (2186983435246917725266771121 / 250000000000000000000000000000) := by
  simp only [manuscriptNormV5_5Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV5_5_enclosure :
    manuscriptNormV5_5Term ∈ Set.Icc ((1093491717623458862478015627 / 125000000000000000000000000000) : ℝ) ((2186983435246917725266771121 / 250000000000000000000000000000) : ℝ) := by
  have hlo : ((1093491717623458862478015627 / 125000000000000000000000000000) : ℝ) ≤ (manuscriptNormV5_5Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV5_5_rounded_endpoints.1
  have hhi : (manuscriptNormV5_5Interval.2 : ℝ) ≤ ((2186983435246917725266771121 / 250000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV5_5_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV5_5_exact_interval.1, manuscriptNormV5_5_exact_interval.2.trans hhi⟩

def manuscriptNormV5_6Arg : ℂ :=
  1 - (barrierV2Tail.getD 5 (0, 0)).1 * (barrierV2Tail.getD 6 (0, 0)).1

def manuscriptNormV5_6Term : ℝ :=
  (-((barrierV2Tail.getD 5 (0, 0)).2 * (barrierV2Tail.getD 6 (0, 0)).2) *
    Complex.log manuscriptNormV5_6Arg).re

def manuscriptNormV5_6Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-555047830758473 / 10000000000000000) (0 / 1) (-3) (0) (958441 / 781250) (0 / 1)

private theorem manuscriptNormV5_6_arg_eq : manuscriptNormV5_6Arg = barrierComplex (979 / 2500) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV5_6Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV5_6_weight_eq :
    -((barrierV2Tail.getD 5 (0, 0)).2 * (barrierV2Tail.getD 6 (0, 0)).2) =
      barrierComplex (-555047830758473 / 10000000000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV5_6_exact_interval :
    manuscriptNormV5_6Term ∈ Set.Icc (manuscriptNormV5_6Interval.1 : ℝ) (manuscriptNormV5_6Interval.2 : ℝ) := by
  unfold manuscriptNormV5_6Term
  rw [manuscriptNormV5_6_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-555047830758473 / 10000000000000000) (0 / 1)
    manuscriptNormV5_6Arg (-3) (0) (958441 / 781250) (979 / 2500) (0 / 1)
  have hratio : ((0 / 1) / (979 / 2500) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV5_6Interval
  apply h
  all_goals
    try rw [manuscriptNormV5_6_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV5_6_rounded_endpoints :
    (52036531644412522036185932323 / 1000000000000000000000000000000) ≤ manuscriptNormV5_6Interval.1 ∧ manuscriptNormV5_6Interval.2 ≤ (52036531644412522047429808083 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV5_6Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV5_6_enclosure :
    manuscriptNormV5_6Term ∈ Set.Icc ((52036531644412522036185932323 / 1000000000000000000000000000000) : ℝ) ((52036531644412522047429808083 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((52036531644412522036185932323 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormV5_6Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV5_6_rounded_endpoints.1
  have hhi : (manuscriptNormV5_6Interval.2 : ℝ) ≤ ((52036531644412522047429808083 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV5_6_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV5_6_exact_interval.1, manuscriptNormV5_6_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
