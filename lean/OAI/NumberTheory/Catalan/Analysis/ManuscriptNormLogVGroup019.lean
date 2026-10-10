import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormV4_5Arg : ℂ :=
  1 - (barrierV2Tail.getD 4 (0, 0)).1 * (barrierV2Tail.getD 5 (0, 0)).1

def manuscriptNormV4_5Term : ℝ :=
  (-((barrierV2Tail.getD 4 (0, 0)).2 * (barrierV2Tail.getD 5 (0, 0)).2) *
    Complex.log manuscriptNormV4_5Arg).re

def manuscriptNormV4_5Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-158231827865049 / 10000000000000000) (-6979596199593 / 312500000000000) (0) (-1) (62073709 / 39062500) (1453 / 11047)

private theorem manuscriptNormV4_5_arg_eq : manuscriptNormV4_5Arg = barrierComplex (1 / 1) (-4797 / 6250) := by
  apply Complex.ext <;> norm_num [manuscriptNormV4_5Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV4_5_weight_eq :
    -((barrierV2Tail.getD 4 (0, 0)).2 * (barrierV2Tail.getD 5 (0, 0)).2) =
      barrierComplex (-158231827865049 / 10000000000000000) (-6979596199593 / 312500000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV4_5_exact_interval :
    manuscriptNormV4_5Term ∈ Set.Icc (manuscriptNormV4_5Interval.1 : ℝ) (manuscriptNormV4_5Interval.2 : ℝ) := by
  unfold manuscriptNormV4_5Term
  rw [manuscriptNormV4_5_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-158231827865049 / 10000000000000000) (-6979596199593 / 312500000000000)
    manuscriptNormV4_5Arg (0) (-1) (62073709 / 39062500) (11047 / 6250) (1453 / 6250)
  have hratio : ((1453 / 6250) / (11047 / 6250) : ℚ) = (1453 / 11047) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV4_5Interval
  apply h
  all_goals
    try rw [manuscriptNormV4_5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV4_5_rounded_endpoints :
    (-18285074699575041905754917947 / 1000000000000000000000000000000) ≤ manuscriptNormV4_5Interval.1 ∧ manuscriptNormV4_5Interval.2 ≤ (-18285074699575041096073057651 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV4_5Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV4_5_enclosure :
    manuscriptNormV4_5Term ∈ Set.Icc ((-18285074699575041905754917947 / 1000000000000000000000000000000) : ℝ) ((-18285074699575041096073057651 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((-18285074699575041905754917947 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormV4_5Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV4_5_rounded_endpoints.1
  have hhi : (manuscriptNormV4_5Interval.2 : ℝ) ≤ ((-18285074699575041096073057651 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV4_5_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV4_5_exact_interval.1, manuscriptNormV4_5_exact_interval.2.trans hhi⟩

def manuscriptNormV4_6Arg : ℂ :=
  1 - (barrierV2Tail.getD 4 (0, 0)).1 * (barrierV2Tail.getD 6 (0, 0)).1

def manuscriptNormV4_6Term : ℝ :=
  (-((barrierV2Tail.getD 4 (0, 0)).2 * (barrierV2Tail.getD 6 (0, 0)).2) *
    Complex.log manuscriptNormV4_6Arg).re

def manuscriptNormV4_6Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-158231827865049 / 10000000000000000) (6979596199593 / 312500000000000) (0) (1) (62073709 / 39062500) (-1453 / 11047)

private theorem manuscriptNormV4_6_arg_eq : manuscriptNormV4_6Arg = barrierComplex (1 / 1) (4797 / 6250) := by
  apply Complex.ext <;> norm_num [manuscriptNormV4_6Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV4_6_weight_eq :
    -((barrierV2Tail.getD 4 (0, 0)).2 * (barrierV2Tail.getD 6 (0, 0)).2) =
      barrierComplex (-158231827865049 / 10000000000000000) (6979596199593 / 312500000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV4_6_exact_interval :
    manuscriptNormV4_6Term ∈ Set.Icc (manuscriptNormV4_6Interval.1 : ℝ) (manuscriptNormV4_6Interval.2 : ℝ) := by
  unfold manuscriptNormV4_6Term
  rw [manuscriptNormV4_6_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-158231827865049 / 10000000000000000) (6979596199593 / 312500000000000)
    manuscriptNormV4_6Arg (0) (1) (62073709 / 39062500) (11047 / 6250) (-1453 / 6250)
  have hratio : ((-1453 / 6250) / (11047 / 6250) : ℚ) = (-1453 / 11047) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV4_6Interval
  apply h
  all_goals
    try rw [manuscriptNormV4_6_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV4_6_rounded_endpoints :
    (-18285074699575041905754917947 / 1000000000000000000000000000000) ≤ manuscriptNormV4_6Interval.1 ∧ manuscriptNormV4_6Interval.2 ≤ (-18285074699575041096073057651 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV4_6Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV4_6_enclosure :
    manuscriptNormV4_6Term ∈ Set.Icc ((-18285074699575041905754917947 / 1000000000000000000000000000000) : ℝ) ((-18285074699575041096073057651 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((-18285074699575041905754917947 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormV4_6Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV4_6_rounded_endpoints.1
  have hhi : (manuscriptNormV4_6Interval.2 : ℝ) ≤ ((-18285074699575041096073057651 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV4_6_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV4_6_exact_interval.1, manuscriptNormV4_6_exact_interval.2.trans hhi⟩

def manuscriptNormV4_7Arg : ℂ :=
  1 - (barrierV2Tail.getD 4 (0, 0)).1 * (barrierV2Tail.getD 7 (0, 0)).1

def manuscriptNormV4_7Term : ℝ :=
  (-((barrierV2Tail.getD 4 (0, 0)).2 * (barrierV2Tail.getD 7 (0, 0)).2) *
    Complex.log manuscriptNormV4_7Arg).re

def manuscriptNormV4_7Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (91031408615547 / 5000000000000000) (-175369027693701 / 10000000000000000) (0) (-1) (2787949 / 1562500) (143 / 2357)

private theorem manuscriptNormV4_7_arg_eq : manuscriptNormV4_7Arg = barrierComplex (1 / 1) (-1107 / 1250) := by
  apply Complex.ext <;> norm_num [manuscriptNormV4_7Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV4_7_weight_eq :
    -((barrierV2Tail.getD 4 (0, 0)).2 * (barrierV2Tail.getD 7 (0, 0)).2) =
      barrierComplex (91031408615547 / 5000000000000000) (-175369027693701 / 10000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV4_7_exact_interval :
    manuscriptNormV4_7Term ∈ Set.Icc (manuscriptNormV4_7Interval.1 : ℝ) (manuscriptNormV4_7Interval.2 : ℝ) := by
  unfold manuscriptNormV4_7Term
  rw [manuscriptNormV4_7_weight_eq]
  have h := manuscript_weighted_complex_log_interval (91031408615547 / 5000000000000000) (-175369027693701 / 10000000000000000)
    manuscriptNormV4_7Arg (0) (-1) (2787949 / 1562500) (2357 / 1250) (143 / 1250)
  have hratio : ((143 / 1250) / (2357 / 1250) : ℚ) = (143 / 2357) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV4_7Interval
  apply h
  all_goals
    try rw [manuscriptNormV4_7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV4_7_rounded_endpoints :
    (-7439891480413310489970227707 / 1000000000000000000000000000000) ≤ manuscriptNormV4_7Interval.1 ∧ manuscriptNormV4_7Interval.2 ≤ (-7439891480413309854216924131 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV4_7Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV4_7_enclosure :
    manuscriptNormV4_7Term ∈ Set.Icc ((-7439891480413310489970227707 / 1000000000000000000000000000000) : ℝ) ((-7439891480413309854216924131 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((-7439891480413310489970227707 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormV4_7Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV4_7_rounded_endpoints.1
  have hhi : (manuscriptNormV4_7Interval.2 : ℝ) ≤ ((-7439891480413309854216924131 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV4_7_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV4_7_exact_interval.1, manuscriptNormV4_7_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
