import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormP7_0Arg : ℂ :=
  1 - (barrierP2Tail.getD 7 (0, 0)).1 * (barrierP2Tail.getD 0 (0, 0)).1

def manuscriptNormP7_0Term : ℝ :=
  (-((barrierP2Tail.getD 7 (0, 0)).2 * (barrierP2Tail.getD 0 (0, 0)).2) *
    Complex.log manuscriptNormP7_0Arg).re

def manuscriptNormP7_0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-3765635049867 / 2500000000000000) (10421985581721 / 2500000000000000) (0) (1) (36530981 / 25000000) (-699 / 8519)

private theorem manuscriptNormP7_0_arg_eq : manuscriptNormP7_0Arg = barrierComplex (4609 / 5000) (391 / 500) := by
  apply Complex.ext <;> norm_num [manuscriptNormP7_0Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP7_0_weight_eq :
    -((barrierP2Tail.getD 7 (0, 0)).2 * (barrierP2Tail.getD 0 (0, 0)).2) =
      barrierComplex (-3765635049867 / 2500000000000000) (10421985581721 / 2500000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP7_0_exact_interval :
    manuscriptNormP7_0Term ∈ Set.Icc (manuscriptNormP7_0Interval.1 : ℝ) (manuscriptNormP7_0Interval.2 : ℝ) := by
  unfold manuscriptNormP7_0Term
  rw [manuscriptNormP7_0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-3765635049867 / 2500000000000000) (10421985581721 / 2500000000000000)
    manuscriptNormP7_0Arg (0) (1) (36530981 / 25000000) (8519 / 5000) (-699 / 5000)
  have hratio : ((-699 / 5000) / (8519 / 5000) : ℚ) = (-699 / 8519) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP7_0Interval
  apply h
  all_goals
    try rw [manuscriptNormP7_0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP7_0_rounded_endpoints :
    (-160926007121511347938212133 / 50000000000000000000000000000) ≤ manuscriptNormP7_0Interval.1 ∧ manuscriptNormP7_0Interval.2 ≤ (-1609260071215113403818180873 / 500000000000000000000000000000) := by
  simp only [manuscriptNormP7_0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP7_0_enclosure :
    manuscriptNormP7_0Term ∈ Set.Icc ((-160926007121511347938212133 / 50000000000000000000000000000) : ℝ) ((-1609260071215113403818180873 / 500000000000000000000000000000) : ℝ) := by
  have hlo : ((-160926007121511347938212133 / 50000000000000000000000000000) : ℝ) ≤ (manuscriptNormP7_0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP7_0_rounded_endpoints.1
  have hhi : (manuscriptNormP7_0Interval.2 : ℝ) ≤ ((-1609260071215113403818180873 / 500000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP7_0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP7_0_exact_interval.1, manuscriptNormP7_0_exact_interval.2.trans hhi⟩

def manuscriptNormP7_1Arg : ℂ :=
  1 - (barrierP2Tail.getD 7 (0, 0)).1 * (barrierP2Tail.getD 1 (0, 0)).1

def manuscriptNormP7_1Term : ℝ :=
  (-((barrierP2Tail.getD 7 (0, 0)).2 * (barrierP2Tail.getD 1 (0, 0)).2) *
    Complex.log manuscriptNormP7_1Arg).re

def manuscriptNormP7_1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-3454166215131 / 10000000000000000) (9559946732553 / 10000000000000000) (0) (1) (247249661 / 156250000) (-609 / 22229)

private theorem manuscriptNormP7_1_arg_eq : manuscriptNormP7_1Arg = barrierComplex (11419 / 12500) (1081 / 1250) := by
  apply Complex.ext <;> norm_num [manuscriptNormP7_1Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP7_1_weight_eq :
    -((barrierP2Tail.getD 7 (0, 0)).2 * (barrierP2Tail.getD 1 (0, 0)).2) =
      barrierComplex (-3454166215131 / 10000000000000000) (9559946732553 / 10000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP7_1_exact_interval :
    manuscriptNormP7_1Term ∈ Set.Icc (manuscriptNormP7_1Interval.1 : ℝ) (manuscriptNormP7_1Interval.2 : ℝ) := by
  unfold manuscriptNormP7_1Term
  rw [manuscriptNormP7_1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-3454166215131 / 10000000000000000) (9559946732553 / 10000000000000000)
    manuscriptNormP7_1Arg (0) (1) (247249661 / 156250000) (22229 / 12500) (-609 / 12500)
  have hratio : ((-609 / 12500) / (22229 / 12500) : ℚ) = (-609 / 22229) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP7_1Interval
  apply h
  all_goals
    try rw [manuscriptNormP7_1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP7_1_rounded_endpoints :
    (-200978735801924450580405149 / 250000000000000000000000000000) ≤ manuscriptNormP7_1Interval.1 ∧ manuscriptNormP7_1Interval.2 ≤ (-803914943207697767664729149 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormP7_1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP7_1_enclosure :
    manuscriptNormP7_1Term ∈ Set.Icc ((-200978735801924450580405149 / 250000000000000000000000000000) : ℝ) ((-803914943207697767664729149 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((-200978735801924450580405149 / 250000000000000000000000000000) : ℝ) ≤ (manuscriptNormP7_1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP7_1_rounded_endpoints.1
  have hhi : (manuscriptNormP7_1Interval.2 : ℝ) ≤ ((-803914943207697767664729149 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP7_1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP7_1_exact_interval.1, manuscriptNormP7_1_exact_interval.2.trans hhi⟩

def manuscriptNormP7_2Arg : ℂ :=
  1 - (barrierP2Tail.getD 7 (0, 0)).1 * (barrierP2Tail.getD 2 (0, 0)).1

def manuscriptNormP7_2Term : ℝ :=
  (-((barrierP2Tail.getD 7 (0, 0)).2 * (barrierP2Tail.getD 2 (0, 0)).2) *
    Complex.log manuscriptNormP7_2Arg).re

def manuscriptNormP7_2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (284284403283 / 160000000000000) (69467599782309 / 4000000000000000) (-3) (0) (818021 / 781250) (-161 / 890)

private theorem manuscriptNormP7_2_arg_eq : manuscriptNormP7_2Arg = barrierComplex (89 / 250) (-161 / 2500) := by
  apply Complex.ext <;> norm_num [manuscriptNormP7_2Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP7_2_weight_eq :
    -((barrierP2Tail.getD 7 (0, 0)).2 * (barrierP2Tail.getD 2 (0, 0)).2) =
      barrierComplex (284284403283 / 160000000000000) (69467599782309 / 4000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP7_2_exact_interval :
    manuscriptNormP7_2Term ∈ Set.Icc (manuscriptNormP7_2Interval.1 : ℝ) (manuscriptNormP7_2Interval.2 : ℝ) := by
  unfold manuscriptNormP7_2Term
  rw [manuscriptNormP7_2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (284284403283 / 160000000000000) (69467599782309 / 4000000000000000)
    manuscriptNormP7_2Arg (-3) (0) (818021 / 781250) (89 / 250) (-161 / 2500)
  have hratio : ((-161 / 2500) / (89 / 250) : ℚ) = (-161 / 890) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP7_2Interval
  apply h
  all_goals
    try rw [manuscriptNormP7_2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP7_2_rounded_endpoints :
    (1301547649377044894437730227 / 1000000000000000000000000000000) ≤ manuscriptNormP7_2Interval.1 ∧ manuscriptNormP7_2Interval.2 ≤ (1301547649377044894797660753 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormP7_2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP7_2_enclosure :
    manuscriptNormP7_2Term ∈ Set.Icc ((1301547649377044894437730227 / 1000000000000000000000000000000) : ℝ) ((1301547649377044894797660753 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((1301547649377044894437730227 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormP7_2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP7_2_rounded_endpoints.1
  have hhi : (manuscriptNormP7_2Interval.2 : ℝ) ≤ ((1301547649377044894797660753 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP7_2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP7_2_exact_interval.1, manuscriptNormP7_2_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
