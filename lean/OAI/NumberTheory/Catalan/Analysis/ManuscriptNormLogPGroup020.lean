import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormP6_1Arg : ℂ :=
  1 - (barrierP2Tail.getD 6 (0, 0)).1 * (barrierP2Tail.getD 1 (0, 0)).1

def manuscriptNormP6_1Term : ℝ :=
  (-((barrierP2Tail.getD 6 (0, 0)).2 * (barrierP2Tail.getD 1 (0, 0)).2) *
    Complex.log manuscriptNormP6_1Arg).re

def manuscriptNormP6_1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-3454166215131 / 10000000000000000) (-9559946732553 / 10000000000000000) (0) (-1) (247249661 / 156250000) (609 / 22229)

private theorem manuscriptNormP6_1_arg_eq : manuscriptNormP6_1Arg = barrierComplex (11419 / 12500) (-1081 / 1250) := by
  apply Complex.ext <;> norm_num [manuscriptNormP6_1Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP6_1_weight_eq :
    -((barrierP2Tail.getD 6 (0, 0)).2 * (barrierP2Tail.getD 1 (0, 0)).2) =
      barrierComplex (-3454166215131 / 10000000000000000) (-9559946732553 / 10000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP6_1_exact_interval :
    manuscriptNormP6_1Term ∈ Set.Icc (manuscriptNormP6_1Interval.1 : ℝ) (manuscriptNormP6_1Interval.2 : ℝ) := by
  unfold manuscriptNormP6_1Term
  rw [manuscriptNormP6_1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-3454166215131 / 10000000000000000) (-9559946732553 / 10000000000000000)
    manuscriptNormP6_1Arg (0) (-1) (247249661 / 156250000) (22229 / 12500) (609 / 12500)
  have hratio : ((609 / 12500) / (22229 / 12500) : ℚ) = (609 / 22229) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP6_1Interval
  apply h
  all_goals
    try rw [manuscriptNormP6_1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP6_1_rounded_endpoints :
    (-200978735801924450580405149 / 250000000000000000000000000000) ≤ manuscriptNormP6_1Interval.1 ∧ manuscriptNormP6_1Interval.2 ≤ (-803914943207697767664729149 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormP6_1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP6_1_enclosure :
    manuscriptNormP6_1Term ∈ Set.Icc ((-200978735801924450580405149 / 250000000000000000000000000000) : ℝ) ((-803914943207697767664729149 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((-200978735801924450580405149 / 250000000000000000000000000000) : ℝ) ≤ (manuscriptNormP6_1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP6_1_rounded_endpoints.1
  have hhi : (manuscriptNormP6_1Interval.2 : ℝ) ≤ ((-803914943207697767664729149 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP6_1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP6_1_exact_interval.1, manuscriptNormP6_1_exact_interval.2.trans hhi⟩

def manuscriptNormP6_2Arg : ℂ :=
  1 - (barrierP2Tail.getD 6 (0, 0)).1 * (barrierP2Tail.getD 2 (0, 0)).1

def manuscriptNormP6_2Term : ℝ :=
  (-((barrierP2Tail.getD 6 (0, 0)).2 * (barrierP2Tail.getD 2 (0, 0)).2) *
    Complex.log manuscriptNormP6_2Arg).re

def manuscriptNormP6_2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-249342691992771 / 20000000000000000) (-244406797738203 / 20000000000000000) (1) (0) (16918021 / 12500000) (-161 / 4110)

private theorem manuscriptNormP6_2_arg_eq : manuscriptNormP6_2Arg = barrierComplex (411 / 250) (-161 / 2500) := by
  apply Complex.ext <;> norm_num [manuscriptNormP6_2Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP6_2_weight_eq :
    -((barrierP2Tail.getD 6 (0, 0)).2 * (barrierP2Tail.getD 2 (0, 0)).2) =
      barrierComplex (-249342691992771 / 20000000000000000) (-244406797738203 / 20000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP6_2_exact_interval :
    manuscriptNormP6_2Term ∈ Set.Icc (manuscriptNormP6_2Interval.1 : ℝ) (manuscriptNormP6_2Interval.2 : ℝ) := by
  unfold manuscriptNormP6_2Term
  rw [manuscriptNormP6_2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-249342691992771 / 20000000000000000) (-244406797738203 / 20000000000000000)
    manuscriptNormP6_2Arg (1) (0) (16918021 / 12500000) (411 / 250) (-161 / 2500)
  have hratio : ((-161 / 2500) / (411 / 250) : ℚ) = (-161 / 4110) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP6_2Interval
  apply h
  all_goals
    try rw [manuscriptNormP6_2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP6_2_rounded_endpoints :
    (-6685833039281012505245132349 / 1000000000000000000000000000000) ≤ manuscriptNormP6_2Interval.1 ∧ manuscriptNormP6_2Interval.2 ≤ (-6685833039281012504403289509 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormP6_2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP6_2_enclosure :
    manuscriptNormP6_2Term ∈ Set.Icc ((-6685833039281012505245132349 / 1000000000000000000000000000000) : ℝ) ((-6685833039281012504403289509 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((-6685833039281012505245132349 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormP6_2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP6_2_rounded_endpoints.1
  have hhi : (manuscriptNormP6_2Interval.2 : ℝ) ≤ ((-6685833039281012504403289509 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP6_2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP6_2_exact_interval.1, manuscriptNormP6_2_exact_interval.2.trans hhi⟩

def manuscriptNormP6_3Arg : ℂ :=
  1 - (barrierP2Tail.getD 6 (0, 0)).1 * (barrierP2Tail.getD 3 (0, 0)).1

def manuscriptNormP6_3Term : ℝ :=
  (-((barrierP2Tail.getD 6 (0, 0)).2 * (barrierP2Tail.getD 3 (0, 0)).2) *
    Complex.log manuscriptNormP6_3Arg).re

def manuscriptNormP6_3Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (284284403283 / 160000000000000) (-69467599782309 / 4000000000000000) (-3) (0) (818021 / 781250) (161 / 890)

private theorem manuscriptNormP6_3_arg_eq : manuscriptNormP6_3Arg = barrierComplex (89 / 250) (161 / 2500) := by
  apply Complex.ext <;> norm_num [manuscriptNormP6_3Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP6_3_weight_eq :
    -((barrierP2Tail.getD 6 (0, 0)).2 * (barrierP2Tail.getD 3 (0, 0)).2) =
      barrierComplex (284284403283 / 160000000000000) (-69467599782309 / 4000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP6_3_exact_interval :
    manuscriptNormP6_3Term ∈ Set.Icc (manuscriptNormP6_3Interval.1 : ℝ) (manuscriptNormP6_3Interval.2 : ℝ) := by
  unfold manuscriptNormP6_3Term
  rw [manuscriptNormP6_3_weight_eq]
  have h := manuscript_weighted_complex_log_interval (284284403283 / 160000000000000) (-69467599782309 / 4000000000000000)
    manuscriptNormP6_3Arg (-3) (0) (818021 / 781250) (89 / 250) (161 / 2500)
  have hratio : ((161 / 2500) / (89 / 250) : ℚ) = (161 / 890) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP6_3Interval
  apply h
  all_goals
    try rw [manuscriptNormP6_3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP6_3_rounded_endpoints :
    (1301547649377044894437730227 / 1000000000000000000000000000000) ≤ manuscriptNormP6_3Interval.1 ∧ manuscriptNormP6_3Interval.2 ≤ (1301547649377044894797660753 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormP6_3Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP6_3_enclosure :
    manuscriptNormP6_3Term ∈ Set.Icc ((1301547649377044894437730227 / 1000000000000000000000000000000) : ℝ) ((1301547649377044894797660753 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((1301547649377044894437730227 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormP6_3Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP6_3_rounded_endpoints.1
  have hhi : (manuscriptNormP6_3Interval.2 : ℝ) ≤ ((1301547649377044894797660753 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP6_3_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP6_3_exact_interval.1, manuscriptNormP6_3_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
