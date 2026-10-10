import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormV3_3Arg : ℂ :=
  1 - (barrierV2Tail.getD 3 (0, 0)).1 * (barrierV2Tail.getD 3 (0, 0)).1

def manuscriptNormV3_3Term : ℝ :=
  (-((barrierV2Tail.getD 3 (0, 0)).2 * (barrierV2Tail.getD 3 (0, 0)).2) *
    Complex.log manuscriptNormV3_3Arg).re

def manuscriptNormV3_3Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-6082719544489 / 2500000000000000) (0 / 1) (-7) (0) (1521 / 1250) (0 / 1)

private theorem manuscriptNormV3_3_arg_eq : manuscriptNormV3_3Arg = barrierComplex (39 / 400) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV3_3Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV3_3_weight_eq :
    -((barrierV2Tail.getD 3 (0, 0)).2 * (barrierV2Tail.getD 3 (0, 0)).2) =
      barrierComplex (-6082719544489 / 2500000000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV3_3_exact_interval :
    manuscriptNormV3_3Term ∈ Set.Icc (manuscriptNormV3_3Interval.1 : ℝ) (manuscriptNormV3_3Interval.2 : ℝ) := by
  unfold manuscriptNormV3_3Term
  rw [manuscriptNormV3_3_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-6082719544489 / 2500000000000000) (0 / 1)
    manuscriptNormV3_3Arg (-7) (0) (1521 / 1250) (39 / 400) (0 / 1)
  have hratio : ((0 / 1) / (39 / 400) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV3_3Interval
  apply h
  all_goals
    try rw [manuscriptNormV3_3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV3_3_rounded_endpoints :
    (2831996094690712588721220711 / 500000000000000000000000000000) ≤ manuscriptNormV3_3Interval.1 ∧ manuscriptNormV3_3Interval.2 ≤ (5663992189381425178592500627 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV3_3Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV3_3_enclosure :
    manuscriptNormV3_3Term ∈ Set.Icc ((2831996094690712588721220711 / 500000000000000000000000000000) : ℝ) ((5663992189381425178592500627 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((2831996094690712588721220711 / 500000000000000000000000000000) : ℝ) ≤ (manuscriptNormV3_3Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV3_3_rounded_endpoints.1
  have hhi : (manuscriptNormV3_3Interval.2 : ℝ) ≤ ((5663992189381425178592500627 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV3_3_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV3_3_exact_interval.1, manuscriptNormV3_3_exact_interval.2.trans hhi⟩

def manuscriptNormV3_4Arg : ℂ :=
  1 - (barrierV2Tail.getD 3 (0, 0)).1 * (barrierV2Tail.getD 4 (0, 0)).1

def manuscriptNormV3_4Term : ℝ :=
  (-((barrierV2Tail.getD 3 (0, 0)).2 * (barrierV2Tail.getD 4 (0, 0)).2) *
    Complex.log manuscriptNormV3_4Arg).re

def manuscriptNormV3_4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (28654058117769 / 5000000000000000) (0 / 1) (-8) (0) (425104 / 390625) (0 / 1)

private theorem manuscriptNormV3_4_arg_eq : manuscriptNormV3_4Arg = barrierComplex (163 / 2500) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV3_4Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV3_4_weight_eq :
    -((barrierV2Tail.getD 3 (0, 0)).2 * (barrierV2Tail.getD 4 (0, 0)).2) =
      barrierComplex (28654058117769 / 5000000000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV3_4_exact_interval :
    manuscriptNormV3_4Term ∈ Set.Icc (manuscriptNormV3_4Interval.1 : ℝ) (manuscriptNormV3_4Interval.2 : ℝ) := by
  unfold manuscriptNormV3_4Term
  rw [manuscriptNormV3_4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (28654058117769 / 5000000000000000) (0 / 1)
    manuscriptNormV3_4Arg (-8) (0) (425104 / 390625) (163 / 2500) (0 / 1)
  have hratio : ((0 / 1) / (163 / 2500) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV3_4Interval
  apply h
  all_goals
    try rw [manuscriptNormV3_4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV3_4_rounded_endpoints :
    (-15646810963972083306715065919 / 1000000000000000000000000000000) ≤ manuscriptNormV3_4Interval.1 ∧ manuscriptNormV3_4Interval.2 ≤ (-97792568524825520647620519 / 6250000000000000000000000000) := by
  simp only [manuscriptNormV3_4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV3_4_enclosure :
    manuscriptNormV3_4Term ∈ Set.Icc ((-15646810963972083306715065919 / 1000000000000000000000000000000) : ℝ) ((-97792568524825520647620519 / 6250000000000000000000000000) : ℝ) := by
  have hlo : ((-15646810963972083306715065919 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormV3_4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV3_4_rounded_endpoints.1
  have hhi : (manuscriptNormV3_4Interval.2 : ℝ) ≤ ((-97792568524825520647620519 / 6250000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV3_4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV3_4_exact_interval.1, manuscriptNormV3_4_exact_interval.2.trans hhi⟩

def manuscriptNormV3_5Arg : ℂ :=
  1 - (barrierV2Tail.getD 3 (0, 0)).1 * (barrierV2Tail.getD 5 (0, 0)).1

def manuscriptNormV3_5Term : ℝ :=
  (-((barrierV2Tail.getD 3 (0, 0)).2 * (barrierV2Tail.getD 5 (0, 0)).2) *
    Complex.log manuscriptNormV3_5Arg).re

def manuscriptNormV3_5Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (33589651698169 / 5000000000000000) (1481637471433 / 156250000000000) (0) (-1) (1549081 / 1000000) (259 / 1741)

private theorem manuscriptNormV3_5_arg_eq : manuscriptNormV3_5Arg = barrierComplex (1 / 1) (-741 / 1000) := by
  apply Complex.ext <;> norm_num [manuscriptNormV3_5Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV3_5_weight_eq :
    -((barrierV2Tail.getD 3 (0, 0)).2 * (barrierV2Tail.getD 5 (0, 0)).2) =
      barrierComplex (33589651698169 / 5000000000000000) (1481637471433 / 156250000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV3_5_exact_interval :
    manuscriptNormV3_5Term ∈ Set.Icc (manuscriptNormV3_5Interval.1 : ℝ) (manuscriptNormV3_5Interval.2 : ℝ) := by
  unfold manuscriptNormV3_5Term
  rw [manuscriptNormV3_5_weight_eq]
  have h := manuscript_weighted_complex_log_interval (33589651698169 / 5000000000000000) (1481637471433 / 156250000000000)
    manuscriptNormV3_5Arg (0) (-1) (1549081 / 1000000) (1741 / 1000) (259 / 1000)
  have hratio : ((259 / 1000) / (1741 / 1000) : ℚ) = (259 / 1741) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV3_5Interval
  apply h
  all_goals
    try rw [manuscriptNormV3_5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV3_5_rounded_endpoints :
    (7517221743037368858959427589 / 1000000000000000000000000000000) ≤ manuscriptNormV3_5Interval.1 ∧ manuscriptNormV3_5Interval.2 ≤ (1879305435759342300679999343 / 250000000000000000000000000000) := by
  simp only [manuscriptNormV3_5Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV3_5_enclosure :
    manuscriptNormV3_5Term ∈ Set.Icc ((7517221743037368858959427589 / 1000000000000000000000000000000) : ℝ) ((1879305435759342300679999343 / 250000000000000000000000000000) : ℝ) := by
  have hlo : ((7517221743037368858959427589 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormV3_5Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV3_5_rounded_endpoints.1
  have hhi : (manuscriptNormV3_5Interval.2 : ℝ) ≤ ((1879305435759342300679999343 / 250000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV3_5_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV3_5_exact_interval.1, manuscriptNormV3_5_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
