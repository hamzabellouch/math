import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormV5_1Arg : ℂ :=
  1 - (barrierV2Tail.getD 5 (0, 0)).1 * (barrierV2Tail.getD 1 (0, 0)).1

def manuscriptNormV5_1Term : ℝ :=
  (-((barrierV2Tail.getD 5 (0, 0)).2 * (barrierV2Tail.getD 1 (0, 0)).2) *
    Complex.log manuscriptNormV5_1Arg).re

def manuscriptNormV5_1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-30314387010667 / 5000000000000000) (-1337165747419 / 156250000000000) (0) (1) (609649 / 390625) (-157 / 1093)

private theorem manuscriptNormV5_1_arg_eq : manuscriptNormV5_1Arg = barrierComplex (1 / 1) (468 / 625) := by
  apply Complex.ext <;> norm_num [manuscriptNormV5_1Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV5_1_weight_eq :
    -((barrierV2Tail.getD 5 (0, 0)).2 * (barrierV2Tail.getD 1 (0, 0)).2) =
      barrierComplex (-30314387010667 / 5000000000000000) (-1337165747419 / 156250000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV5_1_exact_interval :
    manuscriptNormV5_1Term ∈ Set.Icc (manuscriptNormV5_1Interval.1 : ℝ) (manuscriptNormV5_1Interval.2 : ℝ) := by
  unfold manuscriptNormV5_1Term
  rw [manuscriptNormV5_1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-30314387010667 / 5000000000000000) (-1337165747419 / 156250000000000)
    manuscriptNormV5_1Arg (0) (1) (609649 / 390625) (1093 / 625) (-157 / 625)
  have hratio : ((-157 / 625) / (1093 / 625) : ℚ) = (-157 / 1093) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV5_1Interval
  apply h
  all_goals
    try rw [manuscriptNormV5_1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV5_1_rounded_endpoints :
    (518877014766705861242949901 / 125000000000000000000000000000) ≤ manuscriptNormV5_1Interval.1 ∧ manuscriptNormV5_1Interval.2 ≤ (1037754029533411800046178233 / 250000000000000000000000000000) := by
  simp only [manuscriptNormV5_1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV5_1_enclosure :
    manuscriptNormV5_1Term ∈ Set.Icc ((518877014766705861242949901 / 125000000000000000000000000000) : ℝ) ((1037754029533411800046178233 / 250000000000000000000000000000) : ℝ) := by
  have hlo : ((518877014766705861242949901 / 125000000000000000000000000000) : ℝ) ≤ (manuscriptNormV5_1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV5_1_rounded_endpoints.1
  have hhi : (manuscriptNormV5_1Interval.2 : ℝ) ≤ ((1037754029533411800046178233 / 250000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV5_1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV5_1_exact_interval.1, manuscriptNormV5_1_exact_interval.2.trans hhi⟩

def manuscriptNormV5_2Arg : ℂ :=
  1 - (barrierV2Tail.getD 5 (0, 0)).1 * (barrierV2Tail.getD 2 (0, 0)).1

def manuscriptNormV5_2Term : ℝ :=
  (-((barrierV2Tail.getD 5 (0, 0)).2 * (barrierV2Tail.getD 2 (0, 0)).2) *
    Complex.log manuscriptNormV5_2Arg).re

def manuscriptNormV5_2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-17333342034543 / 5000000000000000) (-764572651551 / 156250000000000) (0) (-1) (574666 / 390625) (98 / 527)

private theorem manuscriptNormV5_2_arg_eq : manuscriptNormV5_2Arg = barrierComplex (1 / 1) (-429 / 625) := by
  apply Complex.ext <;> norm_num [manuscriptNormV5_2Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV5_2_weight_eq :
    -((barrierV2Tail.getD 5 (0, 0)).2 * (barrierV2Tail.getD 2 (0, 0)).2) =
      barrierComplex (-17333342034543 / 5000000000000000) (-764572651551 / 156250000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV5_2_exact_interval :
    manuscriptNormV5_2Term ∈ Set.Icc (manuscriptNormV5_2Interval.1 : ℝ) (manuscriptNormV5_2Interval.2 : ℝ) := by
  unfold manuscriptNormV5_2Term
  rw [manuscriptNormV5_2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-17333342034543 / 5000000000000000) (-764572651551 / 156250000000000)
    manuscriptNormV5_2Arg (0) (-1) (574666 / 390625) (1054 / 625) (196 / 625)
  have hratio : ((196 / 625) / (1054 / 625) : ℚ) = (98 / 527) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV5_2Interval
  apply h
  all_goals
    try rw [manuscriptNormV5_2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV5_2_rounded_endpoints :
    (-722526542219310315268128121 / 200000000000000000000000000000) ≤ manuscriptNormV5_2Interval.1 ∧ manuscriptNormV5_2Interval.2 ≤ (-903158177774137849737278943 / 250000000000000000000000000000) := by
  simp only [manuscriptNormV5_2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV5_2_enclosure :
    manuscriptNormV5_2Term ∈ Set.Icc ((-722526542219310315268128121 / 200000000000000000000000000000) : ℝ) ((-903158177774137849737278943 / 250000000000000000000000000000) : ℝ) := by
  have hlo : ((-722526542219310315268128121 / 200000000000000000000000000000) : ℝ) ≤ (manuscriptNormV5_2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV5_2_rounded_endpoints.1
  have hhi : (manuscriptNormV5_2Interval.2 : ℝ) ≤ ((-903158177774137849737278943 / 250000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV5_2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV5_2_exact_interval.1, manuscriptNormV5_2_exact_interval.2.trans hhi⟩

def manuscriptNormV5_3Arg : ℂ :=
  1 - (barrierV2Tail.getD 5 (0, 0)).1 * (barrierV2Tail.getD 3 (0, 0)).1

def manuscriptNormV5_3Term : ℝ :=
  (-((barrierV2Tail.getD 5 (0, 0)).2 * (barrierV2Tail.getD 3 (0, 0)).2) *
    Complex.log manuscriptNormV5_3Arg).re

def manuscriptNormV5_3Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (33589651698169 / 5000000000000000) (1481637471433 / 156250000000000) (0) (-1) (1549081 / 1000000) (259 / 1741)

private theorem manuscriptNormV5_3_arg_eq : manuscriptNormV5_3Arg = barrierComplex (1 / 1) (-741 / 1000) := by
  apply Complex.ext <;> norm_num [manuscriptNormV5_3Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV5_3_weight_eq :
    -((barrierV2Tail.getD 5 (0, 0)).2 * (barrierV2Tail.getD 3 (0, 0)).2) =
      barrierComplex (33589651698169 / 5000000000000000) (1481637471433 / 156250000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV5_3_exact_interval :
    manuscriptNormV5_3Term ∈ Set.Icc (manuscriptNormV5_3Interval.1 : ℝ) (manuscriptNormV5_3Interval.2 : ℝ) := by
  unfold manuscriptNormV5_3Term
  rw [manuscriptNormV5_3_weight_eq]
  have h := manuscript_weighted_complex_log_interval (33589651698169 / 5000000000000000) (1481637471433 / 156250000000000)
    manuscriptNormV5_3Arg (0) (-1) (1549081 / 1000000) (1741 / 1000) (259 / 1000)
  have hratio : ((259 / 1000) / (1741 / 1000) : ℚ) = (259 / 1741) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV5_3Interval
  apply h
  all_goals
    try rw [manuscriptNormV5_3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV5_3_rounded_endpoints :
    (7517221743037368858959427589 / 1000000000000000000000000000000) ≤ manuscriptNormV5_3Interval.1 ∧ manuscriptNormV5_3Interval.2 ≤ (1879305435759342300679999343 / 250000000000000000000000000000) := by
  simp only [manuscriptNormV5_3Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV5_3_enclosure :
    manuscriptNormV5_3Term ∈ Set.Icc ((7517221743037368858959427589 / 1000000000000000000000000000000) : ℝ) ((1879305435759342300679999343 / 250000000000000000000000000000) : ℝ) := by
  have hlo : ((7517221743037368858959427589 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormV5_3Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV5_3_rounded_endpoints.1
  have hhi : (manuscriptNormV5_3Interval.2 : ℝ) ≤ ((1879305435759342300679999343 / 250000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV5_3_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV5_3_exact_interval.1, manuscriptNormV5_3_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
