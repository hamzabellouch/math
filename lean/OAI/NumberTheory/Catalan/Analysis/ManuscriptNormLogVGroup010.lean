import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormV2_4Arg : ℂ :=
  1 - (barrierV2Tail.getD 2 (0, 0)).1 * (barrierV2Tail.getD 4 (0, 0)).1

def manuscriptNormV2_4Term : ℝ :=
  (-((barrierV2Tail.getD 2 (0, 0)).2 * (barrierV2Tail.getD 4 (0, 0)).2) *
    Complex.log manuscriptNormV2_4Arg).re

def manuscriptNormV2_4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-14786416795743 / 5000000000000000) (0 / 1) (-6) (0) (11235904 / 9765625) (0 / 1)

private theorem manuscriptNormV2_4_arg_eq : manuscriptNormV2_4Arg = barrierComplex (419 / 3125) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV2_4Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV2_4_weight_eq :
    -((barrierV2Tail.getD 2 (0, 0)).2 * (barrierV2Tail.getD 4 (0, 0)).2) =
      barrierComplex (-14786416795743 / 5000000000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV2_4_exact_interval :
    manuscriptNormV2_4Term ∈ Set.Icc (manuscriptNormV2_4Interval.1 : ℝ) (manuscriptNormV2_4Interval.2 : ℝ) := by
  unfold manuscriptNormV2_4Term
  rw [manuscriptNormV2_4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-14786416795743 / 5000000000000000) (0 / 1)
    manuscriptNormV2_4Arg (-6) (0) (11235904 / 9765625) (419 / 3125) (0 / 1)
  have hratio : ((0 / 1) / (419 / 3125) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV2_4Interval
  apply h
  all_goals
    try rw [manuscriptNormV2_4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV2_4_rounded_endpoints :
    (5942124583948146371070298357 / 1000000000000000000000000000000) ≤ manuscriptNormV2_4Interval.1 ∧ manuscriptNormV2_4Interval.2 ≤ (2971062291974073186134220553 / 500000000000000000000000000000) := by
  simp only [manuscriptNormV2_4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV2_4_enclosure :
    manuscriptNormV2_4Term ∈ Set.Icc ((5942124583948146371070298357 / 1000000000000000000000000000000) : ℝ) ((2971062291974073186134220553 / 500000000000000000000000000000) : ℝ) := by
  have hlo : ((5942124583948146371070298357 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormV2_4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV2_4_rounded_endpoints.1
  have hhi : (manuscriptNormV2_4Interval.2 : ℝ) ≤ ((2971062291974073186134220553 / 500000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV2_4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV2_4_exact_interval.1, manuscriptNormV2_4_exact_interval.2.trans hhi⟩

def manuscriptNormV2_5Arg : ℂ :=
  1 - (barrierV2Tail.getD 2 (0, 0)).1 * (barrierV2Tail.getD 5 (0, 0)).1

def manuscriptNormV2_5Term : ℝ :=
  (-((barrierV2Tail.getD 2 (0, 0)).2 * (barrierV2Tail.getD 5 (0, 0)).2) *
    Complex.log manuscriptNormV2_5Arg).re

def manuscriptNormV2_5Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-17333342034543 / 5000000000000000) (-764572651551 / 156250000000000) (0) (-1) (574666 / 390625) (98 / 527)

private theorem manuscriptNormV2_5_arg_eq : manuscriptNormV2_5Arg = barrierComplex (1 / 1) (-429 / 625) := by
  apply Complex.ext <;> norm_num [manuscriptNormV2_5Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV2_5_weight_eq :
    -((barrierV2Tail.getD 2 (0, 0)).2 * (barrierV2Tail.getD 5 (0, 0)).2) =
      barrierComplex (-17333342034543 / 5000000000000000) (-764572651551 / 156250000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV2_5_exact_interval :
    manuscriptNormV2_5Term ∈ Set.Icc (manuscriptNormV2_5Interval.1 : ℝ) (manuscriptNormV2_5Interval.2 : ℝ) := by
  unfold manuscriptNormV2_5Term
  rw [manuscriptNormV2_5_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-17333342034543 / 5000000000000000) (-764572651551 / 156250000000000)
    manuscriptNormV2_5Arg (0) (-1) (574666 / 390625) (1054 / 625) (196 / 625)
  have hratio : ((196 / 625) / (1054 / 625) : ℚ) = (98 / 527) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV2_5Interval
  apply h
  all_goals
    try rw [manuscriptNormV2_5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV2_5_rounded_endpoints :
    (-722526542219310315268128121 / 200000000000000000000000000000) ≤ manuscriptNormV2_5Interval.1 ∧ manuscriptNormV2_5Interval.2 ≤ (-903158177774137849737278943 / 250000000000000000000000000000) := by
  simp only [manuscriptNormV2_5Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV2_5_enclosure :
    manuscriptNormV2_5Term ∈ Set.Icc ((-722526542219310315268128121 / 200000000000000000000000000000) : ℝ) ((-903158177774137849737278943 / 250000000000000000000000000000) : ℝ) := by
  have hlo : ((-722526542219310315268128121 / 200000000000000000000000000000) : ℝ) ≤ (manuscriptNormV2_5Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV2_5_rounded_endpoints.1
  have hhi : (manuscriptNormV2_5Interval.2 : ℝ) ≤ ((-903158177774137849737278943 / 250000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV2_5_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV2_5_exact_interval.1, manuscriptNormV2_5_exact_interval.2.trans hhi⟩

def manuscriptNormV2_6Arg : ℂ :=
  1 - (barrierV2Tail.getD 2 (0, 0)).1 * (barrierV2Tail.getD 6 (0, 0)).1

def manuscriptNormV2_6Term : ℝ :=
  (-((barrierV2Tail.getD 2 (0, 0)).2 * (barrierV2Tail.getD 6 (0, 0)).2) *
    Complex.log manuscriptNormV2_6Arg).re

def manuscriptNormV2_6Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-17333342034543 / 5000000000000000) (764572651551 / 156250000000000) (0) (1) (574666 / 390625) (-98 / 527)

private theorem manuscriptNormV2_6_arg_eq : manuscriptNormV2_6Arg = barrierComplex (1 / 1) (429 / 625) := by
  apply Complex.ext <;> norm_num [manuscriptNormV2_6Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV2_6_weight_eq :
    -((barrierV2Tail.getD 2 (0, 0)).2 * (barrierV2Tail.getD 6 (0, 0)).2) =
      barrierComplex (-17333342034543 / 5000000000000000) (764572651551 / 156250000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV2_6_exact_interval :
    manuscriptNormV2_6Term ∈ Set.Icc (manuscriptNormV2_6Interval.1 : ℝ) (manuscriptNormV2_6Interval.2 : ℝ) := by
  unfold manuscriptNormV2_6Term
  rw [manuscriptNormV2_6_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-17333342034543 / 5000000000000000) (764572651551 / 156250000000000)
    manuscriptNormV2_6Arg (0) (1) (574666 / 390625) (1054 / 625) (-196 / 625)
  have hratio : ((-196 / 625) / (1054 / 625) : ℚ) = (-98 / 527) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV2_6Interval
  apply h
  all_goals
    try rw [manuscriptNormV2_6_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV2_6_rounded_endpoints :
    (-722526542219310315268128121 / 200000000000000000000000000000) ≤ manuscriptNormV2_6Interval.1 ∧ manuscriptNormV2_6Interval.2 ≤ (-903158177774137849737278943 / 250000000000000000000000000000) := by
  simp only [manuscriptNormV2_6Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV2_6_enclosure :
    manuscriptNormV2_6Term ∈ Set.Icc ((-722526542219310315268128121 / 200000000000000000000000000000) : ℝ) ((-903158177774137849737278943 / 250000000000000000000000000000) : ℝ) := by
  have hlo : ((-722526542219310315268128121 / 200000000000000000000000000000) : ℝ) ≤ (manuscriptNormV2_6Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV2_6_rounded_endpoints.1
  have hhi : (manuscriptNormV2_6Interval.2 : ℝ) ≤ ((-903158177774137849737278943 / 250000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV2_6_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV2_6_exact_interval.1, manuscriptNormV2_6_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
