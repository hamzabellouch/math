import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormV4_2Arg : ℂ :=
  1 - (barrierV2Tail.getD 4 (0, 0)).1 * (barrierV2Tail.getD 2 (0, 0)).1

def manuscriptNormV4_2Term : ℝ :=
  (-((barrierV2Tail.getD 4 (0, 0)).2 * (barrierV2Tail.getD 2 (0, 0)).2) *
    Complex.log manuscriptNormV4_2Arg).re

def manuscriptNormV4_2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-14786416795743 / 5000000000000000) (0 / 1) (-6) (0) (11235904 / 9765625) (0 / 1)

private theorem manuscriptNormV4_2_arg_eq : manuscriptNormV4_2Arg = barrierComplex (419 / 3125) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV4_2Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV4_2_weight_eq :
    -((barrierV2Tail.getD 4 (0, 0)).2 * (barrierV2Tail.getD 2 (0, 0)).2) =
      barrierComplex (-14786416795743 / 5000000000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV4_2_exact_interval :
    manuscriptNormV4_2Term ∈ Set.Icc (manuscriptNormV4_2Interval.1 : ℝ) (manuscriptNormV4_2Interval.2 : ℝ) := by
  unfold manuscriptNormV4_2Term
  rw [manuscriptNormV4_2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-14786416795743 / 5000000000000000) (0 / 1)
    manuscriptNormV4_2Arg (-6) (0) (11235904 / 9765625) (419 / 3125) (0 / 1)
  have hratio : ((0 / 1) / (419 / 3125) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV4_2Interval
  apply h
  all_goals
    try rw [manuscriptNormV4_2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV4_2_rounded_endpoints :
    (5942124583948146371070298357 / 1000000000000000000000000000000) ≤ manuscriptNormV4_2Interval.1 ∧ manuscriptNormV4_2Interval.2 ≤ (2971062291974073186134220553 / 500000000000000000000000000000) := by
  simp only [manuscriptNormV4_2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV4_2_enclosure :
    manuscriptNormV4_2Term ∈ Set.Icc ((5942124583948146371070298357 / 1000000000000000000000000000000) : ℝ) ((2971062291974073186134220553 / 500000000000000000000000000000) : ℝ) := by
  have hlo : ((5942124583948146371070298357 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormV4_2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV4_2_rounded_endpoints.1
  have hhi : (manuscriptNormV4_2Interval.2 : ℝ) ≤ ((2971062291974073186134220553 / 500000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV4_2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV4_2_exact_interval.1, manuscriptNormV4_2_exact_interval.2.trans hhi⟩

def manuscriptNormV4_3Arg : ℂ :=
  1 - (barrierV2Tail.getD 4 (0, 0)).1 * (barrierV2Tail.getD 3 (0, 0)).1

def manuscriptNormV4_3Term : ℝ :=
  (-((barrierV2Tail.getD 4 (0, 0)).2 * (barrierV2Tail.getD 3 (0, 0)).2) *
    Complex.log manuscriptNormV4_3Arg).re

def manuscriptNormV4_3Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (28654058117769 / 5000000000000000) (0 / 1) (-8) (0) (425104 / 390625) (0 / 1)

private theorem manuscriptNormV4_3_arg_eq : manuscriptNormV4_3Arg = barrierComplex (163 / 2500) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV4_3Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV4_3_weight_eq :
    -((barrierV2Tail.getD 4 (0, 0)).2 * (barrierV2Tail.getD 3 (0, 0)).2) =
      barrierComplex (28654058117769 / 5000000000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV4_3_exact_interval :
    manuscriptNormV4_3Term ∈ Set.Icc (manuscriptNormV4_3Interval.1 : ℝ) (manuscriptNormV4_3Interval.2 : ℝ) := by
  unfold manuscriptNormV4_3Term
  rw [manuscriptNormV4_3_weight_eq]
  have h := manuscript_weighted_complex_log_interval (28654058117769 / 5000000000000000) (0 / 1)
    manuscriptNormV4_3Arg (-8) (0) (425104 / 390625) (163 / 2500) (0 / 1)
  have hratio : ((0 / 1) / (163 / 2500) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV4_3Interval
  apply h
  all_goals
    try rw [manuscriptNormV4_3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV4_3_rounded_endpoints :
    (-15646810963972083306715065919 / 1000000000000000000000000000000) ≤ manuscriptNormV4_3Interval.1 ∧ manuscriptNormV4_3Interval.2 ≤ (-97792568524825520647620519 / 6250000000000000000000000000) := by
  simp only [manuscriptNormV4_3Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV4_3_enclosure :
    manuscriptNormV4_3Term ∈ Set.Icc ((-15646810963972083306715065919 / 1000000000000000000000000000000) : ℝ) ((-97792568524825520647620519 / 6250000000000000000000000000) : ℝ) := by
  have hlo : ((-15646810963972083306715065919 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormV4_3Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV4_3_rounded_endpoints.1
  have hhi : (manuscriptNormV4_3Interval.2 : ℝ) ≤ ((-97792568524825520647620519 / 6250000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV4_3_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV4_3_exact_interval.1, manuscriptNormV4_3_exact_interval.2.trans hhi⟩

def manuscriptNormV4_4Arg : ℂ :=
  1 - (barrierV2Tail.getD 4 (0, 0)).1 * (barrierV2Tail.getD 4 (0, 0)).1

def manuscriptNormV4_4Term : ℝ :=
  (-((barrierV2Tail.getD 4 (0, 0)).2 * (barrierV2Tail.getD 4 (0, 0)).2) *
    Complex.log manuscriptNormV4_4Arg).re

def manuscriptNormV4_4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-134981572076649 / 10000000000000000) (0 / 1) (-10) (0) (251920384 / 244140625) (0 / 1)

private theorem manuscriptNormV4_4_arg_eq : manuscriptNormV4_4Arg = barrierComplex (496 / 15625) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV4_4Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV4_4_weight_eq :
    -((barrierV2Tail.getD 4 (0, 0)).2 * (barrierV2Tail.getD 4 (0, 0)).2) =
      barrierComplex (-134981572076649 / 10000000000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV4_4_exact_interval :
    manuscriptNormV4_4Term ∈ Set.Icc (manuscriptNormV4_4Interval.1 : ℝ) (manuscriptNormV4_4Interval.2 : ℝ) := by
  unfold manuscriptNormV4_4Term
  rw [manuscriptNormV4_4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-134981572076649 / 10000000000000000) (0 / 1)
    manuscriptNormV4_4Arg (-10) (0) (251920384 / 244140625) (496 / 15625) (0 / 1)
  have hratio : ((0 / 1) / (496 / 15625) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV4_4Interval
  apply h
  all_goals
    try rw [manuscriptNormV4_4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV4_4_rounded_endpoints :
    (23284669083913738374859080853 / 500000000000000000000000000000) ≤ manuscriptNormV4_4Interval.1 ∧ manuscriptNormV4_4Interval.2 ≤ (46569338167827476758832787763 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV4_4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV4_4_enclosure :
    manuscriptNormV4_4Term ∈ Set.Icc ((23284669083913738374859080853 / 500000000000000000000000000000) : ℝ) ((46569338167827476758832787763 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((23284669083913738374859080853 / 500000000000000000000000000000) : ℝ) ≤ (manuscriptNormV4_4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV4_4_rounded_endpoints.1
  have hhi : (manuscriptNormV4_4Interval.2 : ℝ) ≤ ((46569338167827476758832787763 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV4_4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV4_4_exact_interval.1, manuscriptNormV4_4_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
