import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormV11_7Arg : ℂ :=
  1 - (barrierV2Tail.getD 11 (0, 0)).1 * (barrierV2Tail.getD 7 (0, 0)).1

def manuscriptNormV11_7Term : ℝ :=
  (-((barrierV2Tail.getD 11 (0, 0)).2 * (barrierV2Tail.getD 7 (0, 0)).2) *
    Complex.log manuscriptNormV11_7Arg).re

def manuscriptNormV11_7Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (359993860770103 / 20000000000000000) (309276931099449 / 20000000000000000) (1) (0) (5555449 / 3125000) (0 / 1)

private theorem manuscriptNormV11_7_arg_eq : manuscriptNormV11_7Arg = barrierComplex (2357 / 1250) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV11_7Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV11_7_weight_eq :
    -((barrierV2Tail.getD 11 (0, 0)).2 * (barrierV2Tail.getD 7 (0, 0)).2) =
      barrierComplex (359993860770103 / 20000000000000000) (309276931099449 / 20000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV11_7_exact_interval :
    manuscriptNormV11_7Term ∈ Set.Icc (manuscriptNormV11_7Interval.1 : ℝ) (manuscriptNormV11_7Interval.2 : ℝ) := by
  unfold manuscriptNormV11_7Term
  rw [manuscriptNormV11_7_weight_eq]
  have h := manuscript_weighted_complex_log_interval (359993860770103 / 20000000000000000) (309276931099449 / 20000000000000000)
    manuscriptNormV11_7Arg (1) (0) (5555449 / 3125000) (2357 / 1250) (0 / 1)
  have hratio : ((0 / 1) / (2357 / 1250) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV11_7Interval
  apply h
  all_goals
    try rw [manuscriptNormV11_7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV11_7_rounded_endpoints :
    (71351466364959732874330401 / 6250000000000000000000000000) ≤ manuscriptNormV11_7Interval.1 ∧ manuscriptNormV11_7Interval.2 ≤ (11416234618393557261110141487 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV11_7Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV11_7_enclosure :
    manuscriptNormV11_7Term ∈ Set.Icc ((71351466364959732874330401 / 6250000000000000000000000000) : ℝ) ((11416234618393557261110141487 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((71351466364959732874330401 / 6250000000000000000000000000) : ℝ) ≤ (manuscriptNormV11_7Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV11_7_rounded_endpoints.1
  have hhi : (manuscriptNormV11_7Interval.2 : ℝ) ≤ ((11416234618393557261110141487 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV11_7_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV11_7_exact_interval.1, manuscriptNormV11_7_exact_interval.2.trans hhi⟩

def manuscriptNormV11_8Arg : ℂ :=
  1 - (barrierV2Tail.getD 11 (0, 0)).1 * (barrierV2Tail.getD 8 (0, 0)).1

def manuscriptNormV11_8Term : ℝ :=
  (-((barrierV2Tail.getD 11 (0, 0)).2 * (barrierV2Tail.getD 8 (0, 0)).2) *
    Complex.log manuscriptNormV11_8Arg).re

def manuscriptNormV11_8Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-295581257499211 / 20000000000000000) (371321316540867 / 20000000000000000) (-7) (0) (654368 / 390625) (0 / 1)

private theorem manuscriptNormV11_8_arg_eq : manuscriptNormV11_8Arg = barrierComplex (143 / 1250) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV11_8Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV11_8_weight_eq :
    -((barrierV2Tail.getD 11 (0, 0)).2 * (barrierV2Tail.getD 8 (0, 0)).2) =
      barrierComplex (-295581257499211 / 20000000000000000) (371321316540867 / 20000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV11_8_exact_interval :
    manuscriptNormV11_8Term ∈ Set.Icc (manuscriptNormV11_8Interval.1 : ℝ) (manuscriptNormV11_8Interval.2 : ℝ) := by
  unfold manuscriptNormV11_8Term
  rw [manuscriptNormV11_8_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-295581257499211 / 20000000000000000) (371321316540867 / 20000000000000000)
    manuscriptNormV11_8Arg (-7) (0) (654368 / 390625) (143 / 1250) (0 / 1)
  have hratio : ((0 / 1) / (143 / 1250) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV11_8Interval
  apply h
  all_goals
    try rw [manuscriptNormV11_8_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV11_8_rounded_endpoints :
    (8010452334665209331488056821 / 250000000000000000000000000000) ≤ manuscriptNormV11_8Interval.1 ∧ manuscriptNormV11_8Interval.2 ≤ (16020904669330418666468974703 / 500000000000000000000000000000) := by
  simp only [manuscriptNormV11_8Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV11_8_enclosure :
    manuscriptNormV11_8Term ∈ Set.Icc ((8010452334665209331488056821 / 250000000000000000000000000000) : ℝ) ((16020904669330418666468974703 / 500000000000000000000000000000) : ℝ) := by
  have hlo : ((8010452334665209331488056821 / 250000000000000000000000000000) : ℝ) ≤ (manuscriptNormV11_8Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV11_8_rounded_endpoints.1
  have hhi : (manuscriptNormV11_8Interval.2 : ℝ) ≤ ((16020904669330418666468974703 / 500000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV11_8_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV11_8_exact_interval.1, manuscriptNormV11_8_exact_interval.2.trans hhi⟩

def manuscriptNormV11_9Arg : ℂ :=
  1 - (barrierV2Tail.getD 11 (0, 0)).1 * (barrierV2Tail.getD 9 (0, 0)).1

def manuscriptNormV11_9Term : ℝ :=
  (-((barrierV2Tail.getD 11 (0, 0)).2 * (barrierV2Tail.getD 9 (0, 0)).2) *
    Complex.log manuscriptNormV11_9Arg).re

def manuscriptNormV11_9Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2391875533 / 390625000000) (8491908331363 / 2000000000000000) (1) (0) (2351571049 / 1250000000) (0 / 1)

private theorem manuscriptNormV11_9_arg_eq : manuscriptNormV11_9Arg = barrierComplex (48493 / 25000) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV11_9Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV11_9_weight_eq :
    -((barrierV2Tail.getD 11 (0, 0)).2 * (barrierV2Tail.getD 9 (0, 0)).2) =
      barrierComplex (-2391875533 / 390625000000) (8491908331363 / 2000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV11_9_exact_interval :
    manuscriptNormV11_9Term ∈ Set.Icc (manuscriptNormV11_9Interval.1 : ℝ) (manuscriptNormV11_9Interval.2 : ℝ) := by
  unfold manuscriptNormV11_9Term
  rw [manuscriptNormV11_9_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2391875533 / 390625000000) (8491908331363 / 2000000000000000)
    manuscriptNormV11_9Arg (1) (0) (2351571049 / 1250000000) (48493 / 25000) (0 / 1)
  have hratio : ((0 / 1) / (48493 / 25000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV11_9Interval
  apply h
  all_goals
    try rw [manuscriptNormV11_9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV11_9_rounded_endpoints :
    (-1014222019038597977530548497 / 250000000000000000000000000000) ≤ manuscriptNormV11_9Interval.1 ∧ manuscriptNormV11_9Interval.2 ≤ (-2028444038077195954845955103 / 500000000000000000000000000000) := by
  simp only [manuscriptNormV11_9Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV11_9_enclosure :
    manuscriptNormV11_9Term ∈ Set.Icc ((-1014222019038597977530548497 / 250000000000000000000000000000) : ℝ) ((-2028444038077195954845955103 / 500000000000000000000000000000) : ℝ) := by
  have hlo : ((-1014222019038597977530548497 / 250000000000000000000000000000) : ℝ) ≤ (manuscriptNormV11_9Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV11_9_rounded_endpoints.1
  have hhi : (manuscriptNormV11_9Interval.2 : ℝ) ≤ ((-2028444038077195954845955103 / 500000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV11_9_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV11_9_exact_interval.1, manuscriptNormV11_9_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
