import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormV12_6Arg : ℂ :=
  1 - (barrierV2Tail.getD 12 (0, 0)).1 * (barrierV2Tail.getD 6 (0, 0)).1

def manuscriptNormV12_6Term : ℝ :=
  (-((barrierV2Tail.getD 12 (0, 0)).2 * (barrierV2Tail.getD 6 (0, 0)).2) *
    Complex.log manuscriptNormV12_6Arg).re

def manuscriptNormV12_6Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (389474106710791 / 20000000000000000) (335265249034277 / 20000000000000000) (1) (0) (122036209 / 78125000) (0 / 1)

private theorem manuscriptNormV12_6_arg_eq : manuscriptNormV12_6Arg = barrierComplex (11047 / 6250) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV12_6Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV12_6_weight_eq :
    -((barrierV2Tail.getD 12 (0, 0)).2 * (barrierV2Tail.getD 6 (0, 0)).2) =
      barrierComplex (389474106710791 / 20000000000000000) (335265249034277 / 20000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV12_6_exact_interval :
    manuscriptNormV12_6Term ∈ Set.Icc (manuscriptNormV12_6Interval.1 : ℝ) (manuscriptNormV12_6Interval.2 : ℝ) := by
  unfold manuscriptNormV12_6Term
  rw [manuscriptNormV12_6_weight_eq]
  have h := manuscript_weighted_complex_log_interval (389474106710791 / 20000000000000000) (335265249034277 / 20000000000000000)
    manuscriptNormV12_6Arg (1) (0) (122036209 / 78125000) (11047 / 6250) (0 / 1)
  have hratio : ((0 / 1) / (11047 / 6250) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV12_6Interval
  apply h
  all_goals
    try rw [manuscriptNormV12_6_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV12_6_rounded_endpoints :
    (2218356623650128240239486083 / 200000000000000000000000000000) ≤ manuscriptNormV12_6Interval.1 ∧ manuscriptNormV12_6Interval.2 ≤ (5545891559125320601256195969 / 500000000000000000000000000000) := by
  simp only [manuscriptNormV12_6Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV12_6_enclosure :
    manuscriptNormV12_6Term ∈ Set.Icc ((2218356623650128240239486083 / 200000000000000000000000000000) : ℝ) ((5545891559125320601256195969 / 500000000000000000000000000000) : ℝ) := by
  have hlo : ((2218356623650128240239486083 / 200000000000000000000000000000) : ℝ) ≤ (manuscriptNormV12_6Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV12_6_rounded_endpoints.1
  have hhi : (manuscriptNormV12_6Interval.2 : ℝ) ≤ ((5545891559125320601256195969 / 500000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV12_6_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV12_6_exact_interval.1, manuscriptNormV12_6_exact_interval.2.trans hhi⟩

def manuscriptNormV12_7Arg : ℂ :=
  1 - (barrierV2Tail.getD 12 (0, 0)).1 * (barrierV2Tail.getD 7 (0, 0)).1

def manuscriptNormV12_7Term : ℝ :=
  (-((barrierV2Tail.getD 12 (0, 0)).2 * (barrierV2Tail.getD 7 (0, 0)).2) *
    Complex.log manuscriptNormV12_7Arg).re

def manuscriptNormV12_7Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-295581257499211 / 20000000000000000) (-371321316540867 / 20000000000000000) (-7) (0) (654368 / 390625) (0 / 1)

private theorem manuscriptNormV12_7_arg_eq : manuscriptNormV12_7Arg = barrierComplex (143 / 1250) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV12_7Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV12_7_weight_eq :
    -((barrierV2Tail.getD 12 (0, 0)).2 * (barrierV2Tail.getD 7 (0, 0)).2) =
      barrierComplex (-295581257499211 / 20000000000000000) (-371321316540867 / 20000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV12_7_exact_interval :
    manuscriptNormV12_7Term ∈ Set.Icc (manuscriptNormV12_7Interval.1 : ℝ) (manuscriptNormV12_7Interval.2 : ℝ) := by
  unfold manuscriptNormV12_7Term
  rw [manuscriptNormV12_7_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-295581257499211 / 20000000000000000) (-371321316540867 / 20000000000000000)
    manuscriptNormV12_7Arg (-7) (0) (654368 / 390625) (143 / 1250) (0 / 1)
  have hratio : ((0 / 1) / (143 / 1250) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV12_7Interval
  apply h
  all_goals
    try rw [manuscriptNormV12_7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV12_7_rounded_endpoints :
    (8010452334665209331488056821 / 250000000000000000000000000000) ≤ manuscriptNormV12_7Interval.1 ∧ manuscriptNormV12_7Interval.2 ≤ (16020904669330418666468974703 / 500000000000000000000000000000) := by
  simp only [manuscriptNormV12_7Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV12_7_enclosure :
    manuscriptNormV12_7Term ∈ Set.Icc ((8010452334665209331488056821 / 250000000000000000000000000000) : ℝ) ((16020904669330418666468974703 / 500000000000000000000000000000) : ℝ) := by
  have hlo : ((8010452334665209331488056821 / 250000000000000000000000000000) : ℝ) ≤ (manuscriptNormV12_7Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV12_7_rounded_endpoints.1
  have hhi : (manuscriptNormV12_7Interval.2 : ℝ) ≤ ((16020904669330418666468974703 / 500000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV12_7_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV12_7_exact_interval.1, manuscriptNormV12_7_exact_interval.2.trans hhi⟩

def manuscriptNormV12_8Arg : ℂ :=
  1 - (barrierV2Tail.getD 12 (0, 0)).1 * (barrierV2Tail.getD 8 (0, 0)).1

def manuscriptNormV12_8Term : ℝ :=
  (-((barrierV2Tail.getD 12 (0, 0)).2 * (barrierV2Tail.getD 8 (0, 0)).2) *
    Complex.log manuscriptNormV12_8Arg).re

def manuscriptNormV12_8Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (359993860770103 / 20000000000000000) (-309276931099449 / 20000000000000000) (1) (0) (5555449 / 3125000) (0 / 1)

private theorem manuscriptNormV12_8_arg_eq : manuscriptNormV12_8Arg = barrierComplex (2357 / 1250) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV12_8Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV12_8_weight_eq :
    -((barrierV2Tail.getD 12 (0, 0)).2 * (barrierV2Tail.getD 8 (0, 0)).2) =
      barrierComplex (359993860770103 / 20000000000000000) (-309276931099449 / 20000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV12_8_exact_interval :
    manuscriptNormV12_8Term ∈ Set.Icc (manuscriptNormV12_8Interval.1 : ℝ) (manuscriptNormV12_8Interval.2 : ℝ) := by
  unfold manuscriptNormV12_8Term
  rw [manuscriptNormV12_8_weight_eq]
  have h := manuscript_weighted_complex_log_interval (359993860770103 / 20000000000000000) (-309276931099449 / 20000000000000000)
    manuscriptNormV12_8Arg (1) (0) (5555449 / 3125000) (2357 / 1250) (0 / 1)
  have hratio : ((0 / 1) / (2357 / 1250) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV12_8Interval
  apply h
  all_goals
    try rw [manuscriptNormV12_8_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV12_8_rounded_endpoints :
    (71351466364959732874330401 / 6250000000000000000000000000) ≤ manuscriptNormV12_8Interval.1 ∧ manuscriptNormV12_8Interval.2 ≤ (11416234618393557261110141487 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV12_8Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV12_8_enclosure :
    manuscriptNormV12_8Term ∈ Set.Icc ((71351466364959732874330401 / 6250000000000000000000000000) : ℝ) ((11416234618393557261110141487 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((71351466364959732874330401 / 6250000000000000000000000000) : ℝ) ≤ (manuscriptNormV12_8Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV12_8_rounded_endpoints.1
  have hhi : (manuscriptNormV12_8Interval.2 : ℝ) ≤ ((11416234618393557261110141487 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV12_8_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV12_8_exact_interval.1, manuscriptNormV12_8_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
