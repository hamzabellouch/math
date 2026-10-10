import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormV3_0Arg : ℂ :=
  1 - (barrierV2Tail.getD 3 (0, 0)).1 * (barrierV2Tail.getD 0 (0, 0)).1

def manuscriptNormV3_0Term : ℝ :=
  (-((barrierV2Tail.getD 3 (0, 0)).2 * (barrierV2Tail.getD 0 (0, 0)).2) *
    Complex.log manuscriptNormV3_0Arg).re

def manuscriptNormV3_0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (37486072475887 / 5000000000000000) (0 / 1) (1) (0) (968 / 625) (0 / 1)

private theorem manuscriptNormV3_0_arg_eq : manuscriptNormV3_0Arg = barrierComplex (44 / 25) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV3_0Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV3_0_weight_eq :
    -((barrierV2Tail.getD 3 (0, 0)).2 * (barrierV2Tail.getD 0 (0, 0)).2) =
      barrierComplex (37486072475887 / 5000000000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV3_0_exact_interval :
    manuscriptNormV3_0Term ∈ Set.Icc (manuscriptNormV3_0Interval.1 : ℝ) (manuscriptNormV3_0Interval.2 : ℝ) := by
  unfold manuscriptNormV3_0Term
  rw [manuscriptNormV3_0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (37486072475887 / 5000000000000000) (0 / 1)
    manuscriptNormV3_0Arg (1) (0) (968 / 625) (44 / 25) (0 / 1)
  have hratio : ((0 / 1) / (44 / 25) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV3_0Interval
  apply h
  all_goals
    try rw [manuscriptNormV3_0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV3_0_rounded_endpoints :
    (2119139441767030891700728641 / 500000000000000000000000000000) ≤ manuscriptNormV3_0Interval.1 ∧ manuscriptNormV3_0Interval.2 ≤ (4238278883534061783907706481 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV3_0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV3_0_enclosure :
    manuscriptNormV3_0Term ∈ Set.Icc ((2119139441767030891700728641 / 500000000000000000000000000000) : ℝ) ((4238278883534061783907706481 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((2119139441767030891700728641 / 500000000000000000000000000000) : ℝ) ≤ (manuscriptNormV3_0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV3_0_rounded_endpoints.1
  have hhi : (manuscriptNormV3_0Interval.2 : ℝ) ≤ ((4238278883534061783907706481 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV3_0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV3_0_exact_interval.1, manuscriptNormV3_0_exact_interval.2.trans hhi⟩

def manuscriptNormV3_1Arg : ℂ :=
  1 - (barrierV2Tail.getD 3 (0, 0)).1 * (barrierV2Tail.getD 1 (0, 0)).1

def manuscriptNormV3_1Term : ℝ :=
  (-((barrierV2Tail.getD 3 (0, 0)).2 * (barrierV2Tail.getD 1 (0, 0)).2) *
    Complex.log manuscriptNormV3_1Arg).re

def manuscriptNormV3_1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (5489604834427 / 2500000000000000) (0 / 1) (1) (0) (57121 / 31250) (0 / 1)

private theorem manuscriptNormV3_1_arg_eq : manuscriptNormV3_1Arg = barrierComplex (239 / 125) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV3_1Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV3_1_weight_eq :
    -((barrierV2Tail.getD 3 (0, 0)).2 * (barrierV2Tail.getD 1 (0, 0)).2) =
      barrierComplex (5489604834427 / 2500000000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV3_1_exact_interval :
    manuscriptNormV3_1Term ∈ Set.Icc (manuscriptNormV3_1Interval.1 : ℝ) (manuscriptNormV3_1Interval.2 : ℝ) := by
  unfold manuscriptNormV3_1Term
  rw [manuscriptNormV3_1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (5489604834427 / 2500000000000000) (0 / 1)
    manuscriptNormV3_1Arg (1) (0) (57121 / 31250) (239 / 125) (0 / 1)
  have hratio : ((0 / 1) / (239 / 125) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV3_1Interval
  apply h
  all_goals
    try rw [manuscriptNormV3_1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV3_1_rounded_endpoints :
    (284646908465717807696825671 / 200000000000000000000000000000) ≤ manuscriptNormV3_1Interval.1 ∧ manuscriptNormV3_1Interval.2 ≤ (1423234542328589038633585387 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV3_1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV3_1_enclosure :
    manuscriptNormV3_1Term ∈ Set.Icc ((284646908465717807696825671 / 200000000000000000000000000000) : ℝ) ((1423234542328589038633585387 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((284646908465717807696825671 / 200000000000000000000000000000) : ℝ) ≤ (manuscriptNormV3_1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV3_1_rounded_endpoints.1
  have hhi : (manuscriptNormV3_1Interval.2 : ℝ) ≤ ((1423234542328589038633585387 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV3_1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV3_1_exact_interval.1, manuscriptNormV3_1_exact_interval.2.trans hhi⟩

def manuscriptNormV3_2Arg : ℂ :=
  1 - (barrierV2Tail.getD 3 (0, 0)).1 * (barrierV2Tail.getD 2 (0, 0)).1

def manuscriptNormV3_2Term : ℝ :=
  (-((barrierV2Tail.getD 3 (0, 0)).2 * (barrierV2Tail.getD 2 (0, 0)).2) *
    Complex.log manuscriptNormV3_2Arg).re

def manuscriptNormV3_2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (3138879179583 / 2500000000000000) (0 / 1) (-6) (0) (26896 / 15625) (0 / 1)

private theorem manuscriptNormV3_2_arg_eq : manuscriptNormV3_2Arg = barrierComplex (41 / 250) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV3_2Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV3_2_weight_eq :
    -((barrierV2Tail.getD 3 (0, 0)).2 * (barrierV2Tail.getD 2 (0, 0)).2) =
      barrierComplex (3138879179583 / 2500000000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV3_2_exact_interval :
    manuscriptNormV3_2Term ∈ Set.Icc (manuscriptNormV3_2Interval.1 : ℝ) (manuscriptNormV3_2Interval.2 : ℝ) := by
  unfold manuscriptNormV3_2Term
  rw [manuscriptNormV3_2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (3138879179583 / 2500000000000000) (0 / 1)
    manuscriptNormV3_2Arg (-6) (0) (26896 / 15625) (41 / 250) (0 / 1)
  have hratio : ((0 / 1) / (41 / 250) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV3_2Interval
  apply h
  all_goals
    try rw [manuscriptNormV3_2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV3_2_rounded_endpoints :
    (-2269897869559953121787323801 / 1000000000000000000000000000000) ≤ manuscriptNormV3_2Interval.1 ∧ manuscriptNormV3_2Interval.2 ≤ (-2269897869559953121278620449 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV3_2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV3_2_enclosure :
    manuscriptNormV3_2Term ∈ Set.Icc ((-2269897869559953121787323801 / 1000000000000000000000000000000) : ℝ) ((-2269897869559953121278620449 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((-2269897869559953121787323801 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormV3_2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV3_2_rounded_endpoints.1
  have hhi : (manuscriptNormV3_2Interval.2 : ℝ) ≤ ((-2269897869559953121278620449 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV3_2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV3_2_exact_interval.1, manuscriptNormV3_2_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
