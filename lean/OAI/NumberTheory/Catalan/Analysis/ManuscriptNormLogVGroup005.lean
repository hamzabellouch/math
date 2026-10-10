import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormV1_2Arg : ℂ :=
  1 - (barrierV2Tail.getD 1 (0, 0)).1 * (barrierV2Tail.getD 2 (0, 0)).1

def manuscriptNormV1_2Term : ℝ :=
  (-((barrierV2Tail.getD 1 (0, 0)).2 * (barrierV2Tail.getD 2 (0, 0)).2) *
    Complex.log manuscriptNormV1_2Arg).re

def manuscriptNormV1_2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2832812887869 / 2500000000000000) (0 / 1) (1) (0) (1329409 / 781250) (0 / 1)

private theorem manuscriptNormV1_2_arg_eq : manuscriptNormV1_2Arg = barrierComplex (1153 / 625) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV1_2Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV1_2_weight_eq :
    -((barrierV2Tail.getD 1 (0, 0)).2 * (barrierV2Tail.getD 2 (0, 0)).2) =
      barrierComplex (-2832812887869 / 2500000000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV1_2_exact_interval :
    manuscriptNormV1_2Term ∈ Set.Icc (manuscriptNormV1_2Interval.1 : ℝ) (manuscriptNormV1_2Interval.2 : ℝ) := by
  unfold manuscriptNormV1_2Term
  rw [manuscriptNormV1_2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2832812887869 / 2500000000000000) (0 / 1)
    manuscriptNormV1_2Arg (1) (0) (1329409 / 781250) (1153 / 625) (0 / 1)
  have hratio : ((0 / 1) / (1153 / 625) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV1_2Interval
  apply h
  all_goals
    try rw [manuscriptNormV1_2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV1_2_rounded_endpoints :
    (-346946418840094216990697913 / 500000000000000000000000000000) ≤ manuscriptNormV1_2Interval.1 ∧ manuscriptNormV1_2Interval.2 ≤ (-693892837680188433904874467 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV1_2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV1_2_enclosure :
    manuscriptNormV1_2Term ∈ Set.Icc ((-346946418840094216990697913 / 500000000000000000000000000000) : ℝ) ((-693892837680188433904874467 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((-346946418840094216990697913 / 500000000000000000000000000000) : ℝ) ≤ (manuscriptNormV1_2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV1_2_rounded_endpoints.1
  have hhi : (manuscriptNormV1_2Interval.2 : ℝ) ≤ ((-693892837680188433904874467 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV1_2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV1_2_exact_interval.1, manuscriptNormV1_2_exact_interval.2.trans hhi⟩

def manuscriptNormV1_3Arg : ℂ :=
  1 - (barrierV2Tail.getD 1 (0, 0)).1 * (barrierV2Tail.getD 3 (0, 0)).1

def manuscriptNormV1_3Term : ℝ :=
  (-((barrierV2Tail.getD 1 (0, 0)).2 * (barrierV2Tail.getD 3 (0, 0)).2) *
    Complex.log manuscriptNormV1_3Arg).re

def manuscriptNormV1_3Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (5489604834427 / 2500000000000000) (0 / 1) (1) (0) (57121 / 31250) (0 / 1)

private theorem manuscriptNormV1_3_arg_eq : manuscriptNormV1_3Arg = barrierComplex (239 / 125) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV1_3Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV1_3_weight_eq :
    -((barrierV2Tail.getD 1 (0, 0)).2 * (barrierV2Tail.getD 3 (0, 0)).2) =
      barrierComplex (5489604834427 / 2500000000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV1_3_exact_interval :
    manuscriptNormV1_3Term ∈ Set.Icc (manuscriptNormV1_3Interval.1 : ℝ) (manuscriptNormV1_3Interval.2 : ℝ) := by
  unfold manuscriptNormV1_3Term
  rw [manuscriptNormV1_3_weight_eq]
  have h := manuscript_weighted_complex_log_interval (5489604834427 / 2500000000000000) (0 / 1)
    manuscriptNormV1_3Arg (1) (0) (57121 / 31250) (239 / 125) (0 / 1)
  have hratio : ((0 / 1) / (239 / 125) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV1_3Interval
  apply h
  all_goals
    try rw [manuscriptNormV1_3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV1_3_rounded_endpoints :
    (284646908465717807696825671 / 200000000000000000000000000000) ≤ manuscriptNormV1_3Interval.1 ∧ manuscriptNormV1_3Interval.2 ≤ (1423234542328589038633585387 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV1_3Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV1_3_enclosure :
    manuscriptNormV1_3Term ∈ Set.Icc ((284646908465717807696825671 / 200000000000000000000000000000) : ℝ) ((1423234542328589038633585387 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((284646908465717807696825671 / 200000000000000000000000000000) : ℝ) ≤ (manuscriptNormV1_3Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV1_3_rounded_endpoints.1
  have hhi : (manuscriptNormV1_3Interval.2 : ℝ) ≤ ((1423234542328589038633585387 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV1_3_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV1_3_exact_interval.1, manuscriptNormV1_3_exact_interval.2.trans hhi⟩

def manuscriptNormV1_4Arg : ℂ :=
  1 - (barrierV2Tail.getD 1 (0, 0)).1 * (barrierV2Tail.getD 4 (0, 0)).1

def manuscriptNormV1_4Term : ℝ :=
  (-((barrierV2Tail.getD 1 (0, 0)).2 * (barrierV2Tail.getD 4 (0, 0)).2) *
    Complex.log manuscriptNormV1_4Arg).re

def manuscriptNormV1_4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-25860054013467 / 5000000000000000) (0 / 1) (1) (0) (36929929 / 19531250) (0 / 1)

private theorem manuscriptNormV1_4_arg_eq : manuscriptNormV1_4Arg = barrierComplex (6077 / 3125) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV1_4Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV1_4_weight_eq :
    -((barrierV2Tail.getD 1 (0, 0)).2 * (barrierV2Tail.getD 4 (0, 0)).2) =
      barrierComplex (-25860054013467 / 5000000000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV1_4_exact_interval :
    manuscriptNormV1_4Term ∈ Set.Icc (manuscriptNormV1_4Interval.1 : ℝ) (manuscriptNormV1_4Interval.2 : ℝ) := by
  unfold manuscriptNormV1_4Term
  rw [manuscriptNormV1_4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-25860054013467 / 5000000000000000) (0 / 1)
    manuscriptNormV1_4Arg (1) (0) (36929929 / 19531250) (6077 / 3125) (0 / 1)
  have hratio : ((0 / 1) / (6077 / 3125) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV1_4Interval
  apply h
  all_goals
    try rw [manuscriptNormV1_4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV1_4_rounded_endpoints :
    (-1719892378039867589903798827 / 500000000000000000000000000000) ≤ manuscriptNormV1_4Interval.1 ∧ manuscriptNormV1_4Interval.2 ≤ (-1719892378039867589719800831 / 500000000000000000000000000000) := by
  simp only [manuscriptNormV1_4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV1_4_enclosure :
    manuscriptNormV1_4Term ∈ Set.Icc ((-1719892378039867589903798827 / 500000000000000000000000000000) : ℝ) ((-1719892378039867589719800831 / 500000000000000000000000000000) : ℝ) := by
  have hlo : ((-1719892378039867589903798827 / 500000000000000000000000000000) : ℝ) ≤ (manuscriptNormV1_4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV1_4_rounded_endpoints.1
  have hhi : (manuscriptNormV1_4Interval.2 : ℝ) ≤ ((-1719892378039867589719800831 / 500000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV1_4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV1_4_exact_interval.1, manuscriptNormV1_4_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
