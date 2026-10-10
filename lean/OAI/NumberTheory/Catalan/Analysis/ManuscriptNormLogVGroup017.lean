import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormV3_12Arg : ℂ :=
  1 - (barrierV2Tail.getD 3 (0, 0)).1 * (barrierV2Tail.getD 12 (0, 0)).1

def manuscriptNormV3_12Term : ℝ :=
  (-((barrierV2Tail.getD 3 (0, 0)).2 * (barrierV2Tail.getD 12 (0, 0)).2) *
    Complex.log manuscriptNormV3_12Arg).re

def manuscriptNormV3_12Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (5068806760521 / 10000000000000000) (-53558167558133 / 10000000000000000) (0) (1) (11711569 / 6250000) (-163 / 4837)

private theorem manuscriptNormV3_12_arg_eq : manuscriptNormV3_12Arg = barrierComplex (1 / 1) (2337 / 2500) := by
  apply Complex.ext <;> norm_num [manuscriptNormV3_12Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV3_12_weight_eq :
    -((barrierV2Tail.getD 3 (0, 0)).2 * (barrierV2Tail.getD 12 (0, 0)).2) =
      barrierComplex (5068806760521 / 10000000000000000) (-53558167558133 / 10000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV3_12_exact_interval :
    manuscriptNormV3_12Term ∈ Set.Icc (manuscriptNormV3_12Interval.1 : ℝ) (manuscriptNormV3_12Interval.2 : ℝ) := by
  unfold manuscriptNormV3_12Term
  rw [manuscriptNormV3_12_weight_eq]
  have h := manuscript_weighted_complex_log_interval (5068806760521 / 10000000000000000) (-53558167558133 / 10000000000000000)
    manuscriptNormV3_12Arg (0) (1) (11711569 / 6250000) (4837 / 2500) (-163 / 2500)
  have hratio : ((-163 / 2500) / (4837 / 2500) : ℚ) = (-163 / 4837) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV3_12Interval
  apply h
  all_goals
    try rw [manuscriptNormV3_12_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV3_12_rounded_endpoints :
    (4185192971723380656657287637 / 1000000000000000000000000000000) ≤ manuscriptNormV3_12Interval.1 ∧ manuscriptNormV3_12Interval.2 ≤ (418519297172338085081844233 / 100000000000000000000000000000) := by
  simp only [manuscriptNormV3_12Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV3_12_enclosure :
    manuscriptNormV3_12Term ∈ Set.Icc ((4185192971723380656657287637 / 1000000000000000000000000000000) : ℝ) ((418519297172338085081844233 / 100000000000000000000000000000) : ℝ) := by
  have hlo : ((4185192971723380656657287637 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormV3_12Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV3_12_rounded_endpoints.1
  have hhi : (manuscriptNormV3_12Interval.2 : ℝ) ≤ ((418519297172338085081844233 / 100000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV3_12_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV3_12_exact_interval.1, manuscriptNormV3_12_exact_interval.2.trans hhi⟩

def manuscriptNormV4_0Arg : ℂ :=
  1 - (barrierV2Tail.getD 4 (0, 0)).1 * (barrierV2Tail.getD 0 (0, 0)).1

def manuscriptNormV4_0Term : ℝ :=
  (-((barrierV2Tail.getD 4 (0, 0)).2 * (barrierV2Tail.getD 0 (0, 0)).2) *
    Complex.log manuscriptNormV4_0Arg).re

def manuscriptNormV4_0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-176586819674127 / 10000000000000000) (0 / 1) (1) (0) (1247689 / 781250) (0 / 1)

private theorem manuscriptNormV4_0_arg_eq : manuscriptNormV4_0Arg = barrierComplex (1117 / 625) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV4_0Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV4_0_weight_eq :
    -((barrierV2Tail.getD 4 (0, 0)).2 * (barrierV2Tail.getD 0 (0, 0)).2) =
      barrierComplex (-176586819674127 / 10000000000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV4_0_exact_interval :
    manuscriptNormV4_0Term ∈ Set.Icc (manuscriptNormV4_0Interval.1 : ℝ) (manuscriptNormV4_0Interval.2 : ℝ) := by
  unfold manuscriptNormV4_0Term
  rw [manuscriptNormV4_0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-176586819674127 / 10000000000000000) (0 / 1)
    manuscriptNormV4_0Arg (1) (0) (1247689 / 781250) (1117 / 625) (0 / 1)
  have hratio : ((0 / 1) / (1117 / 625) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV4_0Interval
  apply h
  all_goals
    try rw [manuscriptNormV4_0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV4_0_rounded_endpoints :
    (-10253516321398592810987099633 / 1000000000000000000000000000000) ≤ manuscriptNormV4_0Interval.1 ∧ manuscriptNormV4_0Interval.2 ≤ (-2050703264279718561958939307 / 200000000000000000000000000000) := by
  simp only [manuscriptNormV4_0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV4_0_enclosure :
    manuscriptNormV4_0Term ∈ Set.Icc ((-10253516321398592810987099633 / 1000000000000000000000000000000) : ℝ) ((-2050703264279718561958939307 / 200000000000000000000000000000) : ℝ) := by
  have hlo : ((-10253516321398592810987099633 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormV4_0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV4_0_rounded_endpoints.1
  have hhi : (manuscriptNormV4_0Interval.2 : ℝ) ≤ ((-2050703264279718561958939307 / 200000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV4_0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV4_0_exact_interval.1, manuscriptNormV4_0_exact_interval.2.trans hhi⟩

def manuscriptNormV4_1Arg : ℂ :=
  1 - (barrierV2Tail.getD 4 (0, 0)).1 * (barrierV2Tail.getD 1 (0, 0)).1

def manuscriptNormV4_1Term : ℝ :=
  (-((barrierV2Tail.getD 4 (0, 0)).2 * (barrierV2Tail.getD 1 (0, 0)).2) *
    Complex.log manuscriptNormV4_1Arg).re

def manuscriptNormV4_1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-25860054013467 / 5000000000000000) (0 / 1) (1) (0) (36929929 / 19531250) (0 / 1)

private theorem manuscriptNormV4_1_arg_eq : manuscriptNormV4_1Arg = barrierComplex (6077 / 3125) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV4_1Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV4_1_weight_eq :
    -((barrierV2Tail.getD 4 (0, 0)).2 * (barrierV2Tail.getD 1 (0, 0)).2) =
      barrierComplex (-25860054013467 / 5000000000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV4_1_exact_interval :
    manuscriptNormV4_1Term ∈ Set.Icc (manuscriptNormV4_1Interval.1 : ℝ) (manuscriptNormV4_1Interval.2 : ℝ) := by
  unfold manuscriptNormV4_1Term
  rw [manuscriptNormV4_1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-25860054013467 / 5000000000000000) (0 / 1)
    manuscriptNormV4_1Arg (1) (0) (36929929 / 19531250) (6077 / 3125) (0 / 1)
  have hratio : ((0 / 1) / (6077 / 3125) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV4_1Interval
  apply h
  all_goals
    try rw [manuscriptNormV4_1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV4_1_rounded_endpoints :
    (-1719892378039867589903798827 / 500000000000000000000000000000) ≤ manuscriptNormV4_1Interval.1 ∧ manuscriptNormV4_1Interval.2 ≤ (-1719892378039867589719800831 / 500000000000000000000000000000) := by
  simp only [manuscriptNormV4_1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV4_1_enclosure :
    manuscriptNormV4_1Term ∈ Set.Icc ((-1719892378039867589903798827 / 500000000000000000000000000000) : ℝ) ((-1719892378039867589719800831 / 500000000000000000000000000000) : ℝ) := by
  have hlo : ((-1719892378039867589903798827 / 500000000000000000000000000000) : ℝ) ≤ (manuscriptNormV4_1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV4_1_rounded_endpoints.1
  have hhi : (manuscriptNormV4_1Interval.2 : ℝ) ≤ ((-1719892378039867589719800831 / 500000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV4_1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV4_1_exact_interval.1, manuscriptNormV4_1_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
