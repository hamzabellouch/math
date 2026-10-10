import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormV0_3Arg : ℂ :=
  1 - (barrierV2Tail.getD 0 (0, 0)).1 * (barrierV2Tail.getD 3 (0, 0)).1

def manuscriptNormV0_3Term : ℝ :=
  (-((barrierV2Tail.getD 0 (0, 0)).2 * (barrierV2Tail.getD 3 (0, 0)).2) *
    Complex.log manuscriptNormV0_3Arg).re

def manuscriptNormV0_3Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (37486072475887 / 5000000000000000) (0 / 1) (1) (0) (968 / 625) (0 / 1)

private theorem manuscriptNormV0_3_arg_eq : manuscriptNormV0_3Arg = barrierComplex (44 / 25) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV0_3Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV0_3_weight_eq :
    -((barrierV2Tail.getD 0 (0, 0)).2 * (barrierV2Tail.getD 3 (0, 0)).2) =
      barrierComplex (37486072475887 / 5000000000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV0_3_exact_interval :
    manuscriptNormV0_3Term ∈ Set.Icc (manuscriptNormV0_3Interval.1 : ℝ) (manuscriptNormV0_3Interval.2 : ℝ) := by
  unfold manuscriptNormV0_3Term
  rw [manuscriptNormV0_3_weight_eq]
  have h := manuscript_weighted_complex_log_interval (37486072475887 / 5000000000000000) (0 / 1)
    manuscriptNormV0_3Arg (1) (0) (968 / 625) (44 / 25) (0 / 1)
  have hratio : ((0 / 1) / (44 / 25) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV0_3Interval
  apply h
  all_goals
    try rw [manuscriptNormV0_3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV0_3_rounded_endpoints :
    (2119139441767030891700728641 / 500000000000000000000000000000) ≤ manuscriptNormV0_3Interval.1 ∧ manuscriptNormV0_3Interval.2 ≤ (4238278883534061783907706481 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV0_3Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV0_3_enclosure :
    manuscriptNormV0_3Term ∈ Set.Icc ((2119139441767030891700728641 / 500000000000000000000000000000) : ℝ) ((4238278883534061783907706481 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((2119139441767030891700728641 / 500000000000000000000000000000) : ℝ) ≤ (manuscriptNormV0_3Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV0_3_rounded_endpoints.1
  have hhi : (manuscriptNormV0_3Interval.2 : ℝ) ≤ ((4238278883534061783907706481 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV0_3_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV0_3_exact_interval.1, manuscriptNormV0_3_exact_interval.2.trans hhi⟩

def manuscriptNormV0_4Arg : ℂ :=
  1 - (barrierV2Tail.getD 0 (0, 0)).1 * (barrierV2Tail.getD 4 (0, 0)).1

def manuscriptNormV0_4Term : ℝ :=
  (-((barrierV2Tail.getD 0 (0, 0)).2 * (barrierV2Tail.getD 4 (0, 0)).2) *
    Complex.log manuscriptNormV0_4Arg).re

def manuscriptNormV0_4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-176586819674127 / 10000000000000000) (0 / 1) (1) (0) (1247689 / 781250) (0 / 1)

private theorem manuscriptNormV0_4_arg_eq : manuscriptNormV0_4Arg = barrierComplex (1117 / 625) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV0_4Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV0_4_weight_eq :
    -((barrierV2Tail.getD 0 (0, 0)).2 * (barrierV2Tail.getD 4 (0, 0)).2) =
      barrierComplex (-176586819674127 / 10000000000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV0_4_exact_interval :
    manuscriptNormV0_4Term ∈ Set.Icc (manuscriptNormV0_4Interval.1 : ℝ) (manuscriptNormV0_4Interval.2 : ℝ) := by
  unfold manuscriptNormV0_4Term
  rw [manuscriptNormV0_4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-176586819674127 / 10000000000000000) (0 / 1)
    manuscriptNormV0_4Arg (1) (0) (1247689 / 781250) (1117 / 625) (0 / 1)
  have hratio : ((0 / 1) / (1117 / 625) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV0_4Interval
  apply h
  all_goals
    try rw [manuscriptNormV0_4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV0_4_rounded_endpoints :
    (-10253516321398592810987099633 / 1000000000000000000000000000000) ≤ manuscriptNormV0_4Interval.1 ∧ manuscriptNormV0_4Interval.2 ≤ (-2050703264279718561958939307 / 200000000000000000000000000000) := by
  simp only [manuscriptNormV0_4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV0_4_enclosure :
    manuscriptNormV0_4Term ∈ Set.Icc ((-10253516321398592810987099633 / 1000000000000000000000000000000) : ℝ) ((-2050703264279718561958939307 / 200000000000000000000000000000) : ℝ) := by
  have hlo : ((-10253516321398592810987099633 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormV0_4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV0_4_rounded_endpoints.1
  have hhi : (manuscriptNormV0_4Interval.2 : ℝ) ≤ ((-2050703264279718561958939307 / 200000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV0_4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV0_4_exact_interval.1, manuscriptNormV0_4_exact_interval.2.trans hhi⟩

def manuscriptNormV0_5Arg : ℂ :=
  1 - (barrierV2Tail.getD 0 (0, 0)).1 * (barrierV2Tail.getD 5 (0, 0)).1

def manuscriptNormV0_5Term : ℝ :=
  (-((barrierV2Tail.getD 0 (0, 0)).2 * (barrierV2Tail.getD 5 (0, 0)).2) *
    Complex.log manuscriptNormV0_5Arg).re

def manuscriptNormV0_5Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-207003480727327 / 10000000000000000) (-9130910809039 / 312500000000000) (0) (1) (21709 / 15625) (-47 / 203)

private theorem manuscriptNormV0_5_arg_eq : manuscriptNormV0_5Arg = barrierComplex (1 / 1) (78 / 125) := by
  apply Complex.ext <;> norm_num [manuscriptNormV0_5Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV0_5_weight_eq :
    -((barrierV2Tail.getD 0 (0, 0)).2 * (barrierV2Tail.getD 5 (0, 0)).2) =
      barrierComplex (-207003480727327 / 10000000000000000) (-9130910809039 / 312500000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV0_5_exact_interval :
    manuscriptNormV0_5Term ∈ Set.Icc (manuscriptNormV0_5Interval.1 : ℝ) (manuscriptNormV0_5Interval.2 : ℝ) := by
  unfold manuscriptNormV0_5Term
  rw [manuscriptNormV0_5_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-207003480727327 / 10000000000000000) (-9130910809039 / 312500000000000)
    manuscriptNormV0_5Arg (0) (1) (21709 / 15625) (203 / 125) (-47 / 125)
  have hratio : ((-47 / 125) / (203 / 125) : ℚ) = (-47 / 203) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV0_5Interval
  apply h
  all_goals
    try rw [manuscriptNormV0_5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV0_5_rounded_endpoints :
    (12896941244777008109092538609 / 1000000000000000000000000000000) ≤ manuscriptNormV0_5Interval.1 ∧ manuscriptNormV0_5Interval.2 ≤ (1612117655597126146042737969 / 125000000000000000000000000000) := by
  simp only [manuscriptNormV0_5Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV0_5_enclosure :
    manuscriptNormV0_5Term ∈ Set.Icc ((12896941244777008109092538609 / 1000000000000000000000000000000) : ℝ) ((1612117655597126146042737969 / 125000000000000000000000000000) : ℝ) := by
  have hlo : ((12896941244777008109092538609 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormV0_5Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV0_5_rounded_endpoints.1
  have hhi : (manuscriptNormV0_5Interval.2 : ℝ) ≤ ((1612117655597126146042737969 / 125000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV0_5_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV0_5_exact_interval.1, manuscriptNormV0_5_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
