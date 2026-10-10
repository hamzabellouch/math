import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointY13

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2Y13YV3Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (2466317 / 50000000) (0 / 1) (-15) (0) (23603499058295809 / 12207031250000000) (0 / 1)

private theorem manuscriptCase2Y13YV3_arg_eq : barrierCase2Y13YV3LogArg = barrierComplex (153634303 / 20000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y13YV3LogArg, Case2PointData.Y13, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y13YV3_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2) = barrierComplex (2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y13YV3_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y13 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc (manuscriptCase2Y13YV3Interval.1 : ℝ) (manuscriptCase2Y13YV3Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2) * Complex.log barrierCase2Y13YV3LogArg).re ∈ _
  rw [manuscriptCase2Y13YV3_weight_eq]
  have h := manuscript_weighted_complex_log_interval (2466317 / 50000000) (0 / 1)
    barrierCase2Y13YV3LogArg (-15) (0) (23603499058295809 / 12207031250000000) (153634303 / 20000000000) (0 / 1)
  have hratio : ((0 / 1) / (153634303 / 20000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y13YV3Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y13YV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y13YV3_rounded_endpoints :
    (-2401656299491192074728609452329208787831 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y13YV3Interval.1 ∧ manuscriptCase2Y13YV3Interval.2 ≤ (-2401656299491192074223061445553050192459 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y13YV3Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y13YV3_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y13 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc ((-2401656299491192074728609452329208787831 / 10000000000000000000000000000000000000000) : ℝ) ((-2401656299491192074223061445553050192459 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-2401656299491192074728609452329208787831 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y13YV3Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y13YV3_rounded_endpoints.1
  have hhi : (manuscriptCase2Y13YV3Interval.2 : ℝ) ≤ ((-2401656299491192074223061445553050192459 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y13YV3_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y13YV3_exact_interval.1, manuscriptCase2Y13YV3_exact_interval.2.trans hhi⟩

def manuscriptCase2Y13YV4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-11618157 / 100000000) (0 / 1) (-15) (0) (494062436773854001 / 476837158203125000) (0 / 1)

private theorem manuscriptCase2Y13YV4_arg_eq : barrierCase2Y13YV4LogArg = barrierComplex (702895751 / 125000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y13YV4LogArg, Case2PointData.Y13, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y13YV4_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2) = barrierComplex (-11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y13YV4_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y13 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc (manuscriptCase2Y13YV4Interval.1 : ℝ) (manuscriptCase2Y13YV4Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2) * Complex.log barrierCase2Y13YV4LogArg).re ∈ _
  rw [manuscriptCase2Y13YV4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-11618157 / 100000000) (0 / 1)
    barrierCase2Y13YV4LogArg (-15) (0) (494062436773854001 / 476837158203125000) (702895751 / 125000000000) (0 / 1)
  have hratio : ((0 / 1) / (702895751 / 125000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y13YV4Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y13YV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y13YV4_rounded_endpoints :
    (6019204983687295438723989919924987739839 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y13YV4Interval.1 ∧ manuscriptCase2Y13YV4Interval.2 ≤ (6019204983687295439900763403366442087133 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y13YV4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y13YV4_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y13 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc ((6019204983687295438723989919924987739839 / 10000000000000000000000000000000000000000) : ℝ) ((6019204983687295439900763403366442087133 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((6019204983687295438723989919924987739839 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y13YV4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y13YV4_rounded_endpoints.1
  have hhi : (manuscriptCase2Y13YV4Interval.2 : ℝ) ≤ ((6019204983687295439900763403366442087133 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y13YV4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y13YV4_exact_interval.1, manuscriptCase2Y13YV4_exact_interval.2.trans hhi⟩

def manuscriptCase2Y13YV5Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-13619357 / 100000000) (-600749 / 3125000) (1) (-2) (6434236856385023179849 / 5000000000000000000000) (19580000000 / 77787276957)

private theorem manuscriptCase2Y13YV5_arg_eq : barrierCase2Y13YV5LogArg = barrierComplex (979 / 2500) (-77787276957 / 50000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2Y13YV5LogArg, Case2PointData.Y13, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y13YV5_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2) = barrierComplex (-13619357 / 100000000) (-600749 / 3125000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y13YV5_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y13 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc (manuscriptCase2Y13YV5Interval.1 : ℝ) (manuscriptCase2Y13YV5Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2) * Complex.log barrierCase2Y13YV5LogArg).re ∈ _
  rw [manuscriptCase2Y13YV5_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-13619357 / 100000000) (-600749 / 3125000)
    barrierCase2Y13YV5LogArg (1) (-2) (6434236856385023179849 / 5000000000000000000000) (77787276957 / 25000000000) (979 / 1250)
  have hratio : ((979 / 1250) / (77787276957 / 25000000000) : ℚ) = (19580000000 / 77787276957) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y13YV5Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y13YV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y13YV5_rounded_endpoints :
    (-1594699492839648168799826525322990680401 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2Y13YV5Interval.1 ∧ manuscriptCase2Y13YV5Interval.2 ≤ (-159469949283964809906276844435649662221 / 500000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y13YV5Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y13YV5_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y13 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc ((-1594699492839648168799826525322990680401 / 5000000000000000000000000000000000000000) : ℝ) ((-159469949283964809906276844435649662221 / 500000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-1594699492839648168799826525322990680401 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y13YV5Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y13YV5_rounded_endpoints.1
  have hhi : (manuscriptCase2Y13YV5Interval.2 : ℝ) ≤ ((-159469949283964809906276844435649662221 / 500000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y13YV5_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y13YV5_exact_interval.1, manuscriptCase2Y13YV5_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
