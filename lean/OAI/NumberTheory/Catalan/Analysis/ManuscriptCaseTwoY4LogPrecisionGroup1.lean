import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointY4

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2Y4YV3Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (2466317 / 50000000) (0 / 1) (1) (0) (5580847934774121774361 / 5000000000000000000000) (0 / 1)

private theorem manuscriptCase2Y4YV3_arg_eq : barrierCase2Y4YV3LogArg = barrierComplex (74705073019 / 50000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y4YV3LogArg, Case2PointData.Y4, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y4YV3_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2) = barrierComplex (2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y4YV3_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y4 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc (manuscriptCase2Y4YV3Interval.1 : ℝ) (manuscriptCase2Y4YV3Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2) * Complex.log barrierCase2Y4YV3LogArg).re ∈ _
  rw [manuscriptCase2Y4YV3_weight_eq]
  have h := manuscript_weighted_complex_log_interval (2466317 / 50000000) (0 / 1)
    barrierCase2Y4YV3LogArg (1) (0) (5580847934774121774361 / 5000000000000000000000) (74705073019 / 50000000000) (0 / 1)
  have hratio : ((0 / 1) / (74705073019 / 50000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y4YV3Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y4YV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y4YV3_rounded_endpoints :
    (198057584862714281584498873489771408177 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y4YV3Interval.1 ∧ manuscriptCase2Y4YV3Interval.2 ≤ (198057584862714281617806467770698837677 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y4YV3Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y4YV3_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y4 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc ((198057584862714281584498873489771408177 / 10000000000000000000000000000000000000000) : ℝ) ((198057584862714281617806467770698837677 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((198057584862714281584498873489771408177 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y4YV3Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y4YV3_rounded_endpoints.1
  have hhi : (manuscriptCase2Y4YV3Interval.2 : ℝ) ≤ ((198057584862714281617806467770698837677 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y4YV3_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y4YV3_exact_interval.1, manuscriptCase2Y4YV3_exact_interval.2.trans hhi⟩

def manuscriptCase2Y4YV4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-11618157 / 100000000) (0 / 1) (1) (0) (233180667104431689901129 / 195312500000000000000000) (0 / 1)

private theorem manuscriptCase2Y4YV4_arg_eq : barrierCase2Y4YV4LogArg = barrierComplex (482887841123 / 312500000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y4YV4LogArg, Case2PointData.Y4, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y4YV4_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2) = barrierComplex (-11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y4YV4_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y4 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc (manuscriptCase2Y4YV4Interval.1 : ℝ) (manuscriptCase2Y4YV4Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2) * Complex.log barrierCase2Y4YV4LogArg).re ∈ _
  rw [manuscriptCase2Y4YV4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-11618157 / 100000000) (0 / 1)
    barrierCase2Y4YV4LogArg (1) (0) (233180667104431689901129 / 195312500000000000000000) (482887841123 / 312500000000) (0 / 1)
  have hratio : ((0 / 1) / (482887841123 / 312500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y4YV4Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y4YV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y4YV4_rounded_endpoints :
    (-101119778372448681426063262900366560903 / 2000000000000000000000000000000000000000) ≤ manuscriptCase2Y4YV4Interval.1 ∧ manuscriptCase2Y4YV4Interval.2 ≤ (-505598891862243407051864748939069181361 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y4YV4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y4YV4_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y4 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc ((-101119778372448681426063262900366560903 / 2000000000000000000000000000000000000000) : ℝ) ((-505598891862243407051864748939069181361 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-101119778372448681426063262900366560903 / 2000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y4YV4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y4YV4_rounded_endpoints.1
  have hhi : (manuscriptCase2Y4YV4Interval.2 : ℝ) ≤ ((-505598891862243407051864748939069181361 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y4YV4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y4YV4_exact_interval.1, manuscriptCase2Y4YV4_exact_interval.2.trans hhi⟩

def manuscriptCase2Y4YV5Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-13619357 / 100000000) (-600749 / 3125000) (-2) (-1) (4152935100111231215521 / 3906250000000000000000) (7035413039 / 90864586961)

private theorem manuscriptCase2Y4YV5_arg_eq : barrierCase2Y4YV5LogArg = barrierComplex (979 / 2500) (-41914586961 / 125000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2Y4YV5LogArg, Case2PointData.Y4, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y4YV5_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2) = barrierComplex (-13619357 / 100000000) (-600749 / 3125000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y4YV5_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y4 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc (manuscriptCase2Y4YV5Interval.1 : ℝ) (manuscriptCase2Y4YV5Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2) * Complex.log barrierCase2Y4YV5LogArg).re ∈ _
  rw [manuscriptCase2Y4YV5_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-13619357 / 100000000) (-600749 / 3125000)
    barrierCase2Y4YV5LogArg (-2) (-1) (4152935100111231215521 / 3906250000000000000000) (90864586961 / 125000000000) (7035413039 / 125000000000)
  have hratio : ((7035413039 / 125000000000) / (90864586961 / 125000000000) : ℚ) = (7035413039 / 90864586961) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y4YV5Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y4YV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y4YV5_rounded_endpoints :
    (-57371987293099645198197793222765085421 / 1250000000000000000000000000000000000000) ≤ manuscriptCase2Y4YV5Interval.1 ∧ manuscriptCase2Y4YV5Interval.2 ≤ (-229487949172398545855288636098920658831 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y4YV5Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y4YV5_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y4 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc ((-57371987293099645198197793222765085421 / 1250000000000000000000000000000000000000) : ℝ) ((-229487949172398545855288636098920658831 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-57371987293099645198197793222765085421 / 1250000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y4YV5Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y4YV5_rounded_endpoints.1
  have hhi : (manuscriptCase2Y4YV5Interval.2 : ℝ) ≤ ((-229487949172398545855288636098920658831 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y4YV5_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y4YV5_exact_interval.1, manuscriptCase2Y4YV5_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
