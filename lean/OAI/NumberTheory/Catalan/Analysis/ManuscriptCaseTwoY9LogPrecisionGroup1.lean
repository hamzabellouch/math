import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoGlobalBounds

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2Y9YV3Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (2466317 / 50000000) (0 / 1) (-3) (0) (1416936798123903344401 / 1250000000000000000000) (0 / 1)

private theorem manuscriptCase2Y9YV3_arg_eq : barrierCase2Y9YV3LogArg = barrierComplex (37642220951 / 100000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y9YV3LogArg, Case2PointData.Y9, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y9YV3_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2) = barrierComplex (2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y9YV3_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y9 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc (manuscriptCase2Y9YV3Interval.1 : ℝ) (manuscriptCase2Y9YV3Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2) * Complex.log barrierCase2Y9YV3LogArg).re ∈ _
  rw [manuscriptCase2Y9YV3_weight_eq]
  have h := manuscript_weighted_complex_log_interval (2466317 / 50000000) (0 / 1)
    barrierCase2Y9YV3LogArg (-3) (0) (1416936798123903344401 / 1250000000000000000000) (37642220951 / 100000000000) (0 / 1)
  have hratio : ((0 / 1) / (37642220951 / 100000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y9YV3Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y9YV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y9YV3_rounded_endpoints :
    (-7530312191373142540645061379251591651 / 156250000000000000000000000000000000000) ≤ manuscriptCase2Y9YV3Interval.1 ∧ manuscriptCase2Y9YV3Interval.2 ≤ (-240969990123940561250680572714659788583 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y9YV3Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y9YV3_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y9 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc ((-7530312191373142540645061379251591651 / 156250000000000000000000000000000000000) : ℝ) ((-240969990123940561250680572714659788583 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-7530312191373142540645061379251591651 / 156250000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y9YV3Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y9YV3_rounded_endpoints.1
  have hhi : (manuscriptCase2Y9YV3Interval.2 : ℝ) ≤ ((-240969990123940561250680572714659788583 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y9YV3_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y9YV3_exact_interval.1, manuscriptCase2Y9YV3_exact_interval.2.trans hhi⟩

def manuscriptCase2Y9YV4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-11618157 / 100000000) (0 / 1) (-3) (0) (58673159116478365754689 / 48828125000000000000000) (0 / 1)

private theorem manuscriptCase2Y9YV4_arg_eq : barrierCase2Y9YV4LogArg = barrierComplex (242225430367 / 625000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y9YV4LogArg, Case2PointData.Y9, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y9YV4_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2) = barrierComplex (-11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y9YV4_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y9 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc (manuscriptCase2Y9YV4Interval.1 : ℝ) (manuscriptCase2Y9YV4Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2) * Complex.log barrierCase2Y9YV4LogArg).re ∈ _
  rw [manuscriptCase2Y9YV4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-11618157 / 100000000) (0 / 1)
    barrierCase2Y9YV4LogArg (-3) (0) (58673159116478365754689 / 48828125000000000000000) (242225430367 / 625000000000) (0 / 1)
  have hratio : ((0 / 1) / (242225430367 / 625000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y9YV4Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y9YV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y9YV4_rounded_endpoints :
    (275316287467538876660742738819972389049 / 2500000000000000000000000000000000000000) ≤ manuscriptCase2Y9YV4Interval.1 ∧ manuscriptCase2Y9YV4Interval.2 ≤ (137658143733769438359790706496022553207 / 1250000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y9YV4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y9YV4_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y9 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc ((275316287467538876660742738819972389049 / 2500000000000000000000000000000000000000) : ℝ) ((137658143733769438359790706496022553207 / 1250000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((275316287467538876660742738819972389049 / 2500000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y9YV4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y9YV4_rounded_endpoints.1
  have hhi : (manuscriptCase2Y9YV4Interval.2 : ℝ) ≤ ((137658143733769438359790706496022553207 / 1250000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y9YV4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y9YV4_exact_interval.1, manuscriptCase2Y9YV4_exact_interval.2.trans hhi⟩

def manuscriptCase2Y9YV5Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-13619357 / 100000000) (-600749 / 3125000) (0) (-2) (107708435368848314367961 / 62500000000000000000000) (8900000000 / 28477049679)

private theorem manuscriptCase2Y9YV5_arg_eq : barrierCase2Y9YV5LogArg = barrierComplex (979 / 2500) (-313247546469 / 250000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2Y9YV5LogArg, Case2PointData.Y9, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y9YV5_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2) = barrierComplex (-13619357 / 100000000) (-600749 / 3125000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y9YV5_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y9 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc (manuscriptCase2Y9YV5Interval.1 : ℝ) (manuscriptCase2Y9YV5Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2) * Complex.log barrierCase2Y9YV5LogArg).re ∈ _
  rw [manuscriptCase2Y9YV5_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-13619357 / 100000000) (-600749 / 3125000)
    barrierCase2Y9YV5LogArg (0) (-2) (107708435368848314367961 / 62500000000000000000000) (313247546469 / 125000000000) (979 / 1250)
  have hratio : ((979 / 1250) / (313247546469 / 125000000000) : ℚ) = (8900000000 / 28477049679) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y9YV5Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y9YV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y9YV5_rounded_endpoints :
    (-2807996707962355313566985624251611495779 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y9YV5Interval.1 ∧ manuscriptCase2Y9YV5Interval.2 ≤ (-2807996707962355174184814413379637169271 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y9YV5Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y9YV5_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y9 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc ((-2807996707962355313566985624251611495779 / 10000000000000000000000000000000000000000) : ℝ) ((-2807996707962355174184814413379637169271 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-2807996707962355313566985624251611495779 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y9YV5Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y9YV5_rounded_endpoints.1
  have hhi : (manuscriptCase2Y9YV5Interval.2 : ℝ) ≤ ((-2807996707962355174184814413379637169271 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y9YV5_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y9YV5_exact_interval.1, manuscriptCase2Y9YV5_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
