import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointY2

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2Y2YV3Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (2466317 / 50000000) (0 / 1) (1) (0) (7719018960174379559641 / 5000000000000000000000) (0 / 1)

private theorem manuscriptCase2Y2YV3_arg_eq : barrierCase2Y2YV3LogArg = barrierComplex (87857947621 / 50000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y2YV3LogArg, Case2PointData.Y2, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y2YV3_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2) = barrierComplex (2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y2YV3_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y2 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc (manuscriptCase2Y2YV3Interval.1 : ℝ) (manuscriptCase2Y2YV3Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2) * Complex.log barrierCase2Y2YV3LogArg).re ∈ _
  rw [manuscriptCase2Y2YV3_weight_eq]
  have h := manuscript_weighted_complex_log_interval (2466317 / 50000000) (0 / 1)
    barrierCase2Y2YV3LogArg (1) (0) (7719018960174379559641 / 5000000000000000000000) (87857947621 / 50000000000) (0 / 1)
  have hratio : ((0 / 1) / (87857947621 / 50000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y2YV3Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y2YV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y2YV3_rounded_endpoints :
    (278051726810258993707358713970906698683 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y2YV3Interval.1 ∧ manuscriptCase2Y2YV3Interval.2 ≤ (278051726810258993740666310509508388501 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y2YV3Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y2YV3_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y2 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc ((278051726810258993707358713970906698683 / 10000000000000000000000000000000000000000) : ℝ) ((278051726810258993740666310509508388501 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((278051726810258993707358713970906698683 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y2YV3Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y2YV3_rounded_endpoints.1
  have hhi : (manuscriptCase2Y2YV3Interval.2 : ℝ) ≤ ((278051726810258993740666310509508388501 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y2YV3_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y2YV3_exact_interval.1, manuscriptCase2Y2YV3_exact_interval.2.trans hhi⟩

def manuscriptCase2Y2YV4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-11618157 / 100000000) (0 / 1) (1) (0) (322664213104953200631049 / 195312500000000000000000) (0 / 1)

private theorem manuscriptCase2Y2YV4_arg_eq : barrierCase2Y2YV4LogArg = barrierComplex (568035397757 / 312500000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y2YV4LogArg, Case2PointData.Y2, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y2YV4_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2) = barrierComplex (-11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y2YV4_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y2 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc (manuscriptCase2Y2YV4Interval.1 : ℝ) (manuscriptCase2Y2YV4Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2) * Complex.log barrierCase2Y2YV4LogArg).re ∈ _
  rw [manuscriptCase2Y2YV4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-11618157 / 100000000) (0 / 1)
    barrierCase2Y2YV4LogArg (1) (0) (322664213104953200631049 / 195312500000000000000000) (568035397757 / 312500000000) (0 / 1)
  have hratio : ((0 / 1) / (568035397757 / 312500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y2YV4Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y2YV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y2YV4_rounded_endpoints :
    (-5424038867885912243587846244956114937 / 78125000000000000000000000000000000000) ≤ manuscriptCase2Y2YV4Interval.1 ∧ manuscriptCase2Y2YV4Interval.2 ≤ (-694276975089396767100791799428326302547 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y2YV4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y2YV4_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y2 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc ((-5424038867885912243587846244956114937 / 78125000000000000000000000000000000000) : ℝ) ((-694276975089396767100791799428326302547 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-5424038867885912243587846244956114937 / 78125000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y2YV4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y2YV4_rounded_endpoints.1
  have hhi : (manuscriptCase2Y2YV4Interval.2 : ℝ) ≤ ((-694276975089396767100791799428326302547 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y2YV4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y2YV4_exact_interval.1, manuscriptCase2Y2YV4_exact_interval.2.trans hhi⟩

def manuscriptCase2Y2YV5Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-13619357 / 100000000) (-600749 / 3125000) (-3) (0) (2618606894666360277601 / 1953125000000000000000) (-14916581199 / 48950000000)

private theorem manuscriptCase2Y2YV5_arg_eq : barrierCase2Y2YV5LogArg = barrierComplex (979 / 2500) (-14916581199 / 125000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2Y2YV5LogArg, Case2PointData.Y2, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y2YV5_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2) = barrierComplex (-13619357 / 100000000) (-600749 / 3125000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y2YV5_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y2 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc (manuscriptCase2Y2YV5Interval.1 : ℝ) (manuscriptCase2Y2YV5Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2) * Complex.log barrierCase2Y2YV5LogArg).re ∈ _
  rw [manuscriptCase2Y2YV5_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-13619357 / 100000000) (-600749 / 3125000)
    barrierCase2Y2YV5LogArg (-3) (0) (2618606894666360277601 / 1953125000000000000000) (979 / 2500) (-14916581199 / 125000000000)
  have hratio : ((-14916581199 / 125000000000) / (979 / 2500) : ℚ) = (-14916581199 / 48950000000) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y2YV5Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y2YV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y2YV5_rounded_endpoints :
    (323868227978994063462812907897160887753 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2Y2YV5Interval.1 ∧ manuscriptCase2Y2YV5Interval.2 ≤ (647736455957988127201519803051041793109 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y2YV5Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y2YV5_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y2 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc ((323868227978994063462812907897160887753 / 5000000000000000000000000000000000000000) : ℝ) ((647736455957988127201519803051041793109 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((323868227978994063462812907897160887753 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y2YV5Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y2YV5_rounded_endpoints.1
  have hhi : (manuscriptCase2Y2YV5Interval.2 : ℝ) ≤ ((647736455957988127201519803051041793109 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y2YV5_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y2YV5_exact_interval.1, manuscriptCase2Y2YV5_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
