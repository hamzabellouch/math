import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX14

namespace OAI

noncomputable section
namespace InternalCatalan

def manuscriptCase2X14XV3Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2466317 / 50000000) (0 / 1) (-4) (0) (3830176138095157749889 / 2500000000000000000000) (0 / 1)

private theorem manuscriptCase2X14XV3_arg_eq : barrierCase2X14XV3LogArg = barrierComplex (61888416833 / 200000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X14XV3LogArg, Case2PointData.X14, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X14XV3_weight_eq : (barrierV2Tail.getD 3 (0, 0)).2 = barrierComplex (-2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X14XV3_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X14 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc (manuscriptCase2X14XV3Interval.1 : ℝ) (manuscriptCase2X14XV3Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2X14XV3LogArg).re ∈ _
  rw [manuscriptCase2X14XV3_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2466317 / 50000000) (0 / 1)
    barrierCase2X14XV3LogArg (-4) (0) (3830176138095157749889 / 2500000000000000000000) (61888416833 / 200000000000) (0 / 1)
  have hratio : ((0 / 1) / (61888416833 / 200000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X14XV3Interval
  apply h
  all_goals
    try rw [manuscriptCase2X14XV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X14XV3_rounded_endpoints :
    (578590239482700893088730271660428803289 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X14XV3Interval.1 ∧ manuscriptCase2X14XV3Interval.2 ≤ (578590239482700893221960649977423759343 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X14XV3Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X14XV3_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X14 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc ((578590239482700893088730271660428803289 / 10000000000000000000000000000000000000000) : ℝ) ((578590239482700893221960649977423759343 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((578590239482700893088730271660428803289 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X14XV3Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X14XV3_rounded_endpoints.1
  have hhi : (manuscriptCase2X14XV3Interval.2 : ℝ) ≤ ((578590239482700893221960649977423759343 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X14XV3_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X14XV3_exact_interval.1, manuscriptCase2X14XV3_exact_interval.2.trans hhi⟩

def manuscriptCase2X14XV4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (11618157 / 100000000) (0 / 1) (-4) (0) (126671376269976015507121 / 97656250000000000000000) (0 / 1)

private theorem manuscriptCase2X14XV4_arg_eq : barrierCase2X14XV4LogArg = barrierComplex (355909224761 / 1250000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X14XV4LogArg, Case2PointData.X14, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X14XV4_weight_eq : (barrierV2Tail.getD 4 (0, 0)).2 = barrierComplex (11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X14XV4_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X14 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc (manuscriptCase2X14XV4Interval.1 : ℝ) (manuscriptCase2X14XV4Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X14XV4LogArg).re ∈ _
  rw [manuscriptCase2X14XV4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (11618157 / 100000000) (0 / 1)
    barrierCase2X14XV4LogArg (-4) (0) (126671376269976015507121 / 97656250000000000000000) (355909224761 / 1250000000000) (0 / 1)
  have hratio : ((0 / 1) / (355909224761 / 1250000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X14XV4Interval
  apply h
  all_goals
    try rw [manuscriptCase2X14XV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X14XV4_rounded_endpoints :
    (-1459499741875407455096260187959587776601 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X14XV4Interval.1 ∧ manuscriptCase2X14XV4Interval.2 ≤ (-1459499741875407454782453925708533240467 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X14XV4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X14XV4_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X14 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc ((-1459499741875407455096260187959587776601 / 10000000000000000000000000000000000000000) : ℝ) ((-1459499741875407454782453925708533240467 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-1459499741875407455096260187959587776601 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X14XV4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X14XV4_rounded_endpoints.1
  have hhi : (manuscriptCase2X14XV4Interval.2 : ℝ) ≤ ((-1459499741875407454782453925708533240467 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X14XV4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X14XV4_exact_interval.1, manuscriptCase2X14XV4_exact_interval.2.trans hhi⟩

def manuscriptCase2X14XV5Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (13619357 / 100000000) (600749 / 3125000) (0) (-1) (330367825775195387638729 / 250000000000000000000000) (216507802973 / 783492197027)

private theorem manuscriptCase2X14XV5_arg_eq : barrierCase2X14XV5LogArg = barrierComplex (1 / 1) (-283492197027 / 500000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X14XV5LogArg, Case2PointData.X14, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X14XV5_weight_eq : (barrierV2Tail.getD 5 (0, 0)).2 = barrierComplex (13619357 / 100000000) (600749 / 3125000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X14XV5_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X14 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc (manuscriptCase2X14XV5Interval.1 : ℝ) (manuscriptCase2X14XV5Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2X14XV5LogArg).re ∈ _
  rw [manuscriptCase2X14XV5_weight_eq]
  have h := manuscript_weighted_complex_log_interval (13619357 / 100000000) (600749 / 3125000)
    barrierCase2X14XV5LogArg (0) (-1) (330367825775195387638729 / 250000000000000000000000) (783492197027 / 500000000000) (216507802973 / 500000000000)
  have hratio : ((216507802973 / 500000000000) / (783492197027 / 500000000000) : ℚ) = (216507802973 / 783492197027) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X14XV5Interval
  apply h
  all_goals
    try rw [manuscriptCase2X14XV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X14XV5_rounded_endpoints :
    (73835557669917422448940509571246830059 / 625000000000000000000000000000000000000) ≤ manuscriptCase2X14XV5Interval.1 ∧ manuscriptCase2X14XV5Interval.2 ≤ (590684461359339414437061951625244423513 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X14XV5Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X14XV5_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X14 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc ((73835557669917422448940509571246830059 / 625000000000000000000000000000000000000) : ℝ) ((590684461359339414437061951625244423513 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((73835557669917422448940509571246830059 / 625000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X14XV5Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X14XV5_rounded_endpoints.1
  have hhi : (manuscriptCase2X14XV5Interval.2 : ℝ) ≤ ((590684461359339414437061951625244423513 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X14XV5_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X14XV5_exact_interval.1, manuscriptCase2X14XV5_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
