import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX13

namespace OAI

noncomputable section
namespace InternalCatalan

def manuscriptCase2X13XV3Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2466317 / 50000000) (0 / 1) (-3) (0) (7889750979937930307961 / 5000000000000000000000) (0 / 1)

private theorem manuscriptCase2X13XV3_arg_eq : barrierCase2X13XV3LogArg = barrierComplex (88824270219 / 200000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X13XV3LogArg, Case2PointData.X13, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X13XV3_weight_eq : (barrierV2Tail.getD 3 (0, 0)).2 = barrierComplex (-2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X13XV3_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X13 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc (manuscriptCase2X13XV3Interval.1 : ℝ) (manuscriptCase2X13XV3Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2X13XV3LogArg).re ∈ _
  rw [manuscriptCase2X13XV3_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2466317 / 50000000) (0 / 1)
    barrierCase2X13XV3LogArg (-3) (0) (7889750979937930307961 / 5000000000000000000000) (88824270219 / 200000000000) (0 / 1)
  have hratio : ((0 / 1) / (88824270219 / 200000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X13XV3Interval
  apply h
  all_goals
    try rw [manuscriptCase2X13XV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X13XV3_rounded_endpoints :
    (100090227198405659127247267513033204179 / 2500000000000000000000000000000000000000) ≤ manuscriptCase2X13XV3Interval.1 ∧ manuscriptCase2X13XV3Interval.2 ≤ (20018045439681131830445593303966638543 / 500000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X13XV3Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X13XV3_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X13 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc ((100090227198405659127247267513033204179 / 2500000000000000000000000000000000000000) : ℝ) ((20018045439681131830445593303966638543 / 500000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((100090227198405659127247267513033204179 / 2500000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X13XV3Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X13XV3_rounded_endpoints.1
  have hhi : (manuscriptCase2X13XV3Interval.2 : ℝ) ≤ ((20018045439681131830445593303966638543 / 500000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X13XV3_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X13XV3_exact_interval.1, manuscriptCase2X13XV3_exact_interval.2.trans hhi⟩

def manuscriptCase2X13XV4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (11618157 / 100000000) (0 / 1) (-3) (0) (281200519868941960191529 / 195312500000000000000000) (0 / 1)

private theorem manuscriptCase2X13XV4_arg_eq : barrierCase2X13XV4LogArg = barrierComplex (530283433523 / 1250000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X13XV4LogArg, Case2PointData.X13, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X13XV4_weight_eq : (barrierV2Tail.getD 4 (0, 0)).2 = barrierComplex (11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X13XV4_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X13 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc (manuscriptCase2X13XV4Interval.1 : ℝ) (manuscriptCase2X13XV4Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X13XV4LogArg).re ∈ _
  rw [manuscriptCase2X13XV4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (11618157 / 100000000) (0 / 1)
    barrierCase2X13XV4LogArg (-3) (0) (281200519868941960191529 / 195312500000000000000000) (530283433523 / 1250000000000) (0 / 1)
  have hratio : ((0 / 1) / (530283433523 / 1250000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X13XV4Interval
  apply h
  all_goals
    try rw [manuscriptCase2X13XV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X13XV4_rounded_endpoints :
    (-996242075780485923046032812958074041827 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X13XV4Interval.1 ∧ manuscriptCase2X13XV4Interval.2 ≤ (-62265129736280370175667382266267295369 / 625000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X13XV4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X13XV4_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X13 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc ((-996242075780485923046032812958074041827 / 10000000000000000000000000000000000000000) : ℝ) ((-62265129736280370175667382266267295369 / 625000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-996242075780485923046032812958074041827 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X13XV4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X13XV4_rounded_endpoints.1
  have hhi : (manuscriptCase2X13XV4Interval.2 : ℝ) ≤ ((-62265129736280370175667382266267295369 / 625000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X13XV4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X13XV4_exact_interval.1, manuscriptCase2X13XV4_exact_interval.2.trans hhi⟩

def manuscriptCase2X13XV5Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (13619357 / 100000000) (600749 / 3125000) (0) (-1) (302076524208437650965121 / 250000000000000000000000) (271797186239 / 728202813761)

private theorem manuscriptCase2X13XV5_arg_eq : barrierCase2X13XV5LogArg = barrierComplex (1 / 1) (-228202813761 / 500000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X13XV5LogArg, Case2PointData.X13, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X13XV5_weight_eq : (barrierV2Tail.getD 5 (0, 0)).2 = barrierComplex (13619357 / 100000000) (600749 / 3125000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X13XV5_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X13 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc (manuscriptCase2X13XV5Interval.1 : ℝ) (manuscriptCase2X13XV5Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2X13XV5LogArg).re ∈ _
  rw [manuscriptCase2X13XV5_weight_eq]
  have h := manuscript_weighted_complex_log_interval (13619357 / 100000000) (600749 / 3125000)
    barrierCase2X13XV5LogArg (0) (-1) (302076524208437650965121 / 250000000000000000000000) (728202813761 / 500000000000) (271797186239 / 500000000000)
  have hratio : ((271797186239 / 500000000000) / (728202813761 / 500000000000) : ℚ) = (271797186239 / 728202813761) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X13XV5Interval
  apply h
  all_goals
    try rw [manuscriptCase2X13XV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X13XV5_rounded_endpoints :
    (951961281386640521608956326329443209421 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X13XV5Interval.1 ∧ manuscriptCase2X13XV5Interval.2 ≤ (190392256277328118260014777368769853527 / 2000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X13XV5Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X13XV5_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X13 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc ((951961281386640521608956326329443209421 / 10000000000000000000000000000000000000000) : ℝ) ((190392256277328118260014777368769853527 / 2000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((951961281386640521608956326329443209421 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X13XV5Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X13XV5_rounded_endpoints.1
  have hhi : (manuscriptCase2X13XV5Interval.2 : ℝ) ≤ ((190392256277328118260014777368769853527 / 2000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X13XV5_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X13XV5_exact_interval.1, manuscriptCase2X13XV5_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
