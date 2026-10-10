import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX10

namespace OAI

noncomputable section
namespace InternalCatalan

def manuscriptCase2X10XV3Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2466317 / 50000000) (0 / 1) (-1) (0) (25799903804725190190801 / 20000000000000000000000) (0 / 1)

private theorem manuscriptCase2X10XV3_arg_eq : barrierCase2X10XV3LogArg = barrierComplex (160623484599 / 200000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X10XV3LogArg, Case2PointData.X10, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X10XV3_weight_eq : (barrierV2Tail.getD 3 (0, 0)).2 = barrierComplex (-2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X10XV3_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X10 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc (manuscriptCase2X10XV3Interval.1 : ℝ) (manuscriptCase2X10XV3Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2X10XV3LogArg).re ∈ _
  rw [manuscriptCase2X10XV3_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2466317 / 50000000) (0 / 1)
    barrierCase2X10XV3LogArg (-1) (0) (25799903804725190190801 / 20000000000000000000000) (160623484599 / 200000000000) (0 / 1)
  have hratio : ((0 / 1) / (160623484599 / 200000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X10XV3Interval
  apply h
  all_goals
    try rw [manuscriptCase2X10XV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X10XV3_rounded_endpoints :
    (108150143850225761373628520600971601391 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X10XV3Interval.1 ∧ manuscriptCase2X10XV3Interval.2 ≤ (54075071925112880703468057440949519667 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X10XV3Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X10XV3_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X10 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc ((108150143850225761373628520600971601391 / 10000000000000000000000000000000000000000) : ℝ) ((54075071925112880703468057440949519667 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((108150143850225761373628520600971601391 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X10XV3Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X10XV3_rounded_endpoints.1
  have hhi : (manuscriptCase2X10XV3Interval.2 : ℝ) ≤ ((54075071925112880703468057440949519667 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X10XV3_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X10XV3_exact_interval.1, manuscriptCase2X10XV3_exact_interval.2.trans hhi⟩

def manuscriptCase2X10XV4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (11618157 / 100000000) (0 / 1) (-1) (0) (990201867124754854284289 / 781250000000000000000000) (0 / 1)

private theorem manuscriptCase2X10XV4_arg_eq : barrierCase2X10XV4LogArg = barrierComplex (995088873983 / 1250000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X10XV4LogArg, Case2PointData.X10, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X10XV4_weight_eq : (barrierV2Tail.getD 4 (0, 0)).2 = barrierComplex (11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X10XV4_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X10 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc (manuscriptCase2X10XV4Interval.1 : ℝ) (manuscriptCase2X10XV4Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X10XV4LogArg).re ∈ _
  rw [manuscriptCase2X10XV4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (11618157 / 100000000) (0 / 1)
    barrierCase2X10XV4LogArg (-1) (0) (990201867124754854284289 / 781250000000000000000000) (995088873983 / 1250000000000) (0 / 1)
  have hratio : ((0 / 1) / (995088873983 / 1250000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X10XV4Interval
  apply h
  all_goals
    try rw [manuscriptCase2X10XV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X10XV4_rounded_endpoints :
    (-132485780816671281192424561714957957437 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2X10XV4Interval.1 ∧ manuscriptCase2X10XV4Interval.2 ≤ (-132485780816671281153198778933576145143 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X10XV4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X10XV4_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X10 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc ((-132485780816671281192424561714957957437 / 5000000000000000000000000000000000000000) : ℝ) ((-132485780816671281153198778933576145143 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-132485780816671281192424561714957957437 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X10XV4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X10XV4_rounded_endpoints.1
  have hhi : (manuscriptCase2X10XV4Interval.2 : ℝ) ≤ ((-132485780816671281153198778933576145143 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X10XV4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X10XV4_exact_interval.1, manuscriptCase2X10XV4_exact_interval.2.trans hhi⟩

def manuscriptCase2X10XV5Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (13619357 / 100000000) (600749 / 3125000) (0) (0) (256532758052508072798361 / 250000000000000000000000) (-80825478981 / 500000000000)

private theorem manuscriptCase2X10XV5_arg_eq : barrierCase2X10XV5LogArg = barrierComplex (1 / 1) (-80825478981 / 500000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X10XV5LogArg, Case2PointData.X10, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X10XV5_weight_eq : (barrierV2Tail.getD 5 (0, 0)).2 = barrierComplex (13619357 / 100000000) (600749 / 3125000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X10XV5_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X10 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc (manuscriptCase2X10XV5Interval.1 : ℝ) (manuscriptCase2X10XV5Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2X10XV5LogArg).re ∈ _
  rw [manuscriptCase2X10XV5_weight_eq]
  have h := manuscript_weighted_complex_log_interval (13619357 / 100000000) (600749 / 3125000)
    barrierCase2X10XV5LogArg (0) (0) (256532758052508072798361 / 250000000000000000000000) (1 / 1) (-80825478981 / 500000000000)
  have hratio : ((-80825478981 / 500000000000) / (1 / 1) : ℚ) = (-80825478981 / 500000000000) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X10XV5Interval
  apply h
  all_goals
    try rw [manuscriptCase2X10XV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X10XV5_rounded_endpoints :
    (20353626020974266061443930866923384619 / 625000000000000000000000000000000000000) ≤ manuscriptCase2X10XV5Interval.1 ∧ manuscriptCase2X10XV5Interval.2 ≤ (65131603267117651396620578774154830781 / 2000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X10XV5Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X10XV5_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X10 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc ((20353626020974266061443930866923384619 / 625000000000000000000000000000000000000) : ℝ) ((65131603267117651396620578774154830781 / 2000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((20353626020974266061443930866923384619 / 625000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X10XV5Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X10XV5_rounded_endpoints.1
  have hhi : (manuscriptCase2X10XV5Interval.2 : ℝ) ≤ ((65131603267117651396620578774154830781 / 2000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X10XV5_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X10XV5_exact_interval.1, manuscriptCase2X10XV5_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
