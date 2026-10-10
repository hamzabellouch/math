import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointY2

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2Y2YV0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-15199211 / 100000000) (0 / 1) (1) (0) (30332296748170026481 / 19531250000000000000) (0 / 1)

private theorem manuscriptCase2Y2YV0_arg_eq : barrierCase2Y2YV0LogArg = barrierComplex (5507476441 / 3125000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y2YV0LogArg, Case2PointData.Y2, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y2YV0_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2) = barrierComplex (-15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y2YV0_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y2 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc (manuscriptCase2Y2YV0Interval.1 : ℝ) (manuscriptCase2Y2YV0Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2) * Complex.log barrierCase2Y2YV0LogArg).re ∈ _
  rw [manuscriptCase2Y2YV0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-15199211 / 100000000) (0 / 1)
    barrierCase2Y2YV0LogArg (1) (0) (30332296748170026481 / 19531250000000000000) (5507476441 / 3125000000) (0 / 1)
  have hratio : ((0 / 1) / (5507476441 / 3125000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y2YV0Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y2YV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y2YV0_rounded_endpoints :
    (-430648546325497037466482507588349052587 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2Y2YV0Interval.1 ∧ manuscriptCase2Y2YV0Interval.2 ≤ (-430648546325497037415166191667499121057 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y2YV0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y2YV0_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y2 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc ((-430648546325497037466482507588349052587 / 5000000000000000000000000000000000000000) : ℝ) ((-430648546325497037415166191667499121057 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-430648546325497037466482507588349052587 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y2YV0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y2YV0_rounded_endpoints.1
  have hhi : (manuscriptCase2Y2YV0Interval.2 : ℝ) ≤ ((-430648546325497037415166191667499121057 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y2YV0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y2YV0_exact_interval.1, manuscriptCase2Y2YV0_exact_interval.2.trans hhi⟩

def manuscriptCase2Y2YV1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2225831 / 50000000) (0 / 1) (2) (0) (261143315724355238329 / 244140625000000000000) (0 / 1)

private theorem manuscriptCase2Y2YV1_arg_eq : barrierCase2Y2YV1LogArg = barrierComplex (16159929323 / 7812500000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y2YV1LogArg, Case2PointData.Y2, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y2YV1_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2) = barrierComplex (-2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y2YV1_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y2 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc (manuscriptCase2Y2YV1Interval.1 : ℝ) (manuscriptCase2Y2YV1Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2) * Complex.log barrierCase2Y2YV1LogArg).re ∈ _
  rw [manuscriptCase2Y2YV1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2225831 / 50000000) (0 / 1)
    barrierCase2Y2YV1LogArg (2) (0) (261143315724355238329 / 244140625000000000000) (16159929323 / 7812500000) (0 / 1)
  have hratio : ((0 / 1) / (16159929323 / 7812500000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y2YV1Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y2YV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y2YV1_rounded_endpoints :
    (-32355109644386964254402989942404875783 / 1000000000000000000000000000000000000000) ≤ manuscriptCase2Y2YV1Interval.1 ∧ manuscriptCase2Y2YV1Interval.2 ≤ (-323551096443869642483910234445125949991 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y2YV1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y2YV1_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y2 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc ((-32355109644386964254402989942404875783 / 1000000000000000000000000000000000000000) : ℝ) ((-323551096443869642483910234445125949991 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-32355109644386964254402989942404875783 / 1000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y2YV1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y2YV1_rounded_endpoints.1
  have hhi : (manuscriptCase2Y2YV1Interval.2 : ℝ) ≤ ((-323551096443869642483910234445125949991 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y2YV1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y2YV1_exact_interval.1, manuscriptCase2Y2YV1_exact_interval.2.trans hhi⟩

def manuscriptCase2Y2YV2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-1272699 / 50000000) (0 / 1) (1) (0) (2625820365202423204201 / 1953125000000000000000) (0 / 1)

private theorem manuscriptCase2Y2YV2_arg_eq : barrierCase2Y2YV2LogArg = barrierComplex (51242759149 / 31250000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y2YV2LogArg, Case2PointData.Y2, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y2YV2_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2) = barrierComplex (-1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y2YV2_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y2 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc (manuscriptCase2Y2YV2Interval.1 : ℝ) (manuscriptCase2Y2YV2Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2) * Complex.log barrierCase2Y2YV2LogArg).re ∈ _
  rw [manuscriptCase2Y2YV2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-1272699 / 50000000) (0 / 1)
    barrierCase2Y2YV2LogArg (1) (0) (2625820365202423204201 / 1953125000000000000000) (51242759149 / 31250000000) (0 / 1)
  have hratio : ((0 / 1) / (51242759149 / 31250000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y2YV2Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y2YV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y2YV2_rounded_endpoints :
    (-15735489660927325025079778431348337599 / 1250000000000000000000000000000000000000) ≤ manuscriptCase2Y2YV2Interval.1 ∧ manuscriptCase2Y2YV2Interval.2 ≤ (-125883917287418600183450436127228257533 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y2YV2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y2YV2_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y2 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc ((-15735489660927325025079778431348337599 / 1250000000000000000000000000000000000000) : ℝ) ((-125883917287418600183450436127228257533 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-15735489660927325025079778431348337599 / 1250000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y2YV2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y2YV2_rounded_endpoints.1
  have hhi : (manuscriptCase2Y2YV2Interval.2 : ℝ) ≤ ((-125883917287418600183450436127228257533 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y2YV2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y2YV2_exact_interval.1, manuscriptCase2Y2YV2_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
