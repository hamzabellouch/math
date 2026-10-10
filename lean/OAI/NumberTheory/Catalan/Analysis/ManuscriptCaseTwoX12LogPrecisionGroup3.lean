import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX12

namespace OAI

noncomputable section
namespace InternalCatalan

def manuscriptCase2X12XV3Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2466317 / 50000000) (0 / 1) (-2) (0) (13632601238342887806769 / 10000000000000000000000) (0 / 1)

private theorem manuscriptCase2X12XV3_arg_eq : barrierCase2X12XV3LogArg = barrierComplex (116758730887 / 200000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X12XV3LogArg, Case2PointData.X12, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X12XV3_weight_eq : (barrierV2Tail.getD 3 (0, 0)).2 = barrierComplex (-2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X12XV3_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X12 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc (manuscriptCase2X12XV3Interval.1 : ℝ) (manuscriptCase2X12XV3Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2X12XV3LogArg).re ∈ _
  rw [manuscriptCase2X12XV3_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2466317 / 50000000) (0 / 1)
    barrierCase2X12XV3LogArg (-2) (0) (13632601238342887806769 / 10000000000000000000000) (116758730887 / 200000000000) (0 / 1)
  have hratio : ((0 / 1) / (116758730887 / 200000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X12XV3Interval
  apply h
  all_goals
    try rw [manuscriptCase2X12XV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X12XV3_rounded_endpoints :
    (66369538773460415170889318297709251143 / 2500000000000000000000000000000000000000) ≤ manuscriptCase2X12XV3Interval.1 ∧ manuscriptCase2X12XV3Interval.2 ≤ (265478155093841660750172461752702914299 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X12XV3Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X12XV3_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X12 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc ((66369538773460415170889318297709251143 / 2500000000000000000000000000000000000000) : ℝ) ((265478155093841660750172461752702914299 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((66369538773460415170889318297709251143 / 2500000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X12XV3Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X12XV3_rounded_endpoints.1
  have hhi : (manuscriptCase2X12XV3Interval.2 : ℝ) ≤ ((265478155093841660750172461752702914299 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X12XV3_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X12XV3_exact_interval.1, manuscriptCase2X12XV3_exact_interval.2.trans hhi⟩

def manuscriptCase2X12XV4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (11618157 / 100000000) (0 / 1) (-2) (0) (505694940460991273209441 / 390625000000000000000000) (0 / 1)

private theorem manuscriptCase2X12XV4_arg_eq : barrierCase2X12XV4LogArg = barrierComplex (711122310479 / 1250000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X12XV4LogArg, Case2PointData.X12, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X12XV4_weight_eq : (barrierV2Tail.getD 4 (0, 0)).2 = barrierComplex (11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X12XV4_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X12 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc (manuscriptCase2X12XV4Interval.1 : ℝ) (manuscriptCase2X12XV4Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X12XV4LogArg).re ∈ _
  rw [manuscriptCase2X12XV4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (11618157 / 100000000) (0 / 1)
    barrierCase2X12XV4LogArg (-2) (0) (505694940460991273209441 / 390625000000000000000000) (711122310479 / 1250000000000) (0 / 1)
  have hratio : ((0 / 1) / (711122310479 / 1250000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X12XV4Interval
  apply h
  all_goals
    try rw [manuscriptCase2X12XV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X12XV4_rounded_endpoints :
    (-327663622570004534969172871693879640387 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2X12XV4Interval.1 ∧ manuscriptCase2X12XV4Interval.2 ≤ (-32766362257000453489072130613111600073 / 500000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X12XV4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X12XV4_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X12 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc ((-327663622570004534969172871693879640387 / 5000000000000000000000000000000000000000) : ℝ) ((-32766362257000453489072130613111600073 / 500000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-327663622570004534969172871693879640387 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X12XV4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X12XV4_rounded_endpoints.1
  have hhi : (manuscriptCase2X12XV4Interval.2 : ℝ) ≤ ((-32766362257000453489072130613111600073 / 500000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X12XV4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X12XV4_exact_interval.1, manuscriptCase2X12XV4_exact_interval.2.trans hhi⟩

def manuscriptCase2X12XV5Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (13619357 / 100000000) (600749 / 3125000) (0) (-1) (279194389506561585468409 / 250000000000000000000000) (329136342347 / 670863657653)

private theorem manuscriptCase2X12XV5_arg_eq : barrierCase2X12XV5LogArg = barrierComplex (1 / 1) (-170863657653 / 500000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X12XV5LogArg, Case2PointData.X12, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X12XV5_weight_eq : (barrierV2Tail.getD 5 (0, 0)).2 = barrierComplex (13619357 / 100000000) (600749 / 3125000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X12XV5_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X12 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc (manuscriptCase2X12XV5Interval.1 : ℝ) (manuscriptCase2X12XV5Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2X12XV5LogArg).re ∈ _
  rw [manuscriptCase2X12XV5_weight_eq]
  have h := manuscript_weighted_complex_log_interval (13619357 / 100000000) (600749 / 3125000)
    barrierCase2X12XV5LogArg (0) (-1) (279194389506561585468409 / 250000000000000000000000) (670863657653 / 500000000000) (329136342347 / 500000000000)
  have hratio : ((329136342347 / 500000000000) / (670863657653 / 500000000000) : ℚ) = (329136342347 / 670863657653) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X12XV5Interval
  apply h
  all_goals
    try rw [manuscriptCase2X12XV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X12XV5_rounded_endpoints :
    (8852868623431266374048344861170765389 / 125000000000000000000000000000000000000) ≤ manuscriptCase2X12XV5Interval.1 ∧ manuscriptCase2X12XV5Interval.2 ≤ (141645897974900281431243457566168347107 / 2000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X12XV5Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X12XV5_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X12 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc ((8852868623431266374048344861170765389 / 125000000000000000000000000000000000000) : ℝ) ((141645897974900281431243457566168347107 / 2000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((8852868623431266374048344861170765389 / 125000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X12XV5Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X12XV5_rounded_endpoints.1
  have hhi : (manuscriptCase2X12XV5Interval.2 : ℝ) ≤ ((141645897974900281431243457566168347107 / 2000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X12XV5_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X12XV5_exact_interval.1, manuscriptCase2X12XV5_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
