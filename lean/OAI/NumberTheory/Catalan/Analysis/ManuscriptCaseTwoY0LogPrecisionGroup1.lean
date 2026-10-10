import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointY0

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2Y0YV3Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (2466317 / 50000000) (0 / 1) (1) (0) (8732748005592198971161 / 5000000000000000000000) (0 / 1)

private theorem manuscriptCase2Y0YV3_arg_eq : barrierCase2Y0YV3LogArg = barrierComplex (93449173381 / 50000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y0YV3LogArg, Case2PointData.Y0, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y0YV3_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2) = barrierComplex (2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y0YV3_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y0 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc (manuscriptCase2Y0YV3Interval.1 : ℝ) (manuscriptCase2Y0YV3Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2) * Complex.log barrierCase2Y0YV3LogArg).re ∈ _
  rw [manuscriptCase2Y0YV3_weight_eq]
  have h := manuscript_weighted_complex_log_interval (2466317 / 50000000) (0 / 1)
    barrierCase2Y0YV3LogArg (1) (0) (8732748005592198971161 / 5000000000000000000000) (93449173381 / 50000000000) (0 / 1)
  have hratio : ((0 / 1) / (93449173381 / 50000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y0YV3Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y0YV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y0YV3_rounded_endpoints :
    (154242153804507984428795202450284879773 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2Y0YV3Interval.1 ∧ manuscriptCase2Y0YV3Interval.2 ≤ (308484307609015968890914835468909113371 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y0YV3Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y0YV3_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y0 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc ((154242153804507984428795202450284879773 / 5000000000000000000000000000000000000000) : ℝ) ((308484307609015968890914835468909113371 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((154242153804507984428795202450284879773 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y0YV3Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y0YV3_rounded_endpoints.1
  have hhi : (manuscriptCase2Y0YV3Interval.2 : ℝ) ≤ ((308484307609015968890914835468909113371 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y0YV3_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y0YV3_exact_interval.1, manuscriptCase2Y0YV3_exact_interval.2.trans hhi⟩

def manuscriptCase2Y0YV4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-11618157 / 100000000) (0 / 1) (1) (0) (365095376500054610816329 / 195312500000000000000000) (0 / 1)

private theorem manuscriptCase2Y0YV4_arg_eq : barrierCase2Y0YV4LogArg = barrierComplex (604231227677 / 312500000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y0YV4LogArg, Case2PointData.Y0, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y0YV4_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2) = barrierComplex (-11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y0YV4_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y0 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc (manuscriptCase2Y0YV4Interval.1 : ℝ) (manuscriptCase2Y0YV4Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2) * Complex.log barrierCase2Y0YV4LogArg).re ∈ _
  rw [manuscriptCase2Y0YV4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-11618157 / 100000000) (0 / 1)
    barrierCase2Y0YV4LogArg (1) (0) (365095376500054610816329 / 195312500000000000000000) (604231227677 / 312500000000) (0 / 1)
  have hratio : ((0 / 1) / (604231227677 / 312500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y0YV4Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y0YV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y0YV4_rounded_endpoints :
    (-191511516581508373441636128884142834899 / 2500000000000000000000000000000000000000) ≤ manuscriptCase2Y0YV4Interval.1 ∧ manuscriptCase2Y0YV4Interval.2 ≤ (-766046066326033493685853378597240997163 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y0YV4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y0YV4_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y0 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc ((-191511516581508373441636128884142834899 / 2500000000000000000000000000000000000000) : ℝ) ((-766046066326033493685853378597240997163 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-191511516581508373441636128884142834899 / 2500000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y0YV4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y0YV4_rounded_endpoints.1
  have hhi : (manuscriptCase2Y0YV4Interval.2 : ℝ) ≤ ((-766046066326033493685853378597240997163 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y0YV4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y0YV4_exact_interval.1, manuscriptCase2Y0YV4_exact_interval.2.trans hhi⟩

def manuscriptCase2Y0YV5Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-13619357 / 100000000) (-600749 / 3125000) (-3) (0) (2407935099937449820321 / 1953125000000000000000) (-3439854639 / 48950000000)

private theorem manuscriptCase2Y0YV5_arg_eq : barrierCase2Y0YV5LogArg = barrierComplex (979 / 2500) (-3439854639 / 125000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2Y0YV5LogArg, Case2PointData.Y0, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y0YV5_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2) = barrierComplex (-13619357 / 100000000) (-600749 / 3125000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y0YV5_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y0 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc (manuscriptCase2Y0YV5Interval.1 : ℝ) (manuscriptCase2Y0YV5Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2) * Complex.log barrierCase2Y0YV5LogArg).re ∈ _
  rw [manuscriptCase2Y0YV5_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-13619357 / 100000000) (-600749 / 3125000)
    barrierCase2Y0YV5LogArg (-3) (0) (2407935099937449820321 / 1953125000000000000000) (979 / 2500) (-3439854639 / 125000000000)
  have hratio : ((-3439854639 / 125000000000) / (979 / 2500) : ℚ) = (-3439854639 / 48950000000) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y0YV5Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y0YV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y0YV5_rounded_endpoints :
    (284652307468121369866857066537073219489 / 2500000000000000000000000000000000000000) ≤ manuscriptCase2Y0YV5Interval.1 ∧ manuscriptCase2Y0YV5Interval.2 ≤ (1138609229872485479743322251384036470611 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y0YV5Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y0YV5_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y0 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc ((284652307468121369866857066537073219489 / 2500000000000000000000000000000000000000) : ℝ) ((1138609229872485479743322251384036470611 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((284652307468121369866857066537073219489 / 2500000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y0YV5Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y0YV5_rounded_endpoints.1
  have hhi : (manuscriptCase2Y0YV5Interval.2 : ℝ) ≤ ((1138609229872485479743322251384036470611 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y0YV5_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y0YV5_exact_interval.1, manuscriptCase2Y0YV5_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
