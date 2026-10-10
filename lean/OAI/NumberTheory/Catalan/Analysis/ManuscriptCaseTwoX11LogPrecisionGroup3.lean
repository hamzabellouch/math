import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX11

namespace OAI

noncomputable section
namespace InternalCatalan

def manuscriptCase2X11XV3Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2466317 / 50000000) (0 / 1) (-2) (0) (1208335060494963868401 / 625000000000000000000) (0 / 1)

private theorem manuscriptCase2X11XV3_arg_eq : barrierCase2X11XV3LogArg = barrierComplex (34761114201 / 50000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X11XV3LogArg, Case2PointData.X11, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X11XV3_weight_eq : (barrierV2Tail.getD 3 (0, 0)).2 = barrierComplex (-2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X11XV3_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X11 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc (manuscriptCase2X11XV3Interval.1 : ℝ) (manuscriptCase2X11XV3Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2X11XV3LogArg).re ∈ _
  rw [manuscriptCase2X11XV3_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2466317 / 50000000) (0 / 1)
    barrierCase2X11XV3LogArg (-2) (0) (1208335060494963868401 / 625000000000000000000) (34761114201 / 50000000000) (0 / 1)
  have hratio : ((0 / 1) / (34761114201 / 50000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X11XV3Interval
  apply h
  all_goals
    try rw [manuscriptCase2X11XV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X11XV3_rounded_endpoints :
    (179312912285148015664921231648392343827 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X11XV3Interval.1 ∧ manuscriptCase2X11XV3Interval.2 ≤ (179312912285148015737428304369589003403 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X11XV3Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X11XV3_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X11 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc ((179312912285148015664921231648392343827 / 10000000000000000000000000000000000000000) : ℝ) ((179312912285148015737428304369589003403 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((179312912285148015664921231648392343827 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X11XV3Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X11XV3_rounded_endpoints.1
  have hhi : (manuscriptCase2X11XV3Interval.2 : ℝ) ≤ ((179312912285148015737428304369589003403 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X11XV3_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X11XV3_exact_interval.1, manuscriptCase2X11XV3_exact_interval.2.trans hhi⟩

def manuscriptCase2X11XV4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (11618157 / 100000000) (0 / 1) (-2) (0) (45731080707398984390689 / 24414062500000000000000) (0 / 1)

private theorem manuscriptCase2X11XV4_arg_eq : barrierCase2X11XV4LogArg = barrierComplex (213848265617 / 312500000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X11XV4LogArg, Case2PointData.X11, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X11XV4_weight_eq : (barrierV2Tail.getD 4 (0, 0)).2 = barrierComplex (11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X11XV4_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X11 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc (manuscriptCase2X11XV4Interval.1 : ℝ) (manuscriptCase2X11XV4Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X11XV4LogArg).re ∈ _
  rw [manuscriptCase2X11XV4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (11618157 / 100000000) (0 / 1)
    barrierCase2X11XV4LogArg (-2) (0) (45731080707398984390689 / 24414062500000000000000) (213848265617 / 312500000000) (0 / 1)
  have hratio : ((0 / 1) / (213848265617 / 312500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X11XV4Interval
  apply h
  all_goals
    try rw [manuscriptCase2X11XV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X11XV4_rounded_endpoints :
    (-220360273764132466481397855146198899807 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2X11XV4Interval.1 ∧ manuscriptCase2X11XV4Interval.2 ≤ (-55090068441033116600422596229986728989 / 1250000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X11XV4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X11XV4_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X11 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc ((-220360273764132466481397855146198899807 / 5000000000000000000000000000000000000000) : ℝ) ((-55090068441033116600422596229986728989 / 1250000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-220360273764132466481397855146198899807 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X11XV4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X11XV4_rounded_endpoints.1
  have hhi : (manuscriptCase2X11XV4Interval.2 : ℝ) ≤ ((-55090068441033116600422596229986728989 / 1250000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X11XV4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X11XV4_exact_interval.1, manuscriptCase2X11XV4_exact_interval.2.trans hhi⟩

def manuscriptCase2X11XV5Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (13619357 / 100000000) (600749 / 3125000) (0) (0) (16603427027813684331961 / 15625000000000000000000) (-31279818219 / 125000000000)

private theorem manuscriptCase2X11XV5_arg_eq : barrierCase2X11XV5LogArg = barrierComplex (1 / 1) (-31279818219 / 125000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X11XV5LogArg, Case2PointData.X11, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X11XV5_weight_eq : (barrierV2Tail.getD 5 (0, 0)).2 = barrierComplex (13619357 / 100000000) (600749 / 3125000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X11XV5_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X11 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc (manuscriptCase2X11XV5Interval.1 : ℝ) (manuscriptCase2X11XV5Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2X11XV5LogArg).re ∈ _
  rw [manuscriptCase2X11XV5_weight_eq]
  have h := manuscript_weighted_complex_log_interval (13619357 / 100000000) (600749 / 3125000)
    barrierCase2X11XV5LogArg (0) (0) (16603427027813684331961 / 15625000000000000000000) (1 / 1) (-31279818219 / 125000000000)
  have hratio : ((-31279818219 / 125000000000) / (1 / 1) : ℚ) = (-31279818219 / 125000000000) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X11XV5Interval
  apply h
  all_goals
    try rw [manuscriptCase2X11XV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X11XV5_rounded_endpoints :
    (512737671992324102452779261863737132299 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X11XV5Interval.1 ∧ manuscriptCase2X11XV5Interval.2 ≤ (12818441799808102561319481546596671279 / 250000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X11XV5Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X11XV5_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X11 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc ((512737671992324102452779261863737132299 / 10000000000000000000000000000000000000000) : ℝ) ((12818441799808102561319481546596671279 / 250000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((512737671992324102452779261863737132299 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X11XV5Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X11XV5_rounded_endpoints.1
  have hhi : (manuscriptCase2X11XV5Interval.2 : ℝ) ≤ ((12818441799808102561319481546596671279 / 250000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X11XV5_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X11XV5_exact_interval.1, manuscriptCase2X11XV5_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
