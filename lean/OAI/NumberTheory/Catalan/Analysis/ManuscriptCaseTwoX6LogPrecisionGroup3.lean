import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX6

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2X6XV3Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2466317 / 50000000) (0 / 1) (0) (0) (16778969885689792680769 / 10000000000000000000000) (0 / 1)

private theorem manuscriptCase2X6XV3_arg_eq : barrierCase2X6XV3LogArg = barrierComplex (129533663137 / 100000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X6XV3LogArg, Case2PointData.X6, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X6XV3_weight_eq : (barrierV2Tail.getD 3 (0, 0)).2 = barrierComplex (-2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X6XV3_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X6 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc (manuscriptCase2X6XV3Interval.1 : ℝ) (manuscriptCase2X6XV3Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2X6XV3LogArg).re ∈ _
  rw [manuscriptCase2X6XV3_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2466317 / 50000000) (0 / 1)
    barrierCase2X6XV3LogArg (0) (0) (16778969885689792680769 / 10000000000000000000000) (129533663137 / 100000000000) (0 / 1)
  have hratio : ((0 / 1) / (129533663137 / 100000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X6XV3Interval
  apply h
  all_goals
    try rw [manuscriptCase2X6XV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X6XV3_rounded_endpoints :
    (-5105682804284712947746093880569505731 / 400000000000000000000000000000000000000) ≤ manuscriptCase2X6XV3Interval.1 ∧ manuscriptCase2X6XV3Interval.2 ≤ (-63821035053558911846825574690812776341 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X6XV3Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X6XV3_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X6 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc ((-5105682804284712947746093880569505731 / 400000000000000000000000000000000000000) : ℝ) ((-63821035053558911846825574690812776341 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-5105682804284712947746093880569505731 / 400000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X6XV3Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X6XV3_rounded_endpoints.1
  have hhi : (manuscriptCase2X6XV3Interval.2 : ℝ) ≤ ((-63821035053558911846825574690812776341 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X6XV3_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X6XV3_exact_interval.1, manuscriptCase2X6XV3_exact_interval.2.trans hhi⟩

def manuscriptCase2X6XV4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (11618157 / 100000000) (0 / 1) (0) (0) (666168742159633028995441 / 390625000000000000000000) (0 / 1)

private theorem manuscriptCase2X6XV4_arg_eq : barrierCase2X6XV4LogArg = barrierComplex (816191608729 / 625000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X6XV4LogArg, Case2PointData.X6, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X6XV4_weight_eq : (barrierV2Tail.getD 4 (0, 0)).2 = barrierComplex (11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X6XV4_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X6 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc (manuscriptCase2X6XV4Interval.1 : ℝ) (manuscriptCase2X6XV4Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X6XV4LogArg).re ∈ _
  rw [manuscriptCase2X6XV4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (11618157 / 100000000) (0 / 1)
    barrierCase2X6XV4LogArg (0) (0) (666168742159633028995441 / 390625000000000000000000) (816191608729 / 625000000000) (0 / 1)
  have hratio : ((0 / 1) / (816191608729 / 625000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X6XV4Interval
  apply h
  all_goals
    try rw [manuscriptCase2X6XV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X6XV4_rounded_endpoints :
    (310085696823787195534541985059122760213 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X6XV4Interval.1 ∧ manuscriptCase2X6XV4Interval.2 ≤ (38760712102973399441818804544897622587 / 1250000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X6XV4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X6XV4_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X6 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc ((310085696823787195534541985059122760213 / 10000000000000000000000000000000000000000) : ℝ) ((38760712102973399441818804544897622587 / 1250000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((310085696823787195534541985059122760213 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X6XV4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X6XV4_rounded_endpoints.1
  have hhi : (manuscriptCase2X6XV4Interval.2 : ℝ) ≤ ((38760712102973399441818804544897622587 / 1250000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X6XV4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X6XV4_exact_interval.1, manuscriptCase2X6XV4_exact_interval.2.trans hhi⟩

def manuscriptCase2X6XV5Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (13619357 / 100000000) (600749 / 3125000) (0) (0) (66174994099331785782409 / 62500000000000000000000) (60621729597 / 250000000000)

private theorem manuscriptCase2X6XV5_arg_eq : barrierCase2X6XV5LogArg = barrierComplex (1 / 1) (60621729597 / 250000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X6XV5LogArg, Case2PointData.X6, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X6XV5_weight_eq : (barrierV2Tail.getD 5 (0, 0)).2 = barrierComplex (13619357 / 100000000) (600749 / 3125000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X6XV5_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X6 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc (manuscriptCase2X6XV5Interval.1 : ℝ) (manuscriptCase2X6XV5Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2X6XV5LogArg).re ∈ _
  rw [manuscriptCase2X6XV5_weight_eq]
  have h := manuscript_weighted_complex_log_interval (13619357 / 100000000) (600749 / 3125000)
    barrierCase2X6XV5LogArg (0) (0) (66174994099331785782409 / 62500000000000000000000) (1 / 1) (60621729597 / 250000000000)
  have hratio : ((60621729597 / 250000000000) / (1 / 1) : ℚ) = (60621729597 / 250000000000) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X6XV5Interval
  apply h
  all_goals
    try rw [manuscriptCase2X6XV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X6XV5_rounded_endpoints :
    (-209210487828622224813571426358651288197 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2X6XV5Interval.1 ∧ manuscriptCase2X6XV5Interval.2 ≤ (-104605243914311112406785713179318704819 / 2500000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X6XV5Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X6XV5_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X6 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc ((-209210487828622224813571426358651288197 / 5000000000000000000000000000000000000000) : ℝ) ((-104605243914311112406785713179318704819 / 2500000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-209210487828622224813571426358651288197 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X6XV5Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X6XV5_rounded_endpoints.1
  have hhi : (manuscriptCase2X6XV5Interval.2 : ℝ) ≤ ((-104605243914311112406785713179318704819 / 2500000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X6XV5_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X6XV5_exact_interval.1, manuscriptCase2X6XV5_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
