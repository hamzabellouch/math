import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX16

namespace OAI

noncomputable section
namespace InternalCatalan

def manuscriptCase2X16XV3Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2466317 / 50000000) (0 / 1) (-7) (0) (32149816516672034041 / 19531250000000000000) (0 / 1)

private theorem manuscriptCase2X16XV3_arg_eq : barrierCase2X16XV3LogArg = barrierComplex (5670080821 / 50000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X16XV3LogArg, Case2PointData.X16, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X16XV3_weight_eq : (barrierV2Tail.getD 3 (0, 0)).2 = barrierComplex (-2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X16XV3_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X16 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc (manuscriptCase2X16XV3Interval.1 : ℝ) (manuscriptCase2X16XV3Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2X16XV3LogArg).re ∈ _
  rw [manuscriptCase2X16XV3_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2466317 / 50000000) (0 / 1)
    barrierCase2X16XV3LogArg (-7) (0) (32149816516672034041 / 19531250000000000000) (5670080821 / 50000000000) (0 / 1)
  have hratio : ((0 / 1) / (5670080821 / 50000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X16XV3Interval
  apply h
  all_goals
    try rw [manuscriptCase2X16XV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X16XV3_rounded_endpoints :
    (536872726839355492201544351567779540671 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2X16XV3Interval.1 ∧ manuscriptCase2X16XV3Interval.2 ≤ (1073745453678710984636242176198448615729 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X16XV3Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X16XV3_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X16 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc ((536872726839355492201544351567779540671 / 5000000000000000000000000000000000000000) : ℝ) ((1073745453678710984636242176198448615729 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((536872726839355492201544351567779540671 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X16XV3Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X16XV3_rounded_endpoints.1
  have hhi : (manuscriptCase2X16XV3Interval.2 : ℝ) ≤ ((1073745453678710984636242176198448615729 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X16XV3_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X16XV3_exact_interval.1, manuscriptCase2X16XV3_exact_interval.2.trans hhi⟩

def manuscriptCase2X16XV4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (11618157 / 100000000) (0 / 1) (-8) (0) (651377698512344052649 / 381469726562500000000) (0 / 1)

private theorem manuscriptCase2X16XV4_arg_eq : barrierCase2X16XV4LogArg = barrierComplex (25522102157 / 312500000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X16XV4LogArg, Case2PointData.X16, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X16XV4_weight_eq : (barrierV2Tail.getD 4 (0, 0)).2 = barrierComplex (11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X16XV4_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X16 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc (manuscriptCase2X16XV4Interval.1 : ℝ) (manuscriptCase2X16XV4Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X16XV4LogArg).re ∈ _
  rw [manuscriptCase2X16XV4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (11618157 / 100000000) (0 / 1)
    barrierCase2X16XV4LogArg (-8) (0) (651377698512344052649 / 381469726562500000000) (25522102157 / 312500000000) (0 / 1)
  have hratio : ((0 / 1) / (25522102157 / 312500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X16XV4Interval
  apply h
  all_goals
    try rw [manuscriptCase2X16XV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X16XV4_rounded_endpoints :
    (-727604405136666125397077995867209396471 / 2500000000000000000000000000000000000000) ≤ manuscriptCase2X16XV4Interval.1 ∧ manuscriptCase2X16XV4Interval.2 ≤ (-727604405136666125240172567334765060549 / 2500000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X16XV4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X16XV4_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X16 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc ((-727604405136666125397077995867209396471 / 2500000000000000000000000000000000000000) : ℝ) ((-727604405136666125240172567334765060549 / 2500000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-727604405136666125397077995867209396471 / 2500000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X16XV4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X16XV4_rounded_endpoints.1
  have hhi : (manuscriptCase2X16XV4Interval.2 : ℝ) ≤ ((-727604405136666125240172567334765060549 / 2500000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X16XV4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X16XV4_exact_interval.1, manuscriptCase2X16XV4_exact_interval.2.trans hhi⟩

def manuscriptCase2X16XV5Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (13619357 / 100000000) (600749 / 3125000) (0) (-1) (23904724592930078016001 / 15625000000000000000000) (34007008001 / 215992991999)

private theorem manuscriptCase2X16XV5_arg_eq : barrierCase2X16XV5LogArg = barrierComplex (1 / 1) (-90992991999 / 125000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X16XV5LogArg, Case2PointData.X16, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X16XV5_weight_eq : (barrierV2Tail.getD 5 (0, 0)).2 = barrierComplex (13619357 / 100000000) (600749 / 3125000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X16XV5_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X16 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc (manuscriptCase2X16XV5Interval.1 : ℝ) (manuscriptCase2X16XV5Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2X16XV5LogArg).re ∈ _
  rw [manuscriptCase2X16XV5_weight_eq]
  have h := manuscript_weighted_complex_log_interval (13619357 / 100000000) (600749 / 3125000)
    barrierCase2X16XV5LogArg (0) (-1) (23904724592930078016001 / 15625000000000000000000) (215992991999 / 125000000000) (34007008001 / 125000000000)
  have hratio : ((34007008001 / 125000000000) / (215992991999 / 125000000000) : ℚ) = (34007008001 / 215992991999) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X16XV5Interval
  apply h
  all_goals
    try rw [manuscriptCase2X16XV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X16XV5_rounded_endpoints :
    (1499189847625779713126923134985916367951 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X16XV5Interval.1 ∧ manuscriptCase2X16XV5Interval.2 ≤ (1499189847625779782817998888002818970037 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X16XV5Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X16XV5_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X16 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc ((1499189847625779713126923134985916367951 / 10000000000000000000000000000000000000000) : ℝ) ((1499189847625779782817998888002818970037 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((1499189847625779713126923134985916367951 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X16XV5Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X16XV5_rounded_endpoints.1
  have hhi : (manuscriptCase2X16XV5Interval.2 : ℝ) ≤ ((1499189847625779782817998888002818970037 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X16XV5_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X16XV5_exact_interval.1, manuscriptCase2X16XV5_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
