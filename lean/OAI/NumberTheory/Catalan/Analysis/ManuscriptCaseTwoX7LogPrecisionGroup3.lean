import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX7

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2X7XV3Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2466317 / 50000000) (0 / 1) (0) (0) (14314987605629857478409 / 10000000000000000000000) (0 / 1)

private theorem manuscriptCase2X7XV3_arg_eq : barrierCase2X7XV3LogArg = barrierComplex (119645257347 / 100000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X7XV3LogArg, Case2PointData.X7, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X7XV3_weight_eq : (barrierV2Tail.getD 3 (0, 0)).2 = barrierComplex (-2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X7XV3_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X7 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc (manuscriptCase2X7XV3Interval.1 : ℝ) (manuscriptCase2X7XV3Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2X7XV3LogArg).re ∈ _
  rw [manuscriptCase2X7XV3_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2466317 / 50000000) (0 / 1)
    barrierCase2X7XV3LogArg (0) (0) (14314987605629857478409 / 10000000000000000000000) (119645257347 / 100000000000) (0 / 1)
  have hratio : ((0 / 1) / (119645257347 / 100000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X7XV3Interval
  apply h
  all_goals
    try rw [manuscriptCase2X7XV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X7XV3_rounded_endpoints :
    (-8847221168686862393383148987812579281 / 1000000000000000000000000000000000000000) ≤ manuscriptCase2X7XV3Interval.1 ∧ manuscriptCase2X7XV3Interval.2 ≤ (-88472211686868623933831489875857611289 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X7XV3Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X7XV3_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X7 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc ((-8847221168686862393383148987812579281 / 1000000000000000000000000000000000000000) : ℝ) ((-88472211686868623933831489875857611289 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-8847221168686862393383148987812579281 / 1000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X7XV3Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X7XV3_rounded_endpoints.1
  have hhi : (manuscriptCase2X7XV3Interval.2 : ℝ) ≤ ((-88472211686868623933831489875857611289 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X7XV3_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X7XV3_exact_interval.1, manuscriptCase2X7XV3_exact_interval.2.trans hhi⟩

def manuscriptCase2X7XV4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (11618157 / 100000000) (0 / 1) (0) (0) (565770528614806824905401 / 390625000000000000000000) (0 / 1)

private theorem manuscriptCase2X7XV4_arg_eq : barrierCase2X7XV4LogArg = barrierComplex (752177192299 / 625000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X7XV4LogArg, Case2PointData.X7, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X7XV4_weight_eq : (barrierV2Tail.getD 4 (0, 0)).2 = barrierComplex (11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X7XV4_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X7 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc (manuscriptCase2X7XV4Interval.1 : ℝ) (manuscriptCase2X7XV4Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X7XV4LogArg).re ∈ _
  rw [manuscriptCase2X7XV4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (11618157 / 100000000) (0 / 1)
    barrierCase2X7XV4LogArg (0) (0) (565770528614806824905401 / 390625000000000000000000) (752177192299 / 625000000000) (0 / 1)
  have hratio : ((0 / 1) / (752177192299 / 625000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X7XV4Interval
  apply h
  all_goals
    try rw [manuscriptCase2X7XV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X7XV4_rounded_endpoints :
    (215191822889474952980661111606878759557 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X7XV4Interval.1 ∧ manuscriptCase2X7XV4Interval.2 ≤ (107595911444737476490330555812007713903 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X7XV4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X7XV4_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X7 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc ((215191822889474952980661111606878759557 / 10000000000000000000000000000000000000000) : ℝ) ((107595911444737476490330555812007713903 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((215191822889474952980661111606878759557 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X7XV4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X7XV4_rounded_endpoints.1
  have hhi : (manuscriptCase2X7XV4Interval.2 : ℝ) ≤ ((107595911444737476490330555812007713903 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X7XV4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X7XV4_exact_interval.1, manuscriptCase2X7XV4_exact_interval.2.trans hhi⟩

def manuscriptCase2X7XV5Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (13619357 / 100000000) (600749 / 3125000) (0) (0) (64126063332979538018449 / 62500000000000000000000) (40324475607 / 250000000000)

private theorem manuscriptCase2X7XV5_arg_eq : barrierCase2X7XV5LogArg = barrierComplex (1 / 1) (40324475607 / 250000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X7XV5LogArg, Case2PointData.X7, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X7XV5_weight_eq : (barrierV2Tail.getD 5 (0, 0)).2 = barrierComplex (13619357 / 100000000) (600749 / 3125000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X7XV5_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X7 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc (manuscriptCase2X7XV5Interval.1 : ℝ) (manuscriptCase2X7XV5Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2X7XV5LogArg).re ∈ _
  rw [manuscriptCase2X7XV5_weight_eq]
  have h := manuscript_weighted_complex_log_interval (13619357 / 100000000) (600749 / 3125000)
    barrierCase2X7XV5LogArg (0) (0) (64126063332979538018449 / 62500000000000000000000) (1 / 1) (40324475607 / 250000000000)
  have hratio : ((40324475607 / 250000000000) / (1 / 1) : ℚ) = (40324475607 / 250000000000) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X7XV5Interval
  apply h
  all_goals
    try rw [manuscriptCase2X7XV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X7XV5_rounded_endpoints :
    (-289940476072594936013106884405614652337 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X7XV5Interval.1 ∧ manuscriptCase2X7XV5Interval.2 ≤ (-18121279754537183500819180275350915771 / 625000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X7XV5Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X7XV5_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X7 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc ((-289940476072594936013106884405614652337 / 10000000000000000000000000000000000000000) : ℝ) ((-18121279754537183500819180275350915771 / 625000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-289940476072594936013106884405614652337 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X7XV5Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X7XV5_rounded_endpoints.1
  have hhi : (manuscriptCase2X7XV5Interval.2 : ℝ) ≤ ((-18121279754537183500819180275350915771 / 625000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X7XV5_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X7XV5_exact_interval.1, manuscriptCase2X7XV5_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
