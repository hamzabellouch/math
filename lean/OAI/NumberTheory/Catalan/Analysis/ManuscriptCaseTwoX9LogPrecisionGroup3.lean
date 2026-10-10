import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX9

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2X9XV3Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2466317 / 50000000) (0 / 1) (-1) (0) (7301103236236066414921 / 5000000000000000000000) (0 / 1)

private theorem manuscriptCase2X9XV3_arg_eq : barrierCase2X9XV3LogArg = barrierComplex (85446493411 / 100000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X9XV3LogArg, Case2PointData.X9, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X9XV3_weight_eq : (barrierV2Tail.getD 3 (0, 0)).2 = barrierComplex (-2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X9XV3_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X9 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc (manuscriptCase2X9XV3Interval.1 : ℝ) (manuscriptCase2X9XV3Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2X9XV3LogArg).re ∈ _
  rw [manuscriptCase2X9XV3_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2466317 / 50000000) (0 / 1)
    barrierCase2X9XV3LogArg (-1) (0) (7301103236236066414921 / 5000000000000000000000) (85446493411 / 100000000000) (0 / 1)
  have hratio : ((0 / 1) / (85446493411 / 100000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X9XV3Interval
  apply h
  all_goals
    try rw [manuscriptCase2X9XV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X9XV3_rounded_endpoints :
    (38790187903355671812332951631683476397 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2X9XV3Interval.1 ∧ manuscriptCase2X9XV3Interval.2 ≤ (15516075161342268731594699512058377691 / 2000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X9XV3Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X9XV3_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X9 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc ((38790187903355671812332951631683476397 / 5000000000000000000000000000000000000000) : ℝ) ((15516075161342268731594699512058377691 / 2000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((38790187903355671812332951631683476397 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X9XV3Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X9XV3_rounded_endpoints.1
  have hhi : (manuscriptCase2X9XV3Interval.2 : ℝ) ≤ ((15516075161342268731594699512058377691 / 2000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X9XV3_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X9XV3_exact_interval.1, manuscriptCase2X9XV3_exact_interval.2.trans hhi⟩

def manuscriptCase2X9XV4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (11618157 / 100000000) (0 / 1) (-1) (0) (281732922368131298590969 / 195312500000000000000000) (0 / 1)

private theorem manuscriptCase2X9XV4_arg_eq : barrierCase2X9XV4LogArg = barrierComplex (530785194187 / 625000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X9XV4LogArg, Case2PointData.X9, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X9XV4_weight_eq : (barrierV2Tail.getD 4 (0, 0)).2 = barrierComplex (11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X9XV4_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X9 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc (manuscriptCase2X9XV4Interval.1 : ℝ) (manuscriptCase2X9XV4Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X9XV4LogArg).re ∈ _
  rw [manuscriptCase2X9XV4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (11618157 / 100000000) (0 / 1)
    barrierCase2X9XV4LogArg (-1) (0) (281732922368131298590969 / 195312500000000000000000) (530785194187 / 625000000000) (0 / 1)
  have hratio : ((0 / 1) / (530785194187 / 625000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X9XV4Interval
  apply h
  all_goals
    try rw [manuscriptCase2X9XV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X9XV4_rounded_endpoints :
    (-37966798910704197284881347367388534941 / 2000000000000000000000000000000000000000) ≤ manuscriptCase2X9XV4Interval.1 ∧ manuscriptCase2X9XV4Interval.2 ≤ (-37966798910704197269191034252542021331 / 2000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X9XV4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X9XV4_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X9 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc ((-37966798910704197284881347367388534941 / 2000000000000000000000000000000000000000) : ℝ) ((-37966798910704197269191034252542021331 / 2000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-37966798910704197284881347367388534941 / 2000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X9XV4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X9XV4_rounded_endpoints.1
  have hhi : (manuscriptCase2X9XV4Interval.2 : ℝ) ≤ ((-37966798910704197269191034252542021331 / 2000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X9XV4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X9XV4_exact_interval.1, manuscriptCase2X9XV4_exact_interval.2.trans hhi⟩

def manuscriptCase2X9XV5Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (13619357 / 100000000) (600749 / 3125000) (0) (0) (63392395364789077609681 / 62500000000000000000000) (-29872987209 / 250000000000)

private theorem manuscriptCase2X9XV5_arg_eq : barrierCase2X9XV5LogArg = barrierComplex (1 / 1) (-29872987209 / 250000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X9XV5LogArg, Case2PointData.X9, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X9XV5_weight_eq : (barrierV2Tail.getD 5 (0, 0)).2 = barrierComplex (13619357 / 100000000) (600749 / 3125000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X9XV5_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X9 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc (manuscriptCase2X9XV5Interval.1 : ℝ) (manuscriptCase2X9XV5Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2X9XV5LogArg).re ∈ _
  rw [manuscriptCase2X9XV5_weight_eq]
  have h := manuscript_weighted_complex_log_interval (13619357 / 100000000) (600749 / 3125000)
    barrierCase2X9XV5LogArg (0) (0) (63392395364789077609681 / 62500000000000000000000) (1 / 1) (-29872987209 / 250000000000)
  have hratio : ((-29872987209 / 250000000000) / (1 / 1) : ℚ) = (-29872987209 / 250000000000) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X9XV5Interval
  apply h
  all_goals
    try rw [manuscriptCase2X9XV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X9XV5_rounded_endpoints :
    (47656247182380850296837880622143248981 / 2000000000000000000000000000000000000000) ≤ manuscriptCase2X9XV5Interval.1 ∧ manuscriptCase2X9XV5Interval.2 ≤ (119140617955952125742094701555358122453 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X9XV5Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X9XV5_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X9 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc ((47656247182380850296837880622143248981 / 2000000000000000000000000000000000000000) : ℝ) ((119140617955952125742094701555358122453 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((47656247182380850296837880622143248981 / 2000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X9XV5Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X9XV5_rounded_endpoints.1
  have hhi : (manuscriptCase2X9XV5Interval.2 : ℝ) ≤ ((119140617955952125742094701555358122453 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X9XV5_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X9XV5_exact_interval.1, manuscriptCase2X9XV5_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
