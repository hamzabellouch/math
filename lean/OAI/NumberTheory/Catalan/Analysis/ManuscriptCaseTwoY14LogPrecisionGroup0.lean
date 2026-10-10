import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointY14

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2Y14YV0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-15199211 / 100000000) (0 / 1) (3) (0) (25608754365265471401 / 19531250000000000000) (0 / 1)

private theorem manuscriptCase2Y14YV0_arg_eq : barrierCase2Y14YV0LogArg = barrierComplex (5060509299 / 1562500000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y14YV0LogArg, Case2PointData.Y14, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y14YV0_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2) = barrierComplex (-15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y14YV0_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y14 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc (manuscriptCase2Y14YV0Interval.1 : ℝ) (manuscriptCase2Y14YV0Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2) * Complex.log barrierCase2Y14YV0LogArg).re ∈ _
  rw [manuscriptCase2Y14YV0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-15199211 / 100000000) (0 / 1)
    barrierCase2Y14YV0LogArg (3) (0) (25608754365265471401 / 19531250000000000000) (5060509299 / 1562500000) (0 / 1)
  have hratio : ((0 / 1) / (5060509299 / 1562500000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y14YV0Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y14YV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y14YV0_rounded_endpoints :
    (-178618092022072057807746075563263233999 / 1000000000000000000000000000000000000000) ≤ manuscriptCase2Y14YV0Interval.1 ∧ manuscriptCase2Y14YV0Interval.2 ≤ (-893090460110360288884781447069110004817 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y14YV0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y14YV0_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y14 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc ((-178618092022072057807746075563263233999 / 1000000000000000000000000000000000000000) : ℝ) ((-893090460110360288884781447069110004817 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-178618092022072057807746075563263233999 / 1000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y14YV0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y14YV0_rounded_endpoints.1
  have hhi : (manuscriptCase2Y14YV0Interval.2 : ℝ) ≤ ((-893090460110360288884781447069110004817 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y14YV0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y14YV0_exact_interval.1, manuscriptCase2Y14YV0_exact_interval.2.trans hhi⟩

def manuscriptCase2Y14YV1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2225831 / 50000000) (0 / 1) (3) (0) (225008336987226742609 / 122070312500000000000) (0 / 1)

private theorem manuscriptCase2Y14YV1_arg_eq : barrierCase2Y14YV1LogArg = barrierComplex (15000277897 / 3906250000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y14YV1LogArg, Case2PointData.Y14, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y14YV1_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2) = barrierComplex (-2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y14YV1_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y14 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc (manuscriptCase2Y14YV1Interval.1 : ℝ) (manuscriptCase2Y14YV1Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2) * Complex.log barrierCase2Y14YV1LogArg).re ∈ _
  rw [manuscriptCase2Y14YV1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2225831 / 50000000) (0 / 1)
    barrierCase2Y14YV1LogArg (3) (0) (225008336987226742609 / 122070312500000000000) (15000277897 / 3906250000) (0 / 1)
  have hratio : ((0 / 1) / (15000277897 / 3906250000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y14YV1Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y14YV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y14YV1_rounded_endpoints :
    (-299483533962267916140300933451671995929 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2Y14YV1Interval.1 ∧ manuscriptCase2Y14YV1Interval.2 ≤ (-149741766981133958047508380100305602461 / 2500000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y14YV1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y14YV1_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y14 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc ((-299483533962267916140300933451671995929 / 5000000000000000000000000000000000000000) : ℝ) ((-149741766981133958047508380100305602461 / 2500000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-299483533962267916140300933451671995929 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y14YV1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y14YV1_rounded_endpoints.1
  have hhi : (manuscriptCase2Y14YV1Interval.2 : ℝ) ≤ ((-149741766981133958047508380100305602461 / 2500000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y14YV1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y14YV1_exact_interval.1, manuscriptCase2Y14YV1_exact_interval.2.trans hhi⟩

def manuscriptCase2Y14YV2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-1272699 / 50000000) (0 / 1) (-12) (0) (60958479697039521 / 59604644775390625) (0 / 1)

private theorem manuscriptCase2Y14YV2_arg_eq : barrierCase2Y14YV2LogArg = barrierComplex (246897711 / 15625000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y14YV2LogArg, Case2PointData.Y14, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y14YV2_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2) = barrierComplex (-1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y14YV2_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y14 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc (manuscriptCase2Y14YV2Interval.1 : ℝ) (manuscriptCase2Y14YV2Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2) * Complex.log barrierCase2Y14YV2LogArg).re ∈ _
  rw [manuscriptCase2Y14YV2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-1272699 / 50000000) (0 / 1)
    barrierCase2Y14YV2LogArg (-12) (0) (60958479697039521 / 59604644775390625) (246897711 / 15625000000) (0 / 1)
  have hratio : ((0 / 1) / (246897711 / 15625000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y14YV2Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y14YV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y14YV2_rounded_endpoints :
    (1055742853989040672504182117923357070913 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y14YV2Interval.1 ∧ manuscriptCase2Y14YV2Interval.2 ≤ (527871426994520336355217806903022795573 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y14YV2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y14YV2_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y14 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc ((1055742853989040672504182117923357070913 / 10000000000000000000000000000000000000000) : ℝ) ((527871426994520336355217806903022795573 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((1055742853989040672504182117923357070913 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y14YV2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y14YV2_rounded_endpoints.1
  have hhi : (manuscriptCase2Y14YV2Interval.2 : ℝ) ≤ ((527871426994520336355217806903022795573 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y14YV2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y14YV2_exact_interval.1, manuscriptCase2Y14YV2_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
