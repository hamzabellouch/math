import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointY15

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2Y15YV0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-15199211 / 100000000) (0 / 1) (2) (0) (2601 / 2500) (0 / 1)

private theorem manuscriptCase2Y15YV0_arg_eq : barrierCase2Y15YV0LogArg = barrierComplex (51 / 25) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y15YV0LogArg, Case2PointData.Y15, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y15YV0_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2) = barrierComplex (-15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y15YV0_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y15 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc (manuscriptCase2Y15YV0Interval.1 : ℝ) (manuscriptCase2Y15YV0Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2) * Complex.log barrierCase2Y15YV0LogArg).re ∈ _
  rw [manuscriptCase2Y15YV0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-15199211 / 100000000) (0 / 1)
    barrierCase2Y15YV0LogArg (2) (0) (2601 / 2500) (51 / 25) (0 / 1)
  have hratio : ((0 / 1) / (51 / 25) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y15YV0Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y15YV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y15YV0_rounded_endpoints :
    (-6772671601259188661567414145278895783 / 62500000000000000000000000000000000000) ≤ manuscriptCase2Y15YV0Interval.1 ∧ manuscriptCase2Y15YV0Interval.2 ≤ (-541813728100735092822760511124174303037 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y15YV0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y15YV0_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y15 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc ((-6772671601259188661567414145278895783 / 62500000000000000000000000000000000000) : ℝ) ((-541813728100735092822760511124174303037 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-6772671601259188661567414145278895783 / 62500000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y15YV0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y15YV0_rounded_endpoints.1
  have hhi : (manuscriptCase2Y15YV0Interval.2 : ℝ) ≤ ((-541813728100735092822760511124174303037 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y15YV0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y15YV0_exact_interval.1, manuscriptCase2Y15YV0_exact_interval.2.trans hhi⟩

def manuscriptCase2Y15YV1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2225831 / 50000000) (0 / 1) (2) (0) (2253001 / 1562500) (0 / 1)

private theorem manuscriptCase2Y15YV1_arg_eq : barrierCase2Y15YV1LogArg = barrierComplex (1501 / 625) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y15YV1LogArg, Case2PointData.Y15, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y15YV1_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2) = barrierComplex (-2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y15YV1_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y15 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc (manuscriptCase2Y15YV1Interval.1 : ℝ) (manuscriptCase2Y15YV1Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2) * Complex.log barrierCase2Y15YV1LogArg).re ∈ _
  rw [manuscriptCase2Y15YV1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2225831 / 50000000) (0 / 1)
    barrierCase2Y15YV1LogArg (2) (0) (2253001 / 1562500) (1501 / 625) (0 / 1)
  have hratio : ((0 / 1) / (1501 / 625) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y15YV1Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y15YV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y15YV1_rounded_endpoints :
    (-975064424028557985674393954975469439 / 25000000000000000000000000000000000000) ≤ manuscriptCase2Y15YV1Interval.1 ∧ manuscriptCase2Y15YV1Interval.2 ≤ (-195012884805711597104818958503516932439 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y15YV1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y15YV1_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y15 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc ((-975064424028557985674393954975469439 / 25000000000000000000000000000000000000) : ℝ) ((-195012884805711597104818958503516932439 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-975064424028557985674393954975469439 / 25000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y15YV1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y15YV1_rounded_endpoints.1
  have hhi : (manuscriptCase2Y15YV1Interval.2 : ℝ) ≤ ((-195012884805711597104818958503516932439 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y15YV1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y15YV1_exact_interval.1, manuscriptCase2Y15YV1_exact_interval.2.trans hhi⟩

def manuscriptCase2Y15YV2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-1272699 / 50000000) (0 / 1) (0) (0) (695556 / 390625) (0 / 1)

private theorem manuscriptCase2Y15YV2_arg_eq : barrierCase2Y15YV2LogArg = barrierComplex (834 / 625) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y15YV2LogArg, Case2PointData.Y15, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y15YV2_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2) = barrierComplex (-1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y15YV2_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y15 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc (manuscriptCase2Y15YV2Interval.1 : ℝ) (manuscriptCase2Y15YV2Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2) * Complex.log barrierCase2Y15YV2LogArg).re ∈ _
  rw [manuscriptCase2Y15YV2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-1272699 / 50000000) (0 / 1)
    barrierCase2Y15YV2LogArg (0) (0) (695556 / 390625) (834 / 625) (0 / 1)
  have hratio : ((0 / 1) / (834 / 625) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y15YV2Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y15YV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y15YV2_rounded_endpoints :
    (-36715043808070618954540191632497521169 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2Y15YV2Interval.1 ∧ manuscriptCase2Y15YV2Interval.2 ≤ (-14686017523228247581810304827775341817 / 2000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y15YV2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y15YV2_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y15 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc ((-36715043808070618954540191632497521169 / 5000000000000000000000000000000000000000) : ℝ) ((-14686017523228247581810304827775341817 / 2000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-36715043808070618954540191632497521169 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y15YV2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y15YV2_rounded_endpoints.1
  have hhi : (manuscriptCase2Y15YV2Interval.2 : ℝ) ≤ ((-14686017523228247581810304827775341817 / 2000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y15YV2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y15YV2_exact_interval.1, manuscriptCase2Y15YV2_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
