import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoLogsX1Group0

namespace OAI

noncomputable section
namespace InternalCatalan

def manuscriptCase2X1XP0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2334613 / 12500000) (0 / 1) (3) (0) (6571915184301530801761 / 5000000000000000000000) (0 / 1)

private theorem manuscriptCase2X1XP0_arg_eq : barrierCase2X1XP0LogArg = barrierComplex (81067349681 / 25000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X1XP0LogArg, Case2PointData.X1, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X1XP0_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 = barrierComplex (-2334613 / 12500000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X1XP0_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X1 : ℝ) (barrierP2Tail.getD 0 (0, 0)) ∈ Set.Icc (manuscriptCase2X1XP0Interval.1 : ℝ) (manuscriptCase2X1XP0Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X1XP0LogArg).re ∈ _
  rw [manuscriptCase2X1XP0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2334613 / 12500000) (0 / 1)
    barrierCase2X1XP0LogArg (3) (0) (6571915184301530801761 / 5000000000000000000000) (81067349681 / 25000000000) (0 / 1)
  have hratio : ((0 / 1) / (81067349681 / 25000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X1XP0Interval
  apply h
  all_goals
    try rw [manuscriptCase2X1XP0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X1XP0_rounded_endpoints :
    (-549289829983968407889326385895574101681 / 2500000000000000000000000000000000000000) ≤ manuscriptCase2X1XP0Interval.1 ∧ manuscriptCase2X1XP0Interval.2 ≤ (-274644914991984203897369793960362329731 / 1250000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X1XP0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X1XP0_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X1 : ℝ) (barrierP2Tail.getD 0 (0, 0)) ∈ Set.Icc ((-549289829983968407889326385895574101681 / 2500000000000000000000000000000000000000) : ℝ) ((-274644914991984203897369793960362329731 / 1250000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-549289829983968407889326385895574101681 / 2500000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X1XP0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X1XP0_rounded_endpoints.1
  have hhi : (manuscriptCase2X1XP0Interval.2 : ℝ) ≤ ((-274644914991984203897369793960362329731 / 1250000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X1XP0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X1XP0_exact_interval.1, manuscriptCase2X1XP0_exact_interval.2.trans hhi⟩

def manuscriptCase2X1XP1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2141509 / 50000000) (0 / 1) (3) (0) (49638606351142352823841 / 31250000000000000000000) (0 / 1)

private theorem manuscriptCase2X1XP1_arg_eq : barrierCase2X1XP1LogArg = barrierComplex (222797231471 / 62500000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X1XP1LogArg, Case2PointData.X1, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X1XP1_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 = barrierComplex (-2141509 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X1XP1_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X1 : ℝ) (barrierP2Tail.getD 1 (0, 0)) ∈ Set.Icc (manuscriptCase2X1XP1Interval.1 : ℝ) (manuscriptCase2X1XP1Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X1XP1LogArg).re ∈ _
  rw [manuscriptCase2X1XP1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2141509 / 50000000) (0 / 1)
    barrierCase2X1XP1LogArg (3) (0) (49638606351142352823841 / 31250000000000000000000) (222797231471 / 62500000000) (0 / 1)
  have hratio : ((0 / 1) / (222797231471 / 62500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X1XP1Interval
  apply h
  all_goals
    try rw [manuscriptCase2X1XP1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X1XP1_rounded_endpoints :
    (-21776500055933629291512418317679481421 / 400000000000000000000000000000000000000) ≤ manuscriptCase2X1XP1Interval.1 ∧ manuscriptCase2X1XP1Interval.2 ≤ (-136103125349585183050261811347592798827 / 2500000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X1XP1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X1XP1_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X1 : ℝ) (barrierP2Tail.getD 1 (0, 0)) ∈ Set.Icc ((-21776500055933629291512418317679481421 / 400000000000000000000000000000000000000) : ℝ) ((-136103125349585183050261811347592798827 / 2500000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-21776500055933629291512418317679481421 / 400000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X1XP1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X1XP1_rounded_endpoints.1
  have hhi : (manuscriptCase2X1XP1Interval.2 : ℝ) ≤ ((-136103125349585183050261811347592798827 / 2500000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X1XP1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X1XP1_exact_interval.1, manuscriptCase2X1XP1_exact_interval.2.trans hhi⟩

def manuscriptCase2X1XP2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-33138961 / 50000000) (31907569 / 100000000) (0) (1) (285533570897906174001 / 156250000000000000000) (3091351917 / 7341351917)

private theorem manuscriptCase2X1XP2_arg_eq : barrierCase2X1XP2LogArg = barrierComplex (51 / 100) (15649055751 / 12500000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X1XP2LogArg, Case2PointData.X1, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X1XP2_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 = barrierComplex (-33138961 / 50000000) (31907569 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X1XP2_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X1 : ℝ) (barrierP2Tail.getD 2 (0, 0)) ∈ Set.Icc (manuscriptCase2X1XP2Interval.1 : ℝ) (manuscriptCase2X1XP2Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X1XP2LogArg).re ∈ _
  rw [manuscriptCase2X1XP2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-33138961 / 50000000) (31907569 / 100000000)
    barrierCase2X1XP2LogArg (0) (1) (285533570897906174001 / 156250000000000000000) (22024055751 / 12500000000) (9274055751 / 12500000000)
  have hratio : ((9274055751 / 12500000000) / (22024055751 / 12500000000) : ℚ) = (3091351917 / 7341351917) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X1XP2Interval
  apply h
  all_goals
    try rw [manuscriptCase2X1XP2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X1XP2_rounded_endpoints :
    (-360978321571005729404658664013222046723 / 625000000000000000000000000000000000000) ≤ manuscriptCase2X1XP2Interval.1 ∧ manuscriptCase2X1XP2Interval.2 ≤ (-2887826572568045777386771066507865963071 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X1XP2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X1XP2_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X1 : ℝ) (barrierP2Tail.getD 2 (0, 0)) ∈ Set.Icc ((-360978321571005729404658664013222046723 / 625000000000000000000000000000000000000) : ℝ) ((-2887826572568045777386771066507865963071 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-360978321571005729404658664013222046723 / 625000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X1XP2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X1XP2_rounded_endpoints.1
  have hhi : (manuscriptCase2X1XP2Interval.2 : ℝ) ≤ ((-2887826572568045777386771066507865963071 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X1XP2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X1XP2_exact_interval.1, manuscriptCase2X1XP2_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
