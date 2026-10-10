import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoLogsX0Group0

namespace OAI

noncomputable section
namespace InternalCatalan

def manuscriptCase2X0XP0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2334613 / 12500000) (0 / 1) (3) (0) (7033709563825930226641 / 5000000000000000000000) (0 / 1)

private theorem manuscriptCase2X0XP0_arg_eq : barrierCase2X0XP0LogArg = barrierComplex (83867213879 / 25000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X0XP0LogArg, Case2PointData.X0, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X0XP0_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 = barrierComplex (-2334613 / 12500000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X0XP0_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X0 : ℝ) (barrierP2Tail.getD 0 (0, 0)) ∈ Set.Icc (manuscriptCase2X0XP0Interval.1 : ℝ) (manuscriptCase2X0XP0Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X0XP0LogArg).re ∈ _
  rw [manuscriptCase2X0XP0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2334613 / 12500000) (0 / 1)
    barrierCase2X0XP0LogArg (3) (0) (7033709563825930226641 / 5000000000000000000000) (83867213879 / 25000000000) (0 / 1)
  have hratio : ((0 / 1) / (83867213879 / 25000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X0XP0Interval
  apply h
  all_goals
    try rw [manuscriptCase2X0XP0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X0XP0_rounded_endpoints :
    (-113028788271490462923218980609 / 500000000000000000000000000000) ≤ manuscriptCase2X0XP0Interval.1 ∧ manuscriptCase2X0XP0Interval.2 ≤ (-113028788271490462904301621013 / 500000000000000000000000000000) := by
  simp only [manuscriptCase2X0XP0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X0XP0_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X0 : ℝ) (barrierP2Tail.getD 0 (0, 0)) ∈ Set.Icc ((-113028788271490462923218980609 / 500000000000000000000000000000) : ℝ) ((-113028788271490462904301621013 / 500000000000000000000000000000) : ℝ) := by
  have hlo : ((-113028788271490462923218980609 / 500000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X0XP0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X0XP0_rounded_endpoints.1
  have hhi : (manuscriptCase2X0XP0Interval.2 : ℝ) ≤ ((-113028788271490462904301621013 / 500000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X0XP0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X0XP0_exact_interval.1, manuscriptCase2X0XP0_exact_interval.2.trans hhi⟩

def manuscriptCase2X0XP1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2141509 / 50000000) (0 / 1) (3) (0) (53147784423899219535121 / 31250000000000000000000) (0 / 1)

private theorem manuscriptCase2X0XP1_arg_eq : barrierCase2X0XP1LogArg = barrierComplex (230538032489 / 62500000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X0XP1LogArg, Case2PointData.X0, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X0XP1_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 = barrierComplex (-2141509 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X0XP1_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X0 : ℝ) (barrierP2Tail.getD 1 (0, 0)) ∈ Set.Icc (manuscriptCase2X0XP1Interval.1 : ℝ) (manuscriptCase2X0XP1Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X0XP1LogArg).re ∈ _
  rw [manuscriptCase2X0XP1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2141509 / 50000000) (0 / 1)
    barrierCase2X0XP1LogArg (3) (0) (53147784423899219535121 / 31250000000000000000000) (230538032489 / 62500000000) (0 / 1)
  have hratio : ((0 / 1) / (230538032489 / 62500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X0XP1Interval
  apply h
  all_goals
    try rw [manuscriptCase2X0XP1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X0XP1_rounded_endpoints :
    (-55904062122758604215281022999 / 1000000000000000000000000000000) ≤ manuscriptCase2X0XP1Interval.1 ∧ manuscriptCase2X0XP1Interval.2 ≤ (-55904062122758604206604444021 / 1000000000000000000000000000000) := by
  simp only [manuscriptCase2X0XP1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X0XP1_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X0 : ℝ) (barrierP2Tail.getD 1 (0, 0)) ∈ Set.Icc ((-55904062122758604215281022999 / 1000000000000000000000000000000) : ℝ) ((-55904062122758604206604444021 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((-55904062122758604215281022999 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X0XP1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X0XP1_rounded_endpoints.1
  have hhi : (manuscriptCase2X0XP1Interval.2 : ℝ) ≤ ((-55904062122758604206604444021 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X0XP1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X0XP1_exact_interval.1, manuscriptCase2X0XP1_exact_interval.2.trans hhi⟩

def manuscriptCase2X0XP2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-33138961 / 50000000) (31907569 / 100000000) (1) (1) (322945846669915938081 / 312500000000000000000) (3475647003 / 7725647003)

private theorem manuscriptCase2X0XP2_arg_eq : barrierCase2X0XP2LogArg = barrierComplex (51 / 100) (16801941009 / 12500000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X0XP2LogArg, Case2PointData.X0, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X0XP2_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 = barrierComplex (-33138961 / 50000000) (31907569 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X0XP2_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X0 : ℝ) (barrierP2Tail.getD 2 (0, 0)) ∈ Set.Icc (manuscriptCase2X0XP2Interval.1 : ℝ) (manuscriptCase2X0XP2Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X0XP2LogArg).re ∈ _
  rw [manuscriptCase2X0XP2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-33138961 / 50000000) (31907569 / 100000000)
    barrierCase2X0XP2LogArg (1) (1) (322945846669915938081 / 312500000000000000000) (23176941009 / 12500000000) (10426941009 / 12500000000)
  have hratio : ((10426941009 / 12500000000) / (23176941009 / 12500000000) : ℚ) = (3475647003 / 7725647003) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X0XP2Interval
  apply h
  all_goals
    try rw [manuscriptCase2X0XP2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X0XP2_rounded_endpoints :
    (-156522770578717389402293413279 / 250000000000000000000000000000) ≤ manuscriptCase2X0XP2Interval.1 ∧ manuscriptCase2X0XP2Interval.2 ≤ (-313045541157434772965910550413 / 500000000000000000000000000000) := by
  simp only [manuscriptCase2X0XP2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X0XP2_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X0 : ℝ) (barrierP2Tail.getD 2 (0, 0)) ∈ Set.Icc ((-156522770578717389402293413279 / 250000000000000000000000000000) : ℝ) ((-313045541157434772965910550413 / 500000000000000000000000000000) : ℝ) := by
  have hlo : ((-156522770578717389402293413279 / 250000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X0XP2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X0XP2_rounded_endpoints.1
  have hhi : (manuscriptCase2X0XP2Interval.2 : ℝ) ≤ ((-313045541157434772965910550413 / 500000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X0XP2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X0XP2_exact_interval.1, manuscriptCase2X0XP2_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
