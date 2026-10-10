import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoLogsX18Group0

namespace OAI

noncomputable section
namespace InternalCatalan

def manuscriptCase2X18XP0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2334613 / 12500000) (0 / 1) (3) (0) (1874161 / 1280000) (0 / 1)

private theorem manuscriptCase2X18XP0_arg_eq : barrierCase2X18XP0LogArg = barrierComplex (1369 / 400) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X18XP0LogArg, Case2PointData.X18, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X18XP0_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 = barrierComplex (-2334613 / 12500000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X18XP0_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X18 : ℝ) (barrierP2Tail.getD 0 (0, 0)) ∈ Set.Icc (manuscriptCase2X18XP0Interval.1 : ℝ) (manuscriptCase2X18XP0Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X18XP0LogArg).re ∈ _
  rw [manuscriptCase2X18XP0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2334613 / 12500000) (0 / 1)
    barrierCase2X18XP0LogArg (3) (0) (1874161 / 1280000) (1369 / 400) (0 / 1)
  have hratio : ((0 / 1) / (1369 / 400) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X18XP0Interval
  apply h
  all_goals
    try rw [manuscriptCase2X18XP0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X18XP0_rounded_endpoints :
    (-2297952624693387500134788742463648019211 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X18XP0Interval.1 ∧ manuscriptCase2X18XP0Interval.2 ≤ (-459590524938677499951288310097161884779 / 2000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X18XP0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X18XP0_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X18 : ℝ) (barrierP2Tail.getD 0 (0, 0)) ∈ Set.Icc ((-2297952624693387500134788742463648019211 / 10000000000000000000000000000000000000000) : ℝ) ((-459590524938677499951288310097161884779 / 2000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-2297952624693387500134788742463648019211 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X18XP0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X18XP0_rounded_endpoints.1
  have hhi : (manuscriptCase2X18XP0Interval.2 : ℝ) ≤ ((-459590524938677499951288310097161884779 / 2000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X18XP0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X18XP0_exact_interval.1, manuscriptCase2X18XP0_exact_interval.2.trans hhi⟩

def manuscriptCase2X18XP1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2141509 / 50000000) (0 / 1) (3) (0) (88529281 / 50000000) (0 / 1)

private theorem manuscriptCase2X18XP1_arg_eq : barrierCase2X18XP1LogArg = barrierComplex (9409 / 2500) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X18XP1LogArg, Case2PointData.X18, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X18XP1_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 = barrierComplex (-2141509 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X18XP1_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X18 : ℝ) (barrierP2Tail.getD 1 (0, 0)) ∈ Set.Icc (manuscriptCase2X18XP1Interval.1 : ℝ) (manuscriptCase2X18XP1Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X18XP1LogArg).re ∈ _
  rw [manuscriptCase2X18XP1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2141509 / 50000000) (0 / 1)
    barrierCase2X18XP1LogArg (3) (0) (88529281 / 50000000) (9409 / 2500) (0 / 1)
  have hratio : ((0 / 1) / (9409 / 2500) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X18XP1Interval
  apply h
  all_goals
    try rw [manuscriptCase2X18XP1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X18XP1_rounded_endpoints :
    (-4541287227303607059722080502401979849 / 80000000000000000000000000000000000000) ≤ manuscriptCase2X18XP1Interval.1 ∧ manuscriptCase2X18XP1Interval.2 ≤ (-70957612926618860297307816781476124153 / 1250000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X18XP1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X18XP1_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X18 : ℝ) (barrierP2Tail.getD 1 (0, 0)) ∈ Set.Icc ((-4541287227303607059722080502401979849 / 80000000000000000000000000000000000000) : ℝ) ((-70957612926618860297307816781476124153 / 1250000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-4541287227303607059722080502401979849 / 80000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X18XP1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X18XP1_rounded_endpoints.1
  have hhi : (manuscriptCase2X18XP1Interval.2 : ℝ) ≤ ((-70957612926618860297307816781476124153 / 1250000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X18XP1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X18XP1_exact_interval.1, manuscriptCase2X18XP1_exact_interval.2.trans hhi⟩

def manuscriptCase2X18XP2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-33138961 / 50000000) (31907569 / 100000000) (1) (1) (22201 / 20000) (89 / 191)

private theorem manuscriptCase2X18XP2_arg_eq : barrierCase2X18XP2LogArg = barrierComplex (51 / 100) (7 / 5) := by
  apply Complex.ext <;> norm_num [barrierCase2X18XP2LogArg, Case2PointData.X18, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X18XP2_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 = barrierComplex (-33138961 / 50000000) (31907569 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X18XP2_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X18 : ℝ) (barrierP2Tail.getD 2 (0, 0)) ∈ Set.Icc (manuscriptCase2X18XP2Interval.1 : ℝ) (manuscriptCase2X18XP2Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X18XP2LogArg).re ∈ _
  rw [manuscriptCase2X18XP2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-33138961 / 50000000) (31907569 / 100000000)
    barrierCase2X18XP2LogArg (1) (1) (22201 / 20000) (191 / 100) (89 / 100)
  have hratio : ((89 / 100) / (191 / 100) : ℚ) = (89 / 191) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X18XP2Interval
  apply h
  all_goals
    try rw [manuscriptCase2X18XP2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X18XP2_rounded_endpoints :
    (-6540361427167749838716377028123786679347 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X18XP2Interval.1 ∧ manuscriptCase2X18XP2Interval.2 ≤ (-1308072285433549943787907261178715733367 / 2000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X18XP2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X18XP2_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X18 : ℝ) (barrierP2Tail.getD 2 (0, 0)) ∈ Set.Icc ((-6540361427167749838716377028123786679347 / 10000000000000000000000000000000000000000) : ℝ) ((-1308072285433549943787907261178715733367 / 2000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-6540361427167749838716377028123786679347 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X18XP2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X18XP2_rounded_endpoints.1
  have hhi : (manuscriptCase2X18XP2Interval.2 : ℝ) ≤ ((-1308072285433549943787907261178715733367 / 2000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X18XP2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X18XP2_exact_interval.1, manuscriptCase2X18XP2_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
