import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoLogsX7Group0

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2X7XP0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2334613 / 12500000) (0 / 1) (2) (0) (10754174392510058341441 / 10000000000000000000000) (0 / 1)

private theorem manuscriptCase2X7XP0_arg_eq : barrierCase2X7XP0LogArg = barrierComplex (103702335521 / 50000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X7XP0LogArg, Case2PointData.X7, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X7XP0_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 = barrierComplex (-2334613 / 12500000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X7XP0_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X7 : ℝ) (barrierP2Tail.getD 0 (0, 0)) ∈ Set.Icc (manuscriptCase2X7XP0Interval.1 : ℝ) (manuscriptCase2X7XP0Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X7XP0LogArg).re ∈ _
  rw [manuscriptCase2X7XP0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2334613 / 12500000) (0 / 1)
    barrierCase2X7XP0LogArg (2) (0) (10754174392510058341441 / 10000000000000000000000) (103702335521 / 50000000000) (0 / 1)
  have hratio : ((0 / 1) / (103702335521 / 50000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X7XP0Interval
  apply h
  all_goals
    try rw [manuscriptCase2X7XP0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X7XP0_rounded_endpoints :
    (-1362483193849913208120368387075694633833 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X7XP0Interval.1 ∧ manuscriptCase2X7XP0Interval.2 ≤ (-1362483193849913207868136925809429740989 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X7XP0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X7XP0_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X7 : ℝ) (barrierP2Tail.getD 0 (0, 0)) ∈ Set.Icc ((-1362483193849913208120368387075694633833 / 10000000000000000000000000000000000000000) : ℝ) ((-1362483193849913207868136925809429740989 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-1362483193849913208120368387075694633833 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X7XP0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X7XP0_rounded_endpoints.1
  have hhi : (manuscriptCase2X7XP0Interval.2 : ℝ) ≤ ((-1362483193849913207868136925809429740989 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X7XP0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X7XP0_exact_interval.1, manuscriptCase2X7XP0_exact_interval.2.trans hhi⟩

def manuscriptCase2X7XP1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2141509 / 50000000) (0 / 1) (2) (0) (80682222664462351993921 / 62500000000000000000000) (0 / 1)

private theorem manuscriptCase2X7XP1_arg_eq : barrierCase2X7XP1LogArg = barrierComplex (284046162911 / 125000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X7XP1LogArg, Case2PointData.X7, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X7XP1_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 = barrierComplex (-2141509 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X7XP1_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X7 : ℝ) (barrierP2Tail.getD 1 (0, 0)) ∈ Set.Icc (manuscriptCase2X7XP1Interval.1 : ℝ) (manuscriptCase2X7XP1Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X7XP1LogArg).re ∈ _
  rw [manuscriptCase2X7XP1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2141509 / 50000000) (0 / 1)
    barrierCase2X7XP1LogArg (2) (0) (80682222664462351993921 / 62500000000000000000000) (284046162911 / 125000000000) (0 / 1)
  have hratio : ((0 / 1) / (284046162911 / 125000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X7XP1Interval
  apply h
  all_goals
    try rw [manuscriptCase2X7XP1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X7XP1_rounded_endpoints :
    (-351559982562939617208162179861828250931 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X7XP1Interval.1 ∧ manuscriptCase2X7XP1Interval.2 ≤ (-17577999128146980857516002547693086677 / 500000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X7XP1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X7XP1_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X7 : ℝ) (barrierP2Tail.getD 1 (0, 0)) ∈ Set.Icc ((-351559982562939617208162179861828250931 / 10000000000000000000000000000000000000000) : ℝ) ((-17577999128146980857516002547693086677 / 500000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-351559982562939617208162179861828250931 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X7XP1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X7XP1_rounded_endpoints.1
  have hhi : (manuscriptCase2X7XP1Interval.2 : ℝ) ≤ ((-17577999128146980857516002547693086677 / 500000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X7XP1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X7XP1_exact_interval.1, manuscriptCase2X7XP1_exact_interval.2.trans hhi⟩

def manuscriptCase2X7XP2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-33138961 / 50000000) (31907569 / 100000000) (-2) (1) (214947183310977884881 / 156250000000000000000) (-5512273609 / 19987726391)

private theorem manuscriptCase2X7XP2_arg_eq : barrierCase2X7XP2LogArg = barrierComplex (51 / 100) (7237726391 / 25000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X7XP2LogArg, Case2PointData.X7, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X7XP2_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 = barrierComplex (-33138961 / 50000000) (31907569 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X7XP2_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X7 : ℝ) (barrierP2Tail.getD 2 (0, 0)) ∈ Set.Icc (manuscriptCase2X7XP2Interval.1 : ℝ) (manuscriptCase2X7XP2Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X7XP2LogArg).re ∈ _
  rw [manuscriptCase2X7XP2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-33138961 / 50000000) (31907569 / 100000000)
    barrierCase2X7XP2LogArg (-2) (1) (214947183310977884881 / 156250000000000000000) (19987726391 / 25000000000) (-5512273609 / 25000000000)
  have hratio : ((-5512273609 / 25000000000) / (19987726391 / 25000000000) : ℚ) = (-5512273609 / 19987726391) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X7XP2Interval
  apply h
  all_goals
    try rw [manuscriptCase2X7XP2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X7XP2_rounded_endpoints :
    (472429150454505367106584619400598426551 / 2500000000000000000000000000000000000000) ≤ manuscriptCase2X7XP2Interval.1 ∧ manuscriptCase2X7XP2Interval.2 ≤ (944858300909010792496658186556533790597 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X7XP2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X7XP2_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X7 : ℝ) (barrierP2Tail.getD 2 (0, 0)) ∈ Set.Icc ((472429150454505367106584619400598426551 / 2500000000000000000000000000000000000000) : ℝ) ((944858300909010792496658186556533790597 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((472429150454505367106584619400598426551 / 2500000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X7XP2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X7XP2_rounded_endpoints.1
  have hhi : (manuscriptCase2X7XP2Interval.2 : ℝ) ≤ ((944858300909010792496658186556533790597 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X7XP2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X7XP2_exact_interval.1, manuscriptCase2X7XP2_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
