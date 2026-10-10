import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoLogsX16Group0

namespace OAI

noncomputable section
namespace InternalCatalan

def manuscriptCase2X16XP0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2334613 / 12500000) (0 / 1) (-6) (0) (11552440336714938609 / 9765625000000000000) (0 / 1)

private theorem manuscriptCase2X16XP0_arg_eq : barrierCase2X16XP0LogArg = barrierComplex (3398888103 / 25000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X16XP0LogArg, Case2PointData.X16, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X16XP0_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 = barrierComplex (-2334613 / 12500000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X16XP0_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X16 : ℝ) (barrierP2Tail.getD 0 (0, 0)) ∈ Set.Icc (manuscriptCase2X16XP0Interval.1 : ℝ) (manuscriptCase2X16XP0Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X16XP0LogArg).re ∈ _
  rw [manuscriptCase2X16XP0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2334613 / 12500000) (0 / 1)
    barrierCase2X16XP0LogArg (-6) (0) (11552440336714938609 / 9765625000000000000) (3398888103 / 25000000000) (0 / 1)
  have hratio : ((0 / 1) / (3398888103 / 25000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X16XP0Interval
  apply h
  all_goals
    try rw [manuscriptCase2X16XP0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X16XP0_rounded_endpoints :
    (1863420369720591928386934087965311741201 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2X16XP0Interval.1 ∧ manuscriptCase2X16XP0Interval.2 ≤ (3726840739441183857530562559729418160931 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X16XP0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X16XP0_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X16 : ℝ) (barrierP2Tail.getD 0 (0, 0)) ∈ Set.Icc ((1863420369720591928386934087965311741201 / 5000000000000000000000000000000000000000) : ℝ) ((3726840739441183857530562559729418160931 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((1863420369720591928386934087965311741201 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X16XP0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X16XP0_rounded_endpoints.1
  have hhi : (manuscriptCase2X16XP0Interval.2 : ℝ) ≤ ((3726840739441183857530562559729418160931 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X16XP0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X16XP0_exact_interval.1, manuscriptCase2X16XP0_exact_interval.2.trans hhi⟩

def manuscriptCase2X16XP1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2141509 / 50000000) (0 / 1) (-6) (0) (65072921385879150129 / 61035156250000000000) (0 / 1)

private theorem manuscriptCase2X16XP1_arg_eq : barrierCase2X16XP1LogArg = barrierComplex (8066778873 / 62500000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X16XP1LogArg, Case2PointData.X16, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X16XP1_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 = barrierComplex (-2141509 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X16XP1_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X16 : ℝ) (barrierP2Tail.getD 1 (0, 0)) ∈ Set.Icc (manuscriptCase2X16XP1Interval.1 : ℝ) (manuscriptCase2X16XP1Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X16XP1LogArg).re ∈ _
  rw [manuscriptCase2X16XP1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2141509 / 50000000) (0 / 1)
    barrierCase2X16XP1LogArg (-6) (0) (65072921385879150129 / 61035156250000000000) (8066778873 / 62500000000) (0 / 1)
  have hratio : ((0 / 1) / (8066778873 / 62500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X16XP1Interval
  apply h
  all_goals
    try rw [manuscriptCase2X16XP1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X16XP1_rounded_endpoints :
    (8769103744894171968688843449969738887 / 100000000000000000000000000000000000000) ≤ manuscriptCase2X16XP1Interval.1 ∧ manuscriptCase2X16XP1Interval.2 ≤ (175382074897883439408482146344174683301 / 2000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X16XP1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X16XP1_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X16 : ℝ) (barrierP2Tail.getD 1 (0, 0)) ∈ Set.Icc ((8769103744894171968688843449969738887 / 100000000000000000000000000000000000000) : ℝ) ((175382074897883439408482146344174683301 / 2000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((8769103744894171968688843449969738887 / 100000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X16XP1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X16XP1_rounded_endpoints.1
  have hhi : (manuscriptCase2X16XP1Interval.2 : ℝ) ≤ ((175382074897883439408482146344174683301 / 2000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X16XP1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X16XP1_exact_interval.1, manuscriptCase2X16XP1_exact_interval.2.trans hhi⟩

def manuscriptCase2X16XP2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-33138961 / 50000000) (31907569 / 100000000) (0) (-2) (307377314713066287169 / 156250000000000000000) (6375000000 / 16332075487)

private theorem manuscriptCase2X16XP2_arg_eq : barrierCase2X16XP2LogArg = barrierComplex (51 / 100) (-16332075487 / 12500000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X16XP2LogArg, Case2PointData.X16, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X16XP2_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 = barrierComplex (-33138961 / 50000000) (31907569 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X16XP2_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X16 : ℝ) (barrierP2Tail.getD 2 (0, 0)) ∈ Set.Icc (manuscriptCase2X16XP2Interval.1 : ℝ) (manuscriptCase2X16XP2Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X16XP2LogArg).re ∈ _
  rw [manuscriptCase2X16XP2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-33138961 / 50000000) (31907569 / 100000000)
    barrierCase2X16XP2LogArg (0) (-2) (307377314713066287169 / 156250000000000000000) (16332075487 / 6250000000) (51 / 50)
  have hratio : ((51 / 50) / (16332075487 / 6250000000) : ℚ) = (6375000000 / 16332075487) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X16XP2Interval
  apply h
  all_goals
    try rw [manuscriptCase2X16XP2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X16XP2_rounded_endpoints :
    (24724245569193752482500039634886188597 / 156250000000000000000000000000000000000) ≤ manuscriptCase2X16XP2Interval.1 ∧ manuscriptCase2X16XP2Interval.2 ≤ (1582351716428400390419125723324526152161 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X16XP2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X16XP2_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X16 : ℝ) (barrierP2Tail.getD 2 (0, 0)) ∈ Set.Icc ((24724245569193752482500039634886188597 / 156250000000000000000000000000000000000) : ℝ) ((1582351716428400390419125723324526152161 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((24724245569193752482500039634886188597 / 156250000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X16XP2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X16XP2_rounded_endpoints.1
  have hhi : (manuscriptCase2X16XP2Interval.2 : ℝ) ≤ ((1582351716428400390419125723324526152161 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X16XP2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X16XP2_exact_interval.1, manuscriptCase2X16XP2_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
