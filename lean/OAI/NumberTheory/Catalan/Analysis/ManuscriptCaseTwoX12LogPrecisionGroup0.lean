import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoLogsX12Group0

namespace OAI

noncomputable section
namespace InternalCatalan

def manuscriptCase2X12XP0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2334613 / 12500000) (0 / 1) (-1) (0) (9559162524095537607081 / 5000000000000000000000) (0 / 1)

private theorem manuscriptCase2X12XP0_arg_eq : barrierCase2X12XP0LogArg = barrierComplex (97770969741 / 100000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X12XP0LogArg, Case2PointData.X12, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X12XP0_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 = barrierComplex (-2334613 / 12500000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X12XP0_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X12 : ℝ) (barrierP2Tail.getD 0 (0, 0)) ∈ Set.Icc (manuscriptCase2X12XP0Interval.1 : ℝ) (manuscriptCase2X12XP0Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X12XP0LogArg).re ∈ _
  rw [manuscriptCase2X12XP0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2334613 / 12500000) (0 / 1)
    barrierCase2X12XP0LogArg (-1) (0) (9559162524095537607081 / 5000000000000000000000) (97770969741 / 100000000000) (0 / 1)
  have hratio : ((0 / 1) / (97770969741 / 100000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X12XP0Interval
  apply h
  all_goals
    try rw [manuscriptCase2X12XP0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X12XP0_rounded_endpoints :
    (8420476910866278121806637369584011077 / 2000000000000000000000000000000000000000) ≤ manuscriptCase2X12XP0Interval.1 ∧ manuscriptCase2X12XP0Interval.2 ≤ (336819076434651125979755098652756257 / 80000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X12XP0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X12XP0_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X12 : ℝ) (barrierP2Tail.getD 0 (0, 0)) ∈ Set.Icc ((8420476910866278121806637369584011077 / 2000000000000000000000000000000000000000) : ℝ) ((336819076434651125979755098652756257 / 80000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((8420476910866278121806637369584011077 / 2000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X12XP0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X12XP0_rounded_endpoints.1
  have hhi : (manuscriptCase2X12XP0Interval.2 : ℝ) ≤ ((336819076434651125979755098652756257 / 80000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X12XP0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X12XP0_exact_interval.1, manuscriptCase2X12XP0_exact_interval.2.trans hhi⟩

def manuscriptCase2X12XP1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2141509 / 50000000) (0 / 1) (0) (0) (70218315232519509598761 / 62500000000000000000000) (0 / 1)

private theorem manuscriptCase2X12XP1_arg_eq : barrierCase2X12XP1LogArg = barrierComplex (264987386931 / 250000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X12XP1LogArg, Case2PointData.X12, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X12XP1_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 = barrierComplex (-2141509 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X12XP1_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X12 : ℝ) (barrierP2Tail.getD 1 (0, 0)) ∈ Set.Icc (manuscriptCase2X12XP1Interval.1 : ℝ) (manuscriptCase2X12XP1Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X12XP1LogArg).re ∈ _
  rw [manuscriptCase2X12XP1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2141509 / 50000000) (0 / 1)
    barrierCase2X12XP1LogArg (0) (0) (70218315232519509598761 / 62500000000000000000000) (264987386931 / 250000000000) (0 / 1)
  have hratio : ((0 / 1) / (264987386931 / 250000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X12XP1Interval
  apply h
  all_goals
    try rw [manuscriptCase2X12XP1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X12XP1_rounded_endpoints :
    (-24936292087408247942305464571212867039 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X12XP1Interval.1 ∧ manuscriptCase2X12XP1Interval.2 ≤ (-12468146043704123971152732285606433519 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X12XP1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X12XP1_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X12 : ℝ) (barrierP2Tail.getD 1 (0, 0)) ∈ Set.Icc ((-24936292087408247942305464571212867039 / 10000000000000000000000000000000000000000) : ℝ) ((-12468146043704123971152732285606433519 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-24936292087408247942305464571212867039 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X12XP1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X12XP1_rounded_endpoints.1
  have hhi : (manuscriptCase2X12XP1Interval.2 : ℝ) ≤ ((-12468146043704123971152732285606433519 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X12XP1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X12XP1_exact_interval.1, manuscriptCase2X12XP1_exact_interval.2.trans hhi⟩

def manuscriptCase2X12XP2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-33138961 / 50000000) (31907569 / 100000000) (-1) (-1) (1590766164248203608121 / 1250000000000000000000) (-5167835989 / 56167835989)

private theorem manuscriptCase2X12XP2_arg_eq : barrierCase2X12XP2LogArg = barrierComplex (51 / 100) (-30667835989 / 50000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X12XP2LogArg, Case2PointData.X12, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X12XP2_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 = barrierComplex (-33138961 / 50000000) (31907569 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X12XP2_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X12 : ℝ) (barrierP2Tail.getD 2 (0, 0)) ∈ Set.Icc (manuscriptCase2X12XP2Interval.1 : ℝ) (manuscriptCase2X12XP2Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X12XP2LogArg).re ∈ _
  rw [manuscriptCase2X12XP2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-33138961 / 50000000) (31907569 / 100000000)
    barrierCase2X12XP2LogArg (-1) (-1) (1590766164248203608121 / 1250000000000000000000) (56167835989 / 50000000000) (-5167835989 / 50000000000)
  have hratio : ((-5167835989 / 50000000000) / (56167835989 / 50000000000) : ℚ) = (-5167835989 / 56167835989) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X12XP2Interval
  apply h
  all_goals
    try rw [manuscriptCase2X12XP2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X12XP2_rounded_endpoints :
    (4296891949601005976939341584635688598727 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X12XP2Interval.1 ∧ manuscriptCase2X12XP2Interval.2 ≤ (1074222987400251523264694509401411858149 / 2500000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X12XP2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X12XP2_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X12 : ℝ) (barrierP2Tail.getD 2 (0, 0)) ∈ Set.Icc ((4296891949601005976939341584635688598727 / 10000000000000000000000000000000000000000) : ℝ) ((1074222987400251523264694509401411858149 / 2500000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((4296891949601005976939341584635688598727 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X12XP2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X12XP2_rounded_endpoints.1
  have hhi : (manuscriptCase2X12XP2Interval.2 : ℝ) ≤ ((1074222987400251523264694509401411858149 / 2500000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X12XP2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X12XP2_exact_interval.1, manuscriptCase2X12XP2_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
