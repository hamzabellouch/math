import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoLogsX8Group0

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2X8XP0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2334613 / 12500000) (0 / 1) (1) (0) (620492166620065472041 / 312500000000000000000) (0 / 1)

private theorem manuscriptCase2X8XP0_arg_eq : barrierCase2X8XP0LogArg = barrierComplex (24909680179 / 12500000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X8XP0LogArg, Case2PointData.X8, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X8XP0_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 = barrierComplex (-2334613 / 12500000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X8XP0_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X8 : ℝ) (barrierP2Tail.getD 0 (0, 0)) ∈ Set.Icc (manuscriptCase2X8XP0Interval.1 : ℝ) (manuscriptCase2X8XP0Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X8XP0LogArg).re ∈ _
  rw [manuscriptCase2X8XP0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2334613 / 12500000) (0 / 1)
    barrierCase2X8XP0LogArg (1) (0) (620492166620065472041 / 312500000000000000000) (24909680179 / 12500000000) (0 / 1)
  have hratio : ((0 / 1) / (24909680179 / 12500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X8XP0Interval
  apply h
  all_goals
    try rw [manuscriptCase2X8XP0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X8XP0_rounded_endpoints :
    (-1287824538175912349037958692404038685523 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X8XP0Interval.1 ∧ manuscriptCase2X8XP0Interval.2 ≤ (-643912269087956174412001234816914442489 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X8XP0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X8XP0_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X8 : ℝ) (barrierP2Tail.getD 0 (0, 0)) ∈ Set.Icc ((-1287824538175912349037958692404038685523 / 10000000000000000000000000000000000000000) : ℝ) ((-643912269087956174412001234816914442489 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-1287824538175912349037958692404038685523 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X8XP0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X8XP0_rounded_endpoints.1
  have hhi : (manuscriptCase2X8XP0Interval.2 : ℝ) ≤ ((-643912269087956174412001234816914442489 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X8XP0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X8XP0_exact_interval.1, manuscriptCase2X8XP0_exact_interval.2.trans hhi⟩

def manuscriptCase2X8XP1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2141509 / 50000000) (0 / 1) (2) (0) (4651630901832346592521 / 3906250000000000000000) (0 / 1)

private theorem manuscriptCase2X8XP1_arg_eq : barrierCase2X8XP1LogArg = barrierComplex (68202865789 / 31250000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X8XP1LogArg, Case2PointData.X8, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X8XP1_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 = barrierComplex (-2141509 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X8XP1_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X8 : ℝ) (barrierP2Tail.getD 1 (0, 0)) ∈ Set.Icc (manuscriptCase2X8XP1Interval.1 : ℝ) (manuscriptCase2X8XP1Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X8XP1LogArg).re ∈ _
  rw [manuscriptCase2X8XP1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2141509 / 50000000) (0 / 1)
    barrierCase2X8XP1LogArg (2) (0) (4651630901832346592521 / 3906250000000000000000) (68202865789 / 31250000000) (0 / 1)
  have hratio : ((0 / 1) / (68202865789 / 31250000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X8XP1Interval
  apply h
  all_goals
    try rw [manuscriptCase2X8XP1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X8XP1_rounded_endpoints :
    (-334275510091938306516541885969418945603 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X8XP1Interval.1 ∧ manuscriptCase2X8XP1Interval.2 ≤ (-167137755045969153229349878530726218167 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X8XP1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X8XP1_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X8 : ℝ) (barrierP2Tail.getD 1 (0, 0)) ∈ Set.Icc ((-334275510091938306516541885969418945603 / 10000000000000000000000000000000000000000) : ℝ) ((-167137755045969153229349878530726218167 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-334275510091938306516541885969418945603 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X8XP1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X8XP1_rounded_endpoints.1
  have hhi : (manuscriptCase2X8XP1Interval.2 : ℝ) ≤ ((-167137755045969153229349878530726218167 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X8XP1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X8XP1_exact_interval.1, manuscriptCase2X8XP1_exact_interval.2.trans hhi⟩

def manuscriptCase2X8XP2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-33138961 / 50000000) (31907569 / 100000000) (-2) (0) (12095366399635019481 / 9765625000000000000) (463706103 / 1062500000)

private theorem manuscriptCase2X8XP2_arg_eq : barrierCase2X8XP2LogArg = barrierComplex (51 / 100) (1391118309 / 6250000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X8XP2LogArg, Case2PointData.X8, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X8XP2_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 = barrierComplex (-33138961 / 50000000) (31907569 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X8XP2_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X8 : ℝ) (barrierP2Tail.getD 2 (0, 0)) ∈ Set.Icc (manuscriptCase2X8XP2Interval.1 : ℝ) (manuscriptCase2X8XP2Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X8XP2LogArg).re ∈ _
  rw [manuscriptCase2X8XP2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-33138961 / 50000000) (31907569 / 100000000)
    barrierCase2X8XP2LogArg (-2) (0) (12095366399635019481 / 9765625000000000000) (51 / 100) (1391118309 / 6250000000)
  have hratio : ((1391118309 / 6250000000) / (51 / 100) : ℚ) = (463706103 / 1062500000) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X8XP2Interval
  apply h
  all_goals
    try rw [manuscriptCase2X8XP2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X8XP2_rounded_endpoints :
    (514396360699213086345634509996050764799 / 2000000000000000000000000000000000000000) ≤ manuscriptCase2X8XP2Interval.1 ∧ manuscriptCase2X8XP2Interval.2 ≤ (2571981803496065432770988401861188039611 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X8XP2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X8XP2_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X8 : ℝ) (barrierP2Tail.getD 2 (0, 0)) ∈ Set.Icc ((514396360699213086345634509996050764799 / 2000000000000000000000000000000000000000) : ℝ) ((2571981803496065432770988401861188039611 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((514396360699213086345634509996050764799 / 2000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X8XP2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X8XP2_rounded_endpoints.1
  have hhi : (manuscriptCase2X8XP2Interval.2 : ℝ) ≤ ((2571981803496065432770988401861188039611 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X8XP2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X8XP2_exact_interval.1, manuscriptCase2X8XP2_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
