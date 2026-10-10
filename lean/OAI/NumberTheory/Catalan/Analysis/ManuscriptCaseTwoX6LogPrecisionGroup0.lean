import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoLogsX6Group0

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2X6XP0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2334613 / 12500000) (0 / 1) (2) (0) (12667470196144694833081 / 10000000000000000000000) (0 / 1)

private theorem manuscriptCase2X6XP0_arg_eq : barrierCase2X6XP0LogArg = barrierComplex (112549856491 / 50000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X6XP0LogArg, Case2PointData.X6, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X6XP0_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 = barrierComplex (-2334613 / 12500000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X6XP0_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X6 : ℝ) (barrierP2Tail.getD 0 (0, 0)) ∈ Set.Icc (manuscriptCase2X6XP0Interval.1 : ℝ) (manuscriptCase2X6XP0Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X6XP0LogArg).re ∈ _
  rw [manuscriptCase2X6XP0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2334613 / 12500000) (0 / 1)
    barrierCase2X6XP0LogArg (2) (0) (12667470196144694833081 / 10000000000000000000000) (112549856491 / 50000000000) (0 / 1)
  have hratio : ((0 / 1) / (112549856491 / 50000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X6XP0Interval
  apply h
  all_goals
    try rw [manuscriptCase2X6XP0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X6XP0_rounded_endpoints :
    (-1515394098675387755058340766756576224151 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X6XP0Interval.1 ∧ manuscriptCase2X6XP0Interval.2 ≤ (-757697049337693877403054652745155664597 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X6XP0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X6XP0_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X6 : ℝ) (barrierP2Tail.getD 0 (0, 0)) ∈ Set.Icc ((-1515394098675387755058340766756576224151 / 10000000000000000000000000000000000000000) : ℝ) ((-757697049337693877403054652745155664597 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-1515394098675387755058340766756576224151 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X6XP0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X6XP0_rounded_endpoints.1
  have hhi : (manuscriptCase2X6XP0Interval.2 : ℝ) ≤ ((-757697049337693877403054652745155664597 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X6XP0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X6XP0_exact_interval.1, manuscriptCase2X6XP0_exact_interval.2.trans hhi⟩

def manuscriptCase2X6XP1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2141509 / 50000000) (0 / 1) (2) (0) (95176542012065454104761 / 62500000000000000000000) (0 / 1)

private theorem manuscriptCase2X6XP1_arg_eq : barrierCase2X6XP1LogArg = barrierComplex (308506956181 / 125000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X6XP1LogArg, Case2PointData.X6, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X6XP1_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 = barrierComplex (-2141509 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X6XP1_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X6 : ℝ) (barrierP2Tail.getD 1 (0, 0)) ∈ Set.Icc (manuscriptCase2X6XP1Interval.1 : ℝ) (manuscriptCase2X6XP1Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X6XP1LogArg).re ∈ _
  rw [manuscriptCase2X6XP1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2141509 / 50000000) (0 / 1)
    barrierCase2X6XP1LogArg (2) (0) (95176542012065454104761 / 62500000000000000000000) (308506956181 / 125000000000) (0 / 1)
  have hratio : ((0 / 1) / (308506956181 / 125000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X6XP1Interval
  apply h
  all_goals
    try rw [manuscriptCase2X6XP1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X6XP1_rounded_endpoints :
    (-193470487681870475114125513116460349471 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2X6XP1Interval.1 ∧ manuscriptCase2X6XP1Interval.2 ≤ (-19347048768187047508520444835278110561 / 500000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X6XP1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X6XP1_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X6 : ℝ) (barrierP2Tail.getD 1 (0, 0)) ∈ Set.Icc ((-193470487681870475114125513116460349471 / 5000000000000000000000000000000000000000) : ℝ) ((-19347048768187047508520444835278110561 / 500000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-193470487681870475114125513116460349471 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X6XP1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X6XP1_rounded_endpoints.1
  have hhi : (manuscriptCase2X6XP1Interval.2 : ℝ) ≤ ((-19347048768187047508520444835278110561 / 500000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X6XP1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X6XP1_exact_interval.1, manuscriptCase2X6XP1_exact_interval.2.trans hhi⟩

def manuscriptCase2X6XP2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-33138961 / 50000000) (31907569 / 100000000) (-2) (1) (280954814837118674121 / 156250000000000000000) (-623058913 / 7876941087)

private theorem manuscriptCase2X6XP2_arg_eq : barrierCase2X6XP2LogArg = barrierComplex (51 / 100) (10880823261 / 25000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X6XP2LogArg, Case2PointData.X6, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X6XP2_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 = barrierComplex (-33138961 / 50000000) (31907569 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X6XP2_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X6 : ℝ) (barrierP2Tail.getD 2 (0, 0)) ∈ Set.Icc (manuscriptCase2X6XP2Interval.1 : ℝ) (manuscriptCase2X6XP2Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X6XP2LogArg).re ∈ _
  rw [manuscriptCase2X6XP2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-33138961 / 50000000) (31907569 / 100000000)
    barrierCase2X6XP2LogArg (-2) (1) (280954814837118674121 / 156250000000000000000) (23630823261 / 25000000000) (-1869176739 / 25000000000)
  have hratio : ((-1869176739 / 25000000000) / (23630823261 / 25000000000) : ℚ) = (-623058913 / 7876941087) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X6XP2Interval
  apply h
  all_goals
    try rw [manuscriptCase2X6XP2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X6XP2_rounded_endpoints :
    (395498434223695961246305642786535272689 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X6XP2Interval.1 ∧ manuscriptCase2X6XP2Interval.2 ≤ (19774921711184803890731992123884841237 / 500000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X6XP2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X6XP2_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X6 : ℝ) (barrierP2Tail.getD 2 (0, 0)) ∈ Set.Icc ((395498434223695961246305642786535272689 / 10000000000000000000000000000000000000000) : ℝ) ((19774921711184803890731992123884841237 / 500000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((395498434223695961246305642786535272689 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X6XP2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X6XP2_rounded_endpoints.1
  have hhi : (manuscriptCase2X6XP2Interval.2 : ℝ) ≤ ((19774921711184803890731992123884841237 / 500000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X6XP2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X6XP2_exact_interval.1, manuscriptCase2X6XP2_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
