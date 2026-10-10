import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoLogsX13Group0

namespace OAI

noncomputable section
namespace InternalCatalan

def manuscriptCase2X13XP0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2334613 / 12500000) (0 / 1) (-1) (0) (5296488616619275232689 / 5000000000000000000000) (0 / 1)

private theorem manuscriptCase2X13XP0_arg_eq : barrierCase2X13XP0LogArg = barrierComplex (72776978617 / 100000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X13XP0LogArg, Case2PointData.X13, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X13XP0_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 = barrierComplex (-2334613 / 12500000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X13XP0_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X13 : ℝ) (barrierP2Tail.getD 0 (0, 0)) ∈ Set.Icc (manuscriptCase2X13XP0Interval.1 : ℝ) (manuscriptCase2X13XP0Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X13XP0LogArg).re ∈ _
  rw [manuscriptCase2X13XP0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2334613 / 12500000) (0 / 1)
    barrierCase2X13XP0LogArg (-1) (0) (5296488616619275232689 / 5000000000000000000000) (72776978617 / 100000000000) (0 / 1)
  have hratio : ((0 / 1) / (72776978617 / 100000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X13XP0Interval
  apply h
  all_goals
    try rw [manuscriptCase2X13XP0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X13XP0_rounded_endpoints :
    (593496928286319408968803339177135743987 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X13XP0Interval.1 ∧ manuscriptCase2X13XP0Interval.2 ≤ (593496928286319409094919069810268190409 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X13XP0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X13XP0_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X13 : ℝ) (barrierP2Tail.getD 0 (0, 0)) ∈ Set.Icc ((593496928286319408968803339177135743987 / 10000000000000000000000000000000000000000) : ℝ) ((593496928286319409094919069810268190409 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((593496928286319408968803339177135743987 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X13XP0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X13XP0_rounded_endpoints.1
  have hhi : (manuscriptCase2X13XP0Interval.2 : ℝ) ≤ ((593496928286319409094919069810268190409 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X13XP0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X13XP0_exact_interval.1, manuscriptCase2X13XP0_exact_interval.2.trans hhi⟩

def manuscriptCase2X13XP1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2141509 / 50000000) (0 / 1) (-1) (0) (38371463153344843906609 / 31250000000000000000000) (0 / 1)

private theorem manuscriptCase2X13XP1_arg_eq : barrierCase2X13XP1LogArg = barrierComplex (195886352647 / 250000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X13XP1LogArg, Case2PointData.X13, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X13XP1_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 = barrierComplex (-2141509 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X13XP1_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X13 : ℝ) (barrierP2Tail.getD 1 (0, 0)) ∈ Set.Icc (manuscriptCase2X13XP1Interval.1 : ℝ) (manuscriptCase2X13XP1Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X13XP1LogArg).re ∈ _
  rw [manuscriptCase2X13XP1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2141509 / 50000000) (0 / 1)
    barrierCase2X13XP1LogArg (-1) (0) (38371463153344843906609 / 31250000000000000000000) (195886352647 / 250000000000) (0 / 1)
  have hratio : ((0 / 1) / (195886352647 / 250000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X13XP1Interval
  apply h
  all_goals
    try rw [manuscriptCase2X13XP1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X13XP1_rounded_endpoints :
    (104474056325412526645082320704268984301 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X13XP1Interval.1 ∧ manuscriptCase2X13XP1Interval.2 ≤ (104474056325412526674003385158252238939 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X13XP1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X13XP1_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X13 : ℝ) (barrierP2Tail.getD 1 (0, 0)) ∈ Set.Icc ((104474056325412526645082320704268984301 / 10000000000000000000000000000000000000000) : ℝ) ((104474056325412526674003385158252238939 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((104474056325412526645082320704268984301 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X13XP1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X13XP1_rounded_endpoints.1
  have hhi : (manuscriptCase2X13XP1Interval.2 : ℝ) ≤ ((104474056325412526674003385158252238939 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X13XP1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X13XP1_exact_interval.1, manuscriptCase2X13XP1_exact_interval.2.trans hhi⟩

def manuscriptCase2X13XP2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-33138961 / 50000000) (31907569 / 100000000) (-1) (-1) (2327928952145591648449 / 1250000000000000000000) (-15459479393 / 66459479393)

private theorem manuscriptCase2X13XP2_arg_eq : barrierCase2X13XP2LogArg = barrierComplex (51 / 100) (-40959479393 / 50000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X13XP2LogArg, Case2PointData.X13, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X13XP2_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 = barrierComplex (-33138961 / 50000000) (31907569 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X13XP2_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X13 : ℝ) (barrierP2Tail.getD 2 (0, 0)) ∈ Set.Icc (manuscriptCase2X13XP2Interval.1 : ℝ) (manuscriptCase2X13XP2Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X13XP2LogArg).re ∈ _
  rw [manuscriptCase2X13XP2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-33138961 / 50000000) (31907569 / 100000000)
    barrierCase2X13XP2LogArg (-1) (-1) (2327928952145591648449 / 1250000000000000000000) (66459479393 / 50000000000) (-15459479393 / 50000000000)
  have hratio : ((-15459479393 / 50000000000) / (66459479393 / 50000000000) : ℚ) = (-15459479393 / 66459479393) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X13XP2Interval
  apply h
  all_goals
    try rw [manuscriptCase2X13XP2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X13XP2_rounded_endpoints :
    (3471583935552620307632666825854747938711 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X13XP2Interval.1 ∧ manuscriptCase2X13XP2Interval.2 ≤ (867895983888155105940619357432865287131 / 2500000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X13XP2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X13XP2_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X13 : ℝ) (barrierP2Tail.getD 2 (0, 0)) ∈ Set.Icc ((3471583935552620307632666825854747938711 / 10000000000000000000000000000000000000000) : ℝ) ((867895983888155105940619357432865287131 / 2500000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((3471583935552620307632666825854747938711 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X13XP2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X13XP2_rounded_endpoints.1
  have hhi : (manuscriptCase2X13XP2Interval.2 : ℝ) ≤ ((867895983888155105940619357432865287131 / 2500000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X13XP2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X13XP2_exact_interval.1, manuscriptCase2X13XP2_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
