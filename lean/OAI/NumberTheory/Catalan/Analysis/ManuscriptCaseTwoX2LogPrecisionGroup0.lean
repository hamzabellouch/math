import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoLogsX2Group0

namespace OAI

noncomputable section
namespace InternalCatalan

def manuscriptCase2X2XP0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2334613 / 12500000) (0 / 1) (3) (0) (90957249360549824369121 / 80000000000000000000000) (0 / 1)

private theorem manuscriptCase2X2XP0_arg_eq : barrierCase2X2XP0LogArg = barrierComplex (301591195761 / 100000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X2XP0LogArg, Case2PointData.X2, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X2XP0_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 = barrierComplex (-2334613 / 12500000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X2XP0_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X2 : ℝ) (barrierP2Tail.getD 0 (0, 0)) ∈ Set.Icc (manuscriptCase2X2XP0Interval.1 : ℝ) (manuscriptCase2X2XP0Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X2XP0LogArg).re ∈ _
  rw [manuscriptCase2X2XP0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2334613 / 12500000) (0 / 1)
    barrierCase2X2XP0LogArg (3) (0) (90957249360549824369121 / 80000000000000000000000) (301591195761 / 100000000000) (0 / 1)
  have hratio : ((0 / 1) / (301591195761 / 100000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X2XP0Interval
  apply h
  all_goals
    try rw [manuscriptCase2X2XP0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X2XP0_rounded_endpoints :
    (-2061747649703598824189541468746300558133 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X2XP0Interval.1 ∧ manuscriptCase2X2XP0Interval.2 ≤ (-515436912425899705952798569211725804717 / 2500000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X2XP0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X2XP0_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X2 : ℝ) (barrierP2Tail.getD 0 (0, 0)) ∈ Set.Icc ((-2061747649703598824189541468746300558133 / 10000000000000000000000000000000000000000) : ℝ) ((-515436912425899705952798569211725804717 / 2500000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-2061747649703598824189541468746300558133 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X2XP0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X2XP0_rounded_endpoints.1
  have hhi : (manuscriptCase2X2XP0Interval.2 : ℝ) ≤ ((-515436912425899705952798569211725804717 / 2500000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X2XP0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X2XP0_exact_interval.1, manuscriptCase2X2XP0_exact_interval.2.trans hhi⟩

def manuscriptCase2X2XP1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2141509 / 50000000) (0 / 1) (3) (0) (686396284485245023292001 / 500000000000000000000000) (0 / 1)

private theorem manuscriptCase2X2XP1_arg_eq : barrierCase2X2XP1LogArg = barrierComplex (828490364751 / 250000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X2XP1LogArg, Case2PointData.X2, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X2XP1_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 = barrierComplex (-2141509 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X2XP1_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X2 : ℝ) (barrierP2Tail.getD 1 (0, 0)) ∈ Set.Icc (manuscriptCase2X2XP1Interval.1 : ℝ) (manuscriptCase2X2XP1Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X2XP1LogArg).re ∈ _
  rw [manuscriptCase2X2XP1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2141509 / 50000000) (0 / 1)
    barrierCase2X2XP1LogArg (3) (0) (686396284485245023292001 / 500000000000000000000000) (828490364751 / 250000000000) (0 / 1)
  have hratio : ((0 / 1) / (828490364751 / 250000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X2XP1Interval
  apply h
  all_goals
    try rw [manuscriptCase2X2XP1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X2XP1_rounded_endpoints :
    (-256583677858910938073488729278870036491 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2X2XP1Interval.1 ∧ manuscriptCase2X2XP1Interval.2 ≤ (-256583677858910938030107132597884363847 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X2XP1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X2XP1_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X2 : ℝ) (barrierP2Tail.getD 1 (0, 0)) ∈ Set.Icc ((-256583677858910938073488729278870036491 / 5000000000000000000000000000000000000000) : ℝ) ((-256583677858910938030107132597884363847 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-256583677858910938073488729278870036491 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X2XP1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X2XP1_rounded_endpoints.1
  have hhi : (manuscriptCase2X2XP1Interval.2 : ℝ) ≤ ((-256583677858910938030107132597884363847 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X2XP1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X2XP1_exact_interval.1, manuscriptCase2X2XP1_exact_interval.2.trans hhi⟩

def manuscriptCase2X2XP2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-33138961 / 50000000) (31907569 / 100000000) (0) (1) (3486679415651837003761 / 2500000000000000000000) (27758139431 / 78758139431)

private theorem manuscriptCase2X2XP2_arg_eq : barrierCase2X2XP2LogArg = barrierComplex (51 / 100) (53258139431 / 50000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X2XP2LogArg, Case2PointData.X2, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X2XP2_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 = barrierComplex (-33138961 / 50000000) (31907569 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X2XP2_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X2 : ℝ) (barrierP2Tail.getD 2 (0, 0)) ∈ Set.Icc (manuscriptCase2X2XP2Interval.1 : ℝ) (manuscriptCase2X2XP2Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X2XP2LogArg).re ∈ _
  rw [manuscriptCase2X2XP2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-33138961 / 50000000) (31907569 / 100000000)
    barrierCase2X2XP2LogArg (0) (1) (3486679415651837003761 / 2500000000000000000000) (78758139431 / 50000000000) (27758139431 / 50000000000)
  have hratio : ((27758139431 / 50000000000) / (78758139431 / 50000000000) : ℚ) = (27758139431 / 78758139431) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X2XP2Interval
  apply h
  all_goals
    try rw [manuscriptCase2X2XP2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X2XP2_rounded_endpoints :
    (-2344806342697712439434307939561253729759 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2X2XP2Interval.1 ∧ manuscriptCase2X2XP2Interval.2 ≤ (-1172403171348856190799179171753185383883 / 2500000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X2XP2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X2XP2_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X2 : ℝ) (barrierP2Tail.getD 2 (0, 0)) ∈ Set.Icc ((-2344806342697712439434307939561253729759 / 5000000000000000000000000000000000000000) : ℝ) ((-1172403171348856190799179171753185383883 / 2500000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-2344806342697712439434307939561253729759 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X2XP2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X2XP2_rounded_endpoints.1
  have hhi : (manuscriptCase2X2XP2Interval.2 : ℝ) ≤ ((-1172403171348856190799179171753185383883 / 2500000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X2XP2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X2XP2_exact_interval.1, manuscriptCase2X2XP2_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
