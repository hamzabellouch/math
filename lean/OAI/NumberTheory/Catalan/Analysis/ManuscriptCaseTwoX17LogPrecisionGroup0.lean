import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoLogsX17Group0

namespace OAI

noncomputable section
namespace InternalCatalan

def manuscriptCase2X17XP0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2334613 / 12500000) (0 / 1) (-8) (0) (51604601425689312729 / 39062500000000000000) (0 / 1)

private theorem manuscriptCase2X17XP0_arg_eq : barrierCase2X17XP0LogArg = barrierComplex (7183634277 / 100000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X17XP0LogArg, Case2PointData.X17, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X17XP0_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 = barrierComplex (-2334613 / 12500000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X17XP0_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X17 : ℝ) (barrierP2Tail.getD 0 (0, 0)) ∈ Set.Icc (manuscriptCase2X17XP0Interval.1 : ℝ) (manuscriptCase2X17XP0Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X17XP0LogArg).re ∈ _
  rw [manuscriptCase2X17XP0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2334613 / 12500000) (0 / 1)
    barrierCase2X17XP0LogArg (-8) (0) (51604601425689312729 / 39062500000000000000) (7183634277 / 100000000000) (0 / 1)
  have hratio : ((0 / 1) / (7183634277 / 100000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X17XP0Interval
  apply h
  all_goals
    try rw [manuscriptCase2X17XP0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X17XP0_rounded_endpoints :
    (2459155044966430962199923636641430426519 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2X17XP0Interval.1 ∧ manuscriptCase2X17XP0Interval.2 ≤ (2459155044966430962704386559173960633441 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X17XP0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X17XP0_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X17 : ℝ) (barrierP2Tail.getD 0 (0, 0)) ∈ Set.Icc ((2459155044966430962199923636641430426519 / 5000000000000000000000000000000000000000) : ℝ) ((2459155044966430962704386559173960633441 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((2459155044966430962199923636641430426519 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X17XP0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X17XP0_rounded_endpoints.1
  have hhi : (manuscriptCase2X17XP0Interval.2 : ℝ) ≤ ((2459155044966430962704386559173960633441 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X17XP0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X17XP0_exact_interval.1, manuscriptCase2X17XP0_exact_interval.2.trans hhi⟩

def manuscriptCase2X17XP1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2141509 / 50000000) (0 / 1) (-9) (0) (211412987321835957849 / 122070312500000000000) (0 / 1)

private theorem manuscriptCase2X17XP1_arg_eq : barrierCase2X17XP1LogArg = barrierComplex (14540047707 / 250000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X17XP1LogArg, Case2PointData.X17, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X17XP1_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 = barrierComplex (-2141509 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X17XP1_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X17 : ℝ) (barrierP2Tail.getD 1 (0, 0)) ∈ Set.Icc (manuscriptCase2X17XP1Interval.1 : ℝ) (manuscriptCase2X17XP1Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X17XP1LogArg).re ∈ _
  rw [manuscriptCase2X17XP1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2141509 / 50000000) (0 / 1)
    barrierCase2X17XP1LogArg (-9) (0) (211412987321835957849 / 122070312500000000000) (14540047707 / 250000000000) (0 / 1)
  have hratio : ((0 / 1) / (14540047707 / 250000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X17XP1Interval
  apply h
  all_goals
    try rw [manuscriptCase2X17XP1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X17XP1_rounded_endpoints :
    (609163834464027601503913166959684980083 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2X17XP1Interval.1 ∧ manuscriptCase2X17XP1Interval.2 ≤ (9518184913500431275532222277962709951 / 78125000000000000000000000000000000000) := by
  simp only [manuscriptCase2X17XP1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X17XP1_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X17 : ℝ) (barrierP2Tail.getD 1 (0, 0)) ∈ Set.Icc ((609163834464027601503913166959684980083 / 5000000000000000000000000000000000000000) : ℝ) ((9518184913500431275532222277962709951 / 78125000000000000000000000000000000000) : ℝ) := by
  have hlo : ((609163834464027601503913166959684980083 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X17XP1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X17XP1_rounded_endpoints.1
  have hhi : (manuscriptCase2X17XP1Interval.2 : ℝ) ≤ ((9518184913500431275532222277962709951 / 78125000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X17XP1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X17XP1_exact_interval.1, manuscriptCase2X17XP1_exact_interval.2.trans hhi⟩

def manuscriptCase2X17XP2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-33138961 / 50000000) (31907569 / 100000000) (1) (-2) (5269967472515433482089 / 5000000000000000000000) (25500000000 / 67968503533)

private theorem manuscriptCase2X17XP2_arg_eq : barrierCase2X17XP2LogArg = barrierComplex (51 / 100) (-67968503533 / 50000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X17XP2LogArg, Case2PointData.X17, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X17XP2_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 = barrierComplex (-33138961 / 50000000) (31907569 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X17XP2_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X17 : ℝ) (barrierP2Tail.getD 2 (0, 0)) ∈ Set.Icc (manuscriptCase2X17XP2Interval.1 : ℝ) (manuscriptCase2X17XP2Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X17XP2LogArg).re ∈ _
  rw [manuscriptCase2X17XP2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-33138961 / 50000000) (31907569 / 100000000)
    barrierCase2X17XP2LogArg (1) (-2) (5269967472515433482089 / 5000000000000000000000) (67968503533 / 25000000000) (51 / 50)
  have hratio : ((51 / 50) / (67968503533 / 25000000000) : ℚ) = (25500000000 / 67968503533) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X17XP2Interval
  apply h
  all_goals
    try rw [manuscriptCase2X17XP2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X17XP2_rounded_endpoints :
    (43609685712302366904285917334993432359 / 312500000000000000000000000000000000000) ≤ manuscriptCase2X17XP2Interval.1 ∧ manuscriptCase2X17XP2Interval.2 ≤ (697754971396837986364285083478018967137 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X17XP2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X17XP2_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X17 : ℝ) (barrierP2Tail.getD 2 (0, 0)) ∈ Set.Icc ((43609685712302366904285917334993432359 / 312500000000000000000000000000000000000) : ℝ) ((697754971396837986364285083478018967137 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((43609685712302366904285917334993432359 / 312500000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X17XP2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X17XP2_rounded_endpoints.1
  have hhi : (manuscriptCase2X17XP2Interval.2 : ℝ) ≤ ((697754971396837986364285083478018967137 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X17XP2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X17XP2_exact_interval.1, manuscriptCase2X17XP2_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
