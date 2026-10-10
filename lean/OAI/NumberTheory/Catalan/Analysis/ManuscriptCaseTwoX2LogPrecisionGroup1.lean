import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoLogsX2Group0

namespace OAI

noncomputable section
namespace InternalCatalan

def manuscriptCase2X2XP4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-1231651 / 100000000) (-1200529 / 20000000) (0) (2) (17499207420885324369121 / 10000000000000000000000) (-27750000000 / 129341195761)

private theorem manuscriptCase2X2XP4_arg_eq : barrierCase2X2XP4LogArg = barrierComplex (111 / 400) (129341195761 / 100000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X2XP4LogArg, Case2PointData.X2, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X2XP4_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 = barrierComplex (-1231651 / 100000000) (-1200529 / 20000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X2XP4_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X2 : ℝ) (barrierP2Tail.getD 4 (0, 0)) ∈ Set.Icc (manuscriptCase2X2XP4Interval.1 : ℝ) (manuscriptCase2X2XP4Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X2XP4LogArg).re ∈ _
  rw [manuscriptCase2X2XP4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-1231651 / 100000000) (-1200529 / 20000000)
    barrierCase2X2XP4LogArg (0) (2) (17499207420885324369121 / 10000000000000000000000) (129341195761 / 50000000000) (-111 / 200)
  have hratio : ((-111 / 200) / (129341195761 / 50000000000) : ℚ) = (-27750000000 / 129341195761) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X2XP4Interval
  apply h
  all_goals
    try rw [manuscriptCase2X2XP4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X2XP4_rounded_endpoints :
    (781570672379026571997003030325795638163 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X2XP4Interval.1 ∧ manuscriptCase2X2XP4Interval.2 ≤ (97696334047378326939850219986936092137 / 1250000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X2XP4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X2XP4_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X2 : ℝ) (barrierP2Tail.getD 4 (0, 0)) ∈ Set.Icc ((781570672379026571997003030325795638163 / 10000000000000000000000000000000000000000) : ℝ) ((97696334047378326939850219986936092137 / 1250000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((781570672379026571997003030325795638163 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X2XP4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X2XP4_rounded_endpoints.1
  have hhi : (manuscriptCase2X2XP4Interval.2 : ℝ) ≤ ((97696334047378326939850219986936092137 / 1250000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X2XP4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X2XP4_exact_interval.1, manuscriptCase2X2XP4_exact_interval.2.trans hhi⟩

def manuscriptCase2X2XP6Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-1612959 / 50000000) (-4464117 / 50000000) (1) (2) (3990082522067812425182581 / 3125000000000000000000000) (-377571029559 / 1961510295590)

private theorem manuscriptCase2X2XP6_arg_eq : barrierCase2X2XP6LogArg = barrierComplex (377571029559 / 1250000000000) (196151029559 / 125000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X2XP6LogArg, Case2PointData.X2, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X2XP6_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 = barrierComplex (-1612959 / 50000000) (-4464117 / 50000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X2XP6_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X2 : ℝ) (barrierP2Tail.getD 6 (0, 0)) ∈ Set.Icc (manuscriptCase2X2XP6Interval.1 : ℝ) (manuscriptCase2X2XP6Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 * Complex.log barrierCase2X2XP6LogArg).re ∈ _
  rw [manuscriptCase2X2XP6_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-1612959 / 50000000) (-4464117 / 50000000)
    barrierCase2X2XP6LogArg (1) (2) (3990082522067812425182581 / 3125000000000000000000000) (196151029559 / 62500000000) (-377571029559 / 625000000000)
  have hratio : ((-377571029559 / 625000000000) / (196151029559 / 62500000000) : ℚ) = (-377571029559 / 1961510295590) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X2XP6Interval
  apply h
  all_goals
    try rw [manuscriptCase2X2XP6_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X2XP6_rounded_endpoints :
    (1081441899865197807109884496150887597537 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X2XP6Interval.1 ∧ manuscriptCase2X2XP6Interval.2 ≤ (270360474966299467966314391436226633543 / 2500000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X2XP6Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X2XP6_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X2 : ℝ) (barrierP2Tail.getD 6 (0, 0)) ∈ Set.Icc ((1081441899865197807109884496150887597537 / 10000000000000000000000000000000000000000) : ℝ) ((270360474966299467966314391436226633543 / 2500000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((1081441899865197807109884496150887597537 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X2XP6Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X2XP6_rounded_endpoints.1
  have hhi : (manuscriptCase2X2XP6Interval.2 : ℝ) ≤ ((270360474966299467966314391436226633543 / 2500000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X2XP6_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X2XP6_exact_interval.1, manuscriptCase2X2XP6_exact_interval.2.trans hhi⟩

def manuscriptCase2X2XP8Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-32899 / 1562500) (9091287 / 100000000) (0) (2) (2367159716808187545182581 / 1562500000000000000000000) (-27588970441 / 1538310295590)

private theorem manuscriptCase2X2XP8_arg_eq : barrierCase2X2XP8LogArg = barrierComplex (27588970441 / 1250000000000) (153831029559 / 125000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X2XP8LogArg, Case2PointData.X2, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X2XP8_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 = barrierComplex (-32899 / 1562500) (9091287 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X2XP8_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X2 : ℝ) (barrierP2Tail.getD 8 (0, 0)) ∈ Set.Icc (manuscriptCase2X2XP8Interval.1 : ℝ) (manuscriptCase2X2XP8Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 * Complex.log barrierCase2X2XP8LogArg).re ∈ _
  rw [manuscriptCase2X2XP8_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-32899 / 1562500) (9091287 / 100000000)
    barrierCase2X2XP8LogArg (0) (2) (2367159716808187545182581 / 1562500000000000000000000) (153831029559 / 62500000000) (-27588970441 / 625000000000)
  have hratio : ((-27588970441 / 625000000000) / (153831029559 / 62500000000) : ℚ) = (-27588970441 / 1538310295590) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X2XP8Interval
  apply h
  all_goals
    try rw [manuscriptCase2X2XP8_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X2XP8_rounded_endpoints :
    (-36387132219651328347221117700848454469 / 250000000000000000000000000000000000000) ≤ manuscriptCase2X2XP8Interval.1 ∧ manuscriptCase2X2XP8Interval.2 ≤ (-1455485288786053067973049281749595933047 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X2XP8Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X2XP8_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X2 : ℝ) (barrierP2Tail.getD 8 (0, 0)) ∈ Set.Icc ((-36387132219651328347221117700848454469 / 250000000000000000000000000000000000000) : ℝ) ((-1455485288786053067973049281749595933047 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-36387132219651328347221117700848454469 / 250000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X2XP8Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X2XP8_rounded_endpoints.1
  have hhi : (manuscriptCase2X2XP8Interval.2 : ℝ) ≤ ((-1455485288786053067973049281749595933047 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X2XP8_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X2XP8_exact_interval.1, manuscriptCase2X2XP8_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
