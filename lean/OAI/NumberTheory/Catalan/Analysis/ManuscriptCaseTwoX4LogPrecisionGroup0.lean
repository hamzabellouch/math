import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoLogsX4Group0

namespace OAI

noncomputable section
namespace InternalCatalan

def manuscriptCase2X4XP0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2334613 / 12500000) (0 / 1) (2) (0) (2712528247190510228041 / 1600000000000000000000) (0 / 1)

private theorem manuscriptCase2X4XP0_arg_eq : barrierCase2X4XP0LogArg = barrierComplex (52081937821 / 20000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X4XP0LogArg, Case2PointData.X4, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X4XP0_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 = barrierComplex (-2334613 / 12500000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X4XP0_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X4 : ℝ) (barrierP2Tail.getD 0 (0, 0)) ∈ Set.Icc (manuscriptCase2X4XP0Interval.1 : ℝ) (manuscriptCase2X4XP0Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X4XP0LogArg).re ∈ _
  rw [manuscriptCase2X4XP0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2334613 / 12500000) (0 / 1)
    barrierCase2X4XP0LogArg (2) (0) (2712528247190510228041 / 1600000000000000000000) (52081937821 / 20000000000) (0 / 1)
  have hratio : ((0 / 1) / (52081937821 / 20000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X4XP0Interval
  apply h
  all_goals
    try rw [manuscriptCase2X4XP0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X4XP0_rounded_endpoints :
    (-893770103771233756793658483883088024433 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2X4XP0Interval.1 ∧ manuscriptCase2X4XP0Interval.2 ≤ (-893770103771233756667538178058202425201 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X4XP0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X4XP0_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X4 : ℝ) (barrierP2Tail.getD 0 (0, 0)) ∈ Set.Icc ((-893770103771233756793658483883088024433 / 5000000000000000000000000000000000000000) : ℝ) ((-893770103771233756667538178058202425201 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-893770103771233756793658483883088024433 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X4XP0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X4XP0_rounded_endpoints.1
  have hhi : (manuscriptCase2X4XP0Interval.2 : ℝ) ≤ ((-893770103771233756667538178058202425201 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X4XP0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X4XP0_exact_interval.1, manuscriptCase2X4XP0_exact_interval.2.trans hhi⟩

def manuscriptCase2X4XP1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2141509 / 50000000) (0 / 1) (3) (0) (20428162263518129528521 / 20000000000000000000000) (0 / 1)

private theorem manuscriptCase2X4XP1_arg_eq : barrierCase2X4XP1LogArg = barrierComplex (142927122211 / 50000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X4XP1LogArg, Case2PointData.X4, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X4XP1_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 = barrierComplex (-2141509 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X4XP1_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X4 : ℝ) (barrierP2Tail.getD 1 (0, 0)) ∈ Set.Icc (manuscriptCase2X4XP1Interval.1 : ℝ) (manuscriptCase2X4XP1Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X4XP1LogArg).re ∈ _
  rw [manuscriptCase2X4XP1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2141509 / 50000000) (0 / 1)
    barrierCase2X4XP1LogArg (3) (0) (20428162263518129528521 / 20000000000000000000000) (142927122211 / 50000000000) (0 / 1)
  have hratio : ((0 / 1) / (142927122211 / 50000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X4XP1Interval
  apply h
  all_goals
    try rw [manuscriptCase2X4XP1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X4XP1_rounded_endpoints :
    (-449850460214617288580699847720431675563 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X4XP1Interval.1 ∧ manuscriptCase2X4XP1Interval.2 ≤ (-22492523010730864424696832717924095583 / 500000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X4XP1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X4XP1_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X4 : ℝ) (barrierP2Tail.getD 1 (0, 0)) ∈ Set.Icc ((-449850460214617288580699847720431675563 / 10000000000000000000000000000000000000000) : ℝ) ((-22492523010730864424696832717924095583 / 500000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-449850460214617288580699847720431675563 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X4XP1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X4XP1_rounded_endpoints.1
  have hhi : (manuscriptCase2X4XP1Interval.2 : ℝ) ≤ ((-22492523010730864424696832717924095583 / 500000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X4XP1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X4XP1_exact_interval.1, manuscriptCase2X4XP1_exact_interval.2.trans hhi⟩

def manuscriptCase2X4XP2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-33138961 / 50000000) (31907569 / 100000000) (-1) (1) (78720644757290315481 / 50000000000000000000) (720069897 / 4120069897)

private theorem manuscriptCase2X4XP2_arg_eq : barrierCase2X4XP2LogArg = barrierComplex (51 / 100) (7260209691 / 10000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X4XP2LogArg, Case2PointData.X4, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X4XP2_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 = barrierComplex (-33138961 / 50000000) (31907569 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X4XP2_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X4 : ℝ) (barrierP2Tail.getD 2 (0, 0)) ∈ Set.Icc (manuscriptCase2X4XP2Interval.1 : ℝ) (manuscriptCase2X4XP2Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X4XP2LogArg).re ∈ _
  rw [manuscriptCase2X4XP2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-33138961 / 50000000) (31907569 / 100000000)
    barrierCase2X4XP2LogArg (-1) (1) (78720644757290315481 / 50000000000000000000) (12360209691 / 10000000000) (2160209691 / 10000000000)
  have hratio : ((2160209691 / 10000000000) / (12360209691 / 10000000000) : ℚ) = (720069897 / 4120069897) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X4XP2Interval
  apply h
  all_goals
    try rw [manuscriptCase2X4XP2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X4XP2_rounded_endpoints :
    (-2265192790678841254922927758454129581213 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X4XP2Interval.1 ∧ manuscriptCase2X4XP2Interval.2 ≤ (-2265192790678841138803491157045809832017 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X4XP2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X4XP2_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X4 : ℝ) (barrierP2Tail.getD 2 (0, 0)) ∈ Set.Icc ((-2265192790678841254922927758454129581213 / 10000000000000000000000000000000000000000) : ℝ) ((-2265192790678841138803491157045809832017 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-2265192790678841254922927758454129581213 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X4XP2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X4XP2_rounded_endpoints.1
  have hhi : (manuscriptCase2X4XP2Interval.2 : ℝ) ≤ ((-2265192790678841138803491157045809832017 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X4XP2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X4XP2_exact_interval.1, manuscriptCase2X4XP2_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
