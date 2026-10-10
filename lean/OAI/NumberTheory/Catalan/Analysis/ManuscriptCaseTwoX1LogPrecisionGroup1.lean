import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoLogsX1Group0

namespace OAI

noncomputable section
namespace InternalCatalan

def manuscriptCase2X1XP4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-1231651 / 100000000) (-1200529 / 20000000) (1) (2) (1492497505525405801761 / 1250000000000000000000) (-2312500000 / 12668283227)

private theorem manuscriptCase2X1XP4_arg_eq : barrierCase2X1XP4LogArg = barrierComplex (111 / 400) (38004849681 / 25000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X1XP4LogArg, Case2PointData.X1, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X1XP4_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 = barrierComplex (-1231651 / 100000000) (-1200529 / 20000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X1XP4_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X1 : ℝ) (barrierP2Tail.getD 4 (0, 0)) ∈ Set.Icc (manuscriptCase2X1XP4Interval.1 : ℝ) (manuscriptCase2X1XP4Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X1XP4LogArg).re ∈ _
  rw [manuscriptCase2X1XP4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-1231651 / 100000000) (-1200529 / 20000000)
    barrierCase2X1XP4LogArg (1) (2) (1492497505525405801761 / 1250000000000000000000) (38004849681 / 12500000000) (-111 / 200)
  have hratio : ((-111 / 200) / (38004849681 / 12500000000) : ℚ) = (-2312500000 / 12668283227) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X1XP4Interval
  apply h
  all_goals
    try rw [manuscriptCase2X1XP4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X1XP4_rounded_endpoints :
    (195226994938700847847972395367891286637 / 2500000000000000000000000000000000000000) ≤ manuscriptCase2X1XP4Interval.1 ∧ manuscriptCase2X1XP4Interval.2 ≤ (390453989877401717461000140787754163063 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X1XP4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X1XP4_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X1 : ℝ) (barrierP2Tail.getD 4 (0, 0)) ∈ Set.Icc ((195226994938700847847972395367891286637 / 2500000000000000000000000000000000000000) : ℝ) ((390453989877401717461000140787754163063 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((195226994938700847847972395367891286637 / 2500000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X1XP4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X1XP4_rounded_endpoints.1
  have hhi : (manuscriptCase2X1XP4Interval.2 : ℝ) ≤ ((390453989877401717461000140787754163063 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X1XP4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X1XP4_exact_interval.1, manuscriptCase2X1XP4_exact_interval.2.trans hhi⟩

def manuscriptCase2X1XP6Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-1612959 / 50000000) (-4464117 / 50000000) (1) (2) (332000346736695758381621 / 195312500000000000000000) (-102063326039 / 567083260390)

private theorem manuscriptCase2X1XP6_arg_eq : barrierCase2X1XP6LogArg = barrierComplex (102063326039 / 312500000000) (56708326039 / 31250000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X1XP6LogArg, Case2PointData.X1, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X1XP6_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 = barrierComplex (-1612959 / 50000000) (-4464117 / 50000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X1XP6_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X1 : ℝ) (barrierP2Tail.getD 6 (0, 0)) ∈ Set.Icc (manuscriptCase2X1XP6Interval.1 : ℝ) (manuscriptCase2X1XP6Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 * Complex.log barrierCase2X1XP6LogArg).re ∈ _
  rw [manuscriptCase2X1XP6_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-1612959 / 50000000) (-4464117 / 50000000)
    barrierCase2X1XP6LogArg (1) (2) (332000346736695758381621 / 195312500000000000000000) (56708326039 / 15625000000) (-102063326039 / 156250000000)
  have hratio : ((-102063326039 / 156250000000) / (56708326039 / 15625000000) : ℚ) = (-102063326039 / 567083260390) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X1XP6Interval
  apply h
  all_goals
    try rw [manuscriptCase2X1XP6_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X1XP6_rounded_endpoints :
    (523040505422656179843389771727449694809 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2X1XP6Interval.1 ∧ manuscriptCase2X1XP6Interval.2 ≤ (3269003158891601326381732817613489509 / 31250000000000000000000000000000000000) := by
  simp only [manuscriptCase2X1XP6Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X1XP6_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X1 : ℝ) (barrierP2Tail.getD 6 (0, 0)) ∈ Set.Icc ((523040505422656179843389771727449694809 / 5000000000000000000000000000000000000000) : ℝ) ((3269003158891601326381732817613489509 / 31250000000000000000000000000000000000) : ℝ) := by
  have hlo : ((523040505422656179843389771727449694809 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X1XP6Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X1XP6_rounded_endpoints.1
  have hhi : (manuscriptCase2X1XP6Interval.2 : ℝ) ≤ ((3269003158891601326381732817613489509 / 31250000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X1XP6_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X1XP6_exact_interval.1, manuscriptCase2X1XP6_exact_interval.2.trans hhi⟩

def manuscriptCase2X1XP8Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-32899 / 1562500) (9091287 / 100000000) (1) (2) (212782844349191138381621 / 195312500000000000000000) (773326039 / 461283260390)

private theorem manuscriptCase2X1XP8_arg_eq : barrierCase2X1XP8LogArg = barrierComplex (-773326039 / 312500000000) (46128326039 / 31250000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X1XP8LogArg, Case2PointData.X1, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X1XP8_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 = barrierComplex (-32899 / 1562500) (9091287 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X1XP8_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X1 : ℝ) (barrierP2Tail.getD 8 (0, 0)) ∈ Set.Icc (manuscriptCase2X1XP8Interval.1 : ℝ) (manuscriptCase2X1XP8Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 * Complex.log barrierCase2X1XP8LogArg).re ∈ _
  rw [manuscriptCase2X1XP8_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-32899 / 1562500) (9091287 / 100000000)
    barrierCase2X1XP8LogArg (1) (2) (212782844349191138381621 / 195312500000000000000000) (46128326039 / 15625000000) (773326039 / 156250000000)
  have hratio : ((773326039 / 156250000000) / (46128326039 / 15625000000) : ℚ) = (773326039 / 461283260390) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X1XP8Interval
  apply h
  all_goals
    try rw [manuscriptCase2X1XP8_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X1XP8_rounded_endpoints :
    (-1511571662088341757996962674443090286487 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X1XP8Interval.1 ∧ manuscriptCase2X1XP8Interval.2 ≤ (-1511571662088341692066949623686818668173 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X1XP8Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X1XP8_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X1 : ℝ) (barrierP2Tail.getD 8 (0, 0)) ∈ Set.Icc ((-1511571662088341757996962674443090286487 / 10000000000000000000000000000000000000000) : ℝ) ((-1511571662088341692066949623686818668173 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-1511571662088341757996962674443090286487 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X1XP8Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X1XP8_rounded_endpoints.1
  have hhi : (manuscriptCase2X1XP8Interval.2 : ℝ) ≤ ((-1511571662088341692066949623686818668173 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X1XP8_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X1XP8_exact_interval.1, manuscriptCase2X1XP8_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
