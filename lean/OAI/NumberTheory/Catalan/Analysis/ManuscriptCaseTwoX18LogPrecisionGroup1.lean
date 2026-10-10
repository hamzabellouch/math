import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoLogsX18Group0

namespace OAI

noncomputable section
namespace InternalCatalan

def manuscriptCase2X18XP4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-1231651 / 100000000) (-1200529 / 20000000) (1) (2) (474721 / 320000) (-111 / 680)

private theorem manuscriptCase2X18XP4_arg_eq : barrierCase2X18XP4LogArg = barrierComplex (111 / 400) (17 / 10) := by
  apply Complex.ext <;> norm_num [barrierCase2X18XP4LogArg, Case2PointData.X18, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X18XP4_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 = barrierComplex (-1231651 / 100000000) (-1200529 / 20000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X18XP4_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X18 : ℝ) (barrierP2Tail.getD 4 (0, 0)) ∈ Set.Icc (manuscriptCase2X18XP4Interval.1 : ℝ) (manuscriptCase2X18XP4Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X18XP4LogArg).re ∈ _
  rw [manuscriptCase2X18XP4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-1231651 / 100000000) (-1200529 / 20000000)
    barrierCase2X18XP4LogArg (1) (2) (474721 / 320000) (17 / 5) (-111 / 200)
  have hratio : ((-111 / 200) / (17 / 5) : ℚ) = (-111 / 680) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X18XP4Interval
  apply h
  all_goals
    try rw [manuscriptCase2X18XP4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X18XP4_rounded_endpoints :
    (77879123987313031111311691611143254697 / 1000000000000000000000000000000000000000) ≤ manuscriptCase2X18XP4Interval.1 ∧ manuscriptCase2X18XP4Interval.2 ≤ (778791239873130354643227616232932558959 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X18XP4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X18XP4_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X18 : ℝ) (barrierP2Tail.getD 4 (0, 0)) ∈ Set.Icc ((77879123987313031111311691611143254697 / 1000000000000000000000000000000000000000) : ℝ) ((778791239873130354643227616232932558959 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((77879123987313031111311691611143254697 / 1000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X18XP4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X18XP4_rounded_endpoints.1
  have hhi : (manuscriptCase2X18XP4Interval.2 : ℝ) ≤ ((778791239873130354643227616232932558959 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X18XP4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X18XP4_exact_interval.1, manuscriptCase2X18XP4_exact_interval.2.trans hhi⟩

def manuscriptCase2X18XP6Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-1612959 / 50000000) (-4464117 / 50000000) (2) (2) (16238150041 / 15625000000) (-21629 / 125580)

private theorem manuscriptCase2X18XP6_arg_eq : barrierCase2X18XP6LogArg = barrierComplex (21629 / 62500) (6279 / 3125) := by
  apply Complex.ext <;> norm_num [barrierCase2X18XP6LogArg, Case2PointData.X18, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X18XP6_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 = barrierComplex (-1612959 / 50000000) (-4464117 / 50000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X18XP6_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X18 : ℝ) (barrierP2Tail.getD 6 (0, 0)) ∈ Set.Icc (manuscriptCase2X18XP6Interval.1 : ℝ) (manuscriptCase2X18XP6Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 * Complex.log barrierCase2X18XP6LogArg).re ∈ _
  rw [manuscriptCase2X18XP6_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-1612959 / 50000000) (-4464117 / 50000000)
    barrierCase2X18XP6LogArg (2) (2) (16238150041 / 15625000000) (12558 / 3125) (-21629 / 31250)
  have hratio : ((-21629 / 31250) / (12558 / 3125) : ℚ) = (-21629 / 125580) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X18XP6Interval
  apply h
  all_goals
    try rw [manuscriptCase2X18XP6_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X18XP6_rounded_endpoints :
    (510176076523769173585399616762667593337 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2X18XP6Interval.1 ∧ manuscriptCase2X18XP6Interval.2 ≤ (8162817224380307295583642427396596709 / 80000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X18XP6Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X18XP6_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X18 : ℝ) (barrierP2Tail.getD 6 (0, 0)) ∈ Set.Icc ((510176076523769173585399616762667593337 / 5000000000000000000000000000000000000000) : ℝ) ((8162817224380307295583642427396596709 / 80000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((510176076523769173585399616762667593337 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X18XP6Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X18XP6_rounded_endpoints.1
  have hhi : (manuscriptCase2X18XP6Interval.2 : ℝ) ≤ ((8162817224380307295583642427396596709 / 80000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X18XP6_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X18XP6_exact_interval.1, manuscriptCase2X18XP6_exact_interval.2.trans hhi⟩

def manuscriptCase2X18XP8Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-32899 / 1562500) (9091287 / 100000000) (1) (2) (10905416041 / 7812500000) (1371 / 104420)

private theorem manuscriptCase2X18XP8_arg_eq : barrierCase2X18XP8LogArg = barrierComplex (-1371 / 62500) (5221 / 3125) := by
  apply Complex.ext <;> norm_num [barrierCase2X18XP8LogArg, Case2PointData.X18, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X18XP8_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 = barrierComplex (-32899 / 1562500) (9091287 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X18XP8_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X18 : ℝ) (barrierP2Tail.getD 8 (0, 0)) ∈ Set.Icc (manuscriptCase2X18XP8Interval.1 : ℝ) (manuscriptCase2X18XP8Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 * Complex.log barrierCase2X18XP8LogArg).re ∈ _
  rw [manuscriptCase2X18XP8_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-32899 / 1562500) (9091287 / 100000000)
    barrierCase2X18XP8LogArg (1) (2) (10905416041 / 7812500000) (10442 / 3125) (1371 / 31250)
  have hratio : ((1371 / 31250) / (10442 / 3125) : ℚ) = (1371 / 104420) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X18XP8Interval
  apply h
  all_goals
    try rw [manuscriptCase2X18XP8_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X18XP8_rounded_endpoints :
    (-774038830477566398675746773127512539643 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2X18XP8Interval.1 ∧ manuscriptCase2X18XP8Interval.2 ≤ (-1548077660955132731421480495498684710259 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X18XP8Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X18XP8_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X18 : ℝ) (barrierP2Tail.getD 8 (0, 0)) ∈ Set.Icc ((-774038830477566398675746773127512539643 / 5000000000000000000000000000000000000000) : ℝ) ((-1548077660955132731421480495498684710259 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-774038830477566398675746773127512539643 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X18XP8Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X18XP8_rounded_endpoints.1
  have hhi : (manuscriptCase2X18XP8Interval.2 : ℝ) ≤ ((-1548077660955132731421480495498684710259 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X18XP8_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X18XP8_exact_interval.1, manuscriptCase2X18XP8_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
