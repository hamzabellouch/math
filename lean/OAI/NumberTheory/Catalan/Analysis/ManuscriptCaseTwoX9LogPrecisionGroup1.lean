import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoLogsX9Group0

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2X9XP4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-1231651 / 100000000) (-1200529 / 20000000) (-3) (-1) (362076611472086409729 / 312500000000000000000) (284480491 / 8965519509)

private theorem manuscriptCase2X9XP4_arg_eq : barrierCase2X9XP4LogArg = barrierComplex (111 / 400) (-13021558527 / 50000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X9XP4LogArg, Case2PointData.X9, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X9XP4_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 = barrierComplex (-1231651 / 100000000) (-1200529 / 20000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X9XP4_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X9 : ℝ) (barrierP2Tail.getD 4 (0, 0)) ∈ Set.Icc (manuscriptCase2X9XP4Interval.1 : ℝ) (manuscriptCase2X9XP4Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X9XP4LogArg).re ∈ _
  rw [manuscriptCase2X9XP4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-1231651 / 100000000) (-1200529 / 20000000)
    barrierCase2X9XP4LogArg (-3) (-1) (362076611472086409729 / 312500000000000000000) (26896558527 / 50000000000) (853441473 / 50000000000)
  have hratio : ((853441473 / 50000000000) / (26896558527 / 50000000000) : ℚ) = (284480491 / 8965519509) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X9XP4Interval
  apply h
  all_goals
    try rw [manuscriptCase2X9XP4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X9XP4_rounded_endpoints :
    (-20838570481651905631040817677046961801 / 625000000000000000000000000000000000000) ≤ manuscriptCase2X9XP4Interval.1 ∧ manuscriptCase2X9XP4Interval.2 ≤ (-20838570481651904269425370926671006423 / 625000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X9XP4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X9XP4_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X9 : ℝ) (barrierP2Tail.getD 4 (0, 0)) ∈ Set.Icc ((-20838570481651905631040817677046961801 / 625000000000000000000000000000000000000) : ℝ) ((-20838570481651904269425370926671006423 / 625000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-20838570481651905631040817677046961801 / 625000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X9XP4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X9XP4_rounded_endpoints.1
  have hhi : (manuscriptCase2X9XP4Interval.2 : ℝ) ≤ ((-20838570481651904269425370926671006423 / 625000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X9XP4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X9XP4_exact_interval.1, manuscriptCase2X9XP4_exact_interval.2.trans hhi⟩

def manuscriptCase2X9XP6Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-1612959 / 50000000) (-4464117 / 50000000) (-6) (-1) (11953607231246455797269 / 6103515625000000000000) (13298570157 / 154046624417)

private theorem manuscriptCase2X9XP6_arg_eq : barrierCase2X9XP6LogArg = barrierComplex (83672597287 / 625000000000) (-7037402713 / 62500000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X9XP6LogArg, Case2PointData.X9, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X9XP6_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 = barrierComplex (-1612959 / 50000000) (-4464117 / 50000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X9XP6_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X9 : ℝ) (barrierP2Tail.getD 6 (0, 0)) ∈ Set.Icc (manuscriptCase2X9XP6Interval.1 : ℝ) (manuscriptCase2X9XP6Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 * Complex.log barrierCase2X9XP6LogArg).re ∈ _
  rw [manuscriptCase2X9XP6_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-1612959 / 50000000) (-4464117 / 50000000)
    barrierCase2X9XP6LogArg (-6) (-1) (11953607231246455797269 / 6103515625000000000000) (154046624417 / 625000000000) (13298570157 / 625000000000)
  have hratio : ((13298570157 / 625000000000) / (154046624417 / 625000000000) : ℚ) = (13298570157 / 154046624417) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X9XP6Interval
  apply h
  all_goals
    try rw [manuscriptCase2X9XP6_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X9XP6_rounded_endpoints :
    (-6194380484819044640636912758727750973 / 1000000000000000000000000000000000000000) ≤ manuscriptCase2X9XP6Interval.1 ∧ manuscriptCase2X9XP6Interval.2 ≤ (-30971902424095206950665783213988638939 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X9XP6Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X9XP6_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X9 : ℝ) (barrierP2Tail.getD 6 (0, 0)) ∈ Set.Icc ((-6194380484819044640636912758727750973 / 1000000000000000000000000000000000000000) : ℝ) ((-30971902424095206950665783213988638939 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-6194380484819044640636912758727750973 / 1000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X9XP6Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X9XP6_rounded_endpoints.1
  have hhi : (manuscriptCase2X9XP6Interval.2 : ℝ) ≤ ((-30971902424095206950665783213988638939 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X9XP6_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X9XP6_exact_interval.1, manuscriptCase2X9XP6_exact_interval.2.trans hhi⟩

def manuscriptCase2X9XP8Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-32899 / 1562500) (9091287 / 100000000) (-3) (-2) (93648322395861535797269 / 48828125000000000000000) (118907402713 / 281974027130)

private theorem manuscriptCase2X9XP8_arg_eq : barrierCase2X9XP8LogArg = barrierComplex (118907402713 / 625000000000) (-28197402713 / 62500000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X9XP8LogArg, Case2PointData.X9, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X9XP8_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 = barrierComplex (-32899 / 1562500) (9091287 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X9XP8_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X9 : ℝ) (barrierP2Tail.getD 8 (0, 0)) ∈ Set.Icc (manuscriptCase2X9XP8Interval.1 : ℝ) (manuscriptCase2X9XP8Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 * Complex.log barrierCase2X9XP8LogArg).re ∈ _
  rw [manuscriptCase2X9XP8_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-32899 / 1562500) (9091287 / 100000000)
    barrierCase2X9XP8LogArg (-3) (-2) (93648322395861535797269 / 48828125000000000000000) (28197402713 / 31250000000) (118907402713 / 312500000000)
  have hratio : ((118907402713 / 312500000000) / (28197402713 / 31250000000) : ℚ) = (118907402713 / 281974027130) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X9XP8Interval
  apply h
  all_goals
    try rw [manuscriptCase2X9XP8_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X9XP8_rounded_endpoints :
    (243121475005977726676136137807170192273 / 2000000000000000000000000000000000000000) ≤ manuscriptCase2X9XP8Interval.1 ∧ manuscriptCase2X9XP8Interval.2 ≤ (243121475005977739869719778833867586059 / 2000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X9XP8Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X9XP8_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X9 : ℝ) (barrierP2Tail.getD 8 (0, 0)) ∈ Set.Icc ((243121475005977726676136137807170192273 / 2000000000000000000000000000000000000000) : ℝ) ((243121475005977739869719778833867586059 / 2000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((243121475005977726676136137807170192273 / 2000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X9XP8Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X9XP8_rounded_endpoints.1
  have hhi : (manuscriptCase2X9XP8Interval.2 : ℝ) ≤ ((243121475005977739869719778833867586059 / 2000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X9XP8_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X9XP8_exact_interval.1, manuscriptCase2X9XP8_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
