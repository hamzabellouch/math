import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoLogsX15Group0

namespace OAI

noncomputable section
namespace InternalCatalan

def manuscriptCase2X15XP4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-1231651 / 100000000) (-1200529 / 20000000) (1) (-2) (5278681165261482578889 / 5000000000000000000000) (4625000000 / 23772452639)

private theorem manuscriptCase2X15XP4_arg_eq : barrierCase2X15XP4LogArg = barrierComplex (111 / 400) (-71317357917 / 50000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X15XP4LogArg, Case2PointData.X15, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X15XP4_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 = barrierComplex (-1231651 / 100000000) (-1200529 / 20000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X15XP4_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X15 : ℝ) (barrierP2Tail.getD 4 (0, 0)) ∈ Set.Icc (manuscriptCase2X15XP4Interval.1 : ℝ) (manuscriptCase2X15XP4Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X15XP4LogArg).re ∈ _
  rw [manuscriptCase2X15XP4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-1231651 / 100000000) (-1200529 / 20000000)
    barrierCase2X15XP4LogArg (1) (-2) (5278681165261482578889 / 5000000000000000000000) (71317357917 / 25000000000) (111 / 200)
  have hratio : ((111 / 200) / (71317357917 / 25000000000) : ℚ) = (4625000000 / 23772452639) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X15XP4Interval
  apply h
  all_goals
    try rw [manuscriptCase2X15XP4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X15XP4_rounded_endpoints :
    (-873576834285991544301306785698792776009 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X15XP4Interval.1 ∧ manuscriptCase2X15XP4Interval.2 ≤ (-436788417142995750385598042797424798131 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X15XP4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X15XP4_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X15 : ℝ) (barrierP2Tail.getD 4 (0, 0)) ∈ Set.Icc ((-873576834285991544301306785698792776009 / 10000000000000000000000000000000000000000) : ℝ) ((-436788417142995750385598042797424798131 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-873576834285991544301306785698792776009 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X15XP4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X15XP4_rounded_endpoints.1
  have hhi : (manuscriptCase2X15XP4Interval.2 : ℝ) ≤ ((-436788417142995750385598042797424798131 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X15XP4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X15XP4_exact_interval.1, manuscriptCase2X15XP4_exact_interval.2.trans hhi⟩

def manuscriptCase2X15XP6Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-1612959 / 50000000) (-4464117 / 50000000) (0) (-2) (738044770399046330268029 / 390625000000000000000000) (4801809877 / 859081901230)

private theorem manuscriptCase2X15XP6_arg_eq : barrierCase2X15XP6LogArg = barrierComplex (4801809877 / 625000000000) (-85908190123 / 62500000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X15XP6LogArg, Case2PointData.X15, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X15XP6_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 = barrierComplex (-1612959 / 50000000) (-4464117 / 50000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X15XP6_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X15 : ℝ) (barrierP2Tail.getD 6 (0, 0)) ∈ Set.Icc (manuscriptCase2X15XP6Interval.1 : ℝ) (manuscriptCase2X15XP6Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 * Complex.log barrierCase2X15XP6LogArg).re ∈ _
  rw [manuscriptCase2X15XP6_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-1612959 / 50000000) (-4464117 / 50000000)
    barrierCase2X15XP6LogArg (0) (-2) (738044770399046330268029 / 390625000000000000000000) (85908190123 / 31250000000) (4801809877 / 312500000000)
  have hratio : ((4801809877 / 312500000000) / (85908190123 / 31250000000) : ℚ) = (4801809877 / 859081901230) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X15XP6Interval
  apply h
  all_goals
    try rw [manuscriptCase2X15XP6_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X15XP6_rounded_endpoints :
    (-1500078921735373772321285742583838338811 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X15XP6Interval.1 ∧ manuscriptCase2X15XP6Interval.2 ≤ (-1500078921735373707586572814433257083653 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X15XP6Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X15XP6_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X15 : ℝ) (barrierP2Tail.getD 6 (0, 0)) ∈ Set.Icc ((-1500078921735373772321285742583838338811 / 10000000000000000000000000000000000000000) : ℝ) ((-1500078921735373707586572814433257083653 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-1500078921735373772321285742583838338811 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X15XP6Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X15XP6_rounded_endpoints.1
  have hhi : (manuscriptCase2X15XP6Interval.2 : ℝ) ≤ ((-1500078921735373707586572814433257083653 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X15XP6_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X15XP6_exact_interval.1, manuscriptCase2X15XP6_exact_interval.2.trans hhi⟩

def manuscriptCase2X15XP8Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-32899 / 1562500) (9091287 / 100000000) (1) (-2) (1185475946109817010268029 / 781250000000000000000000) (197778190123 / 1070681901230)

private theorem manuscriptCase2X15XP8_arg_eq : barrierCase2X15XP8LogArg = barrierComplex (197778190123 / 625000000000) (-107068190123 / 62500000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X15XP8LogArg, Case2PointData.X15, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X15XP8_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 = barrierComplex (-32899 / 1562500) (9091287 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X15XP8_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X15 : ℝ) (barrierP2Tail.getD 8 (0, 0)) ∈ Set.Icc (manuscriptCase2X15XP8Interval.1 : ℝ) (manuscriptCase2X15XP8Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 * Complex.log barrierCase2X15XP8LogArg).re ∈ _
  rw [manuscriptCase2X15XP8_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-32899 / 1562500) (9091287 / 100000000)
    barrierCase2X15XP8LogArg (1) (-2) (1185475946109817010268029 / 781250000000000000000000) (107068190123 / 31250000000) (197778190123 / 312500000000)
  have hratio : ((197778190123 / 312500000000) / (107068190123 / 31250000000) : ℚ) = (197778190123 / 1070681901230) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X15XP8Interval
  apply h
  all_goals
    try rw [manuscriptCase2X15XP8_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X15XP8_rounded_endpoints :
    (1145118938743913724711905795915874826187 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X15XP8Interval.1 ∧ manuscriptCase2X15XP8Interval.2 ≤ (1145118938743913790641918846896265309357 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X15XP8Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X15XP8_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X15 : ℝ) (barrierP2Tail.getD 8 (0, 0)) ∈ Set.Icc ((1145118938743913724711905795915874826187 / 10000000000000000000000000000000000000000) : ℝ) ((1145118938743913790641918846896265309357 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((1145118938743913724711905795915874826187 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X15XP8Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X15XP8_rounded_endpoints.1
  have hhi : (manuscriptCase2X15XP8Interval.2 : ℝ) ≤ ((1145118938743913790641918846896265309357 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X15XP8_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X15XP8_exact_interval.1, manuscriptCase2X15XP8_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
