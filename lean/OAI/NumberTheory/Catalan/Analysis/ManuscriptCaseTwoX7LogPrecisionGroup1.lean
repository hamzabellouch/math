import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoLogsX7Group0

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2X7XP4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-1231651 / 100000000) (-1200529 / 20000000) (-3) (1) (501478349017808341441 / 312500000000000000000) (3702335521 / 31452335521)

private theorem manuscriptCase2X7XP4_arg_eq : barrierCase2X7XP4LogArg = barrierComplex (111 / 400) (17577335521 / 50000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X7XP4LogArg, Case2PointData.X7, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X7XP4_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 = barrierComplex (-1231651 / 100000000) (-1200529 / 20000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X7XP4_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X7 : ℝ) (barrierP2Tail.getD 4 (0, 0)) ∈ Set.Icc (manuscriptCase2X7XP4Interval.1 : ℝ) (manuscriptCase2X7XP4Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X7XP4LogArg).re ∈ _
  rw [manuscriptCase2X7XP4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-1231651 / 100000000) (-1200529 / 20000000)
    barrierCase2X7XP4LogArg (-3) (1) (501478349017808341441 / 312500000000000000000) (31452335521 / 50000000000) (3702335521 / 50000000000)
  have hratio : ((3702335521 / 50000000000) / (31452335521 / 50000000000) : ℚ) = (3702335521 / 31452335521) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X7XP4Interval
  apply h
  all_goals
    try rw [manuscriptCase2X7XP4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X7XP4_rounded_endpoints :
    (640713128270994311795311756980879055459 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X7XP4Interval.1 ∧ manuscriptCase2X7XP4Interval.2 ≤ (320356564135497166790579458517513551127 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X7XP4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X7XP4_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X7 : ℝ) (barrierP2Tail.getD 4 (0, 0)) ∈ Set.Icc ((640713128270994311795311756980879055459 / 10000000000000000000000000000000000000000) : ℝ) ((320356564135497166790579458517513551127 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((640713128270994311795311756980879055459 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X7XP4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X7XP4_rounded_endpoints.1
  have hhi : (manuscriptCase2X7XP4Interval.2 : ℝ) ≤ ((320356564135497166790579458517513551127 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X7XP4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X7XP4_exact_interval.1, manuscriptCase2X7XP4_exact_interval.2.trans hhi⟩

def manuscriptCase2X7XP6Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-1612959 / 50000000) (-4464117 / 50000000) (-2) (1) (133711306491449938598101 / 97656250000000000000000) (218539908991 / 468682110989)

private theorem manuscriptCase2X7XP6_arg_eq : barrierCase2X7XP6LogArg = barrierComplex (125071100999 / 625000000000) (34361100999 / 62500000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X7XP6LogArg, Case2PointData.X7, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X7XP6_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 = barrierComplex (-1612959 / 50000000) (-4464117 / 50000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X7XP6_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X7 : ℝ) (barrierP2Tail.getD 6 (0, 0)) ∈ Set.Icc (manuscriptCase2X7XP6Interval.1 : ℝ) (manuscriptCase2X7XP6Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 * Complex.log barrierCase2X7XP6LogArg).re ∈ _
  rw [manuscriptCase2X7XP6_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-1612959 / 50000000) (-4464117 / 50000000)
    barrierCase2X7XP6LogArg (-2) (1) (133711306491449938598101 / 97656250000000000000000) (468682110989 / 625000000000) (218539908991 / 625000000000)
  have hratio : ((218539908991 / 625000000000) / (468682110989 / 625000000000) : ℚ) = (218539908991 / 468682110989) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X7XP6Interval
  apply h
  all_goals
    try rw [manuscriptCase2X7XP6_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X7XP6_rounded_endpoints :
    (1263693362705087429443858846945164562733 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X7XP6Interval.1 ∧ manuscriptCase2X7XP6Interval.2 ≤ (63184668135254373145617141094112213907 / 500000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X7XP6Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X7XP6_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X7 : ℝ) (barrierP2Tail.getD 6 (0, 0)) ∈ Set.Icc ((1263693362705087429443858846945164562733 / 10000000000000000000000000000000000000000) : ℝ) ((63184668135254373145617141094112213907 / 500000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((1263693362705087429443858846945164562733 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X7XP6Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X7XP6_rounded_endpoints.1
  have hhi : (manuscriptCase2X7XP6Interval.2 : ℝ) ≤ ((63184668135254373145617141094112213907 / 500000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X7XP6_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X7XP6_exact_interval.1, manuscriptCase2X7XP6_exact_interval.2.trans hhi⟩

def manuscriptCase2X7XP8Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-32899 / 1562500) (9091287 / 100000000) (-5) (1) (23434536182927098598101 / 12207031250000000000000) (54502110989 / 209519908991)

private theorem manuscriptCase2X7XP8_arg_eq : barrierCase2X7XP8LogArg = barrierComplex (77508899001 / 625000000000) (13201100999 / 62500000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X7XP8LogArg, Case2PointData.X7, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X7XP8_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 = barrierComplex (-32899 / 1562500) (9091287 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X7XP8_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X7 : ℝ) (barrierP2Tail.getD 8 (0, 0)) ∈ Set.Icc (manuscriptCase2X7XP8Interval.1 : ℝ) (manuscriptCase2X7XP8Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 * Complex.log barrierCase2X7XP8LogArg).re ∈ _
  rw [manuscriptCase2X7XP8_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-32899 / 1562500) (9091287 / 100000000)
    barrierCase2X7XP8LogArg (-5) (1) (23434536182927098598101 / 12207031250000000000000) (209519908991 / 625000000000) (54502110989 / 625000000000)
  have hratio : ((54502110989 / 625000000000) / (209519908991 / 625000000000) : ℚ) = (54502110989 / 209519908991) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X7XP8Interval
  apply h
  all_goals
    try rw [manuscriptCase2X7XP8_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X7XP8_rounded_endpoints :
    (-324595295549605046159521311731058759609 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2X7XP8Interval.1 ∧ manuscriptCase2X7XP8Interval.2 ≤ (-129838118219842011857664894206578031623 / 2000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X7XP8Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X7XP8_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X7 : ℝ) (barrierP2Tail.getD 8 (0, 0)) ∈ Set.Icc ((-324595295549605046159521311731058759609 / 5000000000000000000000000000000000000000) : ℝ) ((-129838118219842011857664894206578031623 / 2000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-324595295549605046159521311731058759609 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X7XP8Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X7XP8_rounded_endpoints.1
  have hhi : (manuscriptCase2X7XP8Interval.2 : ℝ) ≤ ((-129838118219842011857664894206578031623 / 2000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X7XP8_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X7XP8_exact_interval.1, manuscriptCase2X7XP8_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
