import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoLogsX5Group0

namespace OAI

noncomputable section
namespace InternalCatalan

def manuscriptCase2X5XP4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-1231651 / 100000000) (-1200529 / 20000000) (-1) (1) (1357569828167262657649 / 1250000000000000000000) (20257890343 / 48007890343)

private theorem manuscriptCase2X5XP4_arg_eq : barrierCase2X5XP4LogArg = barrierComplex (111 / 400) (34132890343 / 50000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X5XP4LogArg, Case2PointData.X5, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X5XP4_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 = barrierComplex (-1231651 / 100000000) (-1200529 / 20000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X5XP4_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X5 : ℝ) (barrierP2Tail.getD 4 (0, 0)) ∈ Set.Icc (manuscriptCase2X5XP4Interval.1 : ℝ) (manuscriptCase2X5XP4Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X5XP4LogArg).re ∈ _
  rw [manuscriptCase2X5XP4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-1231651 / 100000000) (-1200529 / 20000000)
    barrierCase2X5XP4LogArg (-1) (1) (1357569828167262657649 / 1250000000000000000000) (48007890343 / 50000000000) (20257890343 / 50000000000)
  have hratio : ((20257890343 / 50000000000) / (48007890343 / 50000000000) : ℚ) = (20257890343 / 48007890343) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X5XP4Interval
  apply h
  all_goals
    try rw [manuscriptCase2X5XP4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X5XP4_rounded_endpoints :
    (748735075883438560845866589182805835723 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X5XP4Interval.1 ∧ manuscriptCase2X5XP4Interval.2 ≤ (748735075883438582620412968643460715247 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X5XP4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X5XP4_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X5 : ℝ) (barrierP2Tail.getD 4 (0, 0)) ∈ Set.Icc ((748735075883438560845866589182805835723 / 10000000000000000000000000000000000000000) : ℝ) ((748735075883438582620412968643460715247 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((748735075883438560845866589182805835723 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X5XP4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X5XP4_rounded_endpoints.1
  have hhi : (manuscriptCase2X5XP4Interval.2 : ℝ) ≤ ((748735075883438582620412968643460715247 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X5XP4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X5XP4_exact_interval.1, manuscriptCase2X5XP4_exact_interval.2.trans hhi⟩

def manuscriptCase2X5XP6Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-1612959 / 50000000) (-4464117 / 50000000) (-1) (2) (343914747856365384344389 / 195312500000000000000000) (-147469792817 / 567597928170)

private theorem manuscriptCase2X5XP6_arg_eq : barrierCase2X5XP6LogArg = barrierComplex (147469792817 / 625000000000) (56759792817 / 62500000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X5XP6LogArg, Case2PointData.X5, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X5XP6_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 = barrierComplex (-1612959 / 50000000) (-4464117 / 50000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X5XP6_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X5 : ℝ) (barrierP2Tail.getD 6 (0, 0)) ∈ Set.Icc (manuscriptCase2X5XP6Interval.1 : ℝ) (manuscriptCase2X5XP6Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 * Complex.log barrierCase2X5XP6LogArg).re ∈ _
  rw [manuscriptCase2X5XP6_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-1612959 / 50000000) (-4464117 / 50000000)
    barrierCase2X5XP6LogArg (-1) (2) (343914747856365384344389 / 195312500000000000000000) (56759792817 / 31250000000) (-147469792817 / 312500000000)
  have hratio : ((-147469792817 / 312500000000) / (56759792817 / 31250000000) : ℚ) = (-147469792817 / 567597928170) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X5XP6Interval
  apply h
  all_goals
    try rw [manuscriptCase2X5XP6_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X5XP6_rounded_endpoints :
    (1196035373248216034741634267747303234387 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X5XP6Interval.1 ∧ manuscriptCase2X5XP6Interval.2 ≤ (1196035373248216099497025708466810666361 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X5XP6Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X5XP6_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X5 : ℝ) (barrierP2Tail.getD 6 (0, 0)) ∈ Set.Icc ((1196035373248216034741634267747303234387 / 10000000000000000000000000000000000000000) : ℝ) ((1196035373248216099497025708466810666361 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((1196035373248216034741634267747303234387 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X5XP6Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X5XP6_rounded_endpoints.1
  have hhi : (manuscriptCase2X5XP6Interval.2 : ℝ) ≤ ((1196035373248216099497025708466810666361 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X5XP6_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X5XP6_exact_interval.1, manuscriptCase2X5XP6_exact_interval.2.trans hhi⟩

def manuscriptCase2X5XP8Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-32899 / 1562500) (9091287 / 100000000) (-2) (2) (129771659797085664344389 / 97656250000000000000000) (-55110207183 / 355997928170)

private theorem manuscriptCase2X5XP8_arg_eq : barrierCase2X5XP8LogArg = barrierComplex (55110207183 / 625000000000) (35599792817 / 62500000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X5XP8LogArg, Case2PointData.X5, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X5XP8_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 = barrierComplex (-32899 / 1562500) (9091287 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X5XP8_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X5 : ℝ) (barrierP2Tail.getD 8 (0, 0)) ∈ Set.Icc (manuscriptCase2X5XP8Interval.1 : ℝ) (manuscriptCase2X5XP8Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 * Complex.log barrierCase2X5XP8LogArg).re ∈ _
  rw [manuscriptCase2X5XP8_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-32899 / 1562500) (9091287 / 100000000)
    barrierCase2X5XP8LogArg (-2) (2) (129771659797085664344389 / 97656250000000000000000) (35599792817 / 31250000000) (-55110207183 / 312500000000)
  have hratio : ((-55110207183 / 312500000000) / (35599792817 / 31250000000) : ℚ) = (-55110207183 / 355997928170) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X5XP8Interval
  apply h
  all_goals
    try rw [manuscriptCase2X5XP8_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X5XP8_rounded_endpoints :
    (-1172414789232990960314857696824798509193 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X5XP8Interval.1 ∧ manuscriptCase2X5XP8Interval.2 ≤ (-1172414789232990894370627021401485342449 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X5XP8Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X5XP8_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X5 : ℝ) (barrierP2Tail.getD 8 (0, 0)) ∈ Set.Icc ((-1172414789232990960314857696824798509193 / 10000000000000000000000000000000000000000) : ℝ) ((-1172414789232990894370627021401485342449 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-1172414789232990960314857696824798509193 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X5XP8Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X5XP8_rounded_endpoints.1
  have hhi : (manuscriptCase2X5XP8Interval.2 : ℝ) ≤ ((-1172414789232990894370627021401485342449 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X5XP8_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X5XP8_exact_interval.1, manuscriptCase2X5XP8_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
