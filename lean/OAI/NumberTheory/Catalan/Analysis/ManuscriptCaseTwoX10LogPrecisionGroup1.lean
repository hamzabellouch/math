import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoLogsX10Group0

namespace OAI

noncomputable section
namespace InternalCatalan

def manuscriptCase2X10XP4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-1231651 / 100000000) (-1200529 / 20000000) (-3) (-1) (2011329480391080235849 / 1250000000000000000000) (-7481619043 / 62981619043)

private theorem manuscriptCase2X10XP4_arg_eq : barrierCase2X10XP4LogArg = barrierComplex (111 / 400) (-35231619043 / 100000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X10XP4LogArg, Case2PointData.X10, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X10XP4_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 = barrierComplex (-1231651 / 100000000) (-1200529 / 20000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X10XP4_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X10 : ℝ) (barrierP2Tail.getD 4 (0, 0)) ∈ Set.Icc (manuscriptCase2X10XP4Interval.1 : ℝ) (manuscriptCase2X10XP4Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X10XP4LogArg).re ∈ _
  rw [manuscriptCase2X10XP4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-1231651 / 100000000) (-1200529 / 20000000)
    barrierCase2X10XP4LogArg (-3) (-1) (2011329480391080235849 / 1250000000000000000000) (62981619043 / 100000000000) (-7481619043 / 100000000000)
  have hratio : ((-7481619043 / 100000000000) / (62981619043 / 100000000000) : ℚ) = (-7481619043 / 62981619043) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X10XP4Interval
  apply h
  all_goals
    try rw [manuscriptCase2X10XP4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X10XP4_rounded_endpoints :
    (-443654348419764787003484157297366350949 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X10XP4Interval.1 ∧ manuscriptCase2X10XP4Interval.2 ≤ (-110913587104941191304409248631812696467 / 2500000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X10XP4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X10XP4_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X10 : ℝ) (barrierP2Tail.getD 4 (0, 0)) ∈ Set.Icc ((-443654348419764787003484157297366350949 / 10000000000000000000000000000000000000000) : ℝ) ((-110913587104941191304409248631812696467 / 2500000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-443654348419764787003484157297366350949 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X10XP4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X10XP4_rounded_endpoints.1
  have hhi : (manuscriptCase2X10XP4Interval.2 : ℝ) ≤ ((-110913587104941191304409248631812696467 / 2500000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X10XP4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X10XP4_exact_interval.1, manuscriptCase2X10XP4_exact_interval.2.trans hhi⟩

def manuscriptCase2X10XP6Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-1612959 / 50000000) (-4464117 / 50000000) (-5) (-1) (94256688932155068654589 / 48828125000000000000000) (-110149389287 / 419976773053)

private theorem manuscriptCase2X10XP6_arg_eq : barrierCase2X10XP6LogArg = barrierComplex (154913691883 / 1250000000000) (-26506308117 / 125000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X10XP6LogArg, Case2PointData.X10, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X10XP6_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 = barrierComplex (-1612959 / 50000000) (-4464117 / 50000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X10XP6_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X10 : ℝ) (barrierP2Tail.getD 6 (0, 0)) ∈ Set.Icc (manuscriptCase2X10XP6Interval.1 : ℝ) (manuscriptCase2X10XP6Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 * Complex.log barrierCase2X10XP6LogArg).re ∈ _
  rw [manuscriptCase2X10XP6_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-1612959 / 50000000) (-4464117 / 50000000)
    barrierCase2X10XP6LogArg (-5) (-1) (94256688932155068654589 / 48828125000000000000000) (419976773053 / 1250000000000) (-110149389287 / 1250000000000)
  have hratio : ((-110149389287 / 1250000000000) / (419976773053 / 1250000000000) : ℚ) = (-110149389287 / 419976773053) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X10XP6Interval
  apply h
  all_goals
    try rw [manuscriptCase2X10XP6_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X10XP6_rounded_endpoints :
    (-477306871820870752862849719899943909083 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X10XP6Interval.1 ∧ manuscriptCase2X10XP6Interval.2 ≤ (-477306871820870720383584936860488632029 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X10XP6Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X10XP6_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X10 : ℝ) (barrierP2Tail.getD 6 (0, 0)) ∈ Set.Icc ((-477306871820870752862849719899943909083 / 10000000000000000000000000000000000000000) : ℝ) ((-477306871820870720383584936860488632029 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-477306871820870752862849719899943909083 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X10XP6Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X10XP6_rounded_endpoints.1
  have hhi : (manuscriptCase2X10XP6Interval.2 : ℝ) ≤ ((-477306871820870720383584936860488632029 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X10XP6_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X10XP6_exact_interval.1, manuscriptCase2X10XP6_exact_interval.2.trans hhi⟩

def manuscriptCase2X10XP8Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-32899 / 1562500) (9091287 / 100000000) (-2) (-2) (536329283627810508654589 / 390625000000000000000000) (250246308117 / 688263081170)

private theorem manuscriptCase2X10XP8_arg_eq : barrierCase2X10XP8LogArg = barrierComplex (250246308117 / 1250000000000) (-68826308117 / 125000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X10XP8LogArg, Case2PointData.X10, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X10XP8_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 = barrierComplex (-32899 / 1562500) (9091287 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X10XP8_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X10 : ℝ) (barrierP2Tail.getD 8 (0, 0)) ∈ Set.Icc (manuscriptCase2X10XP8Interval.1 : ℝ) (manuscriptCase2X10XP8Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 * Complex.log barrierCase2X10XP8LogArg).re ∈ _
  rw [manuscriptCase2X10XP8_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-32899 / 1562500) (9091287 / 100000000)
    barrierCase2X10XP8LogArg (-2) (-2) (536329283627810508654589 / 390625000000000000000000) (68826308117 / 62500000000) (250246308117 / 625000000000)
  have hratio : ((250246308117 / 625000000000) / (68826308117 / 62500000000) : ℚ) = (250246308117 / 688263081170) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X10XP8Interval
  apply h
  all_goals
    try rw [manuscriptCase2X10XP8_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X10XP8_rounded_endpoints :
    (152948315420936111934794756319045569721 / 1250000000000000000000000000000000000000) ≤ manuscriptCase2X10XP8Interval.1 ∧ manuscriptCase2X10XP8Interval.2 ≤ (611793261683744480711297101069034631053 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X10XP8Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X10XP8_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X10 : ℝ) (barrierP2Tail.getD 8 (0, 0)) ∈ Set.Icc ((152948315420936111934794756319045569721 / 1250000000000000000000000000000000000000) : ℝ) ((611793261683744480711297101069034631053 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((152948315420936111934794756319045569721 / 1250000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X10XP8Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X10XP8_rounded_endpoints.1
  have hhi : (manuscriptCase2X10XP8Interval.2 : ℝ) ≤ ((611793261683744480711297101069034631053 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X10XP8_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X10XP8_exact_interval.1, manuscriptCase2X10XP8_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
