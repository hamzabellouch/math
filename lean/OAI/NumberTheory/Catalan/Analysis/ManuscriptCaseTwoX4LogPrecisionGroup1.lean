import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoLogsX4Group0

namespace OAI

noncomputable section
namespace InternalCatalan

def manuscriptCase2X4XP4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-1231651 / 100000000) (-1200529 / 20000000) (-1) (2) (341687731323610228041 / 200000000000000000000) (-1850000000 / 5877312607)

private theorem manuscriptCase2X4XP4_arg_eq : barrierCase2X4XP4LogArg = barrierComplex (111 / 400) (17631937821 / 20000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X4XP4LogArg, Case2PointData.X4, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X4XP4_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 = barrierComplex (-1231651 / 100000000) (-1200529 / 20000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X4XP4_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X4 : ℝ) (barrierP2Tail.getD 4 (0, 0)) ∈ Set.Icc (manuscriptCase2X4XP4Interval.1 : ℝ) (manuscriptCase2X4XP4Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X4XP4LogArg).re ∈ _
  rw [manuscriptCase2X4XP4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-1231651 / 100000000) (-1200529 / 20000000)
    barrierCase2X4XP4LogArg (-1) (2) (341687731323610228041 / 200000000000000000000) (17631937821 / 10000000000) (-111 / 200)
  have hratio : ((-111 / 200) / (17631937821 / 10000000000) : ℚ) = (-1850000000 / 5877312607) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X4XP4Interval
  apply h
  all_goals
    try rw [manuscriptCase2X4XP4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X4XP4_rounded_endpoints :
    (769545221221033133967480607573482955627 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X4XP4Interval.1 ∧ manuscriptCase2X4XP4Interval.2 ≤ (96193152652629147187199039899234031123 / 1250000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X4XP4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X4XP4_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X4 : ℝ) (barrierP2Tail.getD 4 (0, 0)) ∈ Set.Icc ((769545221221033133967480607573482955627 / 10000000000000000000000000000000000000000) : ℝ) ((96193152652629147187199039899234031123 / 1250000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((769545221221033133967480607573482955627 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X4XP4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X4XP4_rounded_endpoints.1
  have hhi : (manuscriptCase2X4XP4Interval.2 : ℝ) ≤ ((96193152652629147187199039899234031123 / 1250000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X4XP4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X4XP4_exact_interval.1, manuscriptCase2X4XP4_exact_interval.2.trans hhi⟩

def manuscriptCase2X4XP6Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-1612959 / 50000000) (-4464117 / 50000000) (0) (2) (83031437157925912200701 / 62500000000000000000000) (-64370974699 / 280869746990)

private theorem manuscriptCase2X4XP6_arg_eq : barrierCase2X4XP6LogArg = barrierComplex (64370974699 / 250000000000) (28086974699 / 25000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X4XP6LogArg, Case2PointData.X4, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X4XP6_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 = barrierComplex (-1612959 / 50000000) (-4464117 / 50000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X4XP6_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X4 : ℝ) (barrierP2Tail.getD 6 (0, 0)) ∈ Set.Icc (manuscriptCase2X4XP6Interval.1 : ℝ) (manuscriptCase2X4XP6Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 * Complex.log barrierCase2X4XP6LogArg).re ∈ _
  rw [manuscriptCase2X4XP6_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-1612959 / 50000000) (-4464117 / 50000000)
    barrierCase2X4XP6LogArg (0) (2) (83031437157925912200701 / 62500000000000000000000) (28086974699 / 12500000000) (-64370974699 / 125000000000)
  have hratio : ((-64370974699 / 125000000000) / (28086974699 / 12500000000) : ℚ) = (-64370974699 / 280869746990) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X4XP6Interval
  apply h
  all_goals
    try rw [manuscriptCase2X4XP6_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X4XP6_rounded_endpoints :
    (288869930299151824195615253883776486529 / 2500000000000000000000000000000000000000) ≤ manuscriptCase2X4XP6Interval.1 ∧ manuscriptCase2X4XP6Interval.2 ≤ (57773986059830368075802554241195276417 / 500000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X4XP6Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X4XP6_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X4 : ℝ) (barrierP2Tail.getD 6 (0, 0)) ∈ Set.Icc ((288869930299151824195615253883776486529 / 2500000000000000000000000000000000000000) : ℝ) ((57773986059830368075802554241195276417 / 500000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((288869930299151824195615253883776486529 / 2500000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X4XP6Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X4XP6_rounded_endpoints.1
  have hhi : (manuscriptCase2X4XP6Interval.2 : ℝ) ≤ ((57773986059830368075802554241195276417 / 500000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X4XP6_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X4XP6_exact_interval.1, manuscriptCase2X4XP6_exact_interval.2.trans hhi⟩

def manuscriptCase2X4XP8Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-32899 / 1562500) (9091287 / 100000000) (-1) (2) (38783703367839976200701 / 31250000000000000000000) (-16661025301 / 196229746990)

private theorem manuscriptCase2X4XP8_arg_eq : barrierCase2X4XP8LogArg = barrierComplex (16661025301 / 250000000000) (19622974699 / 25000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X4XP8LogArg, Case2PointData.X4, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X4XP8_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 = barrierComplex (-32899 / 1562500) (9091287 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X4XP8_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X4 : ℝ) (barrierP2Tail.getD 8 (0, 0)) ∈ Set.Icc (manuscriptCase2X4XP8Interval.1 : ℝ) (manuscriptCase2X4XP8Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 * Complex.log barrierCase2X4XP8LogArg).re ∈ _
  rw [manuscriptCase2X4XP8_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-32899 / 1562500) (9091287 / 100000000)
    barrierCase2X4XP8LogArg (-1) (2) (38783703367839976200701 / 31250000000000000000000) (19622974699 / 12500000000) (-16661025301 / 125000000000)
  have hratio : ((-16661025301 / 125000000000) / (19622974699 / 12500000000) : ℚ) = (-16661025301 / 196229746990) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X4XP8Interval
  apply h
  all_goals
    try rw [manuscriptCase2X4XP8_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X4XP8_rounded_endpoints :
    (-1300815944134457929658717426849980650541 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X4XP8Interval.1 ∧ manuscriptCase2X4XP8Interval.2 ≤ (-1300815944134457863728704376093709032219 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X4XP8Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X4XP8_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X4 : ℝ) (barrierP2Tail.getD 8 (0, 0)) ∈ Set.Icc ((-1300815944134457929658717426849980650541 / 10000000000000000000000000000000000000000) : ℝ) ((-1300815944134457863728704376093709032219 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-1300815944134457929658717426849980650541 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X4XP8Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X4XP8_rounded_endpoints.1
  have hhi : (manuscriptCase2X4XP8Interval.2 : ℝ) ≤ ((-1300815944134457863728704376093709032219 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X4XP8_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X4XP8_exact_interval.1, manuscriptCase2X4XP8_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
