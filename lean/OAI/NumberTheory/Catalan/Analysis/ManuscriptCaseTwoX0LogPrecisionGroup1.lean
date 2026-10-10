import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoLogsX0Group0

namespace OAI

noncomputable section
namespace InternalCatalan

def manuscriptCase2X0XP4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-1231651 / 100000000) (-1200529 / 20000000) (1) (2) (1713153580997055226641 / 1250000000000000000000) (-2312500000 / 13601571293)

private theorem manuscriptCase2X0XP4_arg_eq : barrierCase2X0XP4LogArg = barrierComplex (111 / 400) (40804713879 / 25000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X0XP4LogArg, Case2PointData.X0, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X0XP4_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 = barrierComplex (-1231651 / 100000000) (-1200529 / 20000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X0XP4_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X0 : ℝ) (barrierP2Tail.getD 4 (0, 0)) ∈ Set.Icc (manuscriptCase2X0XP4Interval.1 : ℝ) (manuscriptCase2X0XP4Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X0XP4LogArg).re ∈ _
  rw [manuscriptCase2X0XP4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-1231651 / 100000000) (-1200529 / 20000000)
    barrierCase2X0XP4LogArg (1) (2) (1713153580997055226641 / 1250000000000000000000) (40804713879 / 12500000000) (-111 / 200)
  have hratio : ((-111 / 200) / (40804713879 / 12500000000) : ℚ) = (-2312500000 / 13601571293) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X0XP4Interval
  apply h
  all_goals
    try rw [manuscriptCase2X0XP4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X0XP4_rounded_endpoints :
    (1559417063472830426699404167 / 20000000000000000000000000000) ≤ manuscriptCase2X0XP4Interval.1 ∧ manuscriptCase2X0XP4Interval.2 ≤ (77970853173641525687981278361 / 1000000000000000000000000000000) := by
  simp only [manuscriptCase2X0XP4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X0XP4_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X0 : ℝ) (barrierP2Tail.getD 4 (0, 0)) ∈ Set.Icc ((1559417063472830426699404167 / 20000000000000000000000000000) : ℝ) ((77970853173641525687981278361 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((1559417063472830426699404167 / 20000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X0XP4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X0XP4_rounded_endpoints.1
  have hhi : (manuscriptCase2X0XP4Interval.2 : ℝ) ≤ ((77970853173641525687981278361 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X0XP4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X0XP4_exact_interval.1, manuscriptCase2X0XP4_exact_interval.2.trans hhi⟩

def manuscriptCase2X0XP6Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-1612959 / 50000000) (-4464117 / 50000000) (1) (2) (377185684424306936035301 / 195312500000000000000000) (-105851377601 / 604963776010)

private theorem manuscriptCase2X0XP6_arg_eq : barrierCase2X0XP6LogArg = barrierComplex (105851377601 / 312500000000) (60496377601 / 31250000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X0XP6LogArg, Case2PointData.X0, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X0XP6_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 = barrierComplex (-1612959 / 50000000) (-4464117 / 50000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X0XP6_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X0 : ℝ) (barrierP2Tail.getD 6 (0, 0)) ∈ Set.Icc (manuscriptCase2X0XP6Interval.1 : ℝ) (manuscriptCase2X0XP6Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 * Complex.log barrierCase2X0XP6LogArg).re ∈ _
  rw [manuscriptCase2X0XP6_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-1612959 / 50000000) (-4464117 / 50000000)
    barrierCase2X0XP6LogArg (1) (2) (377185684424306936035301 / 195312500000000000000000) (60496377601 / 15625000000) (-105851377601 / 156250000000)
  have hratio : ((-105851377601 / 156250000000) / (60496377601 / 15625000000) : ℚ) = (-105851377601 / 604963776010) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X0XP6Interval
  apply h
  all_goals
    try rw [manuscriptCase2X0XP6_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X0XP6_rounded_endpoints :
    (2574585306168083993541453347 / 25000000000000000000000000000) ≤ manuscriptCase2X0XP6Interval.1 ∧ manuscriptCase2X0XP6Interval.2 ≤ (102983412246723366217558897987 / 1000000000000000000000000000000) := by
  simp only [manuscriptCase2X0XP6Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X0XP6_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X0 : ℝ) (barrierP2Tail.getD 6 (0, 0)) ∈ Set.Icc ((2574585306168083993541453347 / 25000000000000000000000000000) : ℝ) ((102983412246723366217558897987 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((2574585306168083993541453347 / 25000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X0XP6Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X0XP6_rounded_endpoints.1
  have hhi : (manuscriptCase2X0XP6Interval.2 : ℝ) ≤ ((102983412246723366217558897987 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X0XP6_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X0XP6_exact_interval.1, manuscriptCase2X0XP6_exact_interval.2.trans hhi⟩

def manuscriptCase2X0XP8Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-32899 / 1562500) (9091287 / 100000000) (1) (2) (249185281446180356035301 / 195312500000000000000000) (4561377601 / 499163776010)

private theorem manuscriptCase2X0XP8_arg_eq : barrierCase2X0XP8LogArg = barrierComplex (-4561377601 / 312500000000) (49916377601 / 31250000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X0XP8LogArg, Case2PointData.X0, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X0XP8_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 = barrierComplex (-32899 / 1562500) (9091287 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X0XP8_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X0 : ℝ) (barrierP2Tail.getD 8 (0, 0)) ∈ Set.Icc (manuscriptCase2X0XP8Interval.1 : ℝ) (manuscriptCase2X0XP8Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 * Complex.log barrierCase2X0XP8LogArg).re ∈ _
  rw [manuscriptCase2X0XP8_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-32899 / 1562500) (9091287 / 100000000)
    barrierCase2X0XP8LogArg (1) (2) (249185281446180356035301 / 195312500000000000000000) (49916377601 / 15625000000) (4561377601 / 156250000000)
  have hratio : ((4561377601 / 156250000000) / (49916377601 / 15625000000) : ℚ) = (4561377601 / 499163776010) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X0XP8Interval
  apply h
  all_goals
    try rw [manuscriptCase2X0XP8_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X0XP8_rounded_endpoints :
    (-9593629725376562789551333201 / 62500000000000000000000000000) ≤ manuscriptCase2X0XP8Interval.1 ∧ manuscriptCase2X0XP8Interval.2 ≤ (-7674903780301249901991001307 / 50000000000000000000000000000) := by
  simp only [manuscriptCase2X0XP8Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X0XP8_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X0 : ℝ) (barrierP2Tail.getD 8 (0, 0)) ∈ Set.Icc ((-9593629725376562789551333201 / 62500000000000000000000000000) : ℝ) ((-7674903780301249901991001307 / 50000000000000000000000000000) : ℝ) := by
  have hlo : ((-9593629725376562789551333201 / 62500000000000000000000000000) : ℝ) ≤ (manuscriptCase2X0XP8Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X0XP8_rounded_endpoints.1
  have hhi : (manuscriptCase2X0XP8Interval.2 : ℝ) ≤ ((-7674903780301249901991001307 / 50000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X0XP8_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X0XP8_exact_interval.1, manuscriptCase2X0XP8_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
