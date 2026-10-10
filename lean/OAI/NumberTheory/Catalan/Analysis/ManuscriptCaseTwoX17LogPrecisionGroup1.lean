import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoLogsX17Group0

namespace OAI

noncomputable section
namespace InternalCatalan

def manuscriptCase2X17XP4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-1231651 / 100000000) (-1200529 / 20000000) (1) (-2) (28016967592999189312729 / 20000000000000000000000) (27750000000 / 165066365723)

private theorem manuscriptCase2X17XP4_arg_eq : barrierCase2X17XP4LogArg = barrierComplex (111 / 400) (-165066365723 / 100000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X17XP4LogArg, Case2PointData.X17, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X17XP4_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 = barrierComplex (-1231651 / 100000000) (-1200529 / 20000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X17XP4_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X17 : ℝ) (barrierP2Tail.getD 4 (0, 0)) ∈ Set.Icc (manuscriptCase2X17XP4Interval.1 : ℝ) (manuscriptCase2X17XP4Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X17XP4LogArg).re ∈ _
  rw [manuscriptCase2X17XP4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-1231651 / 100000000) (-1200529 / 20000000)
    barrierCase2X17XP4LogArg (1) (-2) (28016967592999189312729 / 20000000000000000000000) (165066365723 / 50000000000) (111 / 200)
  have hratio : ((111 / 200) / (165066365723 / 50000000000) : ℚ) = (27750000000 / 165066365723) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X17XP4Interval
  apply h
  all_goals
    try rw [manuscriptCase2X17XP4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X17XP4_rounded_endpoints :
    (-906359059521228852197763785245368774983 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X17XP4Interval.1 ∧ manuscriptCase2X17XP4Interval.2 ≤ (-453179529760614404333826542570683264947 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X17XP4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X17XP4_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X17 : ℝ) (barrierP2Tail.getD 4 (0, 0)) ∈ Set.Icc ((-906359059521228852197763785245368774983 / 10000000000000000000000000000000000000000) : ℝ) ((-453179529760614404333826542570683264947 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-906359059521228852197763785245368774983 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X17XP4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X17XP4_rounded_endpoints.1
  have hhi : (manuscriptCase2X17XP4Interval.2 : ℝ) ≤ ((-453179529760614404333826542570683264947 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X17XP4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X17XP4_exact_interval.1, manuscriptCase2X17XP4_exact_interval.2.trans hhi⟩

def manuscriptCase2X17XP6Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-1612959 / 50000000) (-4464117 / 50000000) (1) (-2) (4087502438405922539480269 / 3125000000000000000000000) (-20745083037 / 2021650830370)

private theorem manuscriptCase2X17XP6_arg_eq : barrierCase2X17XP6LogArg = barrierComplex (-20745083037 / 1250000000000) (-202165083037 / 125000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X17XP6LogArg, Case2PointData.X17, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X17XP6_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 = barrierComplex (-1612959 / 50000000) (-4464117 / 50000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X17XP6_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X17 : ℝ) (barrierP2Tail.getD 6 (0, 0)) ∈ Set.Icc (manuscriptCase2X17XP6Interval.1 : ℝ) (manuscriptCase2X17XP6Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 * Complex.log barrierCase2X17XP6LogArg).re ∈ _
  rw [manuscriptCase2X17XP6_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-1612959 / 50000000) (-4464117 / 50000000)
    barrierCase2X17XP6LogArg (1) (-2) (4087502438405922539480269 / 3125000000000000000000000) (202165083037 / 62500000000) (-20745083037 / 625000000000)
  have hratio : ((-20745083037 / 625000000000) / (202165083037 / 62500000000) : ℚ) = (-20745083037 / 2021650830370) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X17XP6Interval
  apply h
  all_goals
    try rw [manuscriptCase2X17XP6_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X17XP6_rounded_endpoints :
    (-1566714787775130597452349750375778165153 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X17XP6Interval.1 ∧ manuscriptCase2X17XP6Interval.2 ≤ (-391678696943782633174244170195439797861 / 2500000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X17XP6Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X17XP6_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X17 : ℝ) (barrierP2Tail.getD 6 (0, 0)) ∈ Set.Icc ((-1566714787775130597452349750375778165153 / 10000000000000000000000000000000000000000) : ℝ) ((-391678696943782633174244170195439797861 / 2500000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-1566714787775130597452349750375778165153 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X17XP6Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X17XP6_rounded_endpoints.1
  have hhi : (manuscriptCase2X17XP6Interval.2 : ℝ) ≤ ((-391678696943782633174244170195439797861 / 2500000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X17XP6_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X17XP6_exact_interval.1, manuscriptCase2X17XP6_exact_interval.2.trans hhi⟩

def manuscriptCase2X17XP8Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-32899 / 1562500) (9091287 / 100000000) (1) (-2) (6158690722517632379480269 / 3125000000000000000000000) (425905083037 / 2444850830370)

private theorem manuscriptCase2X17XP8_arg_eq : barrierCase2X17XP8LogArg = barrierComplex (425905083037 / 1250000000000) (-244485083037 / 125000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X17XP8LogArg, Case2PointData.X17, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X17XP8_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 = barrierComplex (-32899 / 1562500) (9091287 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X17XP8_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X17 : ℝ) (barrierP2Tail.getD 8 (0, 0)) ∈ Set.Icc (manuscriptCase2X17XP8Interval.1 : ℝ) (manuscriptCase2X17XP8Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 * Complex.log barrierCase2X17XP8LogArg).re ∈ _
  rw [manuscriptCase2X17XP8_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-32899 / 1562500) (9091287 / 100000000)
    barrierCase2X17XP8LogArg (1) (-2) (6158690722517632379480269 / 3125000000000000000000000) (244485083037 / 62500000000) (425905083037 / 625000000000)
  have hratio : ((425905083037 / 625000000000) / (244485083037 / 62500000000) : ℚ) = (425905083037 / 2444850830370) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X17XP8Interval
  apply h
  all_goals
    try rw [manuscriptCase2X17XP8_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X17XP8_rounded_endpoints :
    (281714899401218695623444480045937393909 / 2500000000000000000000000000000000000000) ≤ manuscriptCase2X17XP8Interval.1 ∧ manuscriptCase2X17XP8Interval.2 ≤ (1126859597604874848430574841129020496489 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X17XP8Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X17XP8_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X17 : ℝ) (barrierP2Tail.getD 8 (0, 0)) ∈ Set.Icc ((281714899401218695623444480045937393909 / 2500000000000000000000000000000000000000) : ℝ) ((1126859597604874848430574841129020496489 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((281714899401218695623444480045937393909 / 2500000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X17XP8Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X17XP8_rounded_endpoints.1
  have hhi : (manuscriptCase2X17XP8Interval.2 : ℝ) ≤ ((1126859597604874848430574841129020496489 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X17XP8_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X17XP8_exact_interval.1, manuscriptCase2X17XP8_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
