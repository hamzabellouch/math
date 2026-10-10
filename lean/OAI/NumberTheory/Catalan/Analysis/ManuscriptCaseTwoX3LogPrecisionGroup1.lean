import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoLogsX3Group0

namespace OAI

noncomputable section
namespace InternalCatalan

def manuscriptCase2X3XP4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-1231651 / 100000000) (-1200529 / 20000000) (0) (2) (3248267517918750351001 / 2500000000000000000000) (-13875000000 / 55278855749)

private theorem manuscriptCase2X3XP4_arg_eq : barrierCase2X3XP4LogArg = barrierComplex (111 / 400) (55278855749 / 50000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X3XP4LogArg, Case2PointData.X3, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X3XP4_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 = barrierComplex (-1231651 / 100000000) (-1200529 / 20000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X3XP4_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X3 : ℝ) (barrierP2Tail.getD 4 (0, 0)) ∈ Set.Icc (manuscriptCase2X3XP4Interval.1 : ℝ) (manuscriptCase2X3XP4Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X3XP4LogArg).re ∈ _
  rw [manuscriptCase2X3XP4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-1231651 / 100000000) (-1200529 / 20000000)
    barrierCase2X3XP4LogArg (0) (2) (3248267517918750351001 / 2500000000000000000000) (55278855749 / 25000000000) (-111 / 200)
  have hratio : ((-111 / 200) / (55278855749 / 25000000000) : ℚ) = (-13875000000 / 55278855749) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X3XP4Interval
  apply h
  all_goals
    try rw [manuscriptCase2X3XP4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X3XP4_rounded_endpoints :
    (155830431561740037241876898045396779537 / 2000000000000000000000000000000000000000) ≤ manuscriptCase2X3XP4Interval.1 ∧ manuscriptCase2X3XP4Interval.2 ≤ (779152157808700229731178471149356612403 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X3XP4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X3XP4_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X3 : ℝ) (barrierP2Tail.getD 4 (0, 0)) ∈ Set.Icc ((155830431561740037241876898045396779537 / 2000000000000000000000000000000000000000) : ℝ) ((779152157808700229731178471149356612403 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((155830431561740037241876898045396779537 / 2000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X3XP4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X3XP4_rounded_endpoints.1
  have hhi : (manuscriptCase2X3XP4Interval.2 : ℝ) ≤ ((779152157808700229731178471149356612403 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X3XP4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X3XP4_exact_interval.1, manuscriptCase2X3XP4_exact_interval.2.trans hhi⟩

def manuscriptCase2X3XP6Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-1612959 / 50000000) (-4464117 / 50000000) (0) (2) (759791129662283158213261 / 390625000000000000000000) (-176079040131 / 853690401310)

private theorem manuscriptCase2X3XP6_arg_eq : barrierCase2X3XP6LogArg = barrierComplex (176079040131 / 625000000000) (85369040131 / 62500000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X3XP6LogArg, Case2PointData.X3, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X3XP6_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 = barrierComplex (-1612959 / 50000000) (-4464117 / 50000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X3XP6_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X3 : ℝ) (barrierP2Tail.getD 6 (0, 0)) ∈ Set.Icc (manuscriptCase2X3XP6Interval.1 : ℝ) (manuscriptCase2X3XP6Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 * Complex.log barrierCase2X3XP6LogArg).re ∈ _
  rw [manuscriptCase2X3XP6_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-1612959 / 50000000) (-4464117 / 50000000)
    barrierCase2X3XP6LogArg (0) (2) (759791129662283158213261 / 390625000000000000000000) (85369040131 / 31250000000) (-176079040131 / 312500000000)
  have hratio : ((-176079040131 / 312500000000) / (85369040131 / 31250000000) : ℚ) = (-176079040131 / 853690401310) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X3XP6Interval
  apply h
  all_goals
    try rw [manuscriptCase2X3XP6_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X3XP6_rounded_endpoints :
    (1113530466899799934603789451243979372163 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X3XP6Interval.1 ∧ manuscriptCase2X3XP6Interval.2 ≤ (278382616724949999835666668965835027631 / 2500000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X3XP6Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X3XP6_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X3 : ℝ) (barrierP2Tail.getD 6 (0, 0)) ∈ Set.Icc ((1113530466899799934603789451243979372163 / 10000000000000000000000000000000000000000) : ℝ) ((278382616724949999835666668965835027631 / 2500000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((1113530466899799934603789451243979372163 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X3XP6Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X3XP6_rounded_endpoints.1
  have hhi : (manuscriptCase2X3XP6Interval.2 : ℝ) ≤ ((278382616724949999835666668965835027631 / 2500000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X3XP6_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X3XP6_exact_interval.1, manuscriptCase2X3XP6_exact_interval.2.trans hhi⟩

def manuscriptCase2X3XP8Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-32899 / 1562500) (9091287 / 100000000) (0) (2) (412982384328415198213261 / 390625000000000000000000) (-26500959869 / 642090401310)

private theorem manuscriptCase2X3XP8_arg_eq : barrierCase2X3XP8LogArg = barrierComplex (26500959869 / 625000000000) (64209040131 / 62500000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X3XP8LogArg, Case2PointData.X3, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X3XP8_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 = barrierComplex (-32899 / 1562500) (9091287 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X3XP8_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X3 : ℝ) (barrierP2Tail.getD 8 (0, 0)) ∈ Set.Icc (manuscriptCase2X3XP8Interval.1 : ℝ) (manuscriptCase2X3XP8Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 * Complex.log barrierCase2X3XP8LogArg).re ∈ _
  rw [manuscriptCase2X3XP8_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-32899 / 1562500) (9091287 / 100000000)
    barrierCase2X3XP8LogArg (0) (2) (412982384328415198213261 / 390625000000000000000000) (64209040131 / 31250000000) (-26500959869 / 312500000000)
  have hratio : ((-26500959869 / 312500000000) / (64209040131 / 31250000000) : ℚ) = (-26500959869 / 642090401310) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X3XP8Interval
  apply h
  all_goals
    try rw [manuscriptCase2X3XP8_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X3XP8_rounded_endpoints :
    (-698207136467194192758432776797913799687 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2X3XP8Interval.1 ∧ manuscriptCase2X3XP8Interval.2 ≤ (-279282854586877663920214025501319465149 / 2000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X3XP8Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X3XP8_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X3 : ℝ) (barrierP2Tail.getD 8 (0, 0)) ∈ Set.Icc ((-698207136467194192758432776797913799687 / 5000000000000000000000000000000000000000) : ℝ) ((-279282854586877663920214025501319465149 / 2000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-698207136467194192758432776797913799687 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X3XP8Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X3XP8_rounded_endpoints.1
  have hhi : (manuscriptCase2X3XP8Interval.2 : ℝ) ≤ ((-279282854586877663920214025501319465149 / 2000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X3XP8_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X3XP8_exact_interval.1, manuscriptCase2X3XP8_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
