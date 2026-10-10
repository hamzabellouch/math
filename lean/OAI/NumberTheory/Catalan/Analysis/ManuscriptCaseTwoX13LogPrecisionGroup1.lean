import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoLogsX13Group0

namespace OAI

noncomputable section
namespace InternalCatalan

def manuscriptCase2X13XP4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-1231651 / 100000000) (-1200529 / 20000000) (0) (-2) (10664944483062775232689 / 10000000000000000000000) (27750000000 / 99473021383)

private theorem manuscriptCase2X13XP4_arg_eq : barrierCase2X13XP4LogArg = barrierComplex (111 / 400) (-99473021383 / 100000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X13XP4LogArg, Case2PointData.X13, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X13XP4_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 = barrierComplex (-1231651 / 100000000) (-1200529 / 20000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X13XP4_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X13 : ℝ) (barrierP2Tail.getD 4 (0, 0)) ∈ Set.Icc (manuscriptCase2X13XP4Interval.1 : ℝ) (manuscriptCase2X13XP4Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X13XP4LogArg).re ∈ _
  rw [manuscriptCase2X13XP4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-1231651 / 100000000) (-1200529 / 20000000)
    barrierCase2X13XP4LogArg (0) (-2) (10664944483062775232689 / 10000000000000000000000) (99473021383 / 50000000000) (111 / 200)
  have hratio : ((111 / 200) / (99473021383 / 50000000000) : ℚ) = (27750000000 / 99473021383) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X13XP4Interval
  apply h
  all_goals
    try rw [manuscriptCase2X13XP4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X13XP4_rounded_endpoints :
    (-391776878176987733226648570706410599749 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2X13XP4Interval.1 ∧ manuscriptCase2X13XP4Interval.2 ≤ (-783553756353975422931503160482168800567 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X13XP4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X13XP4_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X13 : ℝ) (barrierP2Tail.getD 4 (0, 0)) ∈ Set.Icc ((-391776878176987733226648570706410599749 / 5000000000000000000000000000000000000000) : ℝ) ((-783553756353975422931503160482168800567 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-391776878176987733226648570706410599749 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X13XP4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X13XP4_rounded_endpoints.1
  have hhi : (manuscriptCase2X13XP4Interval.2 : ℝ) ≤ ((-783553756353975422931503160482168800567 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X13XP4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X13XP4_exact_interval.1, manuscriptCase2X13XP4_exact_interval.2.trans hhi⟩

def manuscriptCase2X13XP6Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-1612959 / 50000000) (-4464117 / 50000000) (-1) (-2) (1291059493150974520509829 / 781250000000000000000000) (67998853423 / 1134211465770)

private theorem manuscriptCase2X13XP6_arg_eq : barrierCase2X13XP6LogArg = barrierComplex (67998853423 / 1250000000000) (-113421146577 / 125000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X13XP6LogArg, Case2PointData.X13, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X13XP6_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 = barrierComplex (-1612959 / 50000000) (-4464117 / 50000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X13XP6_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X13 : ℝ) (barrierP2Tail.getD 6 (0, 0)) ∈ Set.Icc (manuscriptCase2X13XP6Interval.1 : ℝ) (manuscriptCase2X13XP6Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 * Complex.log barrierCase2X13XP6LogArg).re ∈ _
  rw [manuscriptCase2X13XP6_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-1612959 / 50000000) (-4464117 / 50000000)
    barrierCase2X13XP6LogArg (-1) (-2) (1291059493150974520509829 / 781250000000000000000000) (113421146577 / 62500000000) (67998853423 / 625000000000)
  have hratio : ((67998853423 / 625000000000) / (113421146577 / 62500000000) : ℚ) = (67998853423 / 1134211465770) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X13XP6Interval
  apply h
  all_goals
    try rw [manuscriptCase2X13XP6_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X13XP6_rounded_endpoints :
    (-65910078459638060211360062954249426267 / 500000000000000000000000000000000000000) ≤ manuscriptCase2X13XP6Interval.1 ∧ manuscriptCase2X13XP6Interval.2 ≤ (-20596899518636892804247311227713779503 / 156250000000000000000000000000000000000) := by
  simp only [manuscriptCase2X13XP6Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X13XP6_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X13 : ℝ) (barrierP2Tail.getD 6 (0, 0)) ∈ Set.Icc ((-65910078459638060211360062954249426267 / 500000000000000000000000000000000000000) : ℝ) ((-20596899518636892804247311227713779503 / 156250000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-65910078459638060211360062954249426267 / 500000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X13XP6Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X13XP6_rounded_endpoints.1
  have hhi : (manuscriptCase2X13XP6Interval.2 : ℝ) ≤ ((-20596899518636892804247311227713779503 / 156250000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X13XP6_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X13XP6_exact_interval.1, manuscriptCase2X13XP6_exact_interval.2.trans hhi⟩

def manuscriptCase2X13XP8Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-32899 / 1562500) (9091287 / 100000000) (0) (-2) (2539208112472977160509829 / 1562500000000000000000000) (337161146577 / 1557411465770)

private theorem manuscriptCase2X13XP8_arg_eq : barrierCase2X13XP8LogArg = barrierComplex (337161146577 / 1250000000000) (-155741146577 / 125000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X13XP8LogArg, Case2PointData.X13, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X13XP8_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 = barrierComplex (-32899 / 1562500) (9091287 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X13XP8_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X13 : ℝ) (barrierP2Tail.getD 8 (0, 0)) ∈ Set.Icc (manuscriptCase2X13XP8Interval.1 : ℝ) (manuscriptCase2X13XP8Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 * Complex.log barrierCase2X13XP8LogArg).re ∈ _
  rw [manuscriptCase2X13XP8_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-32899 / 1562500) (9091287 / 100000000)
    barrierCase2X13XP8LogArg (0) (-2) (2539208112472977160509829 / 1562500000000000000000000) (155741146577 / 62500000000) (337161146577 / 625000000000)
  have hratio : ((337161146577 / 625000000000) / (155741146577 / 62500000000) : ℚ) = (337161146577 / 1557411465770) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X13XP8Interval
  apply h
  all_goals
    try rw [manuscriptCase2X13XP8_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X13XP8_rounded_endpoints :
    (1183112731961553713542862551965750385049 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X13XP8Interval.1 ∧ manuscriptCase2X13XP8Interval.2 ≤ (118311273196155377945865803079177629437 / 1000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X13XP8Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X13XP8_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X13 : ℝ) (barrierP2Tail.getD 8 (0, 0)) ∈ Set.Icc ((1183112731961553713542862551965750385049 / 10000000000000000000000000000000000000000) : ℝ) ((118311273196155377945865803079177629437 / 1000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((1183112731961553713542862551965750385049 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X13XP8Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X13XP8_rounded_endpoints.1
  have hhi : (manuscriptCase2X13XP8Interval.2 : ℝ) ≤ ((118311273196155377945865803079177629437 / 1000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X13XP8_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X13XP8_exact_interval.1, manuscriptCase2X13XP8_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
