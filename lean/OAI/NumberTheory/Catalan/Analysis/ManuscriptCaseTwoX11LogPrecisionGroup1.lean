import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoLogsX11Group0

namespace OAI

noncomputable section
namespace InternalCatalan

def manuscriptCase2X11XP4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-1231651 / 100000000) (-1200529 / 20000000) (-2) (-1) (234036474322422598249 / 156250000000000000000) (-6697292557 / 20572292557)

private theorem manuscriptCase2X11XP4_arg_eq : barrierCase2X11XP4LogArg = barrierComplex (111 / 400) (-13634792557 / 25000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X11XP4LogArg, Case2PointData.X11, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X11XP4_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 = barrierComplex (-1231651 / 100000000) (-1200529 / 20000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X11XP4_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X11 : ℝ) (barrierP2Tail.getD 4 (0, 0)) ∈ Set.Icc (manuscriptCase2X11XP4Interval.1 : ℝ) (manuscriptCase2X11XP4Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X11XP4LogArg).re ∈ _
  rw [manuscriptCase2X11XP4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-1231651 / 100000000) (-1200529 / 20000000)
    barrierCase2X11XP4LogArg (-2) (-1) (234036474322422598249 / 156250000000000000000) (20572292557 / 25000000000) (-6697292557 / 25000000000)
  have hratio : ((-6697292557 / 25000000000) / (20572292557 / 25000000000) : ℚ) = (-6697292557 / 20572292557) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X11XP4Interval
  apply h
  all_goals
    try rw [manuscriptCase2X11XP4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X11XP4_rounded_endpoints :
    (-599876011437683344922821042005826368369 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X11XP4Interval.1 ∧ manuscriptCase2X11XP4Interval.2 ≤ (-37492250714855207696580662316052208479 / 625000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X11XP4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X11XP4_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X11 : ℝ) (barrierP2Tail.getD 4 (0, 0)) ∈ Set.Icc ((-599876011437683344922821042005826368369 / 10000000000000000000000000000000000000000) : ℝ) ((-37492250714855207696580662316052208479 / 625000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-599876011437683344922821042005826368369 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X11XP4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X11XP4_rounded_endpoints.1
  have hhi : (manuscriptCase2X11XP4Interval.2 : ℝ) ≤ ((-37492250714855207696580662316052208479 / 625000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X11XP4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X11XP4_exact_interval.1, manuscriptCase2X11XP4_exact_interval.2.trans hhi⟩

def manuscriptCase2X11XP6Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-1612959 / 50000000) (-4464117 / 50000000) (-3) (-2) (18347561655277840040989 / 12207031250000000000000) (32197927717 / 131570722830)

private theorem manuscriptCase2X11XP6_arg_eq : barrierCase2X11XP6LogArg = barrierComplex (32197927717 / 312500000000) (-13157072283 / 31250000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X11XP6LogArg, Case2PointData.X11, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X11XP6_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 = barrierComplex (-1612959 / 50000000) (-4464117 / 50000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X11XP6_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X11 : ℝ) (barrierP2Tail.getD 6 (0, 0)) ∈ Set.Icc (manuscriptCase2X11XP6Interval.1 : ℝ) (manuscriptCase2X11XP6Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 * Complex.log barrierCase2X11XP6LogArg).re ∈ _
  rw [manuscriptCase2X11XP6_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-1612959 / 50000000) (-4464117 / 50000000)
    barrierCase2X11XP6LogArg (-3) (-2) (18347561655277840040989 / 12207031250000000000000) (13157072283 / 15625000000) (32197927717 / 156250000000)
  have hratio : ((32197927717 / 156250000000) / (13157072283 / 15625000000) : ℚ) = (32197927717 / 131570722830) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X11XP6Interval
  apply h
  all_goals
    try rw [manuscriptCase2X11XP6_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X11XP6_rounded_endpoints :
    (-918483900256589409951727877106438713939 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X11XP6Interval.1 ∧ manuscriptCase2X11XP6Interval.2 ≤ (-57405243766036834072049300422039368673 / 625000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X11XP6Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X11XP6_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X11 : ℝ) (barrierP2Tail.getD 6 (0, 0)) ∈ Set.Icc ((-918483900256589409951727877106438713939 / 10000000000000000000000000000000000000000) : ℝ) ((-57405243766036834072049300422039368673 / 625000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-918483900256589409951727877106438713939 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X11XP6Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X11XP6_rounded_endpoints.1
  have hhi : (manuscriptCase2X11XP6Interval.2 : ℝ) ≤ ((-57405243766036834072049300422039368673 / 625000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X11XP6_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X11XP6_exact_interval.1, manuscriptCase2X11XP6_exact_interval.2.trans hhi⟩

def manuscriptCase2X11XP8Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-32899 / 1562500) (9091287 / 100000000) (-1) (-2) (61118574509195980040989 / 48828125000000000000000) (69092072283 / 237370722830)

private theorem manuscriptCase2X11XP8_arg_eq : barrierCase2X11XP8LogArg = barrierComplex (69092072283 / 312500000000) (-23737072283 / 31250000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X11XP8LogArg, Case2PointData.X11, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X11XP8_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 = barrierComplex (-32899 / 1562500) (9091287 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X11XP8_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X11 : ℝ) (barrierP2Tail.getD 8 (0, 0)) ∈ Set.Icc (manuscriptCase2X11XP8Interval.1 : ℝ) (manuscriptCase2X11XP8Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 * Complex.log barrierCase2X11XP8LogArg).re ∈ _
  rw [manuscriptCase2X11XP8_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-32899 / 1562500) (9091287 / 100000000)
    barrierCase2X11XP8LogArg (-1) (-2) (61118574509195980040989 / 48828125000000000000000) (23737072283 / 15625000000) (69092072283 / 156250000000)
  have hratio : ((69092072283 / 156250000000) / (23737072283 / 15625000000) : ℚ) = (69092072283 / 237370722830) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X11XP8Interval
  apply h
  all_goals
    try rw [manuscriptCase2X11XP8_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X11XP8_rounded_endpoints :
    (30497132756145759074145410874634205787 / 250000000000000000000000000000000000000) ≤ manuscriptCase2X11XP8Interval.1 ∧ manuscriptCase2X11XP8Interval.2 ≤ (609942655122915214447914742921338552841 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X11XP8Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X11XP8_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X11 : ℝ) (barrierP2Tail.getD 8 (0, 0)) ∈ Set.Icc ((30497132756145759074145410874634205787 / 250000000000000000000000000000000000000) : ℝ) ((609942655122915214447914742921338552841 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((30497132756145759074145410874634205787 / 250000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X11XP8Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X11XP8_rounded_endpoints.1
  have hhi : (manuscriptCase2X11XP8Interval.2 : ℝ) ≤ ((609942655122915214447914742921338552841 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X11XP8_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X11XP8_exact_interval.1, manuscriptCase2X11XP8_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
