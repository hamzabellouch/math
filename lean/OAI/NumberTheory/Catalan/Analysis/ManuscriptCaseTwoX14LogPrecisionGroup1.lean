import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoLogsSixControl

namespace OAI

noncomputable section
namespace InternalCatalan

def manuscriptCase2X14XP4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-1231651 / 100000000) (-1200529 / 20000000) (0) (-2) (16040477785359281411961 / 10000000000000000000000) (250000000 / 1113274971)

private theorem manuscriptCase2X14XP4_arg_eq : barrierCase2X14XP4LogArg = barrierComplex (111 / 400) (-123573521781 / 100000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X14XP4LogArg, Case2PointData.X14, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X14XP4_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 = barrierComplex (-1231651 / 100000000) (-1200529 / 20000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X14XP4_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X14 : ℝ) (barrierP2Tail.getD 4 (0, 0)) ∈ Set.Icc (manuscriptCase2X14XP4Interval.1 : ℝ) (manuscriptCase2X14XP4Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X14XP4LogArg).re ∈ _
  rw [manuscriptCase2X14XP4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-1231651 / 100000000) (-1200529 / 20000000)
    barrierCase2X14XP4LogArg (0) (-2) (16040477785359281411961 / 10000000000000000000000) (123573521781 / 50000000000) (111 / 200)
  have hratio : ((111 / 200) / (123573521781 / 50000000000) : ℚ) = (250000000 / 1113274971) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X14XP4Interval
  apply h
  all_goals
    try rw [manuscriptCase2X14XP4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X14XP4_rounded_endpoints :
    (-419697788431180680733826392520908915487 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2X14XP4Interval.1 ∧ manuscriptCase2X14XP4Interval.2 ≤ (-839395576862361317945858792453189181839 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X14XP4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X14XP4_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X14 : ℝ) (barrierP2Tail.getD 4 (0, 0)) ∈ Set.Icc ((-419697788431180680733826392520908915487 / 5000000000000000000000000000000000000000) : ℝ) ((-839395576862361317945858792453189181839 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-419697788431180680733826392520908915487 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X14XP4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X14XP4_rounded_endpoints.1
  have hhi : (manuscriptCase2X14XP4Interval.2 : ℝ) ≤ ((-839395576862361317945858792453189181839 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X14XP4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X14XP4_exact_interval.1, manuscriptCase2X14XP4_exact_interval.2.trans hhi⟩

def manuscriptCase2X14XP6Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-1612959 / 50000000) (-4464117 / 50000000) (0) (-2) (2133661704659605883043821 / 1562500000000000000000000) (35392294061 / 1460277059390)

private theorem manuscriptCase2X14XP6_arg_eq : barrierCase2X14XP6LogArg = barrierComplex (35392294061 / 1250000000000) (-146027705939 / 125000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X14XP6LogArg, Case2PointData.X14, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X14XP6_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 = barrierComplex (-1612959 / 50000000) (-4464117 / 50000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X14XP6_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X14 : ℝ) (barrierP2Tail.getD 6 (0, 0)) ∈ Set.Icc (manuscriptCase2X14XP6Interval.1 : ℝ) (manuscriptCase2X14XP6Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 * Complex.log barrierCase2X14XP6LogArg).re ∈ _
  rw [manuscriptCase2X14XP6_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-1612959 / 50000000) (-4464117 / 50000000)
    barrierCase2X14XP6LogArg (0) (-2) (2133661704659605883043821 / 1562500000000000000000000) (146027705939 / 62500000000) (35392294061 / 625000000000)
  have hratio : ((35392294061 / 625000000000) / (146027705939 / 62500000000) : ℚ) = (35392294061 / 1460277059390) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X14XP6Interval
  apply h
  all_goals
    try rw [manuscriptCase2X14XP6_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X14XP6_rounded_endpoints :
    (-1431061004370357297088089429250973861589 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X14XP6Interval.1 ∧ manuscriptCase2X14XP6Interval.2 ≤ (-1431061004370357232354499359962166597777 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X14XP6Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X14XP6_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X14 : ℝ) (barrierP2Tail.getD 6 (0, 0)) ∈ Set.Icc ((-1431061004370357297088089429250973861589 / 10000000000000000000000000000000000000000) : ℝ) ((-1431061004370357232354499359962166597777 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-1431061004370357297088089429250973861589 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X14XP6Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X14XP6_rounded_endpoints.1
  have hhi : (manuscriptCase2X14XP6Interval.2 : ℝ) ≤ ((-1431061004370357232354499359962166597777 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X14XP6_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X14XP6_exact_interval.1, manuscriptCase2X14XP6_exact_interval.2.trans hhi⟩

def manuscriptCase2X14XP8Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-32899 / 1562500) (9091287 / 100000000) (1) (-2) (3684213989603792363043821 / 3125000000000000000000000) (369767705939 / 1883477059390)

private theorem manuscriptCase2X14XP8_arg_eq : barrierCase2X14XP8LogArg = barrierComplex (369767705939 / 1250000000000) (-188347705939 / 125000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X14XP8LogArg, Case2PointData.X14, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X14XP8_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 = barrierComplex (-32899 / 1562500) (9091287 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X14XP8_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X14 : ℝ) (barrierP2Tail.getD 8 (0, 0)) ∈ Set.Icc (manuscriptCase2X14XP8Interval.1 : ℝ) (manuscriptCase2X14XP8Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 * Complex.log barrierCase2X14XP8LogArg).re ∈ _
  rw [manuscriptCase2X14XP8_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-32899 / 1562500) (9091287 / 100000000)
    barrierCase2X14XP8LogArg (1) (-2) (3684213989603792363043821 / 3125000000000000000000000) (188347705939 / 62500000000) (369767705939 / 625000000000)
  have hratio : ((369767705939 / 625000000000) / (188347705939 / 62500000000) : ℚ) = (369767705939 / 1883477059390) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X14XP8Interval
  apply h
  all_goals
    try rw [manuscriptCase2X14XP8_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X14XP8_rounded_endpoints :
    (1161512322330524755603382200582455283637 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X14XP8Interval.1 ∧ manuscriptCase2X14XP8Interval.2 ≤ (1161512322330524821533395251338726902371 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X14XP8Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X14XP8_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X14 : ℝ) (barrierP2Tail.getD 8 (0, 0)) ∈ Set.Icc ((1161512322330524755603382200582455283637 / 10000000000000000000000000000000000000000) : ℝ) ((1161512322330524821533395251338726902371 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((1161512322330524755603382200582455283637 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X14XP8Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X14XP8_rounded_endpoints.1
  have hhi : (manuscriptCase2X14XP8Interval.2 : ℝ) ≤ ((1161512322330524821533395251338726902371 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X14XP8_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X14XP8_exact_interval.1, manuscriptCase2X14XP8_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
