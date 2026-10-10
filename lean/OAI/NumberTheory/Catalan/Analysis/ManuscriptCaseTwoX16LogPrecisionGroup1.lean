import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoLogsX16Group0

namespace OAI

noncomputable section
namespace InternalCatalan

def manuscriptCase2X16XP4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-1231651 / 100000000) (-1200529 / 20000000) (1) (-2) (1621331014965839938609 / 1250000000000000000000) (6937500000 / 39663611897)

private theorem manuscriptCase2X16XP4_arg_eq : barrierCase2X16XP4LogArg = barrierComplex (111 / 400) (-39663611897 / 25000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X16XP4LogArg, Case2PointData.X16, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X16XP4_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 = barrierComplex (-1231651 / 100000000) (-1200529 / 20000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X16XP4_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X16 : ℝ) (barrierP2Tail.getD 4 (0, 0)) ∈ Set.Icc (manuscriptCase2X16XP4Interval.1 : ℝ) (manuscriptCase2X16XP4Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X16XP4LogArg).re ∈ _
  rw [manuscriptCase2X16XP4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-1231651 / 100000000) (-1200529 / 20000000)
    barrierCase2X16XP4LogArg (1) (-2) (1621331014965839938609 / 1250000000000000000000) (39663611897 / 12500000000) (111 / 200)
  have hratio : ((111 / 200) / (39663611897 / 12500000000) : ℚ) = (6937500000 / 39663611897) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X16XP4Interval
  apply h
  all_goals
    try rw [manuscriptCase2X16XP4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X16XP4_rounded_endpoints :
    (-897657014110371842019147862594305613099 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X16XP4Interval.1 ∧ manuscriptCase2X16XP4Interval.2 ≤ (-44882850705518589924451858124518121447 / 500000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X16XP4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X16XP4_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X16 : ℝ) (barrierP2Tail.getD 4 (0, 0)) ∈ Set.Icc ((-897657014110371842019147862594305613099 / 10000000000000000000000000000000000000000) : ℝ) ((-44882850705518589924451858124518121447 / 500000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-897657014110371842019147862594305613099 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X16XP4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X16XP4_rounded_endpoints.1
  have hhi : (manuscriptCase2X16XP4Interval.2 : ℝ) ≤ ((-44882850705518589924451858124518121447 / 500000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X16XP4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X16XP4_exact_interval.1, manuscriptCase2X16XP4_exact_interval.2.trans hhi⟩

def manuscriptCase2X16XP6Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-1612959 / 50000000) (-4464117 / 50000000) (1) (-2) (233999307581657502594949 / 195312500000000000000000) (-3017533743 / 483725337430)

private theorem manuscriptCase2X16XP6_arg_eq : barrierCase2X16XP6LogArg = barrierComplex (-3017533743 / 312500000000) (-48372533743 / 31250000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X16XP6LogArg, Case2PointData.X16, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X16XP6_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 = barrierComplex (-1612959 / 50000000) (-4464117 / 50000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X16XP6_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X16 : ℝ) (barrierP2Tail.getD 6 (0, 0)) ∈ Set.Icc (manuscriptCase2X16XP6Interval.1 : ℝ) (manuscriptCase2X16XP6Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 * Complex.log barrierCase2X16XP6LogArg).re ∈ _
  rw [manuscriptCase2X16XP6_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-1612959 / 50000000) (-4464117 / 50000000)
    barrierCase2X16XP6LogArg (1) (-2) (233999307581657502594949 / 195312500000000000000000) (48372533743 / 15625000000) (-3017533743 / 156250000000)
  have hratio : ((-3017533743 / 156250000000) / (48372533743 / 15625000000) : ℚ) = (-3017533743 / 483725337430) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X16XP6Interval
  apply h
  all_goals
    try rw [manuscriptCase2X16XP6_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X16XP6_rounded_endpoints :
    (-1548963939510796645627052031498875788647 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X16XP6Interval.1 ∧ manuscriptCase2X16XP6Interval.2 ≤ (-96810246219424786304479935119053553337 / 625000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X16XP6Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X16XP6_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X16 : ℝ) (barrierP2Tail.getD 6 (0, 0)) ∈ Set.Icc ((-1548963939510796645627052031498875788647 / 10000000000000000000000000000000000000000) : ℝ) ((-96810246219424786304479935119053553337 / 625000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-1548963939510796645627052031498875788647 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X16XP6Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X16XP6_rounded_endpoints.1
  have hhi : (manuscriptCase2X16XP6Interval.2 : ℝ) ≤ ((-96810246219424786304479935119053553337 / 625000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X16XP6_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X16XP6_exact_interval.1, manuscriptCase2X16XP6_exact_interval.2.trans hhi⟩

def manuscriptCase2X16XP8Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-32899 / 1562500) (9091287 / 100000000) (1) (-2) (358420185067502442594949 / 195312500000000000000000) (104307533743 / 589525337430)

private theorem manuscriptCase2X16XP8_arg_eq : barrierCase2X16XP8LogArg = barrierComplex (104307533743 / 312500000000) (-58952533743 / 31250000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X16XP8LogArg, Case2PointData.X16, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X16XP8_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 = barrierComplex (-32899 / 1562500) (9091287 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X16XP8_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X16 : ℝ) (barrierP2Tail.getD 8 (0, 0)) ∈ Set.Icc (manuscriptCase2X16XP8Interval.1 : ℝ) (manuscriptCase2X16XP8Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 * Complex.log barrierCase2X16XP8LogArg).re ∈ _
  rw [manuscriptCase2X16XP8_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-32899 / 1562500) (9091287 / 100000000)
    barrierCase2X16XP8LogArg (1) (-2) (358420185067502442594949 / 195312500000000000000000) (58952533743 / 15625000000) (104307533743 / 156250000000)
  have hratio : ((104307533743 / 156250000000) / (58952533743 / 15625000000) : ℚ) = (104307533743 / 589525337430) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X16XP8Interval
  apply h
  all_goals
    try rw [manuscriptCase2X16XP8_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X16XP8_rounded_endpoints :
    (565980439364176365657032417222063071083 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2X16XP8Interval.1 ∧ manuscriptCase2X16XP8Interval.2 ≤ (565980439364176398622110227340786261053 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X16XP8Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X16XP8_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X16 : ℝ) (barrierP2Tail.getD 8 (0, 0)) ∈ Set.Icc ((565980439364176365657032417222063071083 / 5000000000000000000000000000000000000000) : ℝ) ((565980439364176398622110227340786261053 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((565980439364176365657032417222063071083 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X16XP8Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X16XP8_rounded_endpoints.1
  have hhi : (manuscriptCase2X16XP8Interval.2 : ℝ) ≤ ((565980439364176398622110227340786261053 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X16XP8_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X16XP8_exact_interval.1, manuscriptCase2X16XP8_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
