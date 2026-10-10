import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoLogsX6Group0

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2X6XP4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-1231651 / 100000000) (-1200529 / 20000000) (-2) (1) (890788665569944833081 / 625000000000000000000) (4183285497 / 13433285497)

private theorem manuscriptCase2X6XP4_arg_eq : barrierCase2X6XP4LogArg = barrierComplex (111 / 400) (26424856491 / 50000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X6XP4LogArg, Case2PointData.X6, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X6XP4_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 = barrierComplex (-1231651 / 100000000) (-1200529 / 20000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X6XP4_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X6 : ℝ) (barrierP2Tail.getD 4 (0, 0)) ∈ Set.Icc (manuscriptCase2X6XP4Interval.1 : ℝ) (manuscriptCase2X6XP4Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X6XP4LogArg).re ∈ _
  rw [manuscriptCase2X6XP4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-1231651 / 100000000) (-1200529 / 20000000)
    barrierCase2X6XP4LogArg (-2) (1) (890788665569944833081 / 625000000000000000000) (40299856491 / 50000000000) (12549856491 / 50000000000)
  have hratio : ((12549856491 / 50000000000) / (40299856491 / 50000000000) : ℚ) = (4183285497 / 13433285497) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X6XP4Interval
  apply h
  all_goals
    try rw [manuscriptCase2X6XP4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X6XP4_rounded_endpoints :
    (179052972939562166054092302297898732517 / 2500000000000000000000000000000000000000) ≤ manuscriptCase2X6XP4Interval.1 ∧ manuscriptCase2X6XP4Interval.2 ≤ (358105945879124342996949819921332566077 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X6XP4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X6XP4_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X6 : ℝ) (barrierP2Tail.getD 4 (0, 0)) ∈ Set.Icc ((179052972939562166054092302297898732517 / 2500000000000000000000000000000000000000) : ℝ) ((358105945879124342996949819921332566077 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((179052972939562166054092302297898732517 / 2500000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X6XP4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X6XP4_rounded_endpoints.1
  have hhi : (manuscriptCase2X6XP4Interval.2 : ℝ) ≤ ((358105945879124342996949819921332566077 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X6XP4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X6XP4_exact_interval.1, manuscriptCase2X6XP4_exact_interval.2.trans hhi⟩

def manuscriptCase2X6XP6Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-1612959 / 50000000) (-4464117 / 50000000) (-1) (2) (233439028999330690196141 / 195312500000000000000000) (-137041276429 / 463312764290)

private theorem manuscriptCase2X6XP6_arg_eq : barrierCase2X6XP6LogArg = barrierComplex (137041276429 / 625000000000) (46331276429 / 62500000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X6XP6LogArg, Case2PointData.X6, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X6XP6_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 = barrierComplex (-1612959 / 50000000) (-4464117 / 50000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X6XP6_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X6 : ℝ) (barrierP2Tail.getD 6 (0, 0)) ∈ Set.Icc (manuscriptCase2X6XP6Interval.1 : ℝ) (manuscriptCase2X6XP6Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 * Complex.log barrierCase2X6XP6LogArg).re ∈ _
  rw [manuscriptCase2X6XP6_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-1612959 / 50000000) (-4464117 / 50000000)
    barrierCase2X6XP6LogArg (-1) (2) (233439028999330690196141 / 195312500000000000000000) (46331276429 / 31250000000) (-137041276429 / 312500000000)
  have hratio : ((-137041276429 / 312500000000) / (46331276429 / 31250000000) : ℚ) = (-137041276429 / 463312764290) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X6XP6Interval
  apply h
  all_goals
    try rw [manuscriptCase2X6XP6_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X6XP6_rounded_endpoints :
    (614359868351751108500773949498685418947 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2X6XP6Interval.1 ∧ manuscriptCase2X6XP6Interval.2 ≤ (1228719736703502281756920968809385935407 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X6XP6Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X6XP6_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X6 : ℝ) (barrierP2Tail.getD 6 (0, 0)) ∈ Set.Icc ((614359868351751108500773949498685418947 / 5000000000000000000000000000000000000000) : ℝ) ((1228719736703502281756920968809385935407 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((614359868351751108500773949498685418947 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X6XP6Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X6XP6_rounded_endpoints.1
  have hhi : (manuscriptCase2X6XP6Interval.2 : ℝ) ≤ ((1228719736703502281756920968809385935407 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X6XP6_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X6XP6_exact_interval.1, manuscriptCase2X6XP6_exact_interval.2.trans hhi⟩

def manuscriptCase2X6XP8Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-32899 / 1562500) (9091287 / 100000000) (-3) (2) (67654639993829050196141 / 48828125000000000000000) (-65538723571 / 251712764290)

private theorem manuscriptCase2X6XP8_arg_eq : barrierCase2X6XP8LogArg = barrierComplex (65538723571 / 625000000000) (25171276429 / 62500000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X6XP8LogArg, Case2PointData.X6, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X6XP8_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 = barrierComplex (-32899 / 1562500) (9091287 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X6XP8_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X6 : ℝ) (barrierP2Tail.getD 8 (0, 0)) ∈ Set.Icc (manuscriptCase2X6XP8Interval.1 : ℝ) (manuscriptCase2X6XP8Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 * Complex.log barrierCase2X6XP8LogArg).re ∈ _
  rw [manuscriptCase2X6XP8_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-32899 / 1562500) (9091287 / 100000000)
    barrierCase2X6XP8LogArg (-3) (2) (67654639993829050196141 / 48828125000000000000000) (25171276429 / 31250000000) (-65538723571 / 312500000000)
  have hratio : ((-65538723571 / 312500000000) / (25171276429 / 31250000000) : ℚ) = (-65538723571 / 251712764290) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X6XP8Interval
  apply h
  all_goals
    try rw [manuscriptCase2X6XP8_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X6XP8_rounded_endpoints :
    (-63243847650671356310893479192004383733 / 625000000000000000000000000000000000000) ≤ manuscriptCase2X6XP8Interval.1 ∧ manuscriptCase2X6XP8Interval.2 ≤ (-1011901562410741635015847366981256514619 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X6XP8Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X6XP8_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X6 : ℝ) (barrierP2Tail.getD 8 (0, 0)) ∈ Set.Icc ((-63243847650671356310893479192004383733 / 625000000000000000000000000000000000000) : ℝ) ((-1011901562410741635015847366981256514619 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-63243847650671356310893479192004383733 / 625000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X6XP8Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X6XP8_rounded_endpoints.1
  have hhi : (manuscriptCase2X6XP8Interval.2 : ℝ) ≤ ((-1011901562410741635015847366981256514619 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X6XP8_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X6XP8_exact_interval.1, manuscriptCase2X6XP8_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
