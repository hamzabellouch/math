import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointY7

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2Y7YV3Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (2466317 / 50000000) (0 / 1) (-1) (0) (1785890616338018089249 / 1250000000000000000000) (0 / 1)

private theorem manuscriptCase2Y7YV3_arg_eq : barrierCase2Y7YV3LogArg = barrierComplex (42259799057 / 50000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y7YV3LogArg, Case2PointData.Y7, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y7YV3_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2) = barrierComplex (2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y7YV3_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y7 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc (manuscriptCase2Y7YV3Interval.1 : ℝ) (manuscriptCase2Y7YV3Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2) * Complex.log barrierCase2Y7YV3LogArg).re ∈ _
  rw [manuscriptCase2Y7YV3_weight_eq]
  have h := manuscript_weighted_complex_log_interval (2466317 / 50000000) (0 / 1)
    barrierCase2Y7YV3LogArg (-1) (0) (1785890616338018089249 / 1250000000000000000000) (42259799057 / 50000000000) (0 / 1)
  have hratio : ((0 / 1) / (42259799057 / 50000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y7YV3Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y7YV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y7YV3_rounded_endpoints :
    (-41480183619490378501105633715513149371 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2Y7YV3Interval.1 ∧ manuscriptCase2Y7YV3Interval.2 ≤ (-82960367238980756968903673148237400467 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y7YV3Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y7YV3_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y7 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc ((-41480183619490378501105633715513149371 / 5000000000000000000000000000000000000000) : ℝ) ((-82960367238980756968903673148237400467 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-41480183619490378501105633715513149371 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y7YV3Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y7YV3_rounded_endpoints.1
  have hhi : (manuscriptCase2Y7YV3Interval.2 : ℝ) ≤ ((-82960367238980756968903673148237400467 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y7YV3_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y7YV3_exact_interval.1, manuscriptCase2Y7YV3_exact_interval.2.trans hhi⟩

def manuscriptCase2Y7YV4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-11618157 / 100000000) (0 / 1) (-1) (0) (74445694611310057790161 / 48828125000000000000000) (0 / 1)

private theorem manuscriptCase2Y7YV4_arg_eq : barrierCase2Y7YV4LogArg = barrierComplex (272847383369 / 312500000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y7YV4LogArg, Case2PointData.Y7, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y7YV4_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2) = barrierComplex (-11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y7YV4_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y7 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc (manuscriptCase2Y7YV4Interval.1 : ℝ) (manuscriptCase2Y7YV4Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2) * Complex.log barrierCase2Y7YV4LogArg).re ∈ _
  rw [manuscriptCase2Y7YV4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-11618157 / 100000000) (0 / 1)
    barrierCase2Y7YV4LogArg (-1) (0) (74445694611310057790161 / 48828125000000000000000) (272847383369 / 312500000000) (0 / 1)
  have hratio : ((0 / 1) / (272847383369 / 312500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y7YV4Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y7YV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y7YV4_rounded_endpoints :
    (157648939802854582001048185430338305061 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y7YV4Interval.1 ∧ manuscriptCase2Y7YV4Interval.2 ≤ (157648939802854582079499752854285762517 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y7YV4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y7YV4_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y7 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc ((157648939802854582001048185430338305061 / 10000000000000000000000000000000000000000) : ℝ) ((157648939802854582079499752854285762517 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((157648939802854582001048185430338305061 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y7YV4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y7YV4_rounded_endpoints.1
  have hhi : (manuscriptCase2Y7YV4Interval.2 : ℝ) ≤ ((157648939802854582079499752854285762517 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y7YV4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y7YV4_exact_interval.1, manuscriptCase2Y7YV4_exact_interval.2.trans hhi⟩

def manuscriptCase2Y7YV5Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-13619357 / 100000000) (-600749 / 3125000) (-1) (-2) (14171126114961970259689 / 7812500000000000000000) (48950000000 / 108512780883)

private theorem manuscriptCase2Y7YV5_arg_eq : barrierCase2Y7YV5LogArg = barrierComplex (979 / 2500) (-108512780883 / 125000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2Y7YV5LogArg, Case2PointData.Y7, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y7YV5_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2) = barrierComplex (-13619357 / 100000000) (-600749 / 3125000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y7YV5_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y7 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc (manuscriptCase2Y7YV5Interval.1 : ℝ) (manuscriptCase2Y7YV5Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2) * Complex.log barrierCase2Y7YV5LogArg).re ∈ _
  rw [manuscriptCase2Y7YV5_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-13619357 / 100000000) (-600749 / 3125000)
    barrierCase2Y7YV5LogArg (-1) (-2) (14171126114961970259689 / 7812500000000000000000) (108512780883 / 62500000000) (979 / 1250)
  have hratio : ((979 / 1250) / (108512780883 / 62500000000) : ℚ) = (48950000000 / 108512780883) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y7YV5Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y7YV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y7YV5_rounded_endpoints :
    (-534634376057736552018497776533383472621 / 2500000000000000000000000000000000000000) ≤ manuscriptCase2Y7YV5Interval.1 ∧ manuscriptCase2Y7YV5Interval.2 ≤ (-427707500846189213629932516692817423959 / 2000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y7YV5Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y7YV5_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y7 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc ((-534634376057736552018497776533383472621 / 2500000000000000000000000000000000000000) : ℝ) ((-427707500846189213629932516692817423959 / 2000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-534634376057736552018497776533383472621 / 2500000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y7YV5Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y7YV5_rounded_endpoints.1
  have hhi : (manuscriptCase2Y7YV5Interval.2 : ℝ) ≤ ((-427707500846189213629932516692817423959 / 2000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y7YV5_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y7YV5_exact_interval.1, manuscriptCase2Y7YV5_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
