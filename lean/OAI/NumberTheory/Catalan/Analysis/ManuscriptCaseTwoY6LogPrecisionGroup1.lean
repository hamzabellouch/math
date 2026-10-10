import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointY6

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2Y6YV3Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (2466317 / 50000000) (0 / 1) (0) (0) (182650890684123084609 / 156250000000000000000) (0 / 1)

private theorem manuscriptCase2Y6YV3_arg_eq : barrierCase2Y6YV3LogArg = barrierComplex (13514839647 / 12500000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y6YV3LogArg, Case2PointData.Y6, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y6YV3_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2) = barrierComplex (2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y6YV3_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y6 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc (manuscriptCase2Y6YV3Interval.1 : ℝ) (manuscriptCase2Y6YV3Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2) * Complex.log barrierCase2Y6YV3LogArg).re ∈ _
  rw [manuscriptCase2Y6YV3_weight_eq]
  have h := manuscript_weighted_complex_log_interval (2466317 / 50000000) (0 / 1)
    barrierCase2Y6YV3LogArg (0) (0) (182650890684123084609 / 156250000000000000000) (13514839647 / 12500000000) (0 / 1)
  have hratio : ((0 / 1) / (13514839647 / 12500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y6YV3Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y6YV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y6YV3_rounded_endpoints :
    (38503978489937004273078819612241040467 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y6YV3Interval.1 ∧ manuscriptCase2Y6YV3Interval.2 ≤ (9625994622484251068269704903060260117 / 2500000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y6YV3Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y6YV3_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y6 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc ((38503978489937004273078819612241040467 / 10000000000000000000000000000000000000000) : ℝ) ((9625994622484251068269704903060260117 / 2500000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((38503978489937004273078819612241040467 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y6YV3Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y6YV3_rounded_endpoints.1
  have hhi : (manuscriptCase2Y6YV3Interval.2 : ℝ) ≤ ((9625994622484251068269704903060260117 / 2500000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y6YV3_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y6YV3_exact_interval.1, manuscriptCase2Y6YV3_exact_interval.2.trans hhi⟩

def manuscriptCase2Y6YV4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-11618157 / 100000000) (0 / 1) (0) (0) (7622774416539184957201 / 6103515625000000000000) (0 / 1)

private theorem manuscriptCase2Y6YV4_arg_eq : barrierCase2Y6YV4LogArg = barrierComplex (87308501399 / 78125000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y6YV4LogArg, Case2PointData.Y6, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y6YV4_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2) = barrierComplex (-11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y6YV4_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y6 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc (manuscriptCase2Y6YV4Interval.1 : ℝ) (manuscriptCase2Y6YV4Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2) * Complex.log barrierCase2Y6YV4LogArg).re ∈ _
  rw [manuscriptCase2Y6YV4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-11618157 / 100000000) (0 / 1)
    barrierCase2Y6YV4LogArg (0) (0) (7622774416539184957201 / 6103515625000000000000) (87308501399 / 78125000000) (0 / 1)
  have hratio : ((0 / 1) / (87308501399 / 78125000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y6YV4Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y6YV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y6YV4_rounded_endpoints :
    (-4035048790479694016767423506769635103 / 312500000000000000000000000000000000000) ≤ manuscriptCase2Y6YV4Interval.1 ∧ manuscriptCase2Y6YV4Interval.2 ≤ (-129121561295350208536557552216628323159 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y6YV4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y6YV4_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y6 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc ((-4035048790479694016767423506769635103 / 312500000000000000000000000000000000000) : ℝ) ((-129121561295350208536557552216628323159 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-4035048790479694016767423506769635103 / 312500000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y6YV4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y6YV4_rounded_endpoints.1
  have hhi : (manuscriptCase2Y6YV4Interval.2 : ℝ) ≤ ((-129121561295350208536557552216628323159 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y6YV4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y6YV4_exact_interval.1, manuscriptCase2Y6YV4_exact_interval.2.trans hhi⟩

def manuscriptCase2Y6YV5Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-13619357 / 100000000) (-600749 / 3125000) (-1) (-1) (593834398262571396649 / 488281250000000000000) (-8835658093 / 33310658093)

private theorem manuscriptCase2Y6YV5_arg_eq : barrierCase2Y6YV5LogArg = barrierComplex (979 / 2500) (-21073158093 / 31250000000) := by
  apply Complex.ext <;> norm_num [barrierCase2Y6YV5LogArg, Case2PointData.Y6, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y6YV5_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2) = barrierComplex (-13619357 / 100000000) (-600749 / 3125000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y6YV5_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y6 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc (manuscriptCase2Y6YV5Interval.1 : ℝ) (manuscriptCase2Y6YV5Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2) * Complex.log barrierCase2Y6YV5LogArg).re ∈ _
  rw [manuscriptCase2Y6YV5_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-13619357 / 100000000) (-600749 / 3125000)
    barrierCase2Y6YV5LogArg (-1) (-1) (593834398262571396649 / 488281250000000000000) (33310658093 / 31250000000) (-8835658093 / 31250000000)
  have hratio : ((-8835658093 / 31250000000) / (33310658093 / 31250000000) : ℚ) = (-8835658093 / 33310658093) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y6YV5Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y6YV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y6YV5_rounded_endpoints :
    (-1669545496372158994743325496147769063923 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y6YV5Interval.1 ∧ manuscriptCase2Y6YV5Interval.2 ≤ (-1669545496372158924960285084306484487041 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y6YV5Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y6YV5_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y6 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc ((-1669545496372158994743325496147769063923 / 10000000000000000000000000000000000000000) : ℝ) ((-1669545496372158924960285084306484487041 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-1669545496372158994743325496147769063923 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y6YV5Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y6YV5_rounded_endpoints.1
  have hhi : (manuscriptCase2Y6YV5Interval.2 : ℝ) ≤ ((-1669545496372158924960285084306484487041 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y6YV5_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y6YV5_exact_interval.1, manuscriptCase2Y6YV5_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
