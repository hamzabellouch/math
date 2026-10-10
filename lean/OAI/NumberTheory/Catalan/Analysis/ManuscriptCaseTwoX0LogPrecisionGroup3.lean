import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX0

namespace OAI

noncomputable section
namespace InternalCatalan

def manuscriptCase2X0XV3Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2466317 / 50000000) (0 / 1) (1) (0) (9140367355970197013209 / 5000000000000000000000) (0 / 1)

private theorem manuscriptCase2X0XV3_arg_eq : barrierCase2X0XV3LogArg = barrierComplex (95605268453 / 50000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X0XV3LogArg, Case2PointData.X0, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X0XV3_weight_eq : (barrierV2Tail.getD 3 (0, 0)).2 = barrierComplex (-2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X0XV3_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X0 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc (manuscriptCase2X0XV3Interval.1 : ℝ) (manuscriptCase2X0XV3Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2X0XV3LogArg).re ∈ _
  rw [manuscriptCase2X0XV3_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2466317 / 50000000) (0 / 1)
    barrierCase2X0XV3LogArg (1) (0) (9140367355970197013209 / 5000000000000000000000) (95605268453 / 50000000000) (0 / 1)
  have hratio : ((0 / 1) / (95605268453 / 50000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X0XV3Interval
  apply h
  all_goals
    try rw [manuscriptCase2X0XV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X0XV3_rounded_endpoints :
    (-15986788197264321664666146737 / 500000000000000000000000000000) ≤ manuscriptCase2X0XV3Interval.1 ∧ manuscriptCase2X0XV3Interval.2 ≤ (-3197357639452864332597479181 / 100000000000000000000000000000) := by
  simp only [manuscriptCase2X0XV3Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X0XV3_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X0 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc ((-15986788197264321664666146737 / 500000000000000000000000000000) : ℝ) ((-3197357639452864332597479181 / 100000000000000000000000000000) : ℝ) := by
  have hlo : ((-15986788197264321664666146737 / 500000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X0XV3Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X0XV3_rounded_endpoints.1
  have hhi : (manuscriptCase2X0XV3Interval.2 : ℝ) ≤ ((-3197357639452864332597479181 / 100000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X0XV3_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X0XV3_exact_interval.1, manuscriptCase2X0XV3_exact_interval.2.trans hhi⟩

def manuscriptCase2X0XV4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (11618157 / 100000000) (0 / 1) (1) (0) (369340743961475167902601 / 195312500000000000000000) (0 / 1)

private theorem manuscriptCase2X0XV4_arg_eq : barrierCase2X0XV4LogArg = barrierComplex (607734106301 / 312500000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X0XV4LogArg, Case2PointData.X0, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X0XV4_weight_eq : (barrierV2Tail.getD 4 (0, 0)).2 = barrierComplex (11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X0XV4_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X0 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc (manuscriptCase2X0XV4Interval.1 : ℝ) (manuscriptCase2X0XV4Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X0XV4LogArg).re ∈ _
  rw [manuscriptCase2X0XV4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (11618157 / 100000000) (0 / 1)
    barrierCase2X0XV4LogArg (1) (0) (369340743961475167902601 / 195312500000000000000000) (607734106301 / 312500000000) (0 / 1)
  have hratio : ((0 / 1) / (607734106301 / 312500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X0XV4Interval
  apply h
  all_goals
    try rw [manuscriptCase2X0XV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X0XV4_rounded_endpoints :
    (38638097633072146229408395391 / 500000000000000000000000000000) ≤ manuscriptCase2X0XV4Interval.1 ∧ manuscriptCase2X0XV4Interval.2 ≤ (77276195266144292467085868023 / 1000000000000000000000000000000) := by
  simp only [manuscriptCase2X0XV4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X0XV4_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X0 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc ((38638097633072146229408395391 / 500000000000000000000000000000) : ℝ) ((77276195266144292467085868023 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((38638097633072146229408395391 / 500000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X0XV4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X0XV4_rounded_endpoints.1
  have hhi : (manuscriptCase2X0XV4Interval.2 : ℝ) ≤ ((77276195266144292467085868023 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X0XV4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X0XV4_exact_interval.1, manuscriptCase2X0XV4_exact_interval.2.trans hhi⟩

def manuscriptCase2X0XV5Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (13619357 / 100000000) (600749 / 3125000) (0) (1) (24387984533876370241249 / 15625000000000000000000) (-31389185807 / 218610814193)

private theorem manuscriptCase2X0XV5_arg_eq : barrierCase2X0XV5LogArg = barrierComplex (1 / 1) (93610814193 / 125000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X0XV5LogArg, Case2PointData.X0, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X0XV5_weight_eq : (barrierV2Tail.getD 5 (0, 0)).2 = barrierComplex (13619357 / 100000000) (600749 / 3125000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X0XV5_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X0 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc (manuscriptCase2X0XV5Interval.1 : ℝ) (manuscriptCase2X0XV5Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2X0XV5LogArg).re ∈ _
  rw [manuscriptCase2X0XV5_weight_eq]
  have h := manuscript_weighted_complex_log_interval (13619357 / 100000000) (600749 / 3125000)
    barrierCase2X0XV5LogArg (0) (1) (24387984533876370241249 / 15625000000000000000000) (218610814193 / 125000000000) (-31389185807 / 125000000000)
  have hratio : ((-31389185807 / 125000000000) / (218610814193 / 125000000000) : ℚ) = (-31389185807 / 218610814193) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X0XV5Interval
  apply h
  all_goals
    try rw [manuscriptCase2X0XV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X0XV5_rounded_endpoints :
    (-93251437796229508094298839591 / 1000000000000000000000000000000) ≤ manuscriptCase2X0XV5Interval.1 ∧ manuscriptCase2X0XV5Interval.2 ≤ (-93251437796229501125191263053 / 1000000000000000000000000000000) := by
  simp only [manuscriptCase2X0XV5Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X0XV5_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X0 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc ((-93251437796229508094298839591 / 1000000000000000000000000000000) : ℝ) ((-93251437796229501125191263053 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((-93251437796229508094298839591 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X0XV5Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X0XV5_rounded_endpoints.1
  have hhi : (manuscriptCase2X0XV5Interval.2 : ℝ) ≤ ((-93251437796229501125191263053 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X0XV5_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X0XV5_exact_interval.1, manuscriptCase2X0XV5_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
