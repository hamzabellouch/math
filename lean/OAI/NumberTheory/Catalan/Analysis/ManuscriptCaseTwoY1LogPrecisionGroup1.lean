import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointY1

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2Y1YV3Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (2466317 / 50000000) (0 / 1) (1) (0) (8461025099760105793449 / 5000000000000000000000) (0 / 1)

private theorem manuscriptCase2Y1YV3_arg_eq : barrierCase2Y1YV3LogArg = barrierComplex (91983830643 / 50000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y1YV3LogArg, Case2PointData.Y1, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y1YV3_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2) = barrierComplex (2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y1YV3_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y1 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc (manuscriptCase2Y1YV3Interval.1 : ℝ) (manuscriptCase2Y1YV3Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2) * Complex.log barrierCase2Y1YV3LogArg).re ∈ _
  rw [manuscriptCase2Y1YV3_weight_eq]
  have h := manuscript_weighted_complex_log_interval (2466317 / 50000000) (0 / 1)
    barrierCase2Y1YV3LogArg (1) (0) (8461025099760105793449 / 5000000000000000000000) (91983830643 / 50000000000) (0 / 1)
  have hratio : ((0 / 1) / (91983830643 / 50000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y1YV3Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y1YV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y1YV3_rounded_endpoints :
    (75172084621208709651070191657247337963 / 2500000000000000000000000000000000000000) ≤ manuscriptCase2Y1YV3Interval.1 ∧ manuscriptCase2Y1YV3Interval.2 ≤ (60137667696966967727518099051557430031 / 2000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y1YV3Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y1YV3_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y1 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc ((75172084621208709651070191657247337963 / 2500000000000000000000000000000000000000) : ℝ) ((60137667696966967727518099051557430031 / 2000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((75172084621208709651070191657247337963 / 2500000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y1YV3Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y1YV3_rounded_endpoints.1
  have hhi : (manuscriptCase2Y1YV3Interval.2 : ℝ) ≤ ((60137667696966967727518099051557430031 / 2000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y1YV3_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y1YV3_exact_interval.1, manuscriptCase2Y1YV3_exact_interval.2.trans hhi⟩

def manuscriptCase2Y1YV4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-11618157 / 100000000) (0 / 1) (1) (0) (353721688215512976063961 / 195312500000000000000000) (0 / 1)

private theorem manuscriptCase2Y1YV4_arg_eq : barrierCase2Y1YV4LogArg = barrierComplex (594745061531 / 312500000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y1YV4LogArg, Case2PointData.Y1, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y1YV4_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2) = barrierComplex (-11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y1YV4_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y1 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc (manuscriptCase2Y1YV4Interval.1 : ℝ) (manuscriptCase2Y1YV4Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2) * Complex.log barrierCase2Y1YV4LogArg).re ∈ _
  rw [manuscriptCase2Y1YV4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-11618157 / 100000000) (0 / 1)
    barrierCase2Y1YV4LogArg (1) (0) (353721688215512976063961 / 195312500000000000000000) (594745061531 / 312500000000) (0 / 1)
  have hratio : ((0 / 1) / (594745061531 / 312500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y1YV4Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y1YV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y1YV4_rounded_endpoints :
    (-747661371254338188887375008990296420667 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y1YV4Interval.1 ∧ manuscriptCase2Y1YV4Interval.2 ≤ (-747661371254338188808559210819644290919 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y1YV4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y1YV4_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y1 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc ((-747661371254338188887375008990296420667 / 10000000000000000000000000000000000000000) : ℝ) ((-747661371254338188808559210819644290919 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-747661371254338188887375008990296420667 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y1YV4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y1YV4_rounded_endpoints.1
  have hhi : (manuscriptCase2Y1YV4Interval.2 : ℝ) ≤ ((-747661371254338188808559210819644290919 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y1YV4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y1YV4_exact_interval.1, manuscriptCase2Y1YV4_exact_interval.2.trans hhi⟩

def manuscriptCase2Y1YV5Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-13619357 / 100000000) (-600749 / 3125000) (-3) (0) (2437674863538920115889 / 1953125000000000000000) (-6447663417 / 48950000000)

private theorem manuscriptCase2Y1YV5_arg_eq : barrierCase2Y1YV5LogArg = barrierComplex (979 / 2500) (-6447663417 / 125000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2Y1YV5LogArg, Case2PointData.Y1, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y1YV5_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2) = barrierComplex (-13619357 / 100000000) (-600749 / 3125000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y1YV5_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y1 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc (manuscriptCase2Y1YV5Interval.1 : ℝ) (manuscriptCase2Y1YV5Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2) * Complex.log barrierCase2Y1YV5LogArg).re ∈ _
  rw [manuscriptCase2Y1YV5_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-13619357 / 100000000) (-600749 / 3125000)
    barrierCase2Y1YV5LogArg (-3) (0) (2437674863538920115889 / 1953125000000000000000) (979 / 2500) (-6447663417 / 125000000000)
  have hratio : ((-6447663417 / 125000000000) / (979 / 2500) : ℚ) = (-6447663417 / 48950000000) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y1YV5Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y1YV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y1YV5_rounded_endpoints :
    (20267065918350815675584791668606947273 / 200000000000000000000000000000000000000) ≤ manuscriptCase2Y1YV5Interval.1 ∧ manuscriptCase2Y1YV5Interval.2 ≤ (1013353295917540784055133568666090956431 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y1YV5Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y1YV5_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y1 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc ((20267065918350815675584791668606947273 / 200000000000000000000000000000000000000) : ℝ) ((1013353295917540784055133568666090956431 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((20267065918350815675584791668606947273 / 200000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y1YV5Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y1YV5_rounded_endpoints.1
  have hhi : (manuscriptCase2Y1YV5Interval.2 : ℝ) ≤ ((1013353295917540784055133568666090956431 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y1YV5_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y1YV5_exact_interval.1, manuscriptCase2Y1YV5_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
