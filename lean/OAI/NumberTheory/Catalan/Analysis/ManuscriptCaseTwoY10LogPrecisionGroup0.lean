import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointY10

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2Y10YV0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-15199211 / 100000000) (0 / 1) (3) (0) (365843576953586698201 / 312500000000000000000) (0 / 1)

private theorem manuscriptCase2Y10YV0_arg_eq : barrierCase2Y10YV0LogArg = barrierComplex (19127037851 / 6250000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y10YV0LogArg, Case2PointData.Y10, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y10YV0_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2) = barrierComplex (-15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y10YV0_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y10 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc (manuscriptCase2Y10YV0Interval.1 : ℝ) (manuscriptCase2Y10YV0Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2) * Complex.log barrierCase2Y10YV0LogArg).re ∈ _
  rw [manuscriptCase2Y10YV0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-15199211 / 100000000) (0 / 1)
    barrierCase2Y10YV0LogArg (3) (0) (365843576953586698201 / 312500000000000000000) (19127037851 / 6250000000) (0 / 1)
  have hratio : ((0 / 1) / (19127037851 / 6250000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y10YV0Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y10YV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y10YV0_rounded_endpoints :
    (-85003218741543390793343665624519336931 / 500000000000000000000000000000000000000) ≤ manuscriptCase2Y10YV0Interval.1 ∧ manuscriptCase2Y10YV0Interval.2 ≤ (-425016093707716953889743862748993664953 / 2500000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y10YV0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y10YV0_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y10 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc ((-85003218741543390793343665624519336931 / 500000000000000000000000000000000000000) : ℝ) ((-425016093707716953889743862748993664953 / 2500000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-85003218741543390793343665624519336931 / 500000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y10YV0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y10YV0_rounded_endpoints.1
  have hhi : (manuscriptCase2Y10YV0Interval.2 : ℝ) ≤ ((-425016093707716953889743862748993664953 / 2500000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y10YV0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y10YV0_exact_interval.1, manuscriptCase2Y10YV0_exact_interval.2.trans hhi⟩

def manuscriptCase2Y10YV1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2225831 / 50000000) (0 / 1) (3) (0) (3209915202930430283809 / 1953125000000000000000) (0 / 1)

private theorem manuscriptCase2Y10YV1_arg_eq : barrierCase2Y10YV1LogArg = barrierComplex (56656113553 / 15625000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y10YV1LogArg, Case2PointData.Y10, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y10YV1_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2) = barrierComplex (-2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y10YV1_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y10 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc (manuscriptCase2Y10YV1Interval.1 : ℝ) (manuscriptCase2Y10YV1Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2) * Complex.log barrierCase2Y10YV1LogArg).re ∈ _
  rw [manuscriptCase2Y10YV1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2225831 / 50000000) (0 / 1)
    barrierCase2Y10YV1LogArg (3) (0) (3209915202930430283809 / 1953125000000000000000) (56656113553 / 15625000000) (0 / 1)
  have hratio : ((0 / 1) / (56656113553 / 15625000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y10YV1Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y10YV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y10YV1_rounded_endpoints :
    (-286715457551938881694425351059339640323 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2Y10YV1Interval.1 ∧ manuscriptCase2Y10YV1Interval.2 ≤ (-573430915103877763298670952263147770209 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y10YV1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y10YV1_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y10 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc ((-286715457551938881694425351059339640323 / 5000000000000000000000000000000000000000) : ℝ) ((-573430915103877763298670952263147770209 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-286715457551938881694425351059339640323 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y10YV1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y10YV1_rounded_endpoints.1
  have hhi : (manuscriptCase2Y10YV1Interval.2 : ℝ) ≤ ((-573430915103877763298670952263147770209 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y10YV1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y10YV1_exact_interval.1, manuscriptCase2Y10YV1_exact_interval.2.trans hhi⟩

def manuscriptCase2Y10YV2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-1272699 / 50000000) (0 / 1) (-5) (0) (175630973108690482321 / 122070312500000000000) (0 / 1)

private theorem manuscriptCase2Y10YV2_arg_eq : barrierCase2Y10YV2LogArg = barrierComplex (13252583639 / 62500000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y10YV2LogArg, Case2PointData.Y10, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y10YV2_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2) = barrierComplex (-1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y10YV2_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y10 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc (manuscriptCase2Y10YV2Interval.1 : ℝ) (manuscriptCase2Y10YV2Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2) * Complex.log barrierCase2Y10YV2LogArg).re ∈ _
  rw [manuscriptCase2Y10YV2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-1272699 / 50000000) (0 / 1)
    barrierCase2Y10YV2LogArg (-5) (0) (175630973108690482321 / 122070312500000000000) (13252583639 / 62500000000) (0 / 1)
  have hratio : ((0 / 1) / (13252583639 / 62500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y10YV2Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y10YV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y10YV2_rounded_endpoints :
    (4934807747913282477978587239331495897 / 125000000000000000000000000000000000000) ≤ manuscriptCase2Y10YV2Interval.1 ∧ manuscriptCase2Y10YV2Interval.2 ≤ (9869615495826564958105648394156326691 / 250000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y10YV2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y10YV2_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y10 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc ((4934807747913282477978587239331495897 / 125000000000000000000000000000000000000) : ℝ) ((9869615495826564958105648394156326691 / 250000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((4934807747913282477978587239331495897 / 125000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y10YV2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y10YV2_rounded_endpoints.1
  have hhi : (manuscriptCase2Y10YV2Interval.2 : ℝ) ≤ ((9869615495826564958105648394156326691 / 250000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y10YV2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y10YV2_exact_interval.1, manuscriptCase2Y10YV2_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
