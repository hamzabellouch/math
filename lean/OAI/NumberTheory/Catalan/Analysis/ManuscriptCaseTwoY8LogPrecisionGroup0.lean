import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointY8

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2Y8YV0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-15199211 / 100000000) (0 / 1) (2) (0) (290768295341780173129 / 156250000000000000000) (0 / 1)

private theorem manuscriptCase2Y8YV0_arg_eq : barrierCase2Y8YV0LogArg = barrierComplex (17051929373 / 6250000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y8YV0LogArg, Case2PointData.Y8, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y8YV0_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2) = barrierComplex (-15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y8YV0_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y8 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc (manuscriptCase2Y8YV0Interval.1 : ℝ) (manuscriptCase2Y8YV0Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2) * Complex.log barrierCase2Y8YV0LogArg).re ∈ _
  rw [manuscriptCase2Y8YV0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-15199211 / 100000000) (0 / 1)
    barrierCase2Y8YV0LogArg (2) (0) (290768295341780173129 / 156250000000000000000) (17051929373 / 6250000000) (0 / 1)
  have hratio : ((0 / 1) / (17051929373 / 6250000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y8YV0Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y8YV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y8YV0_rounded_endpoints :
    (-1525517287293163250161015941785335994273 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y8YV0Interval.1 ∧ manuscriptCase2Y8YV0Interval.2 ≤ (-1525517287293163249953471844384257626611 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y8YV0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y8YV0_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y8 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc ((-1525517287293163250161015941785335994273 / 10000000000000000000000000000000000000000) : ℝ) ((-1525517287293163249953471844384257626611 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-1525517287293163250161015941785335994273 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y8YV0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y8YV0_rounded_endpoints.1
  have hhi : (manuscriptCase2Y8YV0Interval.2 : ℝ) ≤ ((-1525517287293163249953471844384257626611 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y8YV0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y8YV0_exact_interval.1, manuscriptCase2Y8YV0_exact_interval.2.trans hhi⟩

def manuscriptCase2Y8YV1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2225831 / 50000000) (0 / 1) (3) (0) (2543264390303471558161 / 1953125000000000000000) (0 / 1)

private theorem manuscriptCase2Y8YV1_arg_eq : barrierCase2Y8YV1LogArg = barrierComplex (50430788119 / 15625000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y8YV1LogArg, Case2PointData.Y8, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y8YV1_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2) = barrierComplex (-2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y8YV1_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y8 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc (manuscriptCase2Y8YV1Interval.1 : ℝ) (manuscriptCase2Y8YV1Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2) * Complex.log barrierCase2Y8YV1LogArg).re ∈ _
  rw [manuscriptCase2Y8YV1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2225831 / 50000000) (0 / 1)
    barrierCase2Y8YV1LogArg (3) (0) (2543264390303471558161 / 1953125000000000000000) (50430788119 / 15625000000) (0 / 1)
  have hratio : ((0 / 1) / (50430788119 / 15625000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y8YV1Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y8YV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y8YV1_rounded_endpoints :
    (-521614443874801923471282698195150996509 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y8YV1Interval.1 ∧ manuscriptCase2Y8YV1Interval.2 ≤ (-260807221937400961690551600363383378047 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y8YV1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y8YV1_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y8 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc ((-521614443874801923471282698195150996509 / 10000000000000000000000000000000000000000) : ℝ) ((-260807221937400961690551600363383378047 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-521614443874801923471282698195150996509 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y8YV1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y8YV1_rounded_endpoints.1
  have hhi : (manuscriptCase2Y8YV1Interval.2 : ℝ) ≤ ((-260807221937400961690551600363383378047 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y8YV1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y8YV1_exact_interval.1, manuscriptCase2Y8YV1_exact_interval.2.trans hhi⟩

def manuscriptCase2Y8YV2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-1272699 / 50000000) (0 / 1) (-2) (0) (1301678142383500948609 / 976562500000000000000) (0 / 1)

private theorem manuscriptCase2Y8YV2_arg_eq : barrierCase2Y8YV2LogArg = barrierComplex (36078776897 / 62500000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y8YV2LogArg, Case2PointData.Y8, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y8YV2_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2) = barrierComplex (-1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y8YV2_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y8 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc (manuscriptCase2Y8YV2Interval.1 : ℝ) (manuscriptCase2Y8YV2Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2) * Complex.log barrierCase2Y8YV2LogArg).re ∈ _
  rw [manuscriptCase2Y8YV2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-1272699 / 50000000) (0 / 1)
    barrierCase2Y8YV2LogArg (-2) (0) (1301678142383500948609 / 976562500000000000000) (36078776897 / 62500000000) (0 / 1)
  have hratio : ((0 / 1) / (36078776897 / 62500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y8YV2Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y8YV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y8YV2_rounded_endpoints :
    (13985988697482567461267666282778095861 / 1000000000000000000000000000000000000000) ≤ manuscriptCase2Y8YV2Interval.1 ∧ manuscriptCase2Y8YV2Interval.2 ≤ (34964971743706418661763061368724018913 / 2500000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y8YV2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y8YV2_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y8 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc ((13985988697482567461267666282778095861 / 1000000000000000000000000000000000000000) : ℝ) ((34964971743706418661763061368724018913 / 2500000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((13985988697482567461267666282778095861 / 1000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y8YV2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y8YV2_rounded_endpoints.1
  have hhi : (manuscriptCase2Y8YV2Interval.2 : ℝ) ≤ ((34964971743706418661763061368724018913 / 2500000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y8YV2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y8YV2_exact_interval.1, manuscriptCase2Y8YV2_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
