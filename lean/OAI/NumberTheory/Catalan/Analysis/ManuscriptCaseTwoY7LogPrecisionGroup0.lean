import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointY7

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2Y7YV0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-15199211 / 100000000) (0 / 1) (2) (0) (62526642602196726009 / 39062500000000000000) (0 / 1)

private theorem manuscriptCase2Y7YV0_arg_eq : barrierCase2Y7YV0LogArg = barrierComplex (7907378997 / 3125000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y7YV0LogArg, Case2PointData.Y7, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y7YV0_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2) = barrierComplex (-15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y7YV0_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y7 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc (manuscriptCase2Y7YV0Interval.1 : ℝ) (manuscriptCase2Y7YV0Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2) * Complex.log barrierCase2Y7YV0LogArg).re ∈ _
  rw [manuscriptCase2Y7YV0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-15199211 / 100000000) (0 / 1)
    barrierCase2Y7YV0LogArg (2) (0) (62526642602196726009 / 39062500000000000000) (7907378997 / 3125000000) (0 / 1)
  have hratio : ((0 / 1) / (7907378997 / 3125000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y7YV0Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y7YV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y7YV0_rounded_endpoints :
    (-282207425983833226065526800049015576973 / 2000000000000000000000000000000000000000) ≤ manuscriptCase2Y7YV0Interval.1 ∧ manuscriptCase2Y7YV0Interval.2 ≤ (-282207425983833226024473727298015692809 / 2000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y7YV0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y7YV0_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y7 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc ((-282207425983833226065526800049015576973 / 2000000000000000000000000000000000000000) : ℝ) ((-282207425983833226024473727298015692809 / 2000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-282207425983833226065526800049015576973 / 2000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y7YV0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y7YV0_rounded_endpoints.1
  have hhi : (manuscriptCase2Y7YV0Interval.2 : ℝ) ≤ ((-282207425983833226024473727298015692809 / 2000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y7YV0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y7YV0_exact_interval.1, manuscriptCase2Y7YV0_exact_interval.2.trans hhi⟩

def manuscriptCase2Y7YV1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2225831 / 50000000) (0 / 1) (3) (0) (545672640351295534081 / 488281250000000000000) (0 / 1)

private theorem manuscriptCase2Y7YV1_arg_eq : barrierCase2Y7YV1LogArg = barrierComplex (23359636991 / 7812500000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y7YV1LogArg, Case2PointData.Y7, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y7YV1_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2) = barrierComplex (-2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y7YV1_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y7 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc (manuscriptCase2Y7YV1Interval.1 : ℝ) (manuscriptCase2Y7YV1Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2) * Complex.log barrierCase2Y7YV1LogArg).re ∈ _
  rw [manuscriptCase2Y7YV1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2225831 / 50000000) (0 / 1)
    barrierCase2Y7YV1LogArg (3) (0) (545672640351295534081 / 488281250000000000000) (23359636991 / 7812500000) (0 / 1)
  have hratio : ((0 / 1) / (23359636991 / 7812500000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y7YV1Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y7YV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y7YV1_rounded_endpoints :
    (-487583684639547586919781835134440086511 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y7YV1Interval.1 ∧ manuscriptCase2Y7YV1Interval.2 ≤ (-487583684639547586829602337666055874753 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y7YV1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y7YV1_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y7 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc ((-487583684639547586919781835134440086511 / 10000000000000000000000000000000000000000) : ℝ) ((-487583684639547586829602337666055874753 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-487583684639547586919781835134440086511 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y7YV1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y7YV1_rounded_endpoints.1
  have hhi : (manuscriptCase2Y7YV1Interval.2 : ℝ) ≤ ((-487583684639547586829602337666055874753 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y7YV1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y7YV1_exact_interval.1, manuscriptCase2Y7YV1_exact_interval.2.trans hhi⟩

def manuscriptCase2Y7YV2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-1272699 / 50000000) (0 / 1) (-1) (0) (617215940396253847089 / 488281250000000000000) (0 / 1)

private theorem manuscriptCase2Y7YV2_arg_eq : barrierCase2Y7YV2LogArg = barrierComplex (24843831033 / 31250000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y7YV2LogArg, Case2PointData.Y7, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y7YV2_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2) = barrierComplex (-1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y7YV2_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y7 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc (manuscriptCase2Y7YV2Interval.1 : ℝ) (manuscriptCase2Y7YV2Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2) * Complex.log barrierCase2Y7YV2LogArg).re ∈ _
  rw [manuscriptCase2Y7YV2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-1272699 / 50000000) (0 / 1)
    barrierCase2Y7YV2LogArg (-1) (0) (617215940396253847089 / 488281250000000000000) (24843831033 / 31250000000) (0 / 1)
  have hratio : ((0 / 1) / (24843831033 / 31250000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y7YV2Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y7YV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y7YV2_rounded_endpoints :
    (29196975366407096420525310454357498397 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2Y7YV2Interval.1 ∧ manuscriptCase2Y7YV2Interval.2 ≤ (7299243841601774107279801529034046711 / 1250000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y7YV2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y7YV2_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y7 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc ((29196975366407096420525310454357498397 / 5000000000000000000000000000000000000000) : ℝ) ((7299243841601774107279801529034046711 / 1250000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((29196975366407096420525310454357498397 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y7YV2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y7YV2_rounded_endpoints.1
  have hhi : (manuscriptCase2Y7YV2Interval.2 : ℝ) ≤ ((7299243841601774107279801529034046711 / 1250000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y7YV2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y7YV2_exact_interval.1, manuscriptCase2Y7YV2_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
