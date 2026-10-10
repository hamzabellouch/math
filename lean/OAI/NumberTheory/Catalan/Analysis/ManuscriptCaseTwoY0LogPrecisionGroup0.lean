import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointY0

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2Y0YV0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-15199211 / 100000000) (0 / 1) (1) (0) (27177468847388362801 / 19531250000000000000) (0 / 1)

private theorem manuscriptCase2Y0YV0_arg_eq : barrierCase2Y0YV0LogArg = barrierComplex (5213201401 / 3125000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y0YV0LogArg, Case2PointData.Y0, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y0YV0_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2) = barrierComplex (-15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y0YV0_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y0 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc (manuscriptCase2Y0YV0Interval.1 : ℝ) (manuscriptCase2Y0YV0Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2) * Complex.log barrierCase2Y0YV0LogArg).re ∈ _
  rw [manuscriptCase2Y0YV0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-15199211 / 100000000) (0 / 1)
    barrierCase2Y0YV0LogArg (1) (0) (27177468847388362801 / 19531250000000000000) (5213201401 / 3125000000) (0 / 1)
  have hratio : ((0 / 1) / (5213201401 / 3125000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y0YV0Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y0YV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y0YV0_rounded_endpoints :
    (-388917301806127433882490862970613632871 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2Y0YV0Interval.1 ∧ manuscriptCase2Y0YV0Interval.2 ≤ (-388917301806127433831174552721369488013 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y0YV0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y0YV0_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y0 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc ((-388917301806127433882490862970613632871 / 5000000000000000000000000000000000000000) : ℝ) ((-388917301806127433831174552721369488013 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-388917301806127433882490862970613632871 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y0YV0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y0YV0_rounded_endpoints.1
  have hhi : (manuscriptCase2Y0YV0Interval.2 : ℝ) ≤ ((-388917301806127433831174552721369488013 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y0YV0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y0YV0_exact_interval.1, manuscriptCase2Y0YV0_exact_interval.2.trans hhi⟩

def manuscriptCase2Y0YV1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2225831 / 50000000) (0 / 1) (1) (0) (233389912829320265209 / 122070312500000000000) (0 / 1)

private theorem manuscriptCase2Y0YV1_arg_eq : barrierCase2Y0YV1LogArg = barrierComplex (15277104203 / 7812500000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y0YV1LogArg, Case2PointData.Y0, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y0YV1_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2) = barrierComplex (-2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y0YV1_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y0 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc (manuscriptCase2Y0YV1Interval.1 : ℝ) (manuscriptCase2Y0YV1Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2) * Complex.log barrierCase2Y0YV1LogArg).re ∈ _
  rw [manuscriptCase2Y0YV1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2225831 / 50000000) (0 / 1)
    barrierCase2Y0YV1LogArg (1) (0) (233389912829320265209 / 122070312500000000000) (15277104203 / 7812500000) (0 / 1)
  have hratio : ((0 / 1) / (15277104203 / 7812500000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y0YV1Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y0YV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y0YV1_rounded_endpoints :
    (-74635478352834557598585690570176661187 / 2500000000000000000000000000000000000000) ≤ manuscriptCase2Y0YV1Interval.1 ∧ manuscriptCase2Y0YV1Interval.2 ≤ (-14927095670566911518066914039322686667 / 500000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y0YV1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y0YV1_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y0 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc ((-74635478352834557598585690570176661187 / 2500000000000000000000000000000000000000) : ℝ) ((-14927095670566911518066914039322686667 / 500000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-74635478352834557598585690570176661187 / 2500000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y0YV1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y0YV1_rounded_endpoints.1
  have hhi : (manuscriptCase2Y0YV1Interval.2 : ℝ) ≤ ((-14927095670566911518066914039322686667 / 500000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y0YV1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y0YV1_exact_interval.1, manuscriptCase2Y0YV1_exact_interval.2.trans hhi⟩

def manuscriptCase2Y0YV2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-1272699 / 50000000) (0 / 1) (1) (0) (2968046928863841898921 / 1953125000000000000000) (0 / 1)

private theorem manuscriptCase2Y0YV2_arg_eq : barrierCase2Y0YV2LogArg = barrierComplex (54479784589 / 31250000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y0YV2LogArg, Case2PointData.Y0, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y0YV2_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2) = barrierComplex (-1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y0YV2_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y0 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc (manuscriptCase2Y0YV2Interval.1 : ℝ) (manuscriptCase2Y0YV2Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2) * Complex.log barrierCase2Y0YV2LogArg).re ∈ _
  rw [manuscriptCase2Y0YV2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-1272699 / 50000000) (0 / 1)
    barrierCase2Y0YV2LogArg (1) (0) (2968046928863841898921 / 1953125000000000000000) (54479784589 / 31250000000) (0 / 1)
  have hratio : ((0 / 1) / (54479784589 / 31250000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y0YV2Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y0YV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y0YV2_rounded_endpoints :
    (-14147585067002946795987913469994527803 / 1000000000000000000000000000000000000000) ≤ manuscriptCase2Y0YV2Interval.1 ∧ manuscriptCase2Y0YV2Interval.2 ≤ (-141475850670029467942691343068847705199 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y0YV2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y0YV2_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y0 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc ((-14147585067002946795987913469994527803 / 1000000000000000000000000000000000000000) : ℝ) ((-141475850670029467942691343068847705199 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-14147585067002946795987913469994527803 / 1000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y0YV2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y0YV2_rounded_endpoints.1
  have hhi : (manuscriptCase2Y0YV2Interval.2 : ℝ) ≤ ((-141475850670029467942691343068847705199 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y0YV2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y0YV2_exact_interval.1, manuscriptCase2Y0YV2_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
