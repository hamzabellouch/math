import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX17

namespace OAI

noncomputable section
namespace InternalCatalan

def manuscriptCase2X17XV0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (15199211 / 100000000) (0 / 1) (1) (0) (493274603893682315961 / 312500000000000000000) (0 / 1)

private theorem manuscriptCase2X17XV0_arg_eq : barrierCase2X17XV0LogArg = barrierComplex (22209786219 / 12500000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X17XV0LogArg, Case2PointData.X17, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X17XV0_weight_eq : (barrierV2Tail.getD 0 (0, 0)).2 = barrierComplex (15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X17XV0_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X17 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc (manuscriptCase2X17XV0Interval.1 : ℝ) (manuscriptCase2X17XV0Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X17XV0LogArg).re ∈ _
  rw [manuscriptCase2X17XV0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (15199211 / 100000000) (0 / 1)
    barrierCase2X17XV0LogArg (1) (0) (493274603893682315961 / 312500000000000000000) (22209786219 / 12500000000) (0 / 1)
  have hratio : ((0 / 1) / (22209786219 / 12500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X17XV0Interval
  apply h
  all_goals
    try rw [manuscriptCase2X17XV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X17XV0_rounded_endpoints :
    (873657287466757721575046434912016145979 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X17XV0Interval.1 ∧ manuscriptCase2X17XV0Interval.2 ≤ (436828643733378860838839548559582725091 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X17XV0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X17XV0_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X17 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc ((873657287466757721575046434912016145979 / 10000000000000000000000000000000000000000) : ℝ) ((436828643733378860838839548559582725091 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((873657287466757721575046434912016145979 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X17XV0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X17XV0_rounded_endpoints.1
  have hhi : (manuscriptCase2X17XV0Interval.2 : ℝ) ≤ ((436828643733378860838839548559582725091 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X17XV0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X17XV0_exact_interval.1, manuscriptCase2X17XV0_exact_interval.2.trans hhi⟩

def manuscriptCase2X17XV1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (2225831 / 50000000) (0 / 1) (1) (0) (3645666951830640843649 / 1953125000000000000000) (0 / 1)

private theorem manuscriptCase2X17XV1_arg_eq : barrierCase2X17XV1LogArg = barrierComplex (60379358657 / 31250000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X17XV1LogArg, Case2PointData.X17, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X17XV1_weight_eq : (barrierV2Tail.getD 1 (0, 0)).2 = barrierComplex (2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X17XV1_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X17 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc (manuscriptCase2X17XV1Interval.1 : ℝ) (manuscriptCase2X17XV1Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X17XV1LogArg).re ∈ _
  rw [manuscriptCase2X17XV1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (2225831 / 50000000) (0 / 1)
    barrierCase2X17XV1LogArg (1) (0) (3645666951830640843649 / 1953125000000000000000) (60379358657 / 31250000000) (0 / 1)
  have hratio : ((0 / 1) / (60379358657 / 31250000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X17XV1Interval
  apply h
  all_goals
    try rw [manuscriptCase2X17XV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X17XV1_rounded_endpoints :
    (293198891147550150573236670987160543321 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X17XV1Interval.1 ∧ manuscriptCase2X17XV1Interval.2 ≤ (36649861393443768825510991398919215091 / 1250000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X17XV1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X17XV1_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X17 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc ((293198891147550150573236670987160543321 / 10000000000000000000000000000000000000000) : ℝ) ((36649861393443768825510991398919215091 / 1250000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((293198891147550150573236670987160543321 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X17XV1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X17XV1_rounded_endpoints.1
  have hhi : (manuscriptCase2X17XV1Interval.2 : ℝ) ≤ ((36649861393443768825510991398919215091 / 1250000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X17XV1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X17XV1_exact_interval.1, manuscriptCase2X17XV1_exact_interval.2.trans hhi⟩

def manuscriptCase2X17XV2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (1272699 / 50000000) (0 / 1) (-6) (0) (330961656410560231281 / 244140625000000000000) (0 / 1)

private theorem manuscriptCase2X17XV2_arg_eq : barrierCase2X17XV2LogArg = barrierComplex (18192351591 / 125000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X17XV2LogArg, Case2PointData.X17, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X17XV2_weight_eq : (barrierV2Tail.getD 2 (0, 0)).2 = barrierComplex (1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X17XV2_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X17 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc (manuscriptCase2X17XV2Interval.1 : ℝ) (manuscriptCase2X17XV2Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X17XV2LogArg).re ∈ _
  rw [manuscriptCase2X17XV2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (1272699 / 50000000) (0 / 1)
    barrierCase2X17XV2LogArg (-6) (0) (330961656410560231281 / 244140625000000000000) (18192351591 / 125000000000) (0 / 1)
  have hratio : ((0 / 1) / (18192351591 / 125000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X17XV2Interval
  apply h
  all_goals
    try rw [manuscriptCase2X17XV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X17XV2_rounded_endpoints :
    (-245288865809128538866801352111098374137 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2X17XV2Interval.1 ∧ manuscriptCase2X17XV2Interval.2 ≤ (-490577731618257077630475956280849563191 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X17XV2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X17XV2_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X17 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc ((-245288865809128538866801352111098374137 / 5000000000000000000000000000000000000000) : ℝ) ((-490577731618257077630475956280849563191 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-245288865809128538866801352111098374137 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X17XV2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X17XV2_rounded_endpoints.1
  have hhi : (manuscriptCase2X17XV2Interval.2 : ℝ) ≤ ((-490577731618257077630475956280849563191 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X17XV2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X17XV2_exact_interval.1, manuscriptCase2X17XV2_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
