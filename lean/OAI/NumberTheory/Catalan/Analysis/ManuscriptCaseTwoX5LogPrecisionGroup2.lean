import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX5

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2X5XV0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (15199211 / 100000000) (0 / 1) (-2) (0) (17996115935224092241 / 9765625000000000000) (0 / 1)

private theorem manuscriptCase2X5XV0_arg_eq : barrierCase2X5XV0LogArg = barrierComplex (4242182921 / 6250000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X5XV0LogArg, Case2PointData.X5, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X5XV0_weight_eq : (barrierV2Tail.getD 0 (0, 0)).2 = barrierComplex (15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X5XV0_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X5 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc (manuscriptCase2X5XV0Interval.1 : ℝ) (manuscriptCase2X5XV0Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X5XV0LogArg).re ∈ _
  rw [manuscriptCase2X5XV0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (15199211 / 100000000) (0 / 1)
    barrierCase2X5XV0LogArg (-2) (0) (17996115935224092241 / 9765625000000000000) (4242182921 / 6250000000) (0 / 1)
  have hratio : ((0 / 1) / (4242182921 / 6250000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X5XV0Interval
  apply h
  all_goals
    try rw [manuscriptCase2X5XV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X5XV0_rounded_endpoints :
    (-588974726413260119921135533516294815777 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X5XV0Interval.1 ∧ manuscriptCase2X5XV0Interval.2 ≤ (-117794945282652023942912343566059453483 / 2000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X5XV0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X5XV0_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X5 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc ((-588974726413260119921135533516294815777 / 10000000000000000000000000000000000000000) : ℝ) ((-117794945282652023942912343566059453483 / 2000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-588974726413260119921135533516294815777 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X5XV0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X5XV0_rounded_endpoints.1
  have hhi : (manuscriptCase2X5XV0Interval.2 : ℝ) ≤ ((-117794945282652023942912343566059453483 / 2000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X5XV0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X5XV0_exact_interval.1, manuscriptCase2X5XV0_exact_interval.2.trans hhi⟩

def manuscriptCase2X5XV1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (2225831 / 50000000) (0 / 1) (-2) (0) (92189738648266830169 / 61035156250000000000) (0 / 1)

private theorem manuscriptCase2X5XV1_arg_eq : barrierCase2X5XV1LogArg = barrierComplex (9601548763 / 15625000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X5XV1LogArg, Case2PointData.X5, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X5XV1_weight_eq : (barrierV2Tail.getD 1 (0, 0)).2 = barrierComplex (2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X5XV1_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X5 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc (manuscriptCase2X5XV1Interval.1 : ℝ) (manuscriptCase2X5XV1Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X5XV1LogArg).re ∈ _
  rw [manuscriptCase2X5XV1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (2225831 / 50000000) (0 / 1)
    barrierCase2X5XV1LogArg (-2) (0) (92189738648266830169 / 61035156250000000000) (9601548763 / 15625000000) (0 / 1)
  have hratio : ((0 / 1) / (9601548763 / 15625000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X5XV1Interval
  apply h
  all_goals
    try rw [manuscriptCase2X5XV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X5XV1_rounded_endpoints :
    (-216772693124509767758293040343616566919 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X5XV1Interval.1 ∧ manuscriptCase2X5XV1Interval.2 ≤ (-43354538624901953539634675009433043907 / 2000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X5XV1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X5XV1_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X5 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc ((-216772693124509767758293040343616566919 / 10000000000000000000000000000000000000000) : ℝ) ((-43354538624901953539634675009433043907 / 2000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-216772693124509767758293040343616566919 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X5XV1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X5XV1_rounded_endpoints.1
  have hhi : (manuscriptCase2X5XV1Interval.2 : ℝ) ≤ ((-43354538624901953539634675009433043907 / 2000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X5XV1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X5XV1_exact_interval.1, manuscriptCase2X5XV1_exact_interval.2.trans hhi⟩

def manuscriptCase2X5XV2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (1272699 / 50000000) (0 / 1) (0) (0) (7154789343774615161161 / 3906250000000000000000) (0 / 1)

private theorem manuscriptCase2X5XV2_arg_eq : barrierCase2X5XV2LogArg = barrierComplex (84585987869 / 62500000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X5XV2LogArg, Case2PointData.X5, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X5XV2_weight_eq : (barrierV2Tail.getD 2 (0, 0)).2 = barrierComplex (1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X5XV2_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X5 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc (manuscriptCase2X5XV2Interval.1 : ℝ) (manuscriptCase2X5XV2Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X5XV2LogArg).re ∈ _
  rw [manuscriptCase2X5XV2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (1272699 / 50000000) (0 / 1)
    barrierCase2X5XV2LogArg (0) (0) (7154789343774615161161 / 3906250000000000000000) (84585987869 / 62500000000) (0 / 1)
  have hratio : ((0 / 1) / (84585987869 / 62500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X5XV2Interval
  apply h
  all_goals
    try rw [manuscriptCase2X5XV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X5XV2_rounded_endpoints :
    (300876054298334119222703815312544381 / 39062500000000000000000000000000000000) ≤ manuscriptCase2X5XV2Interval.1 ∧ manuscriptCase2X5XV2Interval.2 ≤ (15404853980074706904233321946578091577 / 2000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X5XV2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X5XV2_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X5 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc ((300876054298334119222703815312544381 / 39062500000000000000000000000000000000) : ℝ) ((15404853980074706904233321946578091577 / 2000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((300876054298334119222703815312544381 / 39062500000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X5XV2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X5XV2_rounded_endpoints.1
  have hhi : (manuscriptCase2X5XV2Interval.2 : ℝ) ≤ ((15404853980074706904233321946578091577 / 2000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X5XV2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X5XV2_exact_interval.1, manuscriptCase2X5XV2_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
