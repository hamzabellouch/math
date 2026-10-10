import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX2

namespace OAI

noncomputable section
namespace InternalCatalan

def manuscriptCase2X2XV0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (15199211 / 100000000) (0 / 1) (-3) (0) (23928673780139530689 / 19531250000000000000) (0 / 1)

private theorem manuscriptCase2X2XV0_arg_eq : barrierCase2X2XV0LogArg = barrierComplex (4891694367 / 12500000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X2XV0LogArg, Case2PointData.X2, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X2XV0_weight_eq : (barrierV2Tail.getD 0 (0, 0)).2 = barrierComplex (15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X2XV0_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X2 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc (manuscriptCase2X2XV0Interval.1 : ℝ) (manuscriptCase2X2XV0Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X2XV0LogArg).re ∈ _
  rw [manuscriptCase2X2XV0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (15199211 / 100000000) (0 / 1)
    barrierCase2X2XV0LogArg (-3) (0) (23928673780139530689 / 19531250000000000000) (4891694367 / 12500000000) (0 / 1)
  have hratio : ((0 / 1) / (4891694367 / 12500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X2XV0Interval
  apply h
  all_goals
    try rw [manuscriptCase2X2XV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X2XV0_rounded_endpoints :
    (-285194926336913303715070922428857495491 / 2000000000000000000000000000000000000000) ≤ manuscriptCase2X2XV0Interval.1 ∧ manuscriptCase2X2XV0Interval.2 ≤ (-1425974631684566518267456750649875398641 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X2XV0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X2XV0_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X2 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc ((-285194926336913303715070922428857495491 / 2000000000000000000000000000000000000000) : ℝ) ((-1425974631684566518267456750649875398641 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-285194926336913303715070922428857495491 / 2000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X2XV0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X2XV0_rounded_endpoints.1
  have hhi : (manuscriptCase2X2XV0Interval.2 : ℝ) ≤ ((-1425974631684566518267456750649875398641 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X2XV0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X2XV0_exact_interval.1, manuscriptCase2X2XV0_exact_interval.2.trans hhi⟩

def manuscriptCase2X2XV1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (2225831 / 50000000) (0 / 1) (-4) (0) (70982025258755776201 / 61035156250000000000) (0 / 1)

private theorem manuscriptCase2X2XV1_arg_eq : barrierCase2X2XV1LogArg = barrierComplex (8425083101 / 31250000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X2XV1LogArg, Case2PointData.X2, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X2XV1_weight_eq : (barrierV2Tail.getD 1 (0, 0)).2 = barrierComplex (2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X2XV1_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X2 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc (manuscriptCase2X2XV1Interval.1 : ℝ) (manuscriptCase2X2XV1Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X2XV1LogArg).re ∈ _
  rw [manuscriptCase2X2XV1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (2225831 / 50000000) (0 / 1)
    barrierCase2X2XV1LogArg (-4) (0) (70982025258755776201 / 61035156250000000000) (8425083101 / 31250000000) (0 / 1)
  have hratio : ((0 / 1) / (8425083101 / 31250000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X2XV1Interval
  apply h
  all_goals
    try rw [manuscriptCase2X2XV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X2XV1_rounded_endpoints :
    (-583526542148986340974437591789172273233 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X2XV1Interval.1 ∧ manuscriptCase2X2XV1Interval.2 ≤ (-145881635537246585213549565457831664389 / 2500000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X2XV1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X2XV1_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X2 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc ((-583526542148986340974437591789172273233 / 10000000000000000000000000000000000000000) : ℝ) ((-145881635537246585213549565457831664389 / 2500000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-583526542148986340974437591789172273233 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X2XV1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X2XV1_rounded_endpoints.1
  have hhi : (manuscriptCase2X2XV1Interval.2 : ℝ) ≤ ((-145881635537246585213549565457831664389 / 2500000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X2XV1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X2XV1_exact_interval.1, manuscriptCase2X2XV1_exact_interval.2.trans hhi⟩

def manuscriptCase2X2XV2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (1272699 / 50000000) (0 / 1) (1) (0) (43552084557971883213369 / 31250000000000000000000) (0 / 1)

private theorem manuscriptCase2X2XV2_arg_eq : barrierCase2X2XV2LogArg = barrierComplex (208691361963 / 125000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X2XV2LogArg, Case2PointData.X2, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X2XV2_weight_eq : (barrierV2Tail.getD 2 (0, 0)).2 = barrierComplex (1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X2XV2_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X2 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc (manuscriptCase2X2XV2Interval.1 : ℝ) (manuscriptCase2X2XV2Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X2XV2LogArg).re ∈ _
  rw [manuscriptCase2X2XV2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (1272699 / 50000000) (0 / 1)
    barrierCase2X2XV2LogArg (1) (0) (43552084557971883213369 / 31250000000000000000000) (208691361963 / 125000000000) (0 / 1)
  have hratio : ((0 / 1) / (208691361963 / 125000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X2XV2Interval
  apply h
  all_goals
    try rw [manuscriptCase2X2XV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X2XV2_rounded_endpoints :
    (13046251283492795565754912258677287721 / 1000000000000000000000000000000000000000) ≤ manuscriptCase2X2XV2Interval.1 ∧ manuscriptCase2X2XV2Interval.2 ≤ (65231256417463977837368456955200027933 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X2XV2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X2XV2_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X2 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc ((13046251283492795565754912258677287721 / 1000000000000000000000000000000000000000) : ℝ) ((65231256417463977837368456955200027933 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((13046251283492795565754912258677287721 / 1000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X2XV2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X2XV2_rounded_endpoints.1
  have hhi : (manuscriptCase2X2XV2Interval.2 : ℝ) ≤ ((65231256417463977837368456955200027933 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X2XV2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X2XV2_exact_interval.1, manuscriptCase2X2XV2_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
