import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointY15

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2Y15YV3Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (2466317 / 50000000) (0 / 1) (1) (0) (326041 / 320000) (0 / 1)

private theorem manuscriptCase2Y15YV3_arg_eq : barrierCase2Y15YV3LogArg = barrierComplex (571 / 400) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y15YV3LogArg, Case2PointData.Y15, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y15YV3_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2) = barrierComplex (2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y15YV3_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y15 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc (manuscriptCase2Y15YV3Interval.1 : ℝ) (manuscriptCase2Y15YV3Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2) * Complex.log barrierCase2Y15YV3LogArg).re ∈ _
  rw [manuscriptCase2Y15YV3_weight_eq]
  have h := manuscript_weighted_complex_log_interval (2466317 / 50000000) (0 / 1)
    barrierCase2Y15YV3LogArg (1) (0) (326041 / 320000) (571 / 400) (0 / 1)
  have hratio : ((0 / 1) / (571 / 400) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y15YV3Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y15YV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y15YV3_rounded_endpoints :
    (175564609192293067923391242425095842209 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y15YV3Interval.1 ∧ manuscriptCase2Y15YV3Interval.2 ≤ (175564609192293067956698836706023271709 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y15YV3Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y15YV3_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y15 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc ((175564609192293067923391242425095842209 / 10000000000000000000000000000000000000000) : ℝ) ((175564609192293067956698836706023271709 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((175564609192293067923391242425095842209 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y15YV3Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y15YV3_rounded_endpoints.1
  have hhi : (manuscriptCase2Y15YV3Interval.2 : ℝ) ≤ ((175564609192293067956698836706023271709 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y15YV3_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y15YV3_exact_interval.1, manuscriptCase2Y15YV3_exact_interval.2.trans hhi⟩

def manuscriptCase2Y15YV4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-11618157 / 100000000) (0 / 1) (1) (0) (2128253689 / 1953125000) (0 / 1)

private theorem manuscriptCase2Y15YV4_arg_eq : barrierCase2Y15YV4LogArg = barrierComplex (46133 / 31250) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y15YV4LogArg, Case2PointData.Y15, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y15YV4_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2) = barrierComplex (-11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y15YV4_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y15 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc (manuscriptCase2Y15YV4Interval.1 : ℝ) (manuscriptCase2Y15YV4Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2) * Complex.log barrierCase2Y15YV4LogArg).re ∈ _
  rw [manuscriptCase2Y15YV4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-11618157 / 100000000) (0 / 1)
    barrierCase2Y15YV4LogArg (1) (0) (2128253689 / 1953125000) (46133 / 31250) (0 / 1)
  have hratio : ((0 / 1) / (46133 / 31250) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y15YV4Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y15YV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y15YV4_rounded_endpoints :
    (-226268924551019393170906309089354037121 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2Y15YV4Interval.1 ∧ manuscriptCase2Y15YV4Interval.2 ≤ (-28283615568877424141460065788496528193 / 625000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y15YV4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y15YV4_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y15 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc ((-226268924551019393170906309089354037121 / 5000000000000000000000000000000000000000) : ℝ) ((-28283615568877424141460065788496528193 / 625000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-226268924551019393170906309089354037121 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y15YV4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y15YV4_rounded_endpoints.1
  have hhi : (manuscriptCase2Y15YV4Interval.2 : ℝ) ≤ ((-28283615568877424141460065788496528193 / 625000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y15YV4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y15YV4_exact_interval.1, manuscriptCase2Y15YV4_exact_interval.2.trans hhi⟩

def manuscriptCase2Y15YV5Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-13619357 / 100000000) (-600749 / 3125000) (-2) (-1) (954533 / 781250) (2 / 977)

private theorem manuscriptCase2Y15YV5_arg_eq : barrierCase2Y15YV5LogArg = barrierComplex (979 / 2500) (-39 / 100) := by
  apply Complex.ext <;> norm_num [barrierCase2Y15YV5LogArg, Case2PointData.Y15, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y15YV5_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2) = barrierComplex (-13619357 / 100000000) (-600749 / 3125000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y15YV5_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y15 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc (manuscriptCase2Y15YV5Interval.1 : ℝ) (manuscriptCase2Y15YV5Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2) * Complex.log barrierCase2Y15YV5LogArg).re ∈ _
  rw [manuscriptCase2Y15YV5_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-13619357 / 100000000) (-600749 / 3125000)
    barrierCase2Y15YV5LogArg (-2) (-1) (954533 / 781250) (977 / 1250) (1 / 625)
  have hratio : ((1 / 625) / (977 / 1250) : ℚ) = (2 / 977) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y15YV5Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y15YV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y15YV5_rounded_endpoints :
    (-698305981773683164683943315893420854473 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y15YV5Interval.1 ∧ manuscriptCase2Y15YV5Interval.2 ≤ (-174576495443420773702234560577285372191 / 2500000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y15YV5Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y15YV5_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y15 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc ((-698305981773683164683943315893420854473 / 10000000000000000000000000000000000000000) : ℝ) ((-174576495443420773702234560577285372191 / 2500000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-698305981773683164683943315893420854473 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y15YV5Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y15YV5_rounded_endpoints.1
  have hhi : (manuscriptCase2Y15YV5Interval.2 : ℝ) ≤ ((-174576495443420773702234560577285372191 / 2500000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y15YV5_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y15YV5_exact_interval.1, manuscriptCase2Y15YV5_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
