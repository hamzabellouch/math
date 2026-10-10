import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointY8

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2Y8YV3Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (2466317 / 50000000) (0 / 1) (-2) (0) (3722627891392642499569 / 2500000000000000000000) (0 / 1)

private theorem manuscriptCase2Y8YV3_arg_eq : barrierCase2Y8YV3LogArg = barrierComplex (61013341913 / 100000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y8YV3LogArg, Case2PointData.Y8, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y8YV3_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2) = barrierComplex (2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y8YV3_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y8 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc (manuscriptCase2Y8YV3Interval.1 : ℝ) (manuscriptCase2Y8YV3Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2) * Complex.log barrierCase2Y8YV3LogArg).re ∈ _
  rw [manuscriptCase2Y8YV3_weight_eq]
  have h := manuscript_weighted_complex_log_interval (2466317 / 50000000) (0 / 1)
    barrierCase2Y8YV3LogArg (-2) (0) (3722627891392642499569 / 2500000000000000000000) (61013341913 / 100000000000) (0 / 1)
  have hratio : ((0 / 1) / (61013341913 / 100000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y8YV3Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y8YV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y8YV3_rounded_endpoints :
    (-121855204794175762985228698912807502763 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2Y8YV3Interval.1 ∧ manuscriptCase2Y8YV3Interval.2 ≤ (-243710409588351525903842209164942954481 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y8YV3Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y8YV3_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y8 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc ((-121855204794175762985228698912807502763 / 5000000000000000000000000000000000000000) : ℝ) ((-243710409588351525903842209164942954481 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-121855204794175762985228698912807502763 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y8YV3Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y8YV3_rounded_endpoints.1
  have hhi : (manuscriptCase2Y8YV3Interval.2 : ℝ) ≤ ((-243710409588351525903842209164942954481 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y8YV3_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y8YV3_exact_interval.1, manuscriptCase2Y8YV3_exact_interval.2.trans hhi⟩

def manuscriptCase2Y8YV4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-11618157 / 100000000) (0 / 1) (-2) (0) (154860105278932459268641 / 97656250000000000000000) (0 / 1)

private theorem manuscriptCase2Y8YV4_arg_eq : barrierCase2Y8YV4LogArg = barrierComplex (393522687121 / 625000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y8YV4LogArg, Case2PointData.Y8, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y8YV4_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2) = barrierComplex (-11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y8YV4_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y8 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc (manuscriptCase2Y8YV4Interval.1 : ℝ) (manuscriptCase2Y8YV4Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2) * Complex.log barrierCase2Y8YV4LogArg).re ∈ _
  rw [manuscriptCase2Y8YV4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-11618157 / 100000000) (0 / 1)
    barrierCase2Y8YV4LogArg (-2) (0) (154860105278932459268641 / 97656250000000000000000) (393522687121 / 625000000000) (0 / 1)
  have hratio : ((0 / 1) / (393522687121 / 625000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y8YV4Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y8YV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y8YV4_rounded_endpoints :
    (268735481880269932919046215523791145083 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2Y8YV4Interval.1 ∧ manuscriptCase2Y8YV4Interval.2 ≤ (537470963760539865994995607864994511493 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y8YV4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y8YV4_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y8 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc ((268735481880269932919046215523791145083 / 5000000000000000000000000000000000000000) : ℝ) ((537470963760539865994995607864994511493 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((268735481880269932919046215523791145083 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y8YV4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y8YV4_rounded_endpoints.1
  have hhi : (manuscriptCase2Y8YV4Interval.2 : ℝ) ≤ ((537470963760539865994995607864994511493 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y8YV4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y8YV4_exact_interval.1, manuscriptCase2Y8YV4_exact_interval.2.trans hhi⟩

def manuscriptCase2Y8YV5Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-13619357 / 100000000) (-600749 / 3125000) (0) (-2) (79955365900021143329209 / 62500000000000000000000) (97900000000 / 265275245547)

private theorem manuscriptCase2Y8YV5_arg_eq : barrierCase2Y8YV5LogArg = barrierComplex (979 / 2500) (-265275245547 / 250000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2Y8YV5LogArg, Case2PointData.Y8, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y8YV5_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2) = barrierComplex (-13619357 / 100000000) (-600749 / 3125000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y8YV5_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y8 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc (manuscriptCase2Y8YV5Interval.1 : ℝ) (manuscriptCase2Y8YV5Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2) * Complex.log barrierCase2Y8YV5LogArg).re ∈ _
  rw [manuscriptCase2Y8YV5_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-13619357 / 100000000) (-600749 / 3125000)
    barrierCase2Y8YV5LogArg (0) (-2) (79955365900021143329209 / 62500000000000000000000) (265275245547 / 125000000000) (979 / 1250)
  have hratio : ((979 / 1250) / (265275245547 / 125000000000) : ℚ) = (97900000000 / 265275245547) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y8YV5Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y8YV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y8YV5_rounded_endpoints :
    (-313470565484186947115148513464733711427 / 1250000000000000000000000000000000000000) ≤ manuscriptCase2Y8YV5Interval.1 ∧ manuscriptCase2Y8YV5Interval.2 ≤ (-39183820685523366211547071432648974727 / 156250000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y8YV5Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y8YV5_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y8 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc ((-313470565484186947115148513464733711427 / 1250000000000000000000000000000000000000) : ℝ) ((-39183820685523366211547071432648974727 / 156250000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-313470565484186947115148513464733711427 / 1250000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y8YV5Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y8YV5_rounded_endpoints.1
  have hhi : (manuscriptCase2Y8YV5Interval.2 : ℝ) ≤ ((-39183820685523366211547071432648974727 / 156250000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y8YV5_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y8YV5_exact_interval.1, manuscriptCase2Y8YV5_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
