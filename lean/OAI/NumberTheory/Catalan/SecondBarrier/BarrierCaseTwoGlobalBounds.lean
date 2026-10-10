import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoBracketHeight
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX1
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX10
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX11
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX12
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX13
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX14
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX15
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX16
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX17
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX18
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX2
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX3
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX4
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX5
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX6
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX7
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX8
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX9
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointY0
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointY1
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointY10
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointY11
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointY12
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointY13
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointY14
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointY15
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointY16
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointY17
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointY2
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointY3
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointY4
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointY5
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointY6
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointY7
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointY8

namespace OAI


noncomputable section
namespace InternalCatalan

def barrierCase2Y9YV0LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y9 : ℝ) : ℂ) * (barrierV2Tail.getD 0 (0, 0)).1 + (barrierV2Tail.getD 0 (0, 0)).1 ^ 2

private theorem barrierCase2Y9YV0_arg_eq :
    barrierCase2Y9YV0LogArg = barrierComplex (18281988371 / 6250000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y9YV0LogArg, Case2PointData.Y9, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y9YV0_arg_regular :
    (barrierCase2Y9YV0LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y9YV0LogArg).re := by
  rw [barrierCase2Y9YV0_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y9YV0_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2 = barrierComplex (-15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y9YV0_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2Y9YV0LogArg).re -
      ((barrierWeightedComplexLogRat (-15199211 / 100000000) (0 / 1) (3) (0) (334231098797379233641 / 312500000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y9YV0_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-15199211 / 100000000) (0 / 1)
    barrierCase2Y9YV0LogArg (3) (0) (334231098797379233641 / 312500000000000000000) (18281988371 / 6250000000) (0 / 1)
  have hratio : ((0 / 1) / (18281988371 / 6250000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y9YV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y9YV0_approx_upper :
    barrierWeightedComplexLogRat (-15199211 / 100000000) (0 / 1) (3) (0) (334231098797379233641 / 312500000000000000000) (0 / 1) <
      (-163138431534 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y9YV0_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y9 : ℝ) (barrierV2Tail.getD 0 (0, 0)) <
      (-163138431534 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2Y9YV0LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y9YV0_error).2
  have ha : ((barrierWeightedComplexLogRat (-15199211 / 100000000) (0 / 1) (3) (0) (334231098797379233641 / 312500000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-163138431534 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y9YV0_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y9YV1LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y9 : ℝ) : ℂ) * (barrierV2Tail.getD 1 (0, 0)).1 + (barrierV2Tail.getD 1 (0, 0)).1 ^ 2

private theorem barrierCase2Y9YV1_arg_eq :
    barrierCase2Y9YV1LogArg = barrierComplex (54120965113 / 15625000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y9YV1LogArg, Case2PointData.Y9, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y9YV1_arg_regular :
    (barrierCase2Y9YV1LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y9YV1LogArg).re := by
  rw [barrierCase2Y9YV1_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y9YV1_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2 = barrierComplex (-2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y9YV1_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2Y9YV1LogArg).re -
      ((barrierWeightedComplexLogRat (-2225831 / 50000000) (0 / 1) (3) (0) (2929078864762563102769 / 1953125000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y9YV1_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2225831 / 50000000) (0 / 1)
    barrierCase2Y9YV1LogArg (3) (0) (2929078864762563102769 / 1953125000000000000000) (54120965113 / 15625000000) (0 / 1)
  have hratio : ((0 / 1) / (54120965113 / 15625000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y9YV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y9YV1_approx_upper :
    barrierWeightedComplexLogRat (-2225831 / 50000000) (0 / 1) (3) (0) (2929078864762563102769 / 1953125000000000000000) (0 / 1) <
      (-55305197942 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y9YV1_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y9 : ℝ) (barrierV2Tail.getD 1 (0, 0)) <
      (-55305197942 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2Y9YV1LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y9YV1_error).2
  have ha : ((barrierWeightedComplexLogRat (-2225831 / 50000000) (0 / 1) (3) (0) (2929078864762563102769 / 1953125000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-55305197942 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y9YV1_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y9YV2LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y9 : ℝ) : ℂ) * (barrierV2Tail.getD 2 (0, 0)).1 + (barrierV2Tail.getD 2 (0, 0)).1 ^ 2

private theorem barrierCase2Y9YV2_arg_eq :
    barrierCase2Y9YV2LogArg = barrierComplex (22548127919 / 62500000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y9YV2LogArg, Case2PointData.Y9, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y9YV2_arg_regular :
    (barrierCase2Y9YV2LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y9YV2LogArg).re := by
  rw [barrierCase2Y9YV2_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y9YV2_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2 = barrierComplex (-1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y9YV2_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2Y9YV2LogArg).re -
      ((barrierWeightedComplexLogRat (-1272699 / 50000000) (0 / 1) (-3) (0) (508418072651587270561 / 488281250000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y9YV2_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-1272699 / 50000000) (0 / 1)
    barrierCase2Y9YV2LogArg (-3) (0) (508418072651587270561 / 488281250000000000000) (22548127919 / 62500000000) (0 / 1)
  have hratio : ((0 / 1) / (22548127919 / 62500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y9YV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y9YV2_approx_upper :
    barrierWeightedComplexLogRat (-1272699 / 50000000) (0 / 1) (-3) (0) (508418072651587270561 / 488281250000000000000) (0 / 1) <
      (25950702034 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y9YV2_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y9 : ℝ) (barrierV2Tail.getD 2 (0, 0)) <
      (25950702034 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2Y9YV2LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y9YV2_error).2
  have ha : ((barrierWeightedComplexLogRat (-1272699 / 50000000) (0 / 1) (-3) (0) (508418072651587270561 / 488281250000000000000) (0 / 1) : ℚ) : ℝ) <
      (25950702034 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y9YV2_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y9YV3LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y9 : ℝ) : ℂ) * (barrierV2Tail.getD 3 (0, 0)).1 + (barrierV2Tail.getD 3 (0, 0)).1 ^ 2

private theorem barrierCase2Y9YV3_arg_eq :
    barrierCase2Y9YV3LogArg = barrierComplex (37642220951 / 100000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y9YV3LogArg, Case2PointData.Y9, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y9YV3_arg_regular :
    (barrierCase2Y9YV3LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y9YV3LogArg).re := by
  rw [barrierCase2Y9YV3_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y9YV3_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2 = barrierComplex (2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y9YV3_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2Y9YV3LogArg).re -
      ((barrierWeightedComplexLogRat (2466317 / 50000000) (0 / 1) (-3) (0) (1416936798123903344401 / 1250000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y9YV3_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (2466317 / 50000000) (0 / 1)
    barrierCase2Y9YV3LogArg (-3) (0) (1416936798123903344401 / 1250000000000000000000) (37642220951 / 100000000000) (0 / 1)
  have hratio : ((0 / 1) / (37642220951 / 100000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y9YV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y9YV3_approx_upper :
    barrierWeightedComplexLogRat (2466317 / 50000000) (0 / 1) (-3) (0) (1416936798123903344401 / 1250000000000000000000) (0 / 1) <
      (-48193998023 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y9YV3_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y9 : ℝ) (barrierV2Tail.getD 3 (0, 0)) <
      (-48193998023 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2Y9YV3LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y9YV3_error).2
  have ha : ((barrierWeightedComplexLogRat (2466317 / 50000000) (0 / 1) (-3) (0) (1416936798123903344401 / 1250000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-48193998023 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y9YV3_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y9YV4LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y9 : ℝ) : ℂ) * (barrierV2Tail.getD 4 (0, 0)).1 + (barrierV2Tail.getD 4 (0, 0)).1 ^ 2

private theorem barrierCase2Y9YV4_arg_eq :
    barrierCase2Y9YV4LogArg = barrierComplex (242225430367 / 625000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y9YV4LogArg, Case2PointData.Y9, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y9YV4_arg_regular :
    (barrierCase2Y9YV4LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y9YV4LogArg).re := by
  rw [barrierCase2Y9YV4_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y9YV4_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2 = barrierComplex (-11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y9YV4_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2Y9YV4LogArg).re -
      ((barrierWeightedComplexLogRat (-11618157 / 100000000) (0 / 1) (-3) (0) (58673159116478365754689 / 48828125000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y9YV4_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-11618157 / 100000000) (0 / 1)
    barrierCase2Y9YV4LogArg (-3) (0) (58673159116478365754689 / 48828125000000000000000) (242225430367 / 625000000000) (0 / 1)
  have hratio : ((0 / 1) / (242225430367 / 625000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y9YV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y9YV4_approx_upper :
    barrierWeightedComplexLogRat (-11618157 / 100000000) (0 / 1) (-3) (0) (58673159116478365754689 / 48828125000000000000000) (0 / 1) <
      (110126514989 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y9YV4_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y9 : ℝ) (barrierV2Tail.getD 4 (0, 0)) <
      (110126514989 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2Y9YV4LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y9YV4_error).2
  have ha : ((barrierWeightedComplexLogRat (-11618157 / 100000000) (0 / 1) (-3) (0) (58673159116478365754689 / 48828125000000000000000) (0 / 1) : ℚ) : ℝ) <
      (110126514989 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y9YV4_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y9YV5LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y9 : ℝ) : ℂ) * (barrierV2Tail.getD 5 (0, 0)).1 + (barrierV2Tail.getD 5 (0, 0)).1 ^ 2

private theorem barrierCase2Y9YV5_arg_eq :
    barrierCase2Y9YV5LogArg = barrierComplex (979 / 2500) (-313247546469 / 250000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y9YV5LogArg, Case2PointData.Y9, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y9YV5_arg_regular :
    (barrierCase2Y9YV5LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y9YV5LogArg).re := by
  rw [barrierCase2Y9YV5_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y9YV5_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2 = barrierComplex (-13619357 / 100000000) (-600749 / 3125000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y9YV5_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2Y9YV5LogArg).re -
      ((barrierWeightedComplexLogRat (-13619357 / 100000000) (-600749 / 3125000) (0) (-2) (107708435368848314367961 / 62500000000000000000000) (8900000000 / 28477049679) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y9YV5_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-13619357 / 100000000) (-600749 / 3125000)
    barrierCase2Y9YV5LogArg (0) (-2) (107708435368848314367961 / 62500000000000000000000) (313247546469 / 125000000000) (979 / 1250)
  have hratio : ((979 / 1250) / (313247546469 / 125000000000) : ℚ) = (8900000000 / 28477049679) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y9YV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y9YV5_approx_upper :
    barrierWeightedComplexLogRat (-13619357 / 100000000) (-600749 / 3125000) (0) (-2) (107708435368848314367961 / 62500000000000000000000) (8900000000 / 28477049679) <
      (-280799670795 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y9YV5_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y9 : ℝ) (barrierV2Tail.getD 5 (0, 0)) <
      (-280799670795 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2Y9YV5LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y9YV5_error).2
  have ha : ((barrierWeightedComplexLogRat (-13619357 / 100000000) (-600749 / 3125000) (0) (-2) (107708435368848314367961 / 62500000000000000000000) (8900000000 / 28477049679) : ℚ) : ℝ) <
      (-280799670795 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y9YV5_approx_upper using 1
    norm_num
  linarith






def barrierCase2Y9YV7LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y9 : ℝ) : ℂ) * (barrierV2Tail.getD 7 (0, 0)).1 + (barrierV2Tail.getD 7 (0, 0)).1 ^ 2

private theorem barrierCase2Y9YV7_arg_eq :
    barrierCase2Y9YV7LogArg = barrierComplex (19 / 100) (-72287895339 / 50000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y9YV7LogArg, Case2PointData.Y9, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y9YV7_arg_regular :
    (barrierCase2Y9YV7LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y9YV7LogArg).re := by
  rw [barrierCase2Y9YV7_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y9YV7_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2 = barrierComplex (7835271 / 50000000) (-15094393 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y9YV7_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2Y9YV7LogArg).re -
      ((barrierWeightedComplexLogRat (7835271 / 50000000) (-15094393 / 100000000) (1) (-2) (5315789812542217924921 / 5000000000000000000000) (9500000000 / 72287895339) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y9YV7_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (7835271 / 50000000) (-15094393 / 100000000)
    barrierCase2Y9YV7LogArg (1) (-2) (5315789812542217924921 / 5000000000000000000000) (72287895339 / 25000000000) (19 / 50)
  have hratio : ((19 / 50) / (72287895339 / 25000000000) : ℚ) = (9500000000 / 72287895339) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y9YV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y9YV7_approx_upper :
    barrierWeightedComplexLogRat (7835271 / 50000000) (-15094393 / 100000000) (1) (-2) (5315789812542217924921 / 5000000000000000000000) (9500000000 / 72287895339) <
      (-158269739139 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y9YV7_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y9 : ℝ) (barrierV2Tail.getD 7 (0, 0)) <
      (-158269739139 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2Y9YV7LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y9YV7_error).2
  have ha : ((barrierWeightedComplexLogRat (7835271 / 50000000) (-15094393 / 100000000) (1) (-2) (5315789812542217924921 / 5000000000000000000000) (9500000000 / 72287895339) : ℚ) : ℝ) <
      (-158269739139 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y9YV7_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y9YV9LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y9 : ℝ) : ℂ) * (barrierV2Tail.getD 9 (0, 0)).1 + (barrierV2Tail.getD 9 (0, 0)).1 ^ 2

private theorem barrierCase2Y9YV9_arg_eq :
    barrierCase2Y9YV9LogArg = barrierComplex (3519 / 40000) (-1534109778861 / 1000000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y9YV9LogArg, Case2PointData.Y9, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y9YV9_arg_regular :
    (barrierCase2Y9YV9LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y9YV9LogArg).re := by
  rw [barrierCase2Y9YV9_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y9YV9_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2 = barrierComplex (3346771 / 100000000) (5956127 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y9YV9_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2Y9YV9LogArg).re -
      ((barrierWeightedComplexLogRat (3346771 / 100000000) (5956127 / 100000000) (1) (-2) (2361232414221946322457321 / 2000000000000000000000000) (29325000000 / 511369926287) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y9YV9_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (3346771 / 100000000) (5956127 / 100000000)
    barrierCase2Y9YV9LogArg (1) (-2) (2361232414221946322457321 / 2000000000000000000000000) (1534109778861 / 500000000000) (3519 / 20000)
  have hratio : ((3519 / 20000) / (1534109778861 / 500000000000) : ℚ) = (29325000000 / 511369926287) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y9YV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y9YV9_approx_upper :
    barrierWeightedComplexLogRat (3346771 / 100000000) (5956127 / 100000000) (1) (-2) (2361232414221946322457321 / 2000000000000000000000000) (29325000000 / 511369926287) <
      (104524217938 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y9YV9_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y9 : ℝ) (barrierV2Tail.getD 9 (0, 0)) <
      (104524217938 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2Y9YV9LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y9YV9_error).2
  have ha : ((barrierWeightedComplexLogRat (3346771 / 100000000) (5956127 / 100000000) (1) (-2) (2361232414221946322457321 / 2000000000000000000000000) (29325000000 / 511369926287) : ℚ) : ℝ) <
      (104524217938 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y9YV9_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y9YV11LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y9 : ℝ) : ℂ) * (barrierV2Tail.getD 11 (0, 0)).1 + (barrierV2Tail.getD 11 (0, 0)).1 ^ 2

private theorem barrierCase2Y9YV11_arg_eq :
    barrierCase2Y9YV11LogArg = barrierComplex (496 / 15625) (-987934569633 / 625000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y9YV11LogArg, Case2PointData.Y9, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y9YV11_arg_regular :
    (barrierCase2Y9YV11LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y9YV11LogArg).re := by
  rw [barrierCase2Y9YV11_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y9YV11_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2 = barrierComplex (-2055213 / 200000000) (-21715849 / 200000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y9YV11_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2Y9YV11LogArg).re -
      ((barrierWeightedComplexLogRat (-2055213 / 200000000) (-21715849 / 200000000) (1) (-2) (976408339475940925754689 / 781250000000000000000000) (19840000000 / 987934569633) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y9YV11_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2055213 / 200000000) (-21715849 / 200000000)
    barrierCase2Y9YV11LogArg (1) (-2) (976408339475940925754689 / 781250000000000000000000) (987934569633 / 312500000000) (992 / 15625)
  have hratio : ((992 / 15625) / (987934569633 / 312500000000) : ℚ) = (19840000000 / 987934569633) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y9YV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y9YV11_approx_upper :
    barrierWeightedComplexLogRat (-2055213 / 200000000) (-21715849 / 200000000) (1) (-2) (976408339475940925754689 / 781250000000000000000000) (19840000000 / 987934569633) <
      (-173082771531 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y9YV11_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y9 : ℝ) (barrierV2Tail.getD 11 (0, 0)) <
      (-173082771531 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2Y9YV11LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y9YV11_error).2
  have ha : ((barrierWeightedComplexLogRat (-2055213 / 200000000) (-21715849 / 200000000) (1) (-2) (976408339475940925754689 / 781250000000000000000000) (19840000000 / 987934569633) : ℚ) : ℝ) <
      (-173082771531 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y9YV11_approx_upper using 1
    norm_num
  linarith





open Case2PointData

private theorem barrierCase2Y9_YV_tail_upper :
    (barrierV2Tail.map (barrierCase2YVLogTerm (Y9 : ℝ))).sum <
      (-1145816337530 / 1000000000000 : ℝ) := by
  have hp : ∀ i ∈ [5, 7, 9, 11],
      barrierCase2YVLogTerm (Y9 : ℝ) (barrierV2Tail.getD (i + 1) (0, 0)) =
        barrierCase2YVLogTerm (Y9 : ℝ) (barrierV2Tail.getD i (0, 0)) := by
    intro i hi
    rw [barrierV2Tail_getD_pair i hi]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y9YV5_arg_regular
    · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y9YV7_arg_regular
    · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y9YV9_arg_regular
    · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y9YV11_arg_regular
  rw [barrierV2Tail_paired_sum _ hp]
  linarith only [barrierCase2Y9YV0_log_upper,
    barrierCase2Y9YV1_log_upper,
    barrierCase2Y9YV2_log_upper,
    barrierCase2Y9YV3_log_upper,
    barrierCase2Y9YV4_log_upper,
    barrierCase2Y9YV5_log_upper,
    barrierCase2Y9YV7_log_upper,
    barrierCase2Y9YV9_log_upper,
    barrierCase2Y9YV11_log_upper]

private theorem barrierCase2Y9_approx_upper :
    barrierCase2YApproxRat Y9 (-1) (-3) (8031988371 / 5000000000) (1968011629 / 1250000000) + (-1145816337530 / 1000000000000) <
      (-160890 / 100000 - 1 / 1000000000000000 : ℚ) := by
  unfold barrierCase2YApproxRat barrierCase2YRat
  rw [barrierCase2TV_eq_explicit]
  simp only [barrierScaledLogRat, barrierLogHRat_two_eq]
  decide +kernel

theorem barrierCase2Y9_lt : barrierCase2Y (Y9 : ℝ) < (-160890 / 100000 : ℝ) := by
  have hx : |(Y9 : ℝ)| ≤ 1 := by norm_num [Y9]
  have he := (abs_lt.mp (barrierCase2Y_realLog_approx_error Y9 hx
    (-1) (-3) (8031988371 / 5000000000) (1968011629 / 1250000000)
    Y9_normalizations.1 Y9_normalizations.2)).2
  have ha : ((barrierCase2YApproxRat Y9 (-1) (-3) (8031988371 / 5000000000) (1968011629 / 1250000000) : ℚ) : ℝ) +
      (-1145816337530 / 1000000000000) < (-160890 / 100000 - 1 / 1000000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y9_approx_upper using 1 <;> norm_num
  linarith only [he, ha, barrierCase2Y9_YV_tail_upper]

end InternalCatalan




namespace InternalCatalan

theorem barrierCase2X_bracket_left_lt (m : ℤ)
    (hm : m ∈ barrierCase2XBrackets) :
    barrierCase2X (barrierBracketLeft m : ℝ) < (-98399 / 100000 : ℝ) := by
  simp only [barrierCase2XBrackets, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · convert barrierCase2X0_lt using 1
    norm_num [barrierBracketLeft, Case2PointData.X0]
  · convert barrierCase2X1_lt using 1
    norm_num [barrierBracketLeft, Case2PointData.X1]
  · convert barrierCase2X2_lt using 1
    norm_num [barrierBracketLeft, Case2PointData.X2]
  · convert barrierCase2X3_lt using 1
    norm_num [barrierBracketLeft, Case2PointData.X3]
  · convert barrierCase2X4_lt using 1
    norm_num [barrierBracketLeft, Case2PointData.X4]
  · convert barrierCase2X5_lt using 1
    norm_num [barrierBracketLeft, Case2PointData.X5]
  · convert barrierCase2X6_lt using 1
    norm_num [barrierBracketLeft, Case2PointData.X6]
  · convert barrierCase2X7_lt using 1
    norm_num [barrierBracketLeft, Case2PointData.X7]
  · convert barrierCase2X8_lt using 1
    norm_num [barrierBracketLeft, Case2PointData.X8]
  · convert barrierCase2X9_lt using 1
    norm_num [barrierBracketLeft, Case2PointData.X9]
  · convert barrierCase2X10_lt using 1
    norm_num [barrierBracketLeft, Case2PointData.X10]
  · convert barrierCase2X11_lt using 1
    norm_num [barrierBracketLeft, Case2PointData.X11]
  · convert barrierCase2X12_lt using 1
    norm_num [barrierBracketLeft, Case2PointData.X12]
  · convert barrierCase2X13_lt using 1
    norm_num [barrierBracketLeft, Case2PointData.X13]
  · convert barrierCase2X14_lt using 1
    norm_num [barrierBracketLeft, Case2PointData.X14]
  · convert barrierCase2X15_lt using 1
    norm_num [barrierBracketLeft, Case2PointData.X15]
  · convert barrierCase2X16_lt using 1
    norm_num [barrierBracketLeft, Case2PointData.X16]
  · convert barrierCase2X17_lt using 1
    norm_num [barrierBracketLeft, Case2PointData.X17]

theorem barrierCase2Y_bracket_left_lt (m : ℤ)
    (hm : m ∈ barrierCase2YBrackets) :
    barrierCase2Y (barrierBracketLeft m : ℝ) < (-160890 / 100000 : ℝ) := by
  simp only [barrierCase2YBrackets, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · convert barrierCase2Y0_lt using 1
    norm_num [barrierBracketLeft, Case2PointData.Y0]
  · convert barrierCase2Y1_lt using 1
    norm_num [barrierBracketLeft, Case2PointData.Y1]
  · convert barrierCase2Y2_lt using 1
    norm_num [barrierBracketLeft, Case2PointData.Y2]
  · convert barrierCase2Y3_lt using 1
    norm_num [barrierBracketLeft, Case2PointData.Y3]
  · convert barrierCase2Y4_lt using 1
    norm_num [barrierBracketLeft, Case2PointData.Y4]
  · convert barrierCase2Y5_lt using 1
    norm_num [barrierBracketLeft, Case2PointData.Y5]
  · convert barrierCase2Y6_lt using 1
    norm_num [barrierBracketLeft, Case2PointData.Y6]
  · convert barrierCase2Y7_lt using 1
    norm_num [barrierBracketLeft, Case2PointData.Y7]
  · convert barrierCase2Y8_lt using 1
    norm_num [barrierBracketLeft, Case2PointData.Y8]
  · convert barrierCase2Y9_lt using 1
    norm_num [barrierBracketLeft, Case2PointData.Y9]
  · convert barrierCase2Y10_lt using 1
    norm_num [barrierBracketLeft, Case2PointData.Y10]
  · convert barrierCase2Y11_lt using 1
    norm_num [barrierBracketLeft, Case2PointData.Y11]
  · convert barrierCase2Y12_lt using 1
    norm_num [barrierBracketLeft, Case2PointData.Y12]
  · convert barrierCase2Y13_lt using 1
    norm_num [barrierBracketLeft, Case2PointData.Y13]
  · convert barrierCase2Y14_lt using 1
    norm_num [barrierBracketLeft, Case2PointData.Y14]

theorem barrierCase2X_neg_one_lt : barrierCase2X (-1) < (-98399 / 100000 : ℝ) := by
  simpa [Case2PointData.X18] using barrierCase2X18_lt






theorem barrierCase2X_global_upper {x : ℝ}
    (hx : -1 ≤ x ∧ x < 1 ∧ x ≠ 0) :
    barrierCase2X x ≤ (-98399 / 100000 : ℝ) + 24 / 1000000 := by
  have hbound := barrierCase2X_le_of_bracket_bounds
    ((-98399 / 100000 : ℝ) + 24 / 1000000)
    (by linarith [barrierCase2X_neg_one_lt])
    (by
      intro m hm y hy
      have hp := barrierCase2X_bracket_left_lt m hm
      have hh := barrierCase2X_bracket_height m hm hy
      linarith)
  apply hbound x
  by_cases hneg : x < 0
  · exact Or.inl ⟨hx.1, hneg⟩
  · exact Or.inr ⟨by rcases hx with ⟨_, _, hx0⟩; rcases lt_or_gt_of_ne hx0 with h | h <;> linarith,
      hx.2.1⟩

theorem barrierCase2Y_global_upper {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    barrierCase2Y x ≤ (-160890 / 100000 : ℝ) + 24 / 1000000 := by
  apply barrierCase2Y_le_of_bracket_bounds
    ((-160890 / 100000 : ℝ) + 24 / 1000000) _ x hx
  intro m hm y hy
  have hp := barrierCase2Y_bracket_left_lt m hm
  have hh := barrierCase2Y_bracket_height m hm hy
  linarith

end InternalCatalan

end

end OAI
