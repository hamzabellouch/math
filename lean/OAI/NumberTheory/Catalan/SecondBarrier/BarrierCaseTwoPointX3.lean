import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoLogsX3Group0
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX0

namespace OAI

noncomputable section

namespace InternalCatalan

def barrierCase2X3XV0LogArg : ℂ :=
  1 - ((Case2PointData.X3 : ℝ) : ℂ) * (barrierV2Tail.getD 0 (0, 0)).1

private theorem barrierCase2X3XV0_arg_eq :
    barrierCase2X3XV0LogArg = barrierComplex (2998302603 / 6250000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X3XV0LogArg, Case2PointData.X3, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X3XV0_arg_regular :
    (barrierCase2X3XV0LogArg).im ≠ 0 ∨ 0 < (barrierCase2X3XV0LogArg).re := by
  rw [barrierCase2X3XV0_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X3XV0_weight_eq :
    (barrierV2Tail.getD 0 (0, 0)).2 = barrierComplex (15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X3XV0_error :
    |((barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X3XV0LogArg).re -
      ((barrierWeightedComplexLogRat (15199211 / 100000000) (0 / 1) (-3) (0) (8989818499156575609 / 4882812500000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X3XV0_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (15199211 / 100000000) (0 / 1)
    barrierCase2X3XV0LogArg (-3) (0) (8989818499156575609 / 4882812500000000000) (2998302603 / 6250000000) (0 / 1)
  have hratio : ((0 / 1) / (2998302603 / 6250000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X3XV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X3XV0_approx_upper :
    barrierWeightedComplexLogRat (15199211 / 100000000) (0 / 1) (-3) (0) (8989818499156575609 / 4882812500000000000) (0 / 1) <
      (-111643544915 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X3XV0_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X3 : ℝ) (barrierV2Tail.getD 0 (0, 0)) <
      (-111643544915 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X3XV0LogArg).re < _
  have he := (abs_lt.mp barrierCase2X3XV0_error).2
  have ha : ((barrierWeightedComplexLogRat (15199211 / 100000000) (0 / 1) (-3) (0) (8989818499156575609 / 4882812500000000000) (0 / 1) : ℚ) : ℝ) <
      (-111643544915 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X3XV0_approx_upper using 1
    norm_num
  linarith

def barrierCase2X3XV1LogArg : ℂ :=
  1 - ((Case2PointData.X3 : ℝ) : ℂ) * (barrierV2Tail.getD 1 (0, 0)).1

private theorem barrierCase2X3XV1_arg_eq :
    barrierCase2X3XV1LogArg = barrierComplex (5869907809 / 15625000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X3XV1LogArg, Case2PointData.X3, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X3XV1_arg_regular :
    (barrierCase2X3XV1LogArg).im ≠ 0 ∨ 0 < (barrierCase2X3XV1LogArg).re := by
  rw [barrierCase2X3XV1_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X3XV1_weight_eq :
    (barrierV2Tail.getD 1 (0, 0)).2 = barrierComplex (2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X3XV1_error :
    |((barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X3XV1LogArg).re -
      ((barrierWeightedComplexLogRat (2225831 / 50000000) (0 / 1) (-3) (0) (34455817686159180481 / 30517578125000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X3XV1_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (2225831 / 50000000) (0 / 1)
    barrierCase2X3XV1LogArg (-3) (0) (34455817686159180481 / 30517578125000000000) (5869907809 / 15625000000) (0 / 1)
  have hratio : ((0 / 1) / (5869907809 / 15625000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X3XV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X3XV1_approx_upper :
    barrierWeightedComplexLogRat (2225831 / 50000000) (0 / 1) (-3) (0) (34455817686159180481 / 30517578125000000000) (0 / 1) <
      (-43583251929 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X3XV1_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X3 : ℝ) (barrierV2Tail.getD 1 (0, 0)) <
      (-43583251929 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X3XV1LogArg).re < _
  have he := (abs_lt.mp barrierCase2X3XV1_error).2
  have ha : ((barrierWeightedComplexLogRat (2225831 / 50000000) (0 / 1) (-3) (0) (34455817686159180481 / 30517578125000000000) (0 / 1) : ℚ) : ℝ) <
      (-43583251929 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X3XV1_approx_upper using 1
    norm_num
  linarith

def barrierCase2X3XV2LogArg : ℂ :=
  1 - ((Case2PointData.X3 : ℝ) : ℂ) * (barrierV2Tail.getD 2 (0, 0)).1

private theorem barrierCase2X3XV2_arg_eq :
    barrierCase2X3XV2LogArg = barrierComplex (98268671367 / 62500000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X3XV2LogArg, Case2PointData.X3, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X3XV2_arg_regular :
    (barrierCase2X3XV2LogArg).im ≠ 0 ∨ 0 < (barrierCase2X3XV2LogArg).re := by
  rw [barrierCase2X3XV2_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X3XV2_weight_eq :
    (barrierV2Tail.getD 2 (0, 0)).2 = barrierComplex (1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X3XV2_error :
    |((barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X3XV2LogArg).re -
      ((barrierWeightedComplexLogRat (1272699 / 50000000) (0 / 1) (1) (0) (9656731772235445648689 / 7812500000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X3XV2_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (1272699 / 50000000) (0 / 1)
    barrierCase2X3XV2LogArg (1) (0) (9656731772235445648689 / 7812500000000000000000) (98268671367 / 62500000000) (0 / 1)
  have hratio : ((0 / 1) / (98268671367 / 62500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X3XV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X3XV2_approx_upper :
    barrierWeightedComplexLogRat (1272699 / 50000000) (0 / 1) (1) (0) (9656731772235445648689 / 7812500000000000000000) (0 / 1) <
      (11518911410 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X3XV2_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X3 : ℝ) (barrierV2Tail.getD 2 (0, 0)) <
      (11518911410 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X3XV2LogArg).re < _
  have he := (abs_lt.mp barrierCase2X3XV2_error).2
  have ha : ((barrierWeightedComplexLogRat (1272699 / 50000000) (0 / 1) (1) (0) (9656731772235445648689 / 7812500000000000000000) (0 / 1) : ℚ) : ℝ) <
      (11518911410 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X3XV2_approx_upper using 1
    norm_num
  linarith

def barrierCase2X3XV3LogArg : ℂ :=
  1 - ((Case2PointData.X3 : ℝ) : ℂ) * (barrierV2Tail.getD 3 (0, 0)).1

private theorem barrierCase2X3XV3_arg_eq :
    barrierCase2X3XV3LogArg = barrierComplex (161782250543 / 100000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X3XV3LogArg, Case2PointData.X3, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X3XV3_arg_regular :
    (barrierCase2X3XV3LogArg).im ≠ 0 ∨ 0 < (barrierCase2X3XV3LogArg).re := by
  rw [barrierCase2X3XV3_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X3XV3_weight_eq :
    (barrierV2Tail.getD 3 (0, 0)).2 = barrierComplex (-2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X3XV3_error :
    |((barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2X3XV3LogArg).re -
      ((barrierWeightedComplexLogRat (-2466317 / 50000000) (0 / 1) (1) (0) (26173496590758023794849 / 20000000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X3XV3_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2466317 / 50000000) (0 / 1)
    barrierCase2X3XV3LogArg (1) (0) (26173496590758023794849 / 20000000000000000000000) (161782250543 / 100000000000) (0 / 1)
  have hratio : ((0 / 1) / (161782250543 / 100000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X3XV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X3XV3_approx_upper :
    barrierWeightedComplexLogRat (-2466317 / 50000000) (0 / 1) (1) (0) (26173496590758023794849 / 20000000000000000000000) (0 / 1) <
      (-23729970528 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X3XV3_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X3 : ℝ) (barrierV2Tail.getD 3 (0, 0)) <
      (-23729970528 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2X3XV3LogArg).re < _
  have he := (abs_lt.mp barrierCase2X3XV3_error).2
  have ha : ((barrierWeightedComplexLogRat (-2466317 / 50000000) (0 / 1) (1) (0) (26173496590758023794849 / 20000000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-23729970528 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X3XV3_approx_upper using 1
    norm_num
  linarith

def barrierCase2X3XV4LogArg : ℂ :=
  1 - ((Case2PointData.X3 : ℝ) : ℂ) * (barrierV2Tail.getD 4 (0, 0)).1

private theorem barrierCase2X3XV4_arg_eq :
    barrierCase2X3XV4LogArg = barrierComplex (1024958779831 / 625000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X3XV4LogArg, Case2PointData.X3, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X3XV4_arg_regular :
    (barrierCase2X3XV4LogArg).im ≠ 0 ∨ 0 < (barrierCase2X3XV4LogArg).re := by
  rw [barrierCase2X3XV4_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X3XV4_weight_eq :
    (barrierV2Tail.getD 4 (0, 0)).2 = barrierComplex (11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X3XV4_error :
    |((barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X3XV4LogArg).re -
      ((barrierWeightedComplexLogRat (11618157 / 100000000) (0 / 1) (1) (0) (1050540500352652332388561 / 781250000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X3XV4_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (11618157 / 100000000) (0 / 1)
    barrierCase2X3XV4LogArg (1) (0) (1050540500352652332388561 / 781250000000000000000000) (1024958779831 / 625000000000) (0 / 1)
  have hratio : ((0 / 1) / (1024958779831 / 625000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X3XV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X3XV4_approx_upper :
    barrierWeightedComplexLogRat (11618157 / 100000000) (0 / 1) (1) (0) (1050540500352652332388561 / 781250000000000000000000) (0 / 1) <
      (57469913739 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X3XV4_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X3 : ℝ) (barrierV2Tail.getD 4 (0, 0)) <
      (57469913739 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X3XV4LogArg).re < _
  have he := (abs_lt.mp barrierCase2X3XV4_error).2
  have ha : ((barrierWeightedComplexLogRat (11618157 / 100000000) (0 / 1) (1) (0) (1050540500352652332388561 / 781250000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (57469913739 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X3XV4_approx_upper using 1
    norm_num
  linarith

def barrierCase2X3XV5LogArg : ℂ :=
  1 - ((Case2PointData.X3 : ℝ) : ℂ) * (barrierV2Tail.getD 5 (0, 0)).1

private theorem barrierCase2X3XV5_arg_eq :
    barrierCase2X3XV5LogArg = barrierComplex (1 / 1) (126816198483 / 250000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X3XV5LogArg, Case2PointData.X3, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X3XV5_arg_regular :
    (barrierCase2X3XV5LogArg).im ≠ 0 ∨ 0 < (barrierCase2X3XV5LogArg).re := by
  rw [barrierCase2X3XV5_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X3XV5_weight_eq :
    (barrierV2Tail.getD 5 (0, 0)).2 = barrierComplex (13619357 / 100000000) (600749 / 3125000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X3XV5_error :
    |((barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2X3XV5LogArg).re -
      ((barrierWeightedComplexLogRat (13619357 / 100000000) (600749 / 3125000) (0) (1) (78582348197679651501289 / 62500000000000000000000) (-123183801517 / 376816198483) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X3XV5_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (13619357 / 100000000) (600749 / 3125000)
    barrierCase2X3XV5LogArg (0) (1) (78582348197679651501289 / 62500000000000000000000) (376816198483 / 250000000000) (-123183801517 / 250000000000)
  have hratio : ((-123183801517 / 250000000000) / (376816198483 / 250000000000) : ℚ) = (-123183801517 / 376816198483) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X3XV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X3XV5_approx_upper :
    barrierWeightedComplexLogRat (13619357 / 100000000) (600749 / 3125000) (0) (1) (78582348197679651501289 / 62500000000000000000000) (-123183801517 / 376816198483) <
      (-74652644980 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X3XV5_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X3 : ℝ) (barrierV2Tail.getD 5 (0, 0)) <
      (-74652644980 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2X3XV5LogArg).re < _
  have he := (abs_lt.mp barrierCase2X3XV5_error).2
  have ha : ((barrierWeightedComplexLogRat (13619357 / 100000000) (600749 / 3125000) (0) (1) (78582348197679651501289 / 62500000000000000000000) (-123183801517 / 376816198483) : ℚ) : ℝ) <
      (-74652644980 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X3XV5_approx_upper using 1
    norm_num
  linarith

def barrierCase2X3XV7LogArg : ℂ :=
  1 - ((Case2PointData.X3 : ℝ) : ℂ) * (barrierV2Tail.getD 7 (0, 0)).1

private theorem barrierCase2X3XV7_arg_eq :
    barrierCase2X3XV7LogArg = barrierComplex (1 / 1) (29265276573 / 50000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X3XV7LogArg, Case2PointData.X3, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X3XV7_arg_regular :
    (barrierCase2X3XV7LogArg).im ≠ 0 ∨ 0 < (barrierCase2X3XV7LogArg).re := by
  rw [barrierCase2X3XV7_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X3XV7_weight_eq :
    (barrierV2Tail.getD 7 (0, 0)).2 = barrierComplex (-7835271 / 50000000) (15094393 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X3XV7_error :
    |((barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2X3XV7LogArg).re -
      ((barrierWeightedComplexLogRat (-7835271 / 50000000) (15094393 / 100000000) (0) (1) (3356456412894182624329 / 2500000000000000000000) (-20734723427 / 79265276573) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X3XV7_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-7835271 / 50000000) (15094393 / 100000000)
    barrierCase2X3XV7LogArg (0) (1) (3356456412894182624329 / 2500000000000000000000) (79265276573 / 50000000000) (-20734723427 / 50000000000)
  have hratio : ((-20734723427 / 50000000000) / (79265276573 / 50000000000) : ℚ) = (-20734723427 / 79265276573) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X3XV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X3XV7_approx_upper :
    barrierWeightedComplexLogRat (-7835271 / 50000000) (15094393 / 100000000) (0) (1) (3356456412894182624329 / 2500000000000000000000) (-20734723427 / 79265276573) <
      (-103013873848 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X3XV7_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X3 : ℝ) (barrierV2Tail.getD 7 (0, 0)) <
      (-103013873848 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2X3XV7LogArg).re < _
  have he := (abs_lt.mp barrierCase2X3XV7_error).2
  have ha : ((barrierWeightedComplexLogRat (-7835271 / 50000000) (15094393 / 100000000) (0) (1) (3356456412894182624329 / 2500000000000000000000) (-20734723427 / 79265276573) : ℚ) : ℝ) <
      (-103013873848 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X3XV7_approx_upper using 1
    norm_num
  linarith

def barrierCase2X3XV9LogArg : ℂ :=
  1 - ((Case2PointData.X3 : ℝ) : ℂ) * (barrierV2Tail.getD 9 (0, 0)).1

private theorem barrierCase2X3XV9_arg_eq :
    barrierCase2X3XV9LogArg = barrierComplex (1 / 1) (621074202827 / 1000000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X3XV9LogArg, Case2PointData.X3, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X3XV9_arg_regular :
    (barrierCase2X3XV9LogArg).im ≠ 0 ∨ 0 < (barrierCase2X3XV9LogArg).re := by
  rw [barrierCase2X3XV9_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X3XV9_weight_eq :
    (barrierV2Tail.getD 9 (0, 0)).2 = barrierComplex (-3346771 / 100000000) (-5956127 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X3XV9_error :
    |((barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2X3XV9LogArg).re -
      ((barrierWeightedComplexLogRat (-3346771 / 100000000) (-5956127 / 100000000) (0) (1) (1385733165417193534791929 / 1000000000000000000000000) (-378925797173 / 1621074202827) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X3XV9_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-3346771 / 100000000) (-5956127 / 100000000)
    barrierCase2X3XV9LogArg (0) (1) (1385733165417193534791929 / 1000000000000000000000000) (1621074202827 / 1000000000000) (-378925797173 / 1000000000000)
  have hratio : ((-378925797173 / 1000000000000) / (1621074202827 / 1000000000000) : ℚ) = (-378925797173 / 1621074202827) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X3XV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X3XV9_approx_upper :
    barrierWeightedComplexLogRat (-3346771 / 100000000) (-5956127 / 100000000) (0) (1) (1385733165417193534791929 / 1000000000000000000000000) (-378925797173 / 1621074202827) <
      (27643368918 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X3XV9_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X3 : ℝ) (barrierV2Tail.getD 9 (0, 0)) <
      (27643368918 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2X3XV9LogArg).re < _
  have he := (abs_lt.mp barrierCase2X3XV9_error).2
  have ha : ((barrierWeightedComplexLogRat (-3346771 / 100000000) (-5956127 / 100000000) (0) (1) (1385733165417193534791929 / 1000000000000000000000000) (-378925797173 / 1621074202827) : ℚ) : ℝ) <
      (27643368918 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X3XV9_approx_upper using 1
    norm_num
  linarith

def barrierCase2X3XV11LogArg : ℂ :=
  1 - ((Case2PointData.X3 : ℝ) : ℂ) * (barrierV2Tail.getD 11 (0, 0)).1

private theorem barrierCase2X3XV11_arg_eq :
    barrierCase2X3XV11LogArg = barrierComplex (1 / 1) (399958779831 / 625000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X3XV11LogArg, Case2PointData.X3, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X3XV11_arg_regular :
    (barrierCase2X3XV11LogArg).im ≠ 0 ∨ 0 < (barrierCase2X3XV11LogArg).re := by
  rw [barrierCase2X3XV11_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X3XV11_weight_eq :
    (barrierV2Tail.getD 11 (0, 0)).2 = barrierComplex (2055213 / 200000000) (21715849 / 200000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X3XV11_error :
    |((barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2X3XV11LogArg).re -
      ((barrierWeightedComplexLogRat (2055213 / 200000000) (21715849 / 200000000) (0) (1) (550592025563902332388561 / 390625000000000000000000) (-225041220169 / 1024958779831) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X3XV11_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (2055213 / 200000000) (21715849 / 200000000)
    barrierCase2X3XV11LogArg (0) (1) (550592025563902332388561 / 390625000000000000000000) (1024958779831 / 625000000000) (-225041220169 / 625000000000)
  have hratio : ((-225041220169 / 625000000000) / (1024958779831 / 625000000000) : ℚ) = (-225041220169 / 1024958779831) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X3XV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X3XV11_approx_upper :
    barrierWeightedComplexLogRat (2055213 / 200000000) (21715849 / 200000000) (0) (1) (550592025563902332388561 / 390625000000000000000000) (-225041220169 / 1024958779831) <
      (-60046906546 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X3XV11_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X3 : ℝ) (barrierV2Tail.getD 11 (0, 0)) <
      (-60046906546 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2X3XV11LogArg).re < _
  have he := (abs_lt.mp barrierCase2X3XV11_error).2
  have ha : ((barrierWeightedComplexLogRat (2055213 / 200000000) (21715849 / 200000000) (0) (1) (550592025563902332388561 / 390625000000000000000000) (-225041220169 / 1024958779831) : ℚ) : ℝ) <
      (-60046906546 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X3XV11_approx_upper using 1
    norm_num
  linarith

open Case2PointData

private theorem barrierCase2X3_XP_tail_upper :
    (barrierP2Tail.map (barrierCase2XPLogTerm (X3 : ℝ))).sum <
      (-876568872745 / 1000000000000 : ℝ) := by
  have hp : ∀ i ∈ [2, 4, 6, 8],
      barrierCase2XPLogTerm (X3 : ℝ) (barrierP2Tail.getD (i + 1) (0, 0)) =
        barrierCase2XPLogTerm (X3 : ℝ) (barrierP2Tail.getD i (0, 0)) := by
    intro i hi
    rw [barrierP2Tail_getD_pair i hi]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X3XP2_arg_regular
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X3XP4_arg_regular
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X3XP6_arg_regular
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X3XP8_arg_regular
  rw [barrierP2Tail_paired_sum _ hp]
  linarith only [barrierCase2X3XP0_log_upper,
    barrierCase2X3XP1_log_upper,
    barrierCase2X3XP2_log_upper,
    barrierCase2X3XP4_log_upper,
    barrierCase2X3XP6_log_upper,
    barrierCase2X3XP8_log_upper]

private theorem barrierCase2X3_XV_tail_upper :
    (barrierV2Tail.map (barrierCase2XVLogTerm (X3 : ℝ))).sum <
      (-530108055135 / 1000000000000 : ℝ) := by
  have hp : ∀ i ∈ [5, 7, 9, 11],
      barrierCase2XVLogTerm (X3 : ℝ) (barrierV2Tail.getD (i + 1) (0, 0)) =
        barrierCase2XVLogTerm (X3 : ℝ) (barrierV2Tail.getD i (0, 0)) := by
    intro i hi
    rw [barrierV2Tail_getD_pair i hi]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X3XV5_arg_regular
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X3XV7_arg_regular
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X3XV9_arg_regular
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X3XV11_arg_regular
  rw [barrierV2Tail_paired_sum _ hp]
  linarith only [barrierCase2X3XV0_log_upper,
    barrierCase2X3XV1_log_upper,
    barrierCase2X3XV2_log_upper,
    barrierCase2X3XV3_log_upper,
    barrierCase2X3XV4_log_upper,
    barrierCase2X3XV5_log_upper,
    barrierCase2X3XV7_log_upper,
    barrierCase2X3XV9_log_upper,
    barrierCase2X3XV11_log_upper]

private theorem barrierCase2X3_approx_upper :
    barrierCase2XApproxRat X3 (-1) (0) (0) (3251697397 / 2500000000) (8251697397 / 5000000000) (35573535961656575609 / 25000000000000000000) + (-876568872745 / 1000000000000) + (-530108055135 / 1000000000000) <
      (-98399 / 100000 - 2 / 1000000000000000 : ℚ) := by
  unfold barrierCase2XApproxRat barrierCase2XRat
  rw [barrierCase2TP_eq_explicit, barrierCase2SV_eq_explicit]
  simp only [barrierScaledLogRat, barrierLogHRat_two_eq]
  decide +kernel

theorem barrierCase2X3_lt : barrierCase2X (X3 : ℝ) < (-98399 / 100000 : ℝ) := by
  have hx : |(X3 : ℝ)| ≤ 1 := by norm_num [X3]
  have he := (abs_lt.mp (barrierCase2X_realLog_approx_error X3 hx
    (-1) (0) (0) (3251697397 / 2500000000) (8251697397 / 5000000000) (35573535961656575609 / 25000000000000000000)
    X3_normalizations.1 X3_normalizations.2.1 X3_normalizations.2.2)).2
  have ha : ((barrierCase2XApproxRat X3 (-1) (0) (0) (3251697397 / 2500000000) (8251697397 / 5000000000) (35573535961656575609 / 25000000000000000000) : ℚ) : ℝ) +
      (-876568872745 / 1000000000000) + (-530108055135 / 1000000000000) < (-98399 / 100000 - 2 / 1000000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X3_approx_upper using 1 <;> norm_num
  linarith only [he, ha, barrierCase2X3_XP_tail_upper, barrierCase2X3_XV_tail_upper]

end InternalCatalan

end

end OAI
