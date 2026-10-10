import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoLogsX10Group0
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX0

namespace OAI

noncomputable section

namespace InternalCatalan

def barrierCase2X10XV0LogArg : ℂ :=
  1 - ((Case2PointData.X10 : ℝ) : ℂ) * (barrierV2Tail.getD 0 (0, 0)).1

private theorem barrierCase2X10XV0_arg_eq :
    barrierCase2X10XV0LogArg = barrierComplex (14572448179 / 12500000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X10XV0LogArg, Case2PointData.X10, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X10XV0_arg_regular :
    (barrierCase2X10XV0LogArg).im ≠ 0 ∨ 0 < (barrierCase2X10XV0LogArg).re := by
  rw [barrierCase2X10XV0_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X10XV0_weight_eq :
    (barrierV2Tail.getD 0 (0, 0)).2 = barrierComplex (15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X10XV0_error :
    |((barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X10XV0LogArg).re -
      ((barrierWeightedComplexLogRat (15199211 / 100000000) (0 / 1) (0) (0) (212356245929640416041 / 156250000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X10XV0_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (15199211 / 100000000) (0 / 1)
    barrierCase2X10XV0LogArg (0) (0) (212356245929640416041 / 156250000000000000000) (14572448179 / 12500000000) (0 / 1)
  have hratio : ((0 / 1) / (14572448179 / 12500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X10XV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X10XV0_approx_upper :
    barrierWeightedComplexLogRat (15199211 / 100000000) (0 / 1) (0) (0) (212356245929640416041 / 156250000000000000000) (0 / 1) <
      (23316196206 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X10XV0_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X10 : ℝ) (barrierV2Tail.getD 0 (0, 0)) <
      (23316196206 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X10XV0LogArg).re < _
  have he := (abs_lt.mp barrierCase2X10XV0_error).2
  have ha : ((barrierWeightedComplexLogRat (15199211 / 100000000) (0 / 1) (0) (0) (212356245929640416041 / 156250000000000000000) (0 / 1) : ℚ) : ℝ) <
      (23316196206 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X10XV0_approx_upper using 1
    norm_num
  linarith

def barrierCase2X10XV1LogArg : ℂ :=
  1 - ((Case2PointData.X10 : ℝ) : ℂ) * (barrierV2Tail.getD 1 (0, 0)).1

private theorem barrierCase2X10XV1_arg_eq :
    barrierCase2X10XV1LogArg = barrierComplex (37467344537 / 31250000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X10XV1LogArg, Case2PointData.X10, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X10XV1_arg_regular :
    (barrierCase2X10XV1LogArg).im ≠ 0 ∨ 0 < (barrierCase2X10XV1LogArg).re := by
  rw [barrierCase2X10XV1_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X10XV1_weight_eq :
    (barrierV2Tail.getD 1 (0, 0)).2 = barrierComplex (2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X10XV1_error :
    |((barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X10XV1LogArg).re -
      ((barrierWeightedComplexLogRat (2225831 / 50000000) (0 / 1) (0) (0) (1403801906654263744369 / 976562500000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X10XV1_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (2225831 / 50000000) (0 / 1)
    barrierCase2X10XV1LogArg (0) (0) (1403801906654263744369 / 976562500000000000000) (37467344537 / 31250000000) (0 / 1)
  have hratio : ((0 / 1) / (37467344537 / 31250000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X10XV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X10XV1_approx_upper :
    barrierWeightedComplexLogRat (2225831 / 50000000) (0 / 1) (0) (0) (1403801906654263744369 / 976562500000000000000) (0 / 1) <
      (8077556952 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X10XV1_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X10 : ℝ) (barrierV2Tail.getD 1 (0, 0)) <
      (8077556952 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X10XV1LogArg).re < _
  have he := (abs_lt.mp barrierCase2X10XV1_error).2
  have ha : ((barrierWeightedComplexLogRat (2225831 / 50000000) (0 / 1) (0) (0) (1403801906654263744369 / 976562500000000000000) (0 / 1) : ℚ) : ℝ) <
      (8077556952 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X10XV1_approx_upper using 1
    norm_num
  linarith

def barrierCase2X10XV2LogArg : ℂ :=
  1 - ((Case2PointData.X10 : ℝ) : ℂ) * (barrierV2Tail.getD 2 (0, 0)).1

private theorem barrierCase2X10XV2_arg_eq :
    barrierCase2X10XV2LogArg = barrierComplex (102203070031 / 125000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X10XV2LogArg, Case2PointData.X10, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X10XV2_arg_regular :
    (barrierCase2X10XV2LogArg).im ≠ 0 ∨ 0 < (barrierCase2X10XV2LogArg).re := by
  rw [barrierCase2X10XV2_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X10XV2_weight_eq :
    (barrierV2Tail.getD 2 (0, 0)).2 = barrierComplex (1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X10XV2_error :
    |((barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X10XV2LogArg).re -
      ((barrierWeightedComplexLogRat (1272699 / 50000000) (0 / 1) (-1) (0) (10445467523761490340961 / 7812500000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X10XV2_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (1272699 / 50000000) (0 / 1)
    barrierCase2X10XV2LogArg (-1) (0) (10445467523761490340961 / 7812500000000000000000) (102203070031 / 125000000000) (0 / 1)
  have hratio : ((0 / 1) / (102203070031 / 125000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X10XV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X10XV2_approx_upper :
    barrierWeightedComplexLogRat (1272699 / 50000000) (0 / 1) (-1) (0) (10445467523761490340961 / 7812500000000000000000) (0 / 1) <
      (-5125210302 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X10XV2_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X10 : ℝ) (barrierV2Tail.getD 2 (0, 0)) <
      (-5125210302 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X10XV2LogArg).re < _
  have he := (abs_lt.mp barrierCase2X10XV2_error).2
  have ha : ((barrierWeightedComplexLogRat (1272699 / 50000000) (0 / 1) (-1) (0) (10445467523761490340961 / 7812500000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-5125210302 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X10XV2_approx_upper using 1
    norm_num
  linarith

def barrierCase2X10XV3LogArg : ℂ :=
  1 - ((Case2PointData.X10 : ℝ) : ℂ) * (barrierV2Tail.getD 3 (0, 0)).1

private theorem barrierCase2X10XV3_arg_eq :
    barrierCase2X10XV3LogArg = barrierComplex (160623484599 / 200000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X10XV3LogArg, Case2PointData.X10, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X10XV3_arg_regular :
    (barrierCase2X10XV3LogArg).im ≠ 0 ∨ 0 < (barrierCase2X10XV3LogArg).re := by
  rw [barrierCase2X10XV3_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X10XV3_weight_eq :
    (barrierV2Tail.getD 3 (0, 0)).2 = barrierComplex (-2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X10XV3_error :
    |((barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2X10XV3LogArg).re -
      ((barrierWeightedComplexLogRat (-2466317 / 50000000) (0 / 1) (-1) (0) (25799903804725190190801 / 20000000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X10XV3_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2466317 / 50000000) (0 / 1)
    barrierCase2X10XV3LogArg (-1) (0) (25799903804725190190801 / 20000000000000000000000) (160623484599 / 200000000000) (0 / 1)
  have hratio : ((0 / 1) / (160623484599 / 200000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X10XV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X10XV3_approx_upper :
    barrierWeightedComplexLogRat (-2466317 / 50000000) (0 / 1) (-1) (0) (25799903804725190190801 / 20000000000000000000000) (0 / 1) <
      (10815014387 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X10XV3_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X10 : ℝ) (barrierV2Tail.getD 3 (0, 0)) <
      (10815014387 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2X10XV3LogArg).re < _
  have he := (abs_lt.mp barrierCase2X10XV3_error).2
  have ha : ((barrierWeightedComplexLogRat (-2466317 / 50000000) (0 / 1) (-1) (0) (25799903804725190190801 / 20000000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (10815014387 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X10XV3_approx_upper using 1
    norm_num
  linarith

def barrierCase2X10XV4LogArg : ℂ :=
  1 - ((Case2PointData.X10 : ℝ) : ℂ) * (barrierV2Tail.getD 4 (0, 0)).1

private theorem barrierCase2X10XV4_arg_eq :
    barrierCase2X10XV4LogArg = barrierComplex (995088873983 / 1250000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X10XV4LogArg, Case2PointData.X10, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X10XV4_arg_regular :
    (barrierCase2X10XV4LogArg).im ≠ 0 ∨ 0 < (barrierCase2X10XV4LogArg).re := by
  rw [barrierCase2X10XV4_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X10XV4_weight_eq :
    (barrierV2Tail.getD 4 (0, 0)).2 = barrierComplex (11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X10XV4_error :
    |((barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X10XV4LogArg).re -
      ((barrierWeightedComplexLogRat (11618157 / 100000000) (0 / 1) (-1) (0) (990201867124754854284289 / 781250000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X10XV4_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (11618157 / 100000000) (0 / 1)
    barrierCase2X10XV4LogArg (-1) (0) (990201867124754854284289 / 781250000000000000000000) (995088873983 / 1250000000000) (0 / 1)
  have hratio : ((0 / 1) / (995088873983 / 1250000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X10XV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X10XV4_approx_upper :
    barrierWeightedComplexLogRat (11618157 / 100000000) (0 / 1) (-1) (0) (990201867124754854284289 / 781250000000000000000000) (0 / 1) <
      (-26497156162 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X10XV4_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X10 : ℝ) (barrierV2Tail.getD 4 (0, 0)) <
      (-26497156162 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X10XV4LogArg).re < _
  have he := (abs_lt.mp barrierCase2X10XV4_error).2
  have ha : ((barrierWeightedComplexLogRat (11618157 / 100000000) (0 / 1) (-1) (0) (990201867124754854284289 / 781250000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-26497156162 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X10XV4_approx_upper using 1
    norm_num
  linarith

def barrierCase2X10XV5LogArg : ℂ :=
  1 - ((Case2PointData.X10 : ℝ) : ℂ) * (barrierV2Tail.getD 5 (0, 0)).1

private theorem barrierCase2X10XV5_arg_eq :
    barrierCase2X10XV5LogArg = barrierComplex (1 / 1) (-80825478981 / 500000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X10XV5LogArg, Case2PointData.X10, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X10XV5_arg_regular :
    (barrierCase2X10XV5LogArg).im ≠ 0 ∨ 0 < (barrierCase2X10XV5LogArg).re := by
  rw [barrierCase2X10XV5_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X10XV5_weight_eq :
    (barrierV2Tail.getD 5 (0, 0)).2 = barrierComplex (13619357 / 100000000) (600749 / 3125000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X10XV5_error :
    |((barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2X10XV5LogArg).re -
      ((barrierWeightedComplexLogRat (13619357 / 100000000) (600749 / 3125000) (0) (0) (256532758052508072798361 / 250000000000000000000000) (-80825478981 / 500000000000) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X10XV5_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (13619357 / 100000000) (600749 / 3125000)
    barrierCase2X10XV5LogArg (0) (0) (256532758052508072798361 / 250000000000000000000000) (1 / 1) (-80825478981 / 500000000000)
  have hratio : ((-80825478981 / 500000000000) / (1 / 1) : ℚ) = (-80825478981 / 500000000000) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X10XV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X10XV5_approx_upper :
    barrierWeightedComplexLogRat (13619357 / 100000000) (600749 / 3125000) (0) (0) (256532758052508072798361 / 250000000000000000000000) (-80825478981 / 500000000000) <
      (32565801635 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X10XV5_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X10 : ℝ) (barrierV2Tail.getD 5 (0, 0)) <
      (32565801635 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2X10XV5LogArg).re < _
  have he := (abs_lt.mp barrierCase2X10XV5_error).2
  have ha : ((barrierWeightedComplexLogRat (13619357 / 100000000) (600749 / 3125000) (0) (0) (256532758052508072798361 / 250000000000000000000000) (-80825478981 / 500000000000) : ℚ) : ℝ) <
      (32565801635 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X10XV5_approx_upper using 1
    norm_num
  linarith

def barrierCase2X10XV7LogArg : ℂ :=
  1 - ((Case2PointData.X10 : ℝ) : ℂ) * (barrierV2Tail.getD 7 (0, 0)).1

private theorem barrierCase2X10XV7_arg_eq :
    barrierCase2X10XV7LogArg = barrierComplex (1 / 1) (-18652033611 / 100000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X10XV7LogArg, Case2PointData.X10, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X10XV7_arg_regular :
    (barrierCase2X10XV7LogArg).im ≠ 0 ∨ 0 < (barrierCase2X10XV7LogArg).re := by
  rw [barrierCase2X10XV7_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X10XV7_weight_eq :
    (barrierV2Tail.getD 7 (0, 0)).2 = barrierComplex (-7835271 / 50000000) (15094393 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X10XV7_error :
    |((barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2X10XV7LogArg).re -
      ((barrierWeightedComplexLogRat (-7835271 / 50000000) (15094393 / 100000000) (0) (0) (10347898357825873699321 / 10000000000000000000000) (-18652033611 / 100000000000) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X10XV7_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-7835271 / 50000000) (15094393 / 100000000)
    barrierCase2X10XV7LogArg (0) (0) (10347898357825873699321 / 10000000000000000000000) (1 / 1) (-18652033611 / 100000000000)
  have hratio : ((-18652033611 / 100000000000) / (1 / 1) : ℚ) = (-18652033611 / 100000000000) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X10XV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X10XV7_approx_upper :
    barrierWeightedComplexLogRat (-7835271 / 50000000) (15094393 / 100000000) (0) (0) (10347898357825873699321 / 10000000000000000000000) (-18652033611 / 100000000000) <
      (25154737197 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X10XV7_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X10 : ℝ) (barrierV2Tail.getD 7 (0, 0)) <
      (25154737197 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2X10XV7LogArg).re < _
  have he := (abs_lt.mp barrierCase2X10XV7_error).2
  have ha : ((barrierWeightedComplexLogRat (-7835271 / 50000000) (15094393 / 100000000) (0) (0) (10347898357825873699321 / 10000000000000000000000) (-18652033611 / 100000000000) : ℚ) : ℝ) <
      (25154737197 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X10XV7_approx_upper using 1
    norm_num
  linarith

def barrierCase2X10XV9LogArg : ℂ :=
  1 - ((Case2PointData.X10 : ℝ) : ℂ) * (barrierV2Tail.getD 9 (0, 0)).1

private theorem barrierCase2X10XV9_arg_eq :
    barrierCase2X10XV9LogArg = barrierComplex (1 / 1) (-395837602189 / 2000000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X10XV9LogArg, Case2PointData.X10, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X10XV9_arg_regular :
    (barrierCase2X10XV9LogArg).im ≠ 0 ∨ 0 < (barrierCase2X10XV9LogArg).re := by
  rw [barrierCase2X10XV9_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X10XV9_weight_eq :
    (barrierV2Tail.getD 9 (0, 0)).2 = barrierComplex (-3346771 / 100000000) (-5956127 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X10XV9_error :
    |((barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2X10XV9LogArg).re -
      ((barrierWeightedComplexLogRat (-3346771 / 100000000) (-5956127 / 100000000) (0) (0) (4156687407306737017591721 / 4000000000000000000000000) (-395837602189 / 2000000000000) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X10XV9_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-3346771 / 100000000) (-5956127 / 100000000)
    barrierCase2X10XV9LogArg (0) (0) (4156687407306737017591721 / 4000000000000000000000000) (1 / 1) (-395837602189 / 2000000000000)
  have hratio : ((-395837602189 / 2000000000000) / (1 / 1) : ℚ) = (-395837602189 / 2000000000000) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X10XV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X10XV9_approx_upper :
    barrierWeightedComplexLogRat (-3346771 / 100000000) (-5956127 / 100000000) (0) (0) (4156687407306737017591721 / 4000000000000000000000000) (-395837602189 / 2000000000000) <
      (-12280874781 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X10XV9_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X10 : ℝ) (barrierV2Tail.getD 9 (0, 0)) <
      (-12280874781 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2X10XV9LogArg).re < _
  have he := (abs_lt.mp barrierCase2X10XV9_error).2
  have ha : ((barrierWeightedComplexLogRat (-3346771 / 100000000) (-5956127 / 100000000) (0) (0) (4156687407306737017591721 / 4000000000000000000000000) (-395837602189 / 2000000000000) : ℚ) : ℝ) <
      (-12280874781 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X10XV9_approx_upper using 1
    norm_num
  linarith

def barrierCase2X10XV11LogArg : ℂ :=
  1 - ((Case2PointData.X10 : ℝ) : ℂ) * (barrierV2Tail.getD 11 (0, 0)).1

private theorem barrierCase2X10XV11_arg_eq :
    barrierCase2X10XV11LogArg = barrierComplex (1 / 1) (-254911126017 / 1250000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X10XV11LogArg, Case2PointData.X10, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X10XV11_arg_regular :
    (barrierCase2X10XV11LogArg).im ≠ 0 ∨ 0 < (barrierCase2X10XV11LogArg).re := by
  rw [barrierCase2X10XV11_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X10XV11_weight_eq :
    (barrierV2Tail.getD 11 (0, 0)).2 = barrierComplex (2055213 / 200000000) (21715849 / 200000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X10XV11_error :
    |((barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2X10XV11LogArg).re -
      ((barrierWeightedComplexLogRat (2055213 / 200000000) (21715849 / 200000000) (0) (0) (1627479682167254854284289 / 1562500000000000000000000) (-254911126017 / 1250000000000) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X10XV11_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (2055213 / 200000000) (21715849 / 200000000)
    barrierCase2X10XV11LogArg (0) (0) (1627479682167254854284289 / 1562500000000000000000000) (1 / 1) (-254911126017 / 1250000000000)
  have hratio : ((-254911126017 / 1250000000000) / (1 / 1) : ℚ) = (-254911126017 / 1250000000000) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X10XV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X10XV11_approx_upper :
    barrierWeightedComplexLogRat (2055213 / 200000000) (21715849 / 200000000) (0) (0) (1627479682167254854284289 / 1562500000000000000000000) (-254911126017 / 1250000000000) <
      (22052290471 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X10XV11_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X10 : ℝ) (barrierV2Tail.getD 11 (0, 0)) <
      (22052290471 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2X10XV11LogArg).re < _
  have he := (abs_lt.mp barrierCase2X10XV11_error).2
  have ha : ((barrierWeightedComplexLogRat (2055213 / 200000000) (21715849 / 200000000) (0) (0) (1627479682167254854284289 / 1562500000000000000000000) (-254911126017 / 1250000000000) : ℚ) : ℝ) <
      (22052290471 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X10XV11_approx_upper using 1
    norm_num
  linarith

open Case2PointData

private theorem barrierCase2X10_XP_tail_upper :
    (barrierP2Tail.map (barrierCase2XPLogTerm (X10 : ℝ))).sum <
      (1021304883031 / 1000000000000 : ℝ) := by
  have hp : ∀ i ∈ [2, 4, 6, 8],
      barrierCase2XPLogTerm (X10 : ℝ) (barrierP2Tail.getD (i + 1) (0, 0)) =
        barrierCase2XPLogTerm (X10 : ℝ) (barrierP2Tail.getD i (0, 0)) := by
    intro i hi
    rw [barrierP2Tail_getD_pair i hi]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X10XP2_arg_regular
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X10XP4_arg_regular
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X10XP6_arg_regular
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X10XP8_arg_regular
  rw [barrierP2Tail_paired_sum _ hp]
  linarith only [barrierCase2X10XP0_log_upper,
    barrierCase2X10XP1_log_upper,
    barrierCase2X10XP2_log_upper,
    barrierCase2X10XP4_log_upper,
    barrierCase2X10XP6_log_upper,
    barrierCase2X10XP8_log_upper]

private theorem barrierCase2X10_XV_tail_upper :
    (barrierV2Tail.map (barrierCase2XVLogTerm (X10 : ℝ))).sum <
      (145570310125 / 1000000000000 : ℝ) := by
  have hp : ∀ i ∈ [5, 7, 9, 11],
      barrierCase2XVLogTerm (X10 : ℝ) (barrierV2Tail.getD (i + 1) (0, 0)) =
        barrierCase2XVLogTerm (X10 : ℝ) (barrierV2Tail.getD i (0, 0)) := by
    intro i hi
    rw [barrierV2Tail_getD_pair i hi]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X10XV5_arg_regular
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X10XV7_arg_regular
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X10XV9_arg_regular
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X10XV11_arg_regular
  rw [barrierV2Tail_paired_sum _ hp]
  linarith only [barrierCase2X10XV0_log_upper,
    barrierCase2X10XV1_log_upper,
    barrierCase2X10XV2_log_upper,
    barrierCase2X10XV3_log_upper,
    barrierCase2X10XV4_log_upper,
    barrierCase2X10XV5_log_upper,
    barrierCase2X10XV7_log_upper,
    barrierCase2X10XV9_log_upper,
    barrierCase2X10XV11_log_upper]

private theorem barrierCase2X10_approx_upper :
    barrierCase2XApproxRat X10 (-3) (-1) (0) (2072448179 / 1250000000) (7927551821 / 5000000000) (104295041454640416041 / 100000000000000000000) + (1021304883031 / 1000000000000) + (145570310125 / 1000000000000) <
      (-98399 / 100000 - 2 / 1000000000000000 : ℚ) := by
  unfold barrierCase2XApproxRat barrierCase2XRat
  rw [barrierCase2TP_eq_explicit, barrierCase2SV_eq_explicit]
  simp only [barrierScaledLogRat, barrierLogHRat_two_eq]
  decide +kernel

theorem barrierCase2X10_lt : barrierCase2X (X10 : ℝ) < (-98399 / 100000 : ℝ) := by
  have hx : |(X10 : ℝ)| ≤ 1 := by norm_num [X10]
  have he := (abs_lt.mp (barrierCase2X_realLog_approx_error X10 hx
    (-3) (-1) (0) (2072448179 / 1250000000) (7927551821 / 5000000000) (104295041454640416041 / 100000000000000000000)
    X10_normalizations.1 X10_normalizations.2.1 X10_normalizations.2.2)).2
  have ha : ((barrierCase2XApproxRat X10 (-3) (-1) (0) (2072448179 / 1250000000) (7927551821 / 5000000000) (104295041454640416041 / 100000000000000000000) : ℚ) : ℝ) +
      (1021304883031 / 1000000000000) + (145570310125 / 1000000000000) < (-98399 / 100000 - 2 / 1000000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X10_approx_upper using 1 <;> norm_num
  linarith only [he, ha, barrierCase2X10_XP_tail_upper, barrierCase2X10_XV_tail_upper]

end InternalCatalan

end

end OAI
