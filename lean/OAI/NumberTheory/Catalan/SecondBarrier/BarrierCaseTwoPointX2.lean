import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoLogsX2Group0
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX0

namespace OAI

noncomputable section

namespace InternalCatalan

def barrierCase2X2XV0LogArg : ℂ :=
  1 - ((Case2PointData.X2 : ℝ) : ℂ) * (barrierV2Tail.getD 0 (0, 0)).1

private theorem barrierCase2X2XV0_arg_eq :
    barrierCase2X2XV0LogArg = barrierComplex (4891694367 / 12500000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X2XV0LogArg, Case2PointData.X2, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X2XV0_arg_regular :
    (barrierCase2X2XV0LogArg).im ≠ 0 ∨ 0 < (barrierCase2X2XV0LogArg).re := by
  rw [barrierCase2X2XV0_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X2XV0_weight_eq :
    (barrierV2Tail.getD 0 (0, 0)).2 = barrierComplex (15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X2XV0_error :
    |((barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X2XV0LogArg).re -
      ((barrierWeightedComplexLogRat (15199211 / 100000000) (0 / 1) (-3) (0) (23928673780139530689 / 19531250000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X2XV0_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (15199211 / 100000000) (0 / 1)
    barrierCase2X2XV0LogArg (-3) (0) (23928673780139530689 / 19531250000000000000) (4891694367 / 12500000000) (0 / 1)
  have hratio : ((0 / 1) / (4891694367 / 12500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X2XV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X2XV0_approx_upper :
    barrierWeightedComplexLogRat (15199211 / 100000000) (0 / 1) (-3) (0) (23928673780139530689 / 19531250000000000000) (0 / 1) <
      (-142597463167 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X2XV0_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X2 : ℝ) (barrierV2Tail.getD 0 (0, 0)) <
      (-142597463167 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X2XV0LogArg).re < _
  have he := (abs_lt.mp barrierCase2X2XV0_error).2
  have ha : ((barrierWeightedComplexLogRat (15199211 / 100000000) (0 / 1) (-3) (0) (23928673780139530689 / 19531250000000000000) (0 / 1) : ℚ) : ℝ) <
      (-142597463167 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X2XV0_approx_upper using 1
    norm_num
  linarith

def barrierCase2X2XV1LogArg : ℂ :=
  1 - ((Case2PointData.X2 : ℝ) : ℂ) * (barrierV2Tail.getD 1 (0, 0)).1

private theorem barrierCase2X2XV1_arg_eq :
    barrierCase2X2XV1LogArg = barrierComplex (8425083101 / 31250000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X2XV1LogArg, Case2PointData.X2, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X2XV1_arg_regular :
    (barrierCase2X2XV1LogArg).im ≠ 0 ∨ 0 < (barrierCase2X2XV1LogArg).re := by
  rw [barrierCase2X2XV1_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X2XV1_weight_eq :
    (barrierV2Tail.getD 1 (0, 0)).2 = barrierComplex (2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X2XV1_error :
    |((barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X2XV1LogArg).re -
      ((barrierWeightedComplexLogRat (2225831 / 50000000) (0 / 1) (-4) (0) (70982025258755776201 / 61035156250000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X2XV1_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (2225831 / 50000000) (0 / 1)
    barrierCase2X2XV1LogArg (-4) (0) (70982025258755776201 / 61035156250000000000) (8425083101 / 31250000000) (0 / 1)
  have hratio : ((0 / 1) / (8425083101 / 31250000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X2XV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X2XV1_approx_upper :
    barrierWeightedComplexLogRat (2225831 / 50000000) (0 / 1) (-4) (0) (70982025258755776201 / 61035156250000000000) (0 / 1) <
      (-58352654213 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X2XV1_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X2 : ℝ) (barrierV2Tail.getD 1 (0, 0)) <
      (-58352654213 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X2XV1LogArg).re < _
  have he := (abs_lt.mp barrierCase2X2XV1_error).2
  have ha : ((barrierWeightedComplexLogRat (2225831 / 50000000) (0 / 1) (-4) (0) (70982025258755776201 / 61035156250000000000) (0 / 1) : ℚ) : ℝ) <
      (-58352654213 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X2XV1_approx_upper using 1
    norm_num
  linarith

def barrierCase2X2XV2LogArg : ℂ :=
  1 - ((Case2PointData.X2 : ℝ) : ℂ) * (barrierV2Tail.getD 2 (0, 0)).1

private theorem barrierCase2X2XV2_arg_eq :
    barrierCase2X2XV2LogArg = barrierComplex (208691361963 / 125000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X2XV2LogArg, Case2PointData.X2, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X2XV2_arg_regular :
    (barrierCase2X2XV2LogArg).im ≠ 0 ∨ 0 < (barrierCase2X2XV2LogArg).re := by
  rw [barrierCase2X2XV2_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X2XV2_weight_eq :
    (barrierV2Tail.getD 2 (0, 0)).2 = barrierComplex (1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X2XV2_error :
    |((barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X2XV2LogArg).re -
      ((barrierWeightedComplexLogRat (1272699 / 50000000) (0 / 1) (1) (0) (43552084557971883213369 / 31250000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X2XV2_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (1272699 / 50000000) (0 / 1)
    barrierCase2X2XV2LogArg (1) (0) (43552084557971883213369 / 31250000000000000000000) (208691361963 / 125000000000) (0 / 1)
  have hratio : ((0 / 1) / (208691361963 / 125000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X2XV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X2XV2_approx_upper :
    barrierWeightedComplexLogRat (1272699 / 50000000) (0 / 1) (1) (0) (43552084557971883213369 / 31250000000000000000000) (0 / 1) <
      (13046251285 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X2XV2_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X2 : ℝ) (barrierV2Tail.getD 2 (0, 0)) <
      (13046251285 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X2XV2LogArg).re < _
  have he := (abs_lt.mp barrierCase2X2XV2_error).2
  have ha : ((barrierWeightedComplexLogRat (1272699 / 50000000) (0 / 1) (1) (0) (43552084557971883213369 / 31250000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (13046251285 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X2XV2_approx_upper using 1
    norm_num
  linarith

def barrierCase2X2XV3LogArg : ℂ :=
  1 - ((Case2PointData.X2 : ℝ) : ℂ) * (barrierV2Tail.getD 3 (0, 0)).1

private theorem barrierCase2X2XV3_arg_eq :
    barrierCase2X2XV3LogArg = barrierComplex (344557807027 / 200000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X2XV3LogArg, Case2PointData.X2, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X2XV3_arg_regular :
    (barrierCase2X2XV3LogArg).im ≠ 0 ∨ 0 < (barrierCase2X2XV3LogArg).re := by
  rw [barrierCase2X2XV3_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X2XV3_weight_eq :
    (barrierV2Tail.getD 3 (0, 0)).2 = barrierComplex (-2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X2XV3_error :
    |((barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2X2XV3LogArg).re -
      ((barrierWeightedComplexLogRat (-2466317 / 50000000) (0 / 1) (1) (0) (118720082383255370578729 / 80000000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X2XV3_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2466317 / 50000000) (0 / 1)
    barrierCase2X2XV3LogArg (1) (0) (118720082383255370578729 / 80000000000000000000000) (344557807027 / 200000000000) (0 / 1)
  have hratio : ((0 / 1) / (344557807027 / 200000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X2XV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X2XV3_approx_upper :
    barrierWeightedComplexLogRat (-2466317 / 50000000) (0 / 1) (1) (0) (118720082383255370578729 / 80000000000000000000000) (0 / 1) <
      (-26830791821 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X2XV3_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X2 : ℝ) (barrierV2Tail.getD 3 (0, 0)) <
      (-26830791821 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2X2XV3LogArg).re < _
  have he := (abs_lt.mp barrierCase2X2XV3_error).2
  have ha : ((barrierWeightedComplexLogRat (-2466317 / 50000000) (0 / 1) (1) (0) (118720082383255370578729 / 80000000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-26830791821 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X2XV3_approx_upper using 1
    norm_num
  linarith

def barrierCase2X2XV4LogArg : ℂ :=
  1 - ((Case2PointData.X2 : ℝ) : ℂ) * (barrierV2Tail.getD 4 (0, 0)).1

private theorem barrierCase2X2XV4_arg_eq :
    barrierCase2X2XV4LogArg = barrierComplex (2185821592859 / 1250000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X2XV4LogArg, Case2PointData.X2, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X2XV4_arg_regular :
    (barrierCase2X2XV4LogArg).im ≠ 0 ∨ 0 < (barrierCase2X2XV4LogArg).re := by
  rw [barrierCase2X2XV4_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X2XV4_weight_eq :
    (barrierV2Tail.getD 4 (0, 0)).2 = barrierComplex (11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X2XV4_error :
    |((barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X2XV4LogArg).re -
      ((barrierWeightedComplexLogRat (11618157 / 100000000) (0 / 1) (1) (0) (4777816035808655959793881 / 3125000000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X2XV4_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (11618157 / 100000000) (0 / 1)
    barrierCase2X2XV4LogArg (1) (0) (4777816035808655959793881 / 3125000000000000000000000) (2185821592859 / 1250000000000) (0 / 1)
  have hratio : ((0 / 1) / (2185821592859 / 1250000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X2XV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X2XV4_approx_upper :
    barrierWeightedComplexLogRat (11618157 / 100000000) (0 / 1) (1) (0) (4777816035808655959793881 / 3125000000000000000000000) (0 / 1) <
      (64927863778 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X2XV4_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X2 : ℝ) (barrierV2Tail.getD 4 (0, 0)) <
      (64927863778 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X2XV4LogArg).re < _
  have he := (abs_lt.mp barrierCase2X2XV4_error).2
  have ha : ((barrierWeightedComplexLogRat (11618157 / 100000000) (0 / 1) (1) (0) (4777816035808655959793881 / 3125000000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (64927863778 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X2XV4_approx_upper using 1
    norm_num
  linarith

def barrierCase2X2XV5LogArg : ℂ :=
  1 - ((Case2PointData.X2 : ℝ) : ℂ) * (barrierV2Tail.getD 5 (0, 0)).1

private theorem barrierCase2X2XV5_arg_eq :
    barrierCase2X2XV5LogArg = barrierComplex (1 / 1) (296723919687 / 500000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X2XV5LogArg, Case2PointData.X2, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X2XV5_arg_regular :
    (barrierCase2X2XV5LogArg).im ≠ 0 ∨ 0 < (barrierCase2X2XV5LogArg).re := by
  rw [barrierCase2X2XV5_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X2XV5_weight_eq :
    (barrierV2Tail.getD 5 (0, 0)).2 = barrierComplex (13619357 / 100000000) (600749 / 3125000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X2XV5_error :
    |((barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2X2XV5LogArg).re -
      ((barrierWeightedComplexLogRat (13619357 / 100000000) (600749 / 3125000) (0) (1) (338045084514417226177969 / 250000000000000000000000) (-203276080313 / 796723919687) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X2XV5_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (13619357 / 100000000) (600749 / 3125000)
    barrierCase2X2XV5LogArg (0) (1) (338045084514417226177969 / 250000000000000000000000) (796723919687 / 500000000000) (-203276080313 / 500000000000)
  have hratio : ((-203276080313 / 500000000000) / (796723919687 / 500000000000) : ℚ) = (-203276080313 / 796723919687) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X2XV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X2XV5_approx_upper :
    barrierWeightedComplexLogRat (13619357 / 100000000) (600749 / 3125000) (0) (1) (338045084514417226177969 / 250000000000000000000000) (-203276080313 / 796723919687) <
      (-82415178458 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X2XV5_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X2 : ℝ) (barrierV2Tail.getD 5 (0, 0)) <
      (-82415178458 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2X2XV5LogArg).re < _
  have he := (abs_lt.mp barrierCase2X2XV5_error).2
  have ha : ((barrierWeightedComplexLogRat (13619357 / 100000000) (600749 / 3125000) (0) (1) (338045084514417226177969 / 250000000000000000000000) (-203276080313 / 796723919687) : ℚ) : ℝ) <
      (-82415178458 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X2XV5_approx_upper using 1
    norm_num
  linarith

def barrierCase2X2XV7LogArg : ℂ :=
  1 - ((Case2PointData.X2 : ℝ) : ℂ) * (barrierV2Tail.getD 7 (0, 0)).1

private theorem barrierCase2X2XV7_arg_eq :
    barrierCase2X2XV7LogArg = barrierComplex (1 / 1) (68474750697 / 100000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X2XV7LogArg, Case2PointData.X2, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X2XV7_arg_regular :
    (barrierCase2X2XV7LogArg).im ≠ 0 ∨ 0 < (barrierCase2X2XV7LogArg).re := by
  rw [barrierCase2X2XV7_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X2XV7_weight_eq :
    (barrierV2Tail.getD 7 (0, 0)).2 = barrierComplex (-7835271 / 50000000) (15094393 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X2XV7_error :
    |((barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2X2XV7LogArg).re -
      ((barrierWeightedComplexLogRat (-7835271 / 50000000) (15094393 / 100000000) (0) (1) (14688791483016301985809 / 10000000000000000000000) (-31525249303 / 168474750697) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X2XV7_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-7835271 / 50000000) (15094393 / 100000000)
    barrierCase2X2XV7LogArg (0) (1) (14688791483016301985809 / 10000000000000000000000) (168474750697 / 100000000000) (-31525249303 / 100000000000)
  have hratio : ((-31525249303 / 100000000000) / (168474750697 / 100000000000) : ℚ) = (-31525249303 / 168474750697) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X2XV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X2XV7_approx_upper :
    barrierWeightedComplexLogRat (-7835271 / 50000000) (15094393 / 100000000) (0) (1) (14688791483016301985809 / 10000000000000000000000) (-31525249303 / 168474750697) <
      (-120755719726 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X2XV7_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X2 : ℝ) (barrierV2Tail.getD 7 (0, 0)) <
      (-120755719726 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2X2XV7LogArg).re < _
  have he := (abs_lt.mp barrierCase2X2XV7_error).2
  have ha : ((barrierWeightedComplexLogRat (-7835271 / 50000000) (15094393 / 100000000) (0) (1) (14688791483016301985809 / 10000000000000000000000) (-31525249303 / 168474750697) : ℚ) : ℝ) <
      (-120755719726 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X2XV7_approx_upper using 1
    norm_num
  linarith

def barrierCase2X2XV9LogArg : ℂ :=
  1 - ((Case2PointData.X2 : ℝ) : ℂ) * (barrierV2Tail.getD 9 (0, 0)).1

private theorem barrierCase2X2XV9_arg_eq :
    barrierCase2X2XV9LogArg = barrierComplex (1 / 1) (1453186375903 / 2000000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X2XV9LogArg, Case2PointData.X2, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X2XV9_arg_regular :
    (barrierCase2X2XV9LogArg).im ≠ 0 ∨ 0 < (barrierCase2X2XV9LogArg).re := by
  rw [barrierCase2X2XV9_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X2XV9_weight_eq :
    (barrierV2Tail.getD 9 (0, 0)).2 = barrierComplex (-3346771 / 100000000) (-5956127 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X2XV9_error :
    |((barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2X2XV9LogArg).re -
      ((barrierWeightedComplexLogRat (-3346771 / 100000000) (-5956127 / 100000000) (0) (1) (6111750643110095219065409 / 4000000000000000000000000) (-546813624097 / 3453186375903) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X2XV9_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-3346771 / 100000000) (-5956127 / 100000000)
    barrierCase2X2XV9LogArg (0) (1) (6111750643110095219065409 / 4000000000000000000000000) (3453186375903 / 2000000000000) (-546813624097 / 2000000000000)
  have hratio : ((-546813624097 / 2000000000000) / (3453186375903 / 2000000000000) : ℚ) = (-546813624097 / 3453186375903) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X2XV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X2XV9_approx_upper :
    barrierWeightedComplexLogRat (-3346771 / 100000000) (-5956127 / 100000000) (0) (1) (6111750643110095219065409 / 4000000000000000000000000) (-546813624097 / 3453186375903) <
      (30331627232 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X2XV9_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X2 : ℝ) (barrierV2Tail.getD 9 (0, 0)) <
      (30331627232 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2X2XV9LogArg).re < _
  have he := (abs_lt.mp barrierCase2X2XV9_error).2
  have ha : ((barrierWeightedComplexLogRat (-3346771 / 100000000) (-5956127 / 100000000) (0) (1) (6111750643110095219065409 / 4000000000000000000000000) (-546813624097 / 3453186375903) : ℚ) : ℝ) <
      (30331627232 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X2XV9_approx_upper using 1
    norm_num
  linarith

def barrierCase2X2XV11LogArg : ℂ :=
  1 - ((Case2PointData.X2 : ℝ) : ℂ) * (barrierV2Tail.getD 11 (0, 0)).1

private theorem barrierCase2X2XV11_arg_eq :
    barrierCase2X2XV11LogArg = barrierComplex (1 / 1) (935821592859 / 1250000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X2XV11LogArg, Case2PointData.X2, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X2XV11_arg_regular :
    (barrierCase2X2XV11LogArg).im ≠ 0 ∨ 0 < (barrierCase2X2XV11LogArg).re := by
  rw [barrierCase2X2XV11_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X2XV11_weight_eq :
    (barrierV2Tail.getD 11 (0, 0)).2 = barrierComplex (2055213 / 200000000) (21715849 / 200000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X2XV11_error :
    |((barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2X2XV11LogArg).re -
      ((barrierWeightedComplexLogRat (2055213 / 200000000) (21715849 / 200000000) (0) (1) (2438262053661155959793881 / 1562500000000000000000000) (-314178407141 / 2185821592859) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X2XV11_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (2055213 / 200000000) (21715849 / 200000000)
    barrierCase2X2XV11LogArg (0) (1) (2438262053661155959793881 / 1562500000000000000000000) (2185821592859 / 1250000000000) (-314178407141 / 1250000000000)
  have hratio : ((-314178407141 / 1250000000000) / (2185821592859 / 1250000000000) : ℚ) = (-314178407141 / 2185821592859) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X2XV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X2XV11_approx_upper :
    barrierWeightedComplexLogRat (2055213 / 200000000) (21715849 / 200000000) (0) (1) (2438262053661155959793881 / 1562500000000000000000000) (-314178407141 / 2185821592859) <
      (-67491081131 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X2XV11_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X2 : ℝ) (barrierV2Tail.getD 11 (0, 0)) <
      (-67491081131 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2X2XV11LogArg).re < _
  have he := (abs_lt.mp barrierCase2X2XV11_error).2
  have ha : ((barrierWeightedComplexLogRat (2055213 / 200000000) (21715849 / 200000000) (0) (1) (2438262053661155959793881 / 1562500000000000000000000) (-314178407141 / 2185821592859) : ℚ) : ℝ) <
      (-67491081131 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X2XV11_approx_upper using 1
    norm_num
  linarith

open Case2PointData

private theorem barrierCase2X2_XP_tail_upper :
    (barrierP2Tail.map (barrierCase2XPLogTerm (X2 : ℝ))).sum <
      (-1113908580915 / 1000000000000 : ℝ) := by
  have hp : ∀ i ∈ [2, 4, 6, 8],
      barrierCase2XPLogTerm (X2 : ℝ) (barrierP2Tail.getD (i + 1) (0, 0)) =
        barrierCase2XPLogTerm (X2 : ℝ) (barrierP2Tail.getD i (0, 0)) := by
    intro i hi
    rw [barrierP2Tail_getD_pair i hi]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X2XP2_arg_regular
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X2XP4_arg_regular
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X2XP6_arg_regular
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X2XP8_arg_regular
  rw [barrierP2Tail_paired_sum _ hp]
  linarith only [barrierCase2X2XP0_log_upper,
    barrierCase2X2XP1_log_upper,
    barrierCase2X2XP2_log_upper,
    barrierCase2X2XP4_log_upper,
    barrierCase2X2XP6_log_upper,
    barrierCase2X2XP8_log_upper]

private theorem barrierCase2X2_XV_tail_upper :
    (barrierV2Tail.map (barrierCase2XVLogTerm (X2 : ℝ))).sum <
      (-630467498304 / 1000000000000 : ℝ) := by
  have hp : ∀ i ∈ [5, 7, 9, 11],
      barrierCase2XVLogTerm (X2 : ℝ) (barrierV2Tail.getD (i + 1) (0, 0)) =
        barrierCase2XVLogTerm (X2 : ℝ) (barrierV2Tail.getD i (0, 0)) := by
    intro i hi
    rw [barrierV2Tail_getD_pair i hi]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X2XV5_arg_regular
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X2XV7_arg_regular
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X2XV9_arg_regular
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X2XV11_arg_regular
  rw [barrierV2Tail_paired_sum _ hp]
  linarith only [barrierCase2X2XV0_log_upper,
    barrierCase2X2XV1_log_upper,
    barrierCase2X2XV2_log_upper,
    barrierCase2X2XV3_log_upper,
    barrierCase2X2XV4_log_upper,
    barrierCase2X2XV5_log_upper,
    barrierCase2X2XV7_log_upper,
    barrierCase2X2XV9_log_upper,
    barrierCase2X2XV11_log_upper]

private theorem barrierCase2X2_approx_upper :
    barrierCase2XApproxRat X2 (-1) (0) (0) (7608305633 / 5000000000) (17608305633 / 10000000000) (157886314605139530689 / 100000000000000000000) + (-1113908580915 / 1000000000000) + (-630467498304 / 1000000000000) <
      (-98399 / 100000 - 2 / 1000000000000000 : ℚ) := by
  unfold barrierCase2XApproxRat barrierCase2XRat
  rw [barrierCase2TP_eq_explicit, barrierCase2SV_eq_explicit]
  simp only [barrierScaledLogRat, barrierLogHRat_two_eq]
  decide +kernel

theorem barrierCase2X2_lt : barrierCase2X (X2 : ℝ) < (-98399 / 100000 : ℝ) := by
  have hx : |(X2 : ℝ)| ≤ 1 := by norm_num [X2]
  have he := (abs_lt.mp (barrierCase2X_realLog_approx_error X2 hx
    (-1) (0) (0) (7608305633 / 5000000000) (17608305633 / 10000000000) (157886314605139530689 / 100000000000000000000)
    X2_normalizations.1 X2_normalizations.2.1 X2_normalizations.2.2)).2
  have ha : ((barrierCase2XApproxRat X2 (-1) (0) (0) (7608305633 / 5000000000) (17608305633 / 10000000000) (157886314605139530689 / 100000000000000000000) : ℚ) : ℝ) +
      (-1113908580915 / 1000000000000) + (-630467498304 / 1000000000000) < (-98399 / 100000 - 2 / 1000000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X2_approx_upper using 1 <;> norm_num
  linarith only [he, ha, barrierCase2X2_XP_tail_upper, barrierCase2X2_XV_tail_upper]

end InternalCatalan

end

end OAI
