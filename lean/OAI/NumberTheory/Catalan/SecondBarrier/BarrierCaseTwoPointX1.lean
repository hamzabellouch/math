import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoLogsX1Group0
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX0

namespace OAI

noncomputable section

namespace InternalCatalan

def barrierCase2X1XV0LogArg : ℂ :=
  1 - ((Case2PointData.X1 : ℝ) : ℂ) * (barrierV2Tail.getD 0 (0, 0)).1

private theorem barrierCase2X1XV0_arg_eq :
    barrierCase2X1XV0LogArg = barrierComplex (889420607 / 3125000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X1XV0LogArg, Case2PointData.X1, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X1XV0_arg_regular :
    (barrierCase2X1XV0LogArg).im ≠ 0 ∨ 0 < (barrierCase2X1XV0LogArg).re := by
  rw [barrierCase2X1XV0_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X1XV0_weight_eq :
    (barrierV2Tail.getD 0 (0, 0)).2 = barrierComplex (15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X1XV0_error :
    |((barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X1XV0LogArg).re -
      ((barrierWeightedComplexLogRat (15199211 / 100000000) (0 / 1) (-4) (0) (791069016156248449 / 610351562500000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X1XV0_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (15199211 / 100000000) (0 / 1)
    barrierCase2X1XV0LogArg (-4) (0) (791069016156248449 / 610351562500000000) (889420607 / 3125000000) (0 / 1)
  have hratio : ((0 / 1) / (889420607 / 3125000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X1XV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X1XV0_approx_upper :
    barrierWeightedComplexLogRat (15199211 / 100000000) (0 / 1) (-4) (0) (791069016156248449 / 610351562500000000) (0 / 1) <
      (-190996221123 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X1XV0_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X1 : ℝ) (barrierV2Tail.getD 0 (0, 0)) <
      (-190996221123 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X1XV0LogArg).re < _
  have he := (abs_lt.mp barrierCase2X1XV0_error).2
  have ha : ((barrierWeightedComplexLogRat (15199211 / 100000000) (0 / 1) (-4) (0) (791069016156248449 / 610351562500000000) (0 / 1) : ℚ) : ℝ) <
      (-190996221123 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X1XV0_approx_upper using 1
    norm_num
  linarith

def barrierCase2X1XV1LogArg : ℂ :=
  1 - ((Case2PointData.X1 : ℝ) : ℂ) * (barrierV2Tail.getD 1 (0, 0)).1

private theorem barrierCase2X1XV1_arg_eq :
    barrierCase2X1XV1LogArg = barrierComplex (1105761821 / 7812500000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X1XV1LogArg, Case2PointData.X1, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X1XV1_arg_regular :
    (barrierCase2X1XV1LogArg).im ≠ 0 ∨ 0 < (barrierCase2X1XV1LogArg).re := by
  rw [barrierCase2X1XV1_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X1XV1_weight_eq :
    (barrierV2Tail.getD 1 (0, 0)).2 = barrierComplex (2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X1XV1_error :
    |((barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X1XV1LogArg).re -
      ((barrierWeightedComplexLogRat (2225831 / 50000000) (0 / 1) (-6) (0) (1222709204781236041 / 953674316406250000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X1XV1_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (2225831 / 50000000) (0 / 1)
    barrierCase2X1XV1LogArg (-6) (0) (1222709204781236041 / 953674316406250000) (1105761821 / 7812500000) (0 / 1)
  have hratio : ((0 / 1) / (1105761821 / 7812500000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X1XV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X1XV1_approx_upper :
    barrierWeightedComplexLogRat (2225831 / 50000000) (0 / 1) (-6) (0) (1222709204781236041 / 953674316406250000) (0 / 1) <
      (-87038471930 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X1XV1_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X1 : ℝ) (barrierV2Tail.getD 1 (0, 0)) <
      (-87038471930 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X1XV1LogArg).re < _
  have he := (abs_lt.mp barrierCase2X1XV1_error).2
  have ha : ((barrierWeightedComplexLogRat (2225831 / 50000000) (0 / 1) (-6) (0) (1222709204781236041 / 953674316406250000) (0 / 1) : ℚ) : ℝ) <
      (-87038471930 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X1XV1_approx_upper using 1
    norm_num
  linarith

def barrierCase2X1XV2LogArg : ℂ :=
  1 - ((Case2PointData.X1 : ℝ) : ℂ) * (barrierV2Tail.getD 2 (0, 0)).1

private theorem barrierCase2X1XV2_arg_eq :
    barrierCase2X1XV2LogArg = barrierComplex (55841373323 / 31250000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X1XV2LogArg, Case2PointData.X1, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X1XV2_arg_regular :
    (barrierCase2X1XV2LogArg).im ≠ 0 ∨ 0 < (barrierCase2X1XV2LogArg).re := by
  rw [barrierCase2X1XV2_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X1XV2_weight_eq :
    (barrierV2Tail.getD 2 (0, 0)).2 = barrierComplex (1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X1XV2_error :
    |((barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X1XV2LogArg).re -
      ((barrierWeightedComplexLogRat (1272699 / 50000000) (0 / 1) (1) (0) (3118258974598656062329 / 1953125000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X1XV2_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (1272699 / 50000000) (0 / 1)
    barrierCase2X1XV2LogArg (1) (0) (3118258974598656062329 / 1953125000000000000000) (55841373323 / 31250000000) (0 / 1)
  have hratio : ((0 / 1) / (55841373323 / 31250000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X1XV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X1XV2_approx_upper :
    barrierWeightedComplexLogRat (1272699 / 50000000) (0 / 1) (1) (0) (3118258974598656062329 / 1953125000000000000000) (0 / 1) <
      (14775925325 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X1XV2_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X1 : ℝ) (barrierV2Tail.getD 2 (0, 0)) <
      (14775925325 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X1XV2LogArg).re < _
  have he := (abs_lt.mp barrierCase2X1XV2_error).2
  have ha : ((barrierWeightedComplexLogRat (1272699 / 50000000) (0 / 1) (1) (0) (3118258974598656062329 / 1953125000000000000000) (0 / 1) : ℚ) : ℝ) <
      (14775925325 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X1XV2_approx_upper using 1
    norm_num
  linarith

def barrierCase2X1XV3LogArg : ℂ :=
  1 - ((Case2PointData.X1 : ℝ) : ℂ) * (barrierV2Tail.getD 3 (0, 0)).1

private theorem barrierCase2X1XV3_arg_eq :
    barrierCase2X1XV3LogArg = barrierComplex (92476008467 / 50000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X1XV3LogArg, Case2PointData.X1, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X1XV3_arg_regular :
    (barrierCase2X1XV3LogArg).im ≠ 0 ∨ 0 < (barrierCase2X1XV3LogArg).re := by
  rw [barrierCase2X1XV3_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X1XV3_weight_eq :
    (barrierV2Tail.getD 3 (0, 0)).2 = barrierComplex (-2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X1XV3_error :
    |((barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2X1XV3LogArg).re -
      ((barrierWeightedComplexLogRat (-2466317 / 50000000) (0 / 1) (1) (0) (8551812141988655690089 / 5000000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X1XV3_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2466317 / 50000000) (0 / 1)
    barrierCase2X1XV3LogArg (1) (0) (8551812141988655690089 / 5000000000000000000000) (92476008467 / 50000000000) (0 / 1)
  have hratio : ((0 / 1) / (92476008467 / 50000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X1XV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X1XV3_approx_upper :
    barrierWeightedComplexLogRat (-2466317 / 50000000) (0 / 1) (1) (0) (8551812141988655690089 / 5000000000000000000000) (0 / 1) <
      (-30332060666 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X1XV3_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X1 : ℝ) (barrierV2Tail.getD 3 (0, 0)) <
      (-30332060666 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2X1XV3LogArg).re < _
  have he := (abs_lt.mp barrierCase2X1XV3_error).2
  have ha : ((barrierWeightedComplexLogRat (-2466317 / 50000000) (0 / 1) (1) (0) (8551812141988655690089 / 5000000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-30332060666 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X1XV3_approx_upper using 1
    norm_num
  linarith

def barrierCase2X1XV4LogArg : ℂ :=
  1 - ((Case2PointData.X1 : ℝ) : ℂ) * (barrierV2Tail.getD 4 (0, 0)).1

private theorem barrierCase2X1XV4_arg_eq :
    barrierCase2X1XV4LogArg = barrierComplex (587476265339 / 312500000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X1XV4LogArg, Case2PointData.X1, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X1XV4_arg_regular :
    (barrierCase2X1XV4LogArg).im ≠ 0 ∨ 0 < (barrierCase2X1XV4LogArg).re := by
  rw [barrierCase2X1XV4_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X1XV4_weight_eq :
    (barrierV2Tail.getD 4 (0, 0)).2 = barrierComplex (11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X1XV4_error :
    |((barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X1XV4LogArg).re -
      ((barrierWeightedComplexLogRat (11618157 / 100000000) (0 / 1) (1) (0) (345128362336659132784921 / 195312500000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X1XV4_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (11618157 / 100000000) (0 / 1)
    barrierCase2X1XV4LogArg (1) (0) (345128362336659132784921 / 195312500000000000000000) (587476265339 / 312500000000) (0 / 1)
  have hratio : ((0 / 1) / (587476265339 / 312500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X1XV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X1XV4_approx_upper :
    barrierWeightedComplexLogRat (11618157 / 100000000) (0 / 1) (1) (0) (345128362336659132784921 / 195312500000000000000000) (0 / 1) <
      (73337452368 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X1XV4_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X1 : ℝ) (barrierV2Tail.getD 4 (0, 0)) <
      (73337452368 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X1XV4LogArg).re < _
  have he := (abs_lt.mp barrierCase2X1XV4_error).2
  have ha : ((barrierWeightedComplexLogRat (11618157 / 100000000) (0 / 1) (1) (0) (345128362336659132784921 / 195312500000000000000000) (0 / 1) : ℚ) : ℝ) <
      (73337452368 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X1XV4_approx_upper using 1
    norm_num
  linarith

def barrierCase2X1XV5LogArg : ℂ :=
  1 - ((Case2PointData.X1 : ℝ) : ℂ) * (barrierV2Tail.getD 5 (0, 0)).1

private theorem barrierCase2X1XV5_arg_eq :
    barrierCase2X1XV5LogArg = barrierComplex (1 / 1) (87187596327 / 125000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X1XV5LogArg, Case2PointData.X1, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X1XV5_arg_regular :
    (barrierCase2X1XV5LogArg).im ≠ 0 ∨ 0 < (barrierCase2X1XV5LogArg).re := by
  rw [barrierCase2X1XV5_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X1XV5_weight_eq :
    (barrierV2Tail.getD 5 (0, 0)).2 = barrierComplex (13619357 / 100000000) (600749 / 3125000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X1XV5_error :
    |((barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2X1XV5LogArg).re -
      ((barrierWeightedComplexLogRat (13619357 / 100000000) (600749 / 3125000) (0) (1) (23226676953279903890929 / 15625000000000000000000) (-37812403673 / 212187596327) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X1XV5_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (13619357 / 100000000) (600749 / 3125000)
    barrierCase2X1XV5LogArg (0) (1) (23226676953279903890929 / 15625000000000000000000) (212187596327 / 125000000000) (-37812403673 / 125000000000)
  have hratio : ((-37812403673 / 125000000000) / (212187596327 / 125000000000) : ℚ) = (-37812403673 / 212187596327) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X1XV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X1XV5_approx_upper :
    barrierWeightedComplexLogRat (13619357 / 100000000) (600749 / 3125000) (0) (1) (23226676953279903890929 / 15625000000000000000000) (-37812403673 / 212187596327) <
      (-90087374639 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X1XV5_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X1 : ℝ) (barrierV2Tail.getD 5 (0, 0)) <
      (-90087374639 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2X1XV5LogArg).re < _
  have he := (abs_lt.mp barrierCase2X1XV5_error).2
  have ha : ((barrierWeightedComplexLogRat (13619357 / 100000000) (600749 / 3125000) (0) (1) (23226676953279903890929 / 15625000000000000000000) (-37812403673 / 212187596327) : ℚ) : ℝ) <
      (-90087374639 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X1XV5_approx_upper using 1
    norm_num
  linarith

def barrierCase2X1XV7LogArg : ℂ :=
  1 - ((Case2PointData.X1 : ℝ) : ℂ) * (barrierV2Tail.getD 7 (0, 0)).1

private theorem barrierCase2X1XV7_arg_eq :
    barrierCase2X1XV7LogArg = barrierComplex (1 / 1) (20120214537 / 25000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X1XV7LogArg, Case2PointData.X1, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X1XV7_arg_regular :
    (barrierCase2X1XV7LogArg).im ≠ 0 ∨ 0 < (barrierCase2X1XV7LogArg).re := by
  rw [barrierCase2X1XV7_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X1XV7_weight_eq :
    (barrierV2Tail.getD 7 (0, 0)).2 = barrierComplex (-7835271 / 50000000) (15094393 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X1XV7_error :
    |((barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2X1XV7LogArg).re -
      ((barrierWeightedComplexLogRat (-7835271 / 50000000) (15094393 / 100000000) (0) (1) (1029823033014906124369 / 625000000000000000000) (-4879785463 / 45120214537) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X1XV7_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-7835271 / 50000000) (15094393 / 100000000)
    barrierCase2X1XV7LogArg (0) (1) (1029823033014906124369 / 625000000000000000000) (45120214537 / 25000000000) (-4879785463 / 25000000000)
  have hratio : ((-4879785463 / 25000000000) / (45120214537 / 25000000000) : ℚ) = (-4879785463 / 45120214537) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X1XV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X1XV7_approx_upper :
    barrierWeightedComplexLogRat (-7835271 / 50000000) (15094393 / 100000000) (0) (1) (1029823033014906124369 / 625000000000000000000) (-4879785463 / 45120214537) <
      (-141418196713 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X1XV7_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X1 : ℝ) (barrierV2Tail.getD 7 (0, 0)) <
      (-141418196713 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2X1XV7LogArg).re < _
  have he := (abs_lt.mp barrierCase2X1XV7_error).2
  have ha : ((barrierWeightedComplexLogRat (-7835271 / 50000000) (15094393 / 100000000) (0) (1) (1029823033014906124369 / 625000000000000000000) (-4879785463 / 45120214537) : ℚ) : ℝ) <
      (-141418196713 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X1XV7_approx_upper using 1
    norm_num
  linarith

def barrierCase2X1XV9LogArg : ℂ :=
  1 - ((Case2PointData.X1 : ℝ) : ℂ) * (barrierV2Tail.getD 9 (0, 0)).1

private theorem barrierCase2X1XV9_arg_eq :
    barrierCase2X1XV9LogArg = barrierComplex (1 / 1) (426995664063 / 500000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X1XV9LogArg, Case2PointData.X1, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X1XV9_arg_regular :
    (barrierCase2X1XV9LogArg).im ≠ 0 ∨ 0 < (barrierCase2X1XV9LogArg).re := by
  rw [barrierCase2X1XV9_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X1XV9_weight_eq :
    (barrierV2Tail.getD 9 (0, 0)).2 = barrierComplex (-3346771 / 100000000) (-5956127 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X1XV9_error :
    |((barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2X1XV9LogArg).re -
      ((barrierWeightedComplexLogRat (-3346771 / 100000000) (-5956127 / 100000000) (0) (1) (432325297128602349667969 / 250000000000000000000000) (-73004335937 / 926995664063) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X1XV9_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-3346771 / 100000000) (-5956127 / 100000000)
    barrierCase2X1XV9LogArg (0) (1) (432325297128602349667969 / 250000000000000000000000) (926995664063 / 500000000000) (-73004335937 / 500000000000)
  have hratio : ((-73004335937 / 500000000000) / (926995664063 / 500000000000) : ℚ) = (-73004335937 / 926995664063) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X1XV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X1XV9_approx_upper :
    barrierWeightedComplexLogRat (-3346771 / 100000000) (-5956127 / 100000000) (0) (1) (432325297128602349667969 / 250000000000000000000000) (-73004335937 / 926995664063) <
      (32932879939 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X1XV9_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X1 : ℝ) (barrierV2Tail.getD 9 (0, 0)) <
      (32932879939 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2X1XV9LogArg).re < _
  have he := (abs_lt.mp barrierCase2X1XV9_error).2
  have ha : ((barrierWeightedComplexLogRat (-3346771 / 100000000) (-5956127 / 100000000) (0) (1) (432325297128602349667969 / 250000000000000000000000) (-73004335937 / 926995664063) : ℚ) : ℝ) <
      (32932879939 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X1XV9_approx_upper using 1
    norm_num
  linarith

def barrierCase2X1XV11LogArg : ℂ :=
  1 - ((Case2PointData.X1 : ℝ) : ℂ) * (barrierV2Tail.getD 11 (0, 0)).1

private theorem barrierCase2X1XV11_arg_eq :
    barrierCase2X1XV11LogArg = barrierComplex (1 / 1) (274976265339 / 312500000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X1XV11LogArg, Case2PointData.X1, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X1XV11_arg_regular :
    (barrierCase2X1XV11LogArg).im ≠ 0 ∨ 0 < (barrierCase2X1XV11LogArg).re := by
  rw [barrierCase2X1XV11_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X1XV11_weight_eq :
    (barrierV2Tail.getD 11 (0, 0)).2 = barrierComplex (2055213 / 200000000) (21715849 / 200000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X1XV11_error :
    |((barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2X1XV11LogArg).re -
      ((barrierWeightedComplexLogRat (2055213 / 200000000) (21715849 / 200000000) (0) (1) (173268196499784132784921 / 97656250000000000000000) (-37523734661 / 587476265339) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X1XV11_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (2055213 / 200000000) (21715849 / 200000000)
    barrierCase2X1XV11LogArg (0) (1) (173268196499784132784921 / 97656250000000000000000) (587476265339 / 312500000000) (-37523734661 / 312500000000)
  have hratio : ((-37523734661 / 312500000000) / (587476265339 / 312500000000) : ℚ) = (-37523734661 / 587476265339) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X1XV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X1XV11_approx_upper :
    barrierWeightedComplexLogRat (2055213 / 200000000) (21715849 / 200000000) (0) (1) (173268196499784132784921 / 97656250000000000000000) (-37523734661 / 587476265339) <
      (-75406010027 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X1XV11_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X1 : ℝ) (barrierV2Tail.getD 11 (0, 0)) <
      (-75406010027 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2X1XV11LogArg).re < _
  have he := (abs_lt.mp barrierCase2X1XV11_error).2
  have ha : ((barrierWeightedComplexLogRat (2055213 / 200000000) (21715849 / 200000000) (0) (1) (173268196499784132784921 / 97656250000000000000000) (-37523734661 / 587476265339) : ℚ) : ℝ) <
      (-75406010027 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X1XV11_approx_upper using 1
    norm_num
  linarith

open Case2PointData

private theorem barrierCase2X1_XP_tail_upper :
    (barrierP2Tail.map (barrierCase2XPLogTerm (X1 : ℝ))).sum <
      (-1366204345442 / 1000000000000 : ℝ) := by
  have hp : ∀ i ∈ [2, 4, 6, 8],
      barrierCase2XPLogTerm (X1 : ℝ) (barrierP2Tail.getD (i + 1) (0, 0)) =
        barrierCase2XPLogTerm (X1 : ℝ) (barrierP2Tail.getD i (0, 0)) := by
    intro i hi
    rw [barrierP2Tail_getD_pair i hi]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X1XP2_arg_regular
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X1XP4_arg_regular
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X1XP6_arg_regular
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X1XP8_arg_regular
  rw [barrierP2Tail_paired_sum _ hp]
  linarith only [barrierCase2X1XP0_log_upper,
    barrierCase2X1XP1_log_upper,
    barrierCase2X1XP2_log_upper,
    barrierCase2X1XP4_log_upper,
    barrierCase2X1XP6_log_upper,
    barrierCase2X1XP8_log_upper]

private theorem barrierCase2X1_XV_tail_upper :
    (barrierV2Tail.map (barrierCase2XVLogTerm (X1 : ℝ))).sum <
      (-768210778906 / 1000000000000 : ℝ) := by
  have hp : ∀ i ∈ [5, 7, 9, 11],
      barrierCase2XVLogTerm (X1 : ℝ) (barrierV2Tail.getD (i + 1) (0, 0)) =
        barrierCase2XVLogTerm (X1 : ℝ) (barrierV2Tail.getD i (0, 0)) := by
    intro i hi
    rw [barrierV2Tail_getD_pair i hi]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X1XV5_arg_regular
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X1XV7_arg_regular
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X1XV9_arg_regular
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X1XV11_arg_regular
  rw [barrierV2Tail_paired_sum _ hp]
  linarith only [barrierCase2X1XV0_log_upper,
    barrierCase2X1XV1_log_upper,
    barrierCase2X1XV2_log_upper,
    barrierCase2X1XV3_log_upper,
    barrierCase2X1XV4_log_upper,
    barrierCase2X1XV5_log_upper,
    barrierCase2X1XV7_log_upper,
    barrierCase2X1XV9_log_upper,
    barrierCase2X1XV11_log_upper]

private theorem barrierCase2X1_approx_upper :
    barrierCase2XApproxRat X1 (-1) (0) (0) (2235579393 / 1250000000) (4735579393 / 2500000000) (11247815222406248449 / 6250000000000000000) + (-1366204345442 / 1000000000000) + (-768210778906 / 1000000000000) <
      (-98399 / 100000 - 2 / 1000000000000000 : ℚ) := by
  unfold barrierCase2XApproxRat barrierCase2XRat
  rw [barrierCase2TP_eq_explicit, barrierCase2SV_eq_explicit]
  simp only [barrierScaledLogRat, barrierLogHRat_two_eq]
  decide +kernel

theorem barrierCase2X1_lt : barrierCase2X (X1 : ℝ) < (-98399 / 100000 : ℝ) := by
  have hx : |(X1 : ℝ)| ≤ 1 := by norm_num [X1]
  have he := (abs_lt.mp (barrierCase2X_realLog_approx_error X1 hx
    (-1) (0) (0) (2235579393 / 1250000000) (4735579393 / 2500000000) (11247815222406248449 / 6250000000000000000)
    X1_normalizations.1 X1_normalizations.2.1 X1_normalizations.2.2)).2
  have ha : ((barrierCase2XApproxRat X1 (-1) (0) (0) (2235579393 / 1250000000) (4735579393 / 2500000000) (11247815222406248449 / 6250000000000000000) : ℚ) : ℝ) +
      (-1366204345442 / 1000000000000) + (-768210778906 / 1000000000000) < (-98399 / 100000 - 2 / 1000000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X1_approx_upper using 1 <;> norm_num
  linarith only [he, ha, barrierCase2X1_XP_tail_upper, barrierCase2X1_XV_tail_upper]

end InternalCatalan

end

end OAI
