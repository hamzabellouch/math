import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX0

namespace OAI


noncomputable section
namespace InternalCatalan

def barrierCase2Y4YV0LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y4 : ℝ) : ℂ) * (barrierV2Tail.getD 0 (0, 0)).1 + (barrierV2Tail.getD 0 (0, 0)).1 ^ 2

private theorem barrierCase2Y4YV0_arg_eq :
    barrierCase2Y4YV0LogArg = barrierComplex (6199732999 / 3125000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y4YV0LogArg, Case2PointData.Y4, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y4YV0_arg_regular :
    (barrierCase2Y4YV0LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y4YV0LogArg).re := by
  rw [barrierCase2Y4YV0_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y4YV0_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2 = barrierComplex (-15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y4YV0_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2Y4YV0LogArg).re -
      ((barrierWeightedComplexLogRat (-15199211 / 100000000) (0 / 1) (1) (0) (38436689258889534001 / 19531250000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y4YV0_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-15199211 / 100000000) (0 / 1)
    barrierCase2Y4YV0LogArg (1) (0) (38436689258889534001 / 19531250000000000000) (6199732999 / 3125000000) (0 / 1)
  have hratio : ((0 / 1) / (6199732999 / 3125000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y4YV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y4YV0_approx_upper :
    barrierWeightedComplexLogRat (-15199211 / 100000000) (0 / 1) (1) (0) (38436689258889534001 / 19531250000000000000) (0 / 1) <
      (-104125530156 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y4YV0_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y4 : ℝ) (barrierV2Tail.getD 0 (0, 0)) <
      (-104125530156 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2Y4YV0LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y4YV0_error).2
  have ha : ((barrierWeightedComplexLogRat (-15199211 / 100000000) (0 / 1) (1) (0) (38436689258889534001 / 19531250000000000000) (0 / 1) : ℚ) : ℝ) <
      (-104125530156 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y4YV0_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y4YV1LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y4 : ℝ) : ℂ) * (barrierV2Tail.getD 1 (0, 0)).1 + (barrierV2Tail.getD 1 (0, 0)).1 ^ 2

private theorem barrierCase2Y4YV1_arg_eq :
    barrierCase2Y4YV1LogArg = barrierComplex (18236698997 / 7812500000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y4YV1LogArg, Case2PointData.Y4, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y4YV1_arg_regular :
    (barrierCase2Y4YV1LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y4YV1LogArg).re := by
  rw [barrierCase2Y4YV1_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y4YV1_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2 = barrierComplex (-2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y4YV1_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2Y4YV1LogArg).re -
      ((barrierWeightedComplexLogRat (-2225831 / 50000000) (0 / 1) (2) (0) (332577190307180806009 / 244140625000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y4YV1_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2225831 / 50000000) (0 / 1)
    barrierCase2Y4YV1LogArg (2) (0) (332577190307180806009 / 244140625000000000000) (18236698997 / 7812500000) (0 / 1)
  have hratio : ((0 / 1) / (18236698997 / 7812500000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y4YV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y4YV1_approx_upper :
    barrierWeightedComplexLogRat (-2225831 / 50000000) (0 / 1) (2) (0) (332577190307180806009 / 244140625000000000000) (0 / 1) <
      (-37737227439 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y4YV1_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y4 : ℝ) (barrierV2Tail.getD 1 (0, 0)) <
      (-37737227439 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2Y4YV1LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y4YV1_error).2
  have ha : ((barrierWeightedComplexLogRat (-2225831 / 50000000) (0 / 1) (2) (0) (332577190307180806009 / 244140625000000000000) (0 / 1) : ℚ) : ℝ) <
      (-37737227439 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y4YV1_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y4YV2LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y4 : ℝ) : ℂ) * (barrierV2Tail.getD 2 (0, 0)).1 + (barrierV2Tail.getD 2 (0, 0)).1 ^ 2

private theorem barrierCase2Y4YV2_arg_eq :
    barrierCase2Y4YV2LogArg = barrierComplex (43627937011 / 31250000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y4YV2LogArg, Case2PointData.Y4, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y4YV2_arg_regular :
    (barrierCase2Y4YV2LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y4YV2LogArg).re := by
  rw [barrierCase2Y4YV2_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y4YV2_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2 = barrierComplex (-1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y4YV2_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2Y4YV2LogArg).re -
      ((barrierWeightedComplexLogRat (-1272699 / 50000000) (0 / 1) (0) (0) (1903396887835783614121 / 976562500000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y4YV2_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-1272699 / 50000000) (0 / 1)
    barrierCase2Y4YV2LogArg (0) (0) (1903396887835783614121 / 976562500000000000000) (43627937011 / 31250000000) (0 / 1)
  have hratio : ((0 / 1) / (43627937011 / 31250000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y4YV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y4YV2_approx_upper :
    barrierWeightedComplexLogRat (-1272699 / 50000000) (0 / 1) (0) (0) (1903396887835783614121 / 976562500000000000000) (0 / 1) <
      (-8493441438 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y4YV2_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y4 : ℝ) (barrierV2Tail.getD 2 (0, 0)) <
      (-8493441438 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2Y4YV2LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y4YV2_error).2
  have ha : ((barrierWeightedComplexLogRat (-1272699 / 50000000) (0 / 1) (0) (0) (1903396887835783614121 / 976562500000000000000) (0 / 1) : ℚ) : ℝ) <
      (-8493441438 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y4YV2_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y4YV3LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y4 : ℝ) : ℂ) * (barrierV2Tail.getD 3 (0, 0)).1 + (barrierV2Tail.getD 3 (0, 0)).1 ^ 2

private theorem barrierCase2Y4YV3_arg_eq :
    barrierCase2Y4YV3LogArg = barrierComplex (74705073019 / 50000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y4YV3LogArg, Case2PointData.Y4, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y4YV3_arg_regular :
    (barrierCase2Y4YV3LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y4YV3LogArg).re := by
  rw [barrierCase2Y4YV3_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y4YV3_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2 = barrierComplex (2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y4YV3_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2Y4YV3LogArg).re -
      ((barrierWeightedComplexLogRat (2466317 / 50000000) (0 / 1) (1) (0) (5580847934774121774361 / 5000000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y4YV3_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (2466317 / 50000000) (0 / 1)
    barrierCase2Y4YV3LogArg (1) (0) (5580847934774121774361 / 5000000000000000000000) (74705073019 / 50000000000) (0 / 1)
  have hratio : ((0 / 1) / (74705073019 / 50000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y4YV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y4YV3_approx_upper :
    barrierWeightedComplexLogRat (2466317 / 50000000) (0 / 1) (1) (0) (5580847934774121774361 / 5000000000000000000000) (0 / 1) <
      (19805758488 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y4YV3_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y4 : ℝ) (barrierV2Tail.getD 3 (0, 0)) <
      (19805758488 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2Y4YV3LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y4YV3_error).2
  have ha : ((barrierWeightedComplexLogRat (2466317 / 50000000) (0 / 1) (1) (0) (5580847934774121774361 / 5000000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (19805758488 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y4YV3_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y4YV4LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y4 : ℝ) : ℂ) * (barrierV2Tail.getD 4 (0, 0)).1 + (barrierV2Tail.getD 4 (0, 0)).1 ^ 2

private theorem barrierCase2Y4YV4_arg_eq :
    barrierCase2Y4YV4LogArg = barrierComplex (482887841123 / 312500000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y4YV4LogArg, Case2PointData.Y4, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y4YV4_arg_regular :
    (barrierCase2Y4YV4LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y4YV4LogArg).re := by
  rw [barrierCase2Y4YV4_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y4YV4_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2 = barrierComplex (-11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y4YV4_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2Y4YV4LogArg).re -
      ((barrierWeightedComplexLogRat (-11618157 / 100000000) (0 / 1) (1) (0) (233180667104431689901129 / 195312500000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y4YV4_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-11618157 / 100000000) (0 / 1)
    barrierCase2Y4YV4LogArg (1) (0) (233180667104431689901129 / 195312500000000000000000) (482887841123 / 312500000000) (0 / 1)
  have hratio : ((0 / 1) / (482887841123 / 312500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y4YV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y4YV4_approx_upper :
    barrierWeightedComplexLogRat (-11618157 / 100000000) (0 / 1) (1) (0) (233180667104431689901129 / 195312500000000000000000) (0 / 1) <
      (-50559889185 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y4YV4_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y4 : ℝ) (barrierV2Tail.getD 4 (0, 0)) <
      (-50559889185 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2Y4YV4LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y4YV4_error).2
  have ha : ((barrierWeightedComplexLogRat (-11618157 / 100000000) (0 / 1) (1) (0) (233180667104431689901129 / 195312500000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-50559889185 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y4YV4_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y4YV5LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y4 : ℝ) : ℂ) * (barrierV2Tail.getD 5 (0, 0)).1 + (barrierV2Tail.getD 5 (0, 0)).1 ^ 2

private theorem barrierCase2Y4YV5_arg_eq :
    barrierCase2Y4YV5LogArg = barrierComplex (979 / 2500) (-41914586961 / 125000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y4YV5LogArg, Case2PointData.Y4, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y4YV5_arg_regular :
    (barrierCase2Y4YV5LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y4YV5LogArg).re := by
  rw [barrierCase2Y4YV5_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y4YV5_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2 = barrierComplex (-13619357 / 100000000) (-600749 / 3125000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y4YV5_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2Y4YV5LogArg).re -
      ((barrierWeightedComplexLogRat (-13619357 / 100000000) (-600749 / 3125000) (-2) (-1) (4152935100111231215521 / 3906250000000000000000) (7035413039 / 90864586961) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y4YV5_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-13619357 / 100000000) (-600749 / 3125000)
    barrierCase2Y4YV5LogArg (-2) (-1) (4152935100111231215521 / 3906250000000000000000) (90864586961 / 125000000000) (7035413039 / 125000000000)
  have hratio : ((7035413039 / 125000000000) / (90864586961 / 125000000000) : ℚ) = (7035413039 / 90864586961) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y4YV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y4YV5_approx_upper :
    barrierWeightedComplexLogRat (-13619357 / 100000000) (-600749 / 3125000) (-2) (-1) (4152935100111231215521 / 3906250000000000000000) (7035413039 / 90864586961) <
      (-45897589833 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y4YV5_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y4 : ℝ) (barrierV2Tail.getD 5 (0, 0)) <
      (-45897589833 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2Y4YV5LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y4YV5_error).2
  have ha : ((barrierWeightedComplexLogRat (-13619357 / 100000000) (-600749 / 3125000) (-2) (-1) (4152935100111231215521 / 3906250000000000000000) (7035413039 / 90864586961) : ℚ) : ℝ) <
      (-45897589833 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y4YV5_approx_upper using 1
    norm_num
  linarith






def barrierCase2Y4YV7LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y4 : ℝ) : ℂ) * (barrierV2Tail.getD 7 (0, 0)).1 + (barrierV2Tail.getD 7 (0, 0)).1 ^ 2

private theorem barrierCase2Y4YV7_arg_eq :
    barrierCase2Y4YV7LogArg = barrierComplex (19 / 100) (-9672596991 / 25000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y4YV7LogArg, Case2PointData.Y4, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y4YV7_arg_regular :
    (barrierCase2Y4YV7LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y4YV7LogArg).re := by
  rw [barrierCase2Y4YV7_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y4YV7_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2 = barrierComplex (7835271 / 50000000) (-15094393 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y4YV7_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2Y4YV7LogArg).re -
      ((barrierWeightedComplexLogRat (7835271 / 50000000) (-15094393 / 100000000) (-3) (-1) (116121632550302254081 / 78125000000000000000) (-4922596991 / 14422596991) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y4YV7_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (7835271 / 50000000) (-15094393 / 100000000)
    barrierCase2Y4YV7LogArg (-3) (-1) (116121632550302254081 / 78125000000000000000) (14422596991 / 25000000000) (-4922596991 / 25000000000)
  have hratio : ((-4922596991 / 25000000000) / (14422596991 / 25000000000) : ℚ) = (-4922596991 / 14422596991) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y4YV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y4YV7_approx_upper :
    barrierWeightedComplexLogRat (7835271 / 50000000) (-15094393 / 100000000) (-3) (-1) (116121632550302254081 / 78125000000000000000) (-4922596991 / 14422596991) <
      (-300075091122 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y4YV7_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y4 : ℝ) (barrierV2Tail.getD 7 (0, 0)) <
      (-300075091122 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2Y4YV7LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y4YV7_error).2
  have ha : ((barrierWeightedComplexLogRat (7835271 / 50000000) (-15094393 / 100000000) (-3) (-1) (116121632550302254081 / 78125000000000000000) (-4922596991 / 14422596991) : ℚ) : ℝ) <
      (-300075091122 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y4YV7_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y4YV9LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y4 : ℝ) : ℂ) * (barrierV2Tail.getD 9 (0, 0)).1 + (barrierV2Tail.getD 9 (0, 0)).1 ^ 2

private theorem barrierCase2Y4YV9_arg_eq :
    barrierCase2Y4YV9LogArg = barrierComplex (3519 / 40000) (-205274002809 / 500000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y4YV9LogArg, Case2PointData.Y4, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y4YV9_arg_regular :
    (barrierCase2Y4YV9LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y4YV9LogArg).re := by
  rw [barrierCase2Y4YV9_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y4YV9_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2 = barrierComplex (3346771 / 100000000) (5956127 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y4YV9_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2Y4YV9LogArg).re -
      ((barrierWeightedComplexLogRat (3346771 / 100000000) (5956127 / 100000000) (-3) (-2) (44072316385479339890481 / 31250000000000000000000) (14662500000 / 68424667603) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y4YV9_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (3346771 / 100000000) (5956127 / 100000000)
    barrierCase2Y4YV9LogArg (-3) (-2) (44072316385479339890481 / 31250000000000000000000) (205274002809 / 250000000000) (3519 / 20000)
  have hratio : ((3519 / 20000) / (205274002809 / 250000000000) : ℚ) = (14662500000 / 68424667603) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y4YV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y4YV9_approx_upper :
    barrierWeightedComplexLogRat (3346771 / 100000000) (5956127 / 100000000) (-3) (-2) (44072316385479339890481 / 31250000000000000000000) (14662500000 / 68424667603) <
      (51941812502 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y4YV9_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y4 : ℝ) (barrierV2Tail.getD 9 (0, 0)) <
      (51941812502 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2Y4YV9LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y4YV9_error).2
  have ha : ((barrierWeightedComplexLogRat (3346771 / 100000000) (5956127 / 100000000) (-3) (-2) (44072316385479339890481 / 31250000000000000000000) (14662500000 / 68424667603) : ℚ) : ℝ) <
      (51941812502 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y4YV9_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y4YV11LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y4 : ℝ) : ℂ) * (barrierV2Tail.getD 11 (0, 0)).1 + (barrierV2Tail.getD 11 (0, 0)).1 ^ 2

private theorem barrierCase2Y4YV11_arg_eq :
    barrierCase2Y4YV11LogArg = barrierComplex (496 / 15625) (-132192158877 / 312500000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y4YV11LogArg, Case2PointData.Y4, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y4YV11_arg_regular :
    (barrierCase2Y4YV11LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y4YV11LogArg).re := by
  rw [barrierCase2Y4YV11_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y4YV11_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2 = barrierComplex (-2055213 / 200000000) (-21715849 / 200000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y4YV11_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2Y4YV11LogArg).re -
      ((barrierWeightedComplexLogRat (-2055213 / 200000000) (-21715849 / 200000000) (-3) (-2) (17573173268562009901129 / 12207031250000000000000) (9920000000 / 132192158877) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y4YV11_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2055213 / 200000000) (-21715849 / 200000000)
    barrierCase2Y4YV11LogArg (-3) (-2) (17573173268562009901129 / 12207031250000000000000) (132192158877 / 156250000000) (992 / 15625)
  have hratio : ((992 / 15625) / (132192158877 / 156250000000) : ℚ) = (9920000000 / 132192158877) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y4YV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y4YV11_approx_upper :
    barrierWeightedComplexLogRat (-2055213 / 200000000) (-21715849 / 200000000) (-3) (-2) (17573173268562009901129 / 12207031250000000000000) (9920000000 / 132192158877) <
      (-153610951610 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y4YV11_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y4 : ℝ) (barrierV2Tail.getD 11 (0, 0)) <
      (-153610951610 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2Y4YV11LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y4YV11_error).2
  have ha : ((barrierWeightedComplexLogRat (-2055213 / 200000000) (-21715849 / 200000000) (-3) (-2) (17573173268562009901129 / 12207031250000000000000) (9920000000 / 132192158877) : ℚ) : ℝ) <
      (-153610951610 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y4YV11_approx_upper using 1
    norm_num
  linarith





open Case2PointData

private theorem barrierCase2Y4_YV_tail_upper :
    (barrierV2Tail.map (barrierCase2YVLogTerm (Y4 : ℝ))).sum <
      (-1076393969856 / 1000000000000 : ℝ) := by
  have hp : ∀ i ∈ [5, 7, 9, 11],
      barrierCase2YVLogTerm (Y4 : ℝ) (barrierV2Tail.getD (i + 1) (0, 0)) =
        barrierCase2YVLogTerm (Y4 : ℝ) (barrierV2Tail.getD i (0, 0)) := by
    intro i hi
    rw [barrierV2Tail_getD_pair i hi]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y4YV5_arg_regular
    · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y4YV7_arg_regular
    · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y4YV9_arg_regular
    · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y4YV11_arg_regular
  rw [barrierV2Tail_paired_sum _ hp]
  linarith only [barrierCase2Y4YV0_log_upper,
    barrierCase2Y4YV1_log_upper,
    barrierCase2Y4YV2_log_upper,
    barrierCase2Y4YV3_log_upper,
    barrierCase2Y4YV4_log_upper,
    barrierCase2Y4YV5_log_upper,
    barrierCase2Y4YV7_log_upper,
    barrierCase2Y4YV9_log_upper,
    barrierCase2Y4YV11_log_upper]

private theorem barrierCase2Y4_approx_upper :
    barrierCase2YApproxRat Y4 (-3) (-1) (1074732999 / 625000000) (3925267001 / 2500000000) + (-1076393969856 / 1000000000000) <
      (-160890 / 100000 - 1 / 1000000000000000 : ℚ) := by
  unfold barrierCase2YApproxRat barrierCase2YRat
  rw [barrierCase2TV_eq_explicit]
  simp only [barrierScaledLogRat, barrierLogHRat_two_eq]
  decide +kernel

theorem barrierCase2Y4_lt : barrierCase2Y (Y4 : ℝ) < (-160890 / 100000 : ℝ) := by
  have hx : |(Y4 : ℝ)| ≤ 1 := by norm_num [Y4]
  have he := (abs_lt.mp (barrierCase2Y_realLog_approx_error Y4 hx
    (-3) (-1) (1074732999 / 625000000) (3925267001 / 2500000000)
    Y4_normalizations.1 Y4_normalizations.2)).2
  have ha : ((barrierCase2YApproxRat Y4 (-3) (-1) (1074732999 / 625000000) (3925267001 / 2500000000) : ℚ) : ℝ) +
      (-1076393969856 / 1000000000000) < (-160890 / 100000 - 1 / 1000000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y4_approx_upper using 1 <;> norm_num
  linarith only [he, ha, barrierCase2Y4_YV_tail_upper]

end InternalCatalan

end

end OAI
