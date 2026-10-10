import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX0

namespace OAI


noncomputable section
namespace InternalCatalan

def barrierCase2Y8YV0LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y8 : ℝ) : ℂ) * (barrierV2Tail.getD 0 (0, 0)).1 + (barrierV2Tail.getD 0 (0, 0)).1 ^ 2

private theorem barrierCase2Y8YV0_arg_eq :
    barrierCase2Y8YV0LogArg = barrierComplex (17051929373 / 6250000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y8YV0LogArg, Case2PointData.Y8, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y8YV0_arg_regular :
    (barrierCase2Y8YV0LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y8YV0LogArg).re := by
  rw [barrierCase2Y8YV0_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y8YV0_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2 = barrierComplex (-15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y8YV0_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2Y8YV0LogArg).re -
      ((barrierWeightedComplexLogRat (-15199211 / 100000000) (0 / 1) (2) (0) (290768295341780173129 / 156250000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y8YV0_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-15199211 / 100000000) (0 / 1)
    barrierCase2Y8YV0LogArg (2) (0) (290768295341780173129 / 156250000000000000000) (17051929373 / 6250000000) (0 / 1)
  have hratio : ((0 / 1) / (17051929373 / 6250000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y8YV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y8YV0_approx_upper :
    barrierWeightedComplexLogRat (-15199211 / 100000000) (0 / 1) (2) (0) (290768295341780173129 / 156250000000000000000) (0 / 1) <
      (-152551728728 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y8YV0_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y8 : ℝ) (barrierV2Tail.getD 0 (0, 0)) <
      (-152551728728 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2Y8YV0LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y8YV0_error).2
  have ha : ((barrierWeightedComplexLogRat (-15199211 / 100000000) (0 / 1) (2) (0) (290768295341780173129 / 156250000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-152551728728 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y8YV0_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y8YV1LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y8 : ℝ) : ℂ) * (barrierV2Tail.getD 1 (0, 0)).1 + (barrierV2Tail.getD 1 (0, 0)).1 ^ 2

private theorem barrierCase2Y8YV1_arg_eq :
    barrierCase2Y8YV1LogArg = barrierComplex (50430788119 / 15625000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y8YV1LogArg, Case2PointData.Y8, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y8YV1_arg_regular :
    (barrierCase2Y8YV1LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y8YV1LogArg).re := by
  rw [barrierCase2Y8YV1_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y8YV1_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2 = barrierComplex (-2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y8YV1_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2Y8YV1LogArg).re -
      ((barrierWeightedComplexLogRat (-2225831 / 50000000) (0 / 1) (3) (0) (2543264390303471558161 / 1953125000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y8YV1_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2225831 / 50000000) (0 / 1)
    barrierCase2Y8YV1LogArg (3) (0) (2543264390303471558161 / 1953125000000000000000) (50430788119 / 15625000000) (0 / 1)
  have hratio : ((0 / 1) / (50430788119 / 15625000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y8YV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y8YV1_approx_upper :
    barrierWeightedComplexLogRat (-2225831 / 50000000) (0 / 1) (3) (0) (2543264390303471558161 / 1953125000000000000000) (0 / 1) <
      (-52161444386 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y8YV1_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y8 : ℝ) (barrierV2Tail.getD 1 (0, 0)) <
      (-52161444386 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2Y8YV1LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y8YV1_error).2
  have ha : ((barrierWeightedComplexLogRat (-2225831 / 50000000) (0 / 1) (3) (0) (2543264390303471558161 / 1953125000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-52161444386 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y8YV1_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y8YV2LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y8 : ℝ) : ℂ) * (barrierV2Tail.getD 2 (0, 0)).1 + (barrierV2Tail.getD 2 (0, 0)).1 ^ 2

private theorem barrierCase2Y8YV2_arg_eq :
    barrierCase2Y8YV2LogArg = barrierComplex (36078776897 / 62500000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y8YV2LogArg, Case2PointData.Y8, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y8YV2_arg_regular :
    (barrierCase2Y8YV2LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y8YV2LogArg).re := by
  rw [barrierCase2Y8YV2_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y8YV2_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2 = barrierComplex (-1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y8YV2_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2Y8YV2LogArg).re -
      ((barrierWeightedComplexLogRat (-1272699 / 50000000) (0 / 1) (-2) (0) (1301678142383500948609 / 976562500000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y8YV2_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-1272699 / 50000000) (0 / 1)
    barrierCase2Y8YV2LogArg (-2) (0) (1301678142383500948609 / 976562500000000000000) (36078776897 / 62500000000) (0 / 1)
  have hratio : ((0 / 1) / (36078776897 / 62500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y8YV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y8YV2_approx_upper :
    barrierWeightedComplexLogRat (-1272699 / 50000000) (0 / 1) (-2) (0) (1301678142383500948609 / 976562500000000000000) (0 / 1) <
      (13985988699 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y8YV2_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y8 : ℝ) (barrierV2Tail.getD 2 (0, 0)) <
      (13985988699 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2Y8YV2LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y8YV2_error).2
  have ha : ((barrierWeightedComplexLogRat (-1272699 / 50000000) (0 / 1) (-2) (0) (1301678142383500948609 / 976562500000000000000) (0 / 1) : ℚ) : ℝ) <
      (13985988699 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y8YV2_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y8YV3LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y8 : ℝ) : ℂ) * (barrierV2Tail.getD 3 (0, 0)).1 + (barrierV2Tail.getD 3 (0, 0)).1 ^ 2

private theorem barrierCase2Y8YV3_arg_eq :
    barrierCase2Y8YV3LogArg = barrierComplex (61013341913 / 100000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y8YV3LogArg, Case2PointData.Y8, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y8YV3_arg_regular :
    (barrierCase2Y8YV3LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y8YV3LogArg).re := by
  rw [barrierCase2Y8YV3_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y8YV3_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2 = barrierComplex (2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y8YV3_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2Y8YV3LogArg).re -
      ((barrierWeightedComplexLogRat (2466317 / 50000000) (0 / 1) (-2) (0) (3722627891392642499569 / 2500000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y8YV3_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (2466317 / 50000000) (0 / 1)
    barrierCase2Y8YV3LogArg (-2) (0) (3722627891392642499569 / 2500000000000000000000) (61013341913 / 100000000000) (0 / 1)
  have hratio : ((0 / 1) / (61013341913 / 100000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y8YV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y8YV3_approx_upper :
    barrierWeightedComplexLogRat (2466317 / 50000000) (0 / 1) (-2) (0) (3722627891392642499569 / 2500000000000000000000) (0 / 1) <
      (-24371040957 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y8YV3_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y8 : ℝ) (barrierV2Tail.getD 3 (0, 0)) <
      (-24371040957 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2Y8YV3LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y8YV3_error).2
  have ha : ((barrierWeightedComplexLogRat (2466317 / 50000000) (0 / 1) (-2) (0) (3722627891392642499569 / 2500000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-24371040957 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y8YV3_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y8YV4LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y8 : ℝ) : ℂ) * (barrierV2Tail.getD 4 (0, 0)).1 + (barrierV2Tail.getD 4 (0, 0)).1 ^ 2

private theorem barrierCase2Y8YV4_arg_eq :
    barrierCase2Y8YV4LogArg = barrierComplex (393522687121 / 625000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y8YV4LogArg, Case2PointData.Y8, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y8YV4_arg_regular :
    (barrierCase2Y8YV4LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y8YV4LogArg).re := by
  rw [barrierCase2Y8YV4_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y8YV4_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2 = barrierComplex (-11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y8YV4_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2Y8YV4LogArg).re -
      ((barrierWeightedComplexLogRat (-11618157 / 100000000) (0 / 1) (-2) (0) (154860105278932459268641 / 97656250000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y8YV4_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-11618157 / 100000000) (0 / 1)
    barrierCase2Y8YV4LogArg (-2) (0) (154860105278932459268641 / 97656250000000000000000) (393522687121 / 625000000000) (0 / 1)
  have hratio : ((0 / 1) / (393522687121 / 625000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y8YV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y8YV4_approx_upper :
    barrierWeightedComplexLogRat (-11618157 / 100000000) (0 / 1) (-2) (0) (154860105278932459268641 / 97656250000000000000000) (0 / 1) <
      (53747096378 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y8YV4_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y8 : ℝ) (barrierV2Tail.getD 4 (0, 0)) <
      (53747096378 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2Y8YV4LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y8YV4_error).2
  have ha : ((barrierWeightedComplexLogRat (-11618157 / 100000000) (0 / 1) (-2) (0) (154860105278932459268641 / 97656250000000000000000) (0 / 1) : ℚ) : ℝ) <
      (53747096378 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y8YV4_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y8YV5LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y8 : ℝ) : ℂ) * (barrierV2Tail.getD 5 (0, 0)).1 + (barrierV2Tail.getD 5 (0, 0)).1 ^ 2

private theorem barrierCase2Y8YV5_arg_eq :
    barrierCase2Y8YV5LogArg = barrierComplex (979 / 2500) (-265275245547 / 250000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y8YV5LogArg, Case2PointData.Y8, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y8YV5_arg_regular :
    (barrierCase2Y8YV5LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y8YV5LogArg).re := by
  rw [barrierCase2Y8YV5_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y8YV5_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2 = barrierComplex (-13619357 / 100000000) (-600749 / 3125000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y8YV5_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2Y8YV5LogArg).re -
      ((barrierWeightedComplexLogRat (-13619357 / 100000000) (-600749 / 3125000) (0) (-1) (79955365900021143329209 / 62500000000000000000000) (-167375245547 / 363175245547) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y8YV5_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-13619357 / 100000000) (-600749 / 3125000)
    barrierCase2Y8YV5LogArg (0) (-1) (79955365900021143329209 / 62500000000000000000000) (363175245547 / 250000000000) (-167375245547 / 250000000000)
  have hratio : ((-167375245547 / 250000000000) / (363175245547 / 250000000000) : ℚ) = (-167375245547 / 363175245547) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y8YV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y8YV5_approx_upper :
    barrierWeightedComplexLogRat (-13619357 / 100000000) (-600749 / 3125000) (0) (-1) (79955365900021143329209 / 62500000000000000000000) (-167375245547 / 363175245547) <
      (-250776452386 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y8YV5_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y8 : ℝ) (barrierV2Tail.getD 5 (0, 0)) <
      (-250776452386 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2Y8YV5LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y8YV5_error).2
  have ha : ((barrierWeightedComplexLogRat (-13619357 / 100000000) (-600749 / 3125000) (0) (-1) (79955365900021143329209 / 62500000000000000000000) (-167375245547 / 363175245547) : ℚ) : ℝ) <
      (-250776452386 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y8YV5_approx_upper using 1
    norm_num
  linarith






def barrierCase2Y8YV7LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y8 : ℝ) : ℂ) * (barrierV2Tail.getD 7 (0, 0)).1 + (barrierV2Tail.getD 7 (0, 0)).1 ^ 2

private theorem barrierCase2Y8YV7_arg_eq :
    barrierCase2Y8YV7LogArg = barrierComplex (19 / 100) (-61217364357 / 50000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y8YV7LogArg, Case2PointData.Y8, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y8YV7_arg_regular :
    (barrierCase2Y8YV7LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y8YV7LogArg).re := by
  rw [barrierCase2Y8YV7_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y8YV7_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2 = barrierComplex (7835271 / 50000000) (-15094393 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y8YV7_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2Y8YV7LogArg).re -
      ((barrierWeightedComplexLogRat (7835271 / 50000000) (-15094393 / 100000000) (0) (-2) (3837815698817694023449 / 2500000000000000000000) (9500000000 / 61217364357) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y8YV7_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (7835271 / 50000000) (-15094393 / 100000000)
    barrierCase2Y8YV7LogArg (0) (-2) (3837815698817694023449 / 2500000000000000000000) (61217364357 / 25000000000) (19 / 50)
  have hratio : ((19 / 50) / (61217364357 / 25000000000) : ℚ) = (9500000000 / 61217364357) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y8YV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y8YV7_approx_upper :
    barrierWeightedComplexLogRat (7835271 / 50000000) (-15094393 / 100000000) (0) (-2) (3837815698817694023449 / 2500000000000000000000) (9500000000 / 61217364357) <
      (-180280380946 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y8YV7_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y8 : ℝ) (barrierV2Tail.getD 7 (0, 0)) <
      (-180280380946 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2Y8YV7LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y8YV7_error).2
  have ha : ((barrierWeightedComplexLogRat (7835271 / 50000000) (-15094393 / 100000000) (0) (-2) (3837815698817694023449 / 2500000000000000000000) (9500000000 / 61217364357) : ℚ) : ℝ) <
      (-180280380946 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y8YV7_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y8YV9LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y8 : ℝ) : ℂ) * (barrierV2Tail.getD 9 (0, 0)).1 + (barrierV2Tail.getD 9 (0, 0)).1 ^ 2

private theorem barrierCase2Y8YV9_arg_eq :
    barrierCase2Y8YV9LogArg = barrierComplex (3519 / 40000) (-1299168510243 / 1000000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y8YV9LogArg, Case2PointData.Y8, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y8YV9_arg_regular :
    (barrierCase2Y8YV9LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y8YV9LogArg).re := by
  rw [barrierCase2Y8YV9_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y8YV9_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2 = barrierComplex (3346771 / 100000000) (5956127 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y8YV9_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2Y8YV9LogArg).re -
      ((barrierWeightedComplexLogRat (3346771 / 100000000) (5956127 / 100000000) (0) (-2) (1695578418632015995919049 / 1000000000000000000000000) (29325000000 / 433056170081) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y8YV9_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (3346771 / 100000000) (5956127 / 100000000)
    barrierCase2Y8YV9LogArg (0) (-2) (1695578418632015995919049 / 1000000000000000000000000) (1299168510243 / 500000000000) (3519 / 20000)
  have hratio : ((3519 / 20000) / (1299168510243 / 500000000000) : ℚ) = (29325000000 / 433056170081) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y8YV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y8YV9_approx_upper :
    barrierWeightedComplexLogRat (3346771 / 100000000) (5956127 / 100000000) (0) (-2) (1695578418632015995919049 / 1000000000000000000000000) (29325000000 / 433056170081) <
      (98367373908 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y8YV9_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y8 : ℝ) (barrierV2Tail.getD 9 (0, 0)) <
      (98367373908 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2Y8YV9LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y8YV9_error).2
  have ha : ((barrierWeightedComplexLogRat (3346771 / 100000000) (5956127 / 100000000) (0) (-2) (1695578418632015995919049 / 1000000000000000000000000) (29325000000 / 433056170081) : ℚ) : ℝ) <
      (98367373908 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y8YV9_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y8YV11LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y8 : ℝ) : ℂ) * (barrierV2Tail.getD 11 (0, 0)).1 + (barrierV2Tail.getD 11 (0, 0)).1 ^ 2

private theorem barrierCase2Y8YV11_arg_eq :
    barrierCase2Y8YV11LogArg = barrierComplex (496 / 15625) (-836637312879 / 625000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y8YV11LogArg, Case2PointData.Y8, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y8YV11_arg_regular :
    (barrierCase2Y8YV11LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y8YV11LogArg).re := by
  rw [barrierCase2Y8YV11_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y8YV11_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2 = barrierComplex (-2055213 / 200000000) (-21715849 / 200000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y8YV11_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2Y8YV11LogArg).re -
      ((barrierWeightedComplexLogRat (-2055213 / 200000000) (-21715849 / 200000000) (0) (-2) (700355618901393739268641 / 390625000000000000000000) (19840000000 / 836637312879) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y8YV11_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2055213 / 200000000) (-21715849 / 200000000)
    barrierCase2Y8YV11LogArg (0) (-2) (700355618901393739268641 / 390625000000000000000000) (836637312879 / 312500000000) (992 / 15625)
  have hratio : ((992 / 15625) / (836637312879 / 312500000000) : ℚ) = (19840000000 / 836637312879) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y8YV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y8YV11_approx_upper :
    barrierWeightedComplexLogRat (-2055213 / 200000000) (-21715849 / 200000000) (0) (-2) (700355618901393739268641 / 390625000000000000000000) (19840000000 / 836637312879) <
      (-170981305713 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y8YV11_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y8 : ℝ) (barrierV2Tail.getD 11 (0, 0)) <
      (-170981305713 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2Y8YV11LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y8YV11_error).2
  have ha : ((barrierWeightedComplexLogRat (-2055213 / 200000000) (-21715849 / 200000000) (0) (-2) (700355618901393739268641 / 390625000000000000000000) (19840000000 / 836637312879) : ℚ) : ℝ) <
      (-170981305713 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y8YV11_approx_upper using 1
    norm_num
  linarith





open Case2PointData

private theorem barrierCase2Y8_YV_tail_upper :
    (barrierV2Tail.map (barrierCase2YVLogTerm (Y8 : ℝ))).sum <
      (-1168692659268 / 1000000000000 : ℝ) := by
  have hp : ∀ i ∈ [5, 7, 9, 11],
      barrierCase2YVLogTerm (Y8 : ℝ) (barrierV2Tail.getD (i + 1) (0, 0)) =
        barrierCase2YVLogTerm (Y8 : ℝ) (barrierV2Tail.getD i (0, 0)) := by
    intro i hi
    rw [barrierV2Tail_getD_pair i hi]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y8YV5_arg_regular
    · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y8YV7_arg_regular
    · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y8YV9_arg_regular
    · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y8YV11_arg_regular
  rw [barrierV2Tail_paired_sum _ hp]
  linarith only [barrierCase2Y8YV0_log_upper,
    barrierCase2Y8YV1_log_upper,
    barrierCase2Y8YV2_log_upper,
    barrierCase2Y8YV3_log_upper,
    barrierCase2Y8YV4_log_upper,
    barrierCase2Y8YV5_log_upper,
    barrierCase2Y8YV7_log_upper,
    barrierCase2Y8YV9_log_upper,
    barrierCase2Y8YV11_log_upper]

private theorem barrierCase2Y8_approx_upper :
    barrierCase2YApproxRat Y8 (-1) (-2) (6801929373 / 5000000000) (3198070627 / 2500000000) + (-1168692659268 / 1000000000000) <
      (-160890 / 100000 - 1 / 1000000000000000 : ℚ) := by
  unfold barrierCase2YApproxRat barrierCase2YRat
  rw [barrierCase2TV_eq_explicit]
  simp only [barrierScaledLogRat, barrierLogHRat_two_eq]
  decide +kernel

theorem barrierCase2Y8_lt : barrierCase2Y (Y8 : ℝ) < (-160890 / 100000 : ℝ) := by
  have hx : |(Y8 : ℝ)| ≤ 1 := by norm_num [Y8]
  have he := (abs_lt.mp (barrierCase2Y_realLog_approx_error Y8 hx
    (-1) (-2) (6801929373 / 5000000000) (3198070627 / 2500000000)
    Y8_normalizations.1 Y8_normalizations.2)).2
  have ha : ((barrierCase2YApproxRat Y8 (-1) (-2) (6801929373 / 5000000000) (3198070627 / 2500000000) : ℚ) : ℝ) +
      (-1168692659268 / 1000000000000) < (-160890 / 100000 - 1 / 1000000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y8_approx_upper using 1 <;> norm_num
  linarith only [he, ha, barrierCase2Y8_YV_tail_upper]

end InternalCatalan

end

end OAI
