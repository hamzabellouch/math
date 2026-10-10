import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX0

namespace OAI


noncomputable section
namespace InternalCatalan

def barrierCase2Y1YV0LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y1 : ℝ) : ℂ) * (barrierV2Tail.getD 0 (0, 0)).1 + (barrierV2Tail.getD 0 (0, 0)).1 ^ 2

private theorem barrierCase2Y1YV0_arg_eq :
    barrierCase2Y1YV0LogArg = barrierComplex (5290324703 / 3125000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y1YV0LogArg, Case2PointData.Y1, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y1YV0_arg_regular :
    (barrierCase2Y1YV0LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y1YV0LogArg).re := by
  rw [barrierCase2Y1YV0_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y1YV0_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2 = barrierComplex (-15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y1YV0_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2Y1YV0LogArg).re -
      ((barrierWeightedComplexLogRat (-15199211 / 100000000) (0 / 1) (1) (0) (27987535463172038209 / 19531250000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y1YV0_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-15199211 / 100000000) (0 / 1)
    barrierCase2Y1YV0LogArg (1) (0) (27987535463172038209 / 19531250000000000000) (5290324703 / 3125000000) (0 / 1)
  have hratio : ((0 / 1) / (5290324703 / 3125000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y1YV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y1YV0_approx_upper :
    barrierWeightedComplexLogRat (-15199211 / 100000000) (0 / 1) (1) (0) (27987535463172038209 / 19531250000000000000) (0 / 1) <
      (-80015538227 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y1YV0_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y1 : ℝ) (barrierV2Tail.getD 0 (0, 0)) <
      (-80015538227 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2Y1YV0LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y1YV0_error).2
  have ha : ((barrierWeightedComplexLogRat (-15199211 / 100000000) (0 / 1) (1) (0) (27987535463172038209 / 19531250000000000000) (0 / 1) : ℚ) : ℝ) <
      (-80015538227 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y1YV0_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y1YV1LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y1 : ℝ) : ℂ) * (barrierV2Tail.getD 1 (0, 0)).1 + (barrierV2Tail.getD 1 (0, 0)).1 ^ 2

private theorem barrierCase2Y1YV1_arg_eq :
    barrierCase2Y1YV1LogArg = barrierComplex (15508474109 / 7812500000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y1YV1LogArg, Case2PointData.Y1, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y1YV1_arg_regular :
    (barrierCase2Y1YV1LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y1YV1LogArg).re := by
  rw [barrierCase2Y1YV1_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y1YV1_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2 = barrierComplex (-2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y1YV1_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2Y1YV1LogArg).re -
      ((barrierWeightedComplexLogRat (-2225831 / 50000000) (0 / 1) (1) (0) (240512769189523343881 / 122070312500000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y1YV1_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2225831 / 50000000) (0 / 1)
    barrierCase2Y1YV1LogArg (1) (0) (240512769189523343881 / 122070312500000000000) (15508474109 / 7812500000) (0 / 1)
  have hratio : ((0 / 1) / (15508474109 / 7812500000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y1YV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y1YV1_approx_upper :
    barrierWeightedComplexLogRat (-2225831 / 50000000) (0 / 1) (1) (0) (240512769189523343881 / 122070312500000000000) (0 / 1) <
      (-30523335834 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y1YV1_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y1 : ℝ) (barrierV2Tail.getD 1 (0, 0)) <
      (-30523335834 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2Y1YV1LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y1YV1_error).2
  have ha : ((barrierWeightedComplexLogRat (-2225831 / 50000000) (0 / 1) (1) (0) (240512769189523343881 / 122070312500000000000) (0 / 1) : ℚ) : ℝ) <
      (-30523335834 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y1YV1_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y1YV2LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y1 : ℝ) : ℂ) * (barrierV2Tail.getD 2 (0, 0)).1 + (barrierV2Tail.getD 2 (0, 0)).1 ^ 2

private theorem barrierCase2Y1YV2_arg_eq :
    barrierCase2Y1YV2LogArg = barrierComplex (53631428267 / 31250000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y1YV2LogArg, Case2PointData.Y1, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y1YV2_arg_regular :
    (barrierCase2Y1YV2LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y1YV2LogArg).re := by
  rw [barrierCase2Y1YV2_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y1YV2_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2 = barrierComplex (-1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y1YV2_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2Y1YV2LogArg).re -
      ((barrierWeightedComplexLogRat (-1272699 / 50000000) (0 / 1) (1) (0) (2876330097958366623289 / 1953125000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y1YV2_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-1272699 / 50000000) (0 / 1)
    barrierCase2Y1YV2LogArg (1) (0) (2876330097958366623289 / 1953125000000000000000) (53631428267 / 31250000000) (0 / 1)
  have hratio : ((0 / 1) / (53631428267 / 31250000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y1YV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y1YV2_approx_upper :
    barrierWeightedComplexLogRat (-1272699 / 50000000) (0 / 1) (1) (0) (2876330097958366623289 / 1953125000000000000000) (0 / 1) <
      (-13748098509 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y1YV2_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y1 : ℝ) (barrierV2Tail.getD 2 (0, 0)) <
      (-13748098509 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2Y1YV2LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y1YV2_error).2
  have ha : ((barrierWeightedComplexLogRat (-1272699 / 50000000) (0 / 1) (1) (0) (2876330097958366623289 / 1953125000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-13748098509 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y1YV2_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y1YV3LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y1 : ℝ) : ℂ) * (barrierV2Tail.getD 3 (0, 0)).1 + (barrierV2Tail.getD 3 (0, 0)).1 ^ 2

private theorem barrierCase2Y1YV3_arg_eq :
    barrierCase2Y1YV3LogArg = barrierComplex (91983830643 / 50000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y1YV3LogArg, Case2PointData.Y1, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y1YV3_arg_regular :
    (barrierCase2Y1YV3LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y1YV3LogArg).re := by
  rw [barrierCase2Y1YV3_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y1YV3_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2 = barrierComplex (2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y1YV3_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2Y1YV3LogArg).re -
      ((barrierWeightedComplexLogRat (2466317 / 50000000) (0 / 1) (1) (0) (8461025099760105793449 / 5000000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y1YV3_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (2466317 / 50000000) (0 / 1)
    barrierCase2Y1YV3LogArg (1) (0) (8461025099760105793449 / 5000000000000000000000) (91983830643 / 50000000000) (0 / 1)
  have hratio : ((0 / 1) / (91983830643 / 50000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y1YV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y1YV3_approx_upper :
    barrierWeightedComplexLogRat (2466317 / 50000000) (0 / 1) (1) (0) (8461025099760105793449 / 5000000000000000000000) (0 / 1) <
      (30068833850 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y1YV3_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y1 : ℝ) (barrierV2Tail.getD 3 (0, 0)) <
      (30068833850 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2Y1YV3LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y1YV3_error).2
  have ha : ((barrierWeightedComplexLogRat (2466317 / 50000000) (0 / 1) (1) (0) (8461025099760105793449 / 5000000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (30068833850 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y1YV3_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y1YV4LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y1 : ℝ) : ℂ) * (barrierV2Tail.getD 4 (0, 0)).1 + (barrierV2Tail.getD 4 (0, 0)).1 ^ 2

private theorem barrierCase2Y1YV4_arg_eq :
    barrierCase2Y1YV4LogArg = barrierComplex (594745061531 / 312500000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y1YV4LogArg, Case2PointData.Y1, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y1YV4_arg_regular :
    (barrierCase2Y1YV4LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y1YV4LogArg).re := by
  rw [barrierCase2Y1YV4_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y1YV4_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2 = barrierComplex (-11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y1YV4_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2Y1YV4LogArg).re -
      ((barrierWeightedComplexLogRat (-11618157 / 100000000) (0 / 1) (1) (0) (353721688215512976063961 / 195312500000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y1YV4_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-11618157 / 100000000) (0 / 1)
    barrierCase2Y1YV4LogArg (1) (0) (353721688215512976063961 / 195312500000000000000000) (594745061531 / 312500000000) (0 / 1)
  have hratio : ((0 / 1) / (594745061531 / 312500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y1YV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y1YV4_approx_upper :
    barrierWeightedComplexLogRat (-11618157 / 100000000) (0 / 1) (1) (0) (353721688215512976063961 / 195312500000000000000000) (0 / 1) <
      (-74766137124 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y1YV4_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y1 : ℝ) (barrierV2Tail.getD 4 (0, 0)) <
      (-74766137124 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2Y1YV4LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y1YV4_error).2
  have ha : ((barrierWeightedComplexLogRat (-11618157 / 100000000) (0 / 1) (1) (0) (353721688215512976063961 / 195312500000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-74766137124 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y1YV4_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y1YV5LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y1 : ℝ) : ℂ) * (barrierV2Tail.getD 5 (0, 0)).1 + (barrierV2Tail.getD 5 (0, 0)).1 ^ 2

private theorem barrierCase2Y1YV5_arg_eq :
    barrierCase2Y1YV5LogArg = barrierComplex (979 / 2500) (-6447663417 / 125000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y1YV5LogArg, Case2PointData.Y1, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y1YV5_arg_regular :
    (barrierCase2Y1YV5LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y1YV5LogArg).re := by
  rw [barrierCase2Y1YV5_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y1YV5_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2 = barrierComplex (-13619357 / 100000000) (-600749 / 3125000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y1YV5_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2Y1YV5LogArg).re -
      ((barrierWeightedComplexLogRat (-13619357 / 100000000) (-600749 / 3125000) (-3) (0) (2437674863538920115889 / 1953125000000000000000) (-6447663417 / 48950000000) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y1YV5_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-13619357 / 100000000) (-600749 / 3125000)
    barrierCase2Y1YV5LogArg (-3) (0) (2437674863538920115889 / 1953125000000000000000) (979 / 2500) (-6447663417 / 125000000000)
  have hratio : ((-6447663417 / 125000000000) / (979 / 2500) : ℚ) = (-6447663417 / 48950000000) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y1YV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y1YV5_approx_upper :
    barrierWeightedComplexLogRat (-13619357 / 100000000) (-600749 / 3125000) (-3) (0) (2437674863538920115889 / 1953125000000000000000) (-6447663417 / 48950000000) <
      (101335329593 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y1YV5_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y1 : ℝ) (barrierV2Tail.getD 5 (0, 0)) <
      (101335329593 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2Y1YV5LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y1YV5_error).2
  have ha : ((barrierWeightedComplexLogRat (-13619357 / 100000000) (-600749 / 3125000) (-3) (0) (2437674863538920115889 / 1953125000000000000000) (-6447663417 / 48950000000) : ℚ) : ℝ) <
      (101335329593 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y1YV5_approx_upper using 1
    norm_num
  linarith






def barrierCase2Y1YV7LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y1 : ℝ) : ℂ) * (barrierV2Tail.getD 7 (0, 0)).1 + (barrierV2Tail.getD 7 (0, 0)).1 ^ 2

private theorem barrierCase2Y1YV7_arg_eq :
    barrierCase2Y1YV7LogArg = barrierComplex (19 / 100) (-1487922327 / 25000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y1YV7LogArg, Case2PointData.Y1, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y1YV7_arg_regular :
    (barrierCase2Y1YV7LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y1YV7LogArg).re := by
  rw [barrierCase2Y1YV7_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y1YV7_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2 = barrierComplex (7835271 / 50000000) (-15094393 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y1YV7_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2Y1YV7LogArg).re -
      ((barrierWeightedComplexLogRat (7835271 / 50000000) (-15094393 / 100000000) (-5) (0) (24776412851185094929 / 19531250000000000000) (-1487922327 / 4750000000) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y1YV7_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (7835271 / 50000000) (-15094393 / 100000000)
    barrierCase2Y1YV7LogArg (-5) (0) (24776412851185094929 / 19531250000000000000) (19 / 100) (-1487922327 / 25000000000)
  have hratio : ((-1487922327 / 25000000000) / (19 / 100) : ℚ) = (-1487922327 / 4750000000) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y1YV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y1YV7_approx_upper :
    barrierWeightedComplexLogRat (7835271 / 50000000) (-15094393 / 100000000) (-5) (0) (24776412851185094929 / 19531250000000000000) (-1487922327 / 4750000000) <
      (-298732850083 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y1YV7_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y1 : ℝ) (barrierV2Tail.getD 7 (0, 0)) <
      (-298732850083 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2Y1YV7LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y1YV7_error).2
  have ha : ((barrierWeightedComplexLogRat (7835271 / 50000000) (-15094393 / 100000000) (-5) (0) (24776412851185094929 / 19531250000000000000) (-1487922327 / 4750000000) : ℚ) : ℝ) <
      (-298732850083 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y1YV7_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y1YV9LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y1 : ℝ) : ℂ) * (barrierV2Tail.getD 9 (0, 0)).1 + (barrierV2Tail.getD 9 (0, 0)).1 ^ 2

private theorem barrierCase2Y1YV9_arg_eq :
    barrierCase2Y1YV9LogArg = barrierComplex (3519 / 40000) (-31577018273 / 500000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y1YV9LogArg, Case2PointData.Y1, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y1YV9_arg_regular :
    (barrierCase2Y1YV9LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y1YV9LogArg).re := by
  rw [barrierCase2Y1YV9_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y1YV9_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2 = barrierComplex (3346771 / 100000000) (5956127 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y1YV9_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2Y1YV9LogArg).re -
      ((barrierWeightedComplexLogRat (3346771 / 100000000) (5956127 / 100000000) (-7) (-1) (2932008239263375902529 / 1953125000000000000000) (12410481727 / 75564518273) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y1YV9_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (3346771 / 100000000) (5956127 / 100000000)
    barrierCase2Y1YV9LogArg (-7) (-1) (2932008239263375902529 / 1953125000000000000000) (75564518273 / 500000000000) (12410481727 / 500000000000)
  have hratio : ((12410481727 / 500000000000) / (75564518273 / 500000000000) : ℚ) = (12410481727 / 75564518273) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y1YV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y1YV9_approx_upper :
    barrierWeightedComplexLogRat (3346771 / 100000000) (5956127 / 100000000) (-7) (-1) (2932008239263375902529 / 1953125000000000000000) (12410481727 / 75564518273) <
      (-37311214794 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y1YV9_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y1 : ℝ) (barrierV2Tail.getD 9 (0, 0)) <
      (-37311214794 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2Y1YV9LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y1YV9_error).2
  have ha : ((barrierWeightedComplexLogRat (3346771 / 100000000) (5956127 / 100000000) (-7) (-1) (2932008239263375902529 / 1953125000000000000000) (12410481727 / 75564518273) : ℚ) : ℝ) <
      (-37311214794 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y1YV9_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y1YV11LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y1 : ℝ) : ℂ) * (barrierV2Tail.getD 11 (0, 0)).1 + (barrierV2Tail.getD 11 (0, 0)).1 ^ 2

private theorem barrierCase2Y1YV11_arg_eq :
    barrierCase2Y1YV11LogArg = barrierComplex (496 / 15625) (-20334938469 / 312500000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y1YV11LogArg, Case2PointData.Y1, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y1YV11_arg_regular :
    (barrierCase2Y1YV11LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y1YV11LogArg).re := by
  rw [barrierCase2Y1YV11_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y1YV11_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2 = barrierComplex (-2055213 / 200000000) (-21715849 / 200000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y1YV11_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2Y1YV11LogArg).re -
      ((barrierWeightedComplexLogRat (-2055213 / 200000000) (-21715849 / 200000000) (-8) (-1) (511916122538016063961 / 381469726562500000000) (-10414938469 / 30254938469) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y1YV11_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2055213 / 200000000) (-21715849 / 200000000)
    barrierCase2Y1YV11LogArg (-8) (-1) (511916122538016063961 / 381469726562500000000) (30254938469 / 312500000000) (-10414938469 / 312500000000)
  have hratio : ((-10414938469 / 312500000000) / (30254938469 / 312500000000) : ℚ) = (-10414938469 / 30254938469) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y1YV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y1YV11_approx_upper :
    barrierWeightedComplexLogRat (-2055213 / 200000000) (-21715849 / 200000000) (-8) (-1) (511916122538016063961 / 381469726562500000000) (-10414938469 / 30254938469) <
      (-94295550686 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y1YV11_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y1 : ℝ) (barrierV2Tail.getD 11 (0, 0)) <
      (-94295550686 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2Y1YV11LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y1YV11_error).2
  have ha : ((barrierWeightedComplexLogRat (-2055213 / 200000000) (-21715849 / 200000000) (-8) (-1) (511916122538016063961 / 381469726562500000000) (-10414938469 / 30254938469) : ℚ) : ℝ) <
      (-94295550686 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y1YV11_approx_upper using 1
    norm_num
  linarith





open Case2PointData

private theorem barrierCase2Y1_YV_tail_upper :
    (barrierV2Tail.map (barrierCase2YVLogTerm (Y1 : ℝ))).sum <
      (-826992847784 / 1000000000000 : ℝ) := by
  have hp : ∀ i ∈ [5, 7, 9, 11],
      barrierCase2YVLogTerm (Y1 : ℝ) (barrierV2Tail.getD (i + 1) (0, 0)) =
        barrierCase2YVLogTerm (Y1 : ℝ) (barrierV2Tail.getD i (0, 0)) := by
    intro i hi
    rw [barrierV2Tail_getD_pair i hi]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y1YV5_arg_regular
    · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y1YV7_arg_regular
    · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y1YV9_arg_regular
    · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y1YV11_arg_regular
  rw [barrierV2Tail_paired_sum _ hp]
  linarith only [barrierCase2Y1YV0_log_upper,
    barrierCase2Y1YV1_log_upper,
    barrierCase2Y1YV2_log_upper,
    barrierCase2Y1YV3_log_upper,
    barrierCase2Y1YV4_log_upper,
    barrierCase2Y1YV5_log_upper,
    barrierCase2Y1YV7_log_upper,
    barrierCase2Y1YV9_log_upper,
    barrierCase2Y1YV11_log_upper]

private theorem barrierCase2Y1_approx_upper :
    barrierCase2YApproxRat Y1 (-5) (-1) (165324703 / 156250000) (4834675297 / 2500000000) + (-826992847784 / 1000000000000) <
      (-160890 / 100000 - 1 / 1000000000000000 : ℚ) := by
  unfold barrierCase2YApproxRat barrierCase2YRat
  rw [barrierCase2TV_eq_explicit]
  simp only [barrierScaledLogRat, barrierLogHRat_two_eq]
  decide +kernel

theorem barrierCase2Y1_lt : barrierCase2Y (Y1 : ℝ) < (-160890 / 100000 : ℝ) := by
  have hx : |(Y1 : ℝ)| ≤ 1 := by norm_num [Y1]
  have he := (abs_lt.mp (barrierCase2Y_realLog_approx_error Y1 hx
    (-5) (-1) (165324703 / 156250000) (4834675297 / 2500000000)
    Y1_normalizations.1 Y1_normalizations.2)).2
  have ha : ((barrierCase2YApproxRat Y1 (-5) (-1) (165324703 / 156250000) (4834675297 / 2500000000) : ℚ) : ℝ) +
      (-826992847784 / 1000000000000) < (-160890 / 100000 - 1 / 1000000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y1_approx_upper using 1 <;> norm_num
  linarith only [he, ha, barrierCase2Y1_YV_tail_upper]

end InternalCatalan

end

end OAI
