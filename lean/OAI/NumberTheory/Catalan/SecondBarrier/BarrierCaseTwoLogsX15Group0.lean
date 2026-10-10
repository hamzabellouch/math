import OAI.NumberTheory.Catalan.Energy.BarrierLogRatConstants
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoMaxReduction
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointData

namespace OAI

noncomputable section
namespace InternalCatalan

def barrierCase2X15XP0LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X15 : ℝ) : ℂ) * (barrierP2Tail.getD 0 (0, 0)).1 + (barrierP2Tail.getD 0 (0, 0)).1 ^ 2

private theorem barrierCase2X15XP0_arg_eq :
    barrierCase2X15XP0LogArg = barrierComplex (14807642083 / 50000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X15XP0LogArg, Case2PointData.X15, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X15XP0_arg_regular :
    (barrierCase2X15XP0LogArg).im ≠ 0 ∨ 0 < (barrierCase2X15XP0LogArg).re := by
  rw [barrierCase2X15XP0_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X15XP0_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 = barrierComplex (-2334613 / 12500000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X15XP0_error :
    |((2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X15XP0LogArg).re -
      ((barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (-4) (0) (219266264058232578889 / 156250000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X15XP0_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2334613 / 12500000) (0 / 1)
    barrierCase2X15XP0LogArg (-4) (0) (219266264058232578889 / 156250000000000000000) (14807642083 / 50000000000) (0 / 1)
  have hratio : ((0 / 1) / (14807642083 / 50000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X15XP0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X15XP0_approx_upper :
    barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (-4) (0) (219266264058232578889 / 156250000000000000000) (0 / 1) <
      (227275434869 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X15XP0_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X15 : ℝ) (barrierP2Tail.getD 0 (0, 0)) <
      (227275434869 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X15XP0LogArg).re < _
  have he := (abs_lt.mp barrierCase2X15XP0_error).2
  have ha : ((barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (-4) (0) (219266264058232578889 / 156250000000000000000) (0 / 1) : ℚ) : ℝ) <
      (227275434869 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X15XP0_approx_upper using 1
    norm_num
  linarith

def barrierCase2X15XP1LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X15 : ℝ) : ℂ) * (barrierP2Tail.getD 1 (0, 0)).1 + (barrierP2Tail.getD 1 (0, 0)).1 ^ 2

private theorem barrierCase2X15XP1_arg_eq :
    barrierCase2X15XP1LogArg = barrierComplex (38278481053 / 125000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X15XP1LogArg, Case2PointData.X15, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X15XP1_arg_regular :
    (barrierCase2X15XP1LogArg).im ≠ 0 ∨ 0 < (barrierCase2X15XP1LogArg).re := by
  rw [barrierCase2X15XP1_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X15XP1_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 = barrierComplex (-2141509 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X15XP1_error :
    |((2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X15XP1LogArg).re -
      ((barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (-4) (0) (1465242111724879988809 / 976562500000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X15XP1_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2141509 / 50000000) (0 / 1)
    barrierCase2X15XP1LogArg (-4) (0) (1465242111724879988809 / 976562500000000000000) (38278481053 / 125000000000) (0 / 1)
  have hratio : ((0 / 1) / (38278481053 / 125000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X15XP1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X15XP1_approx_upper :
    barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (-4) (0) (1465242111724879988809 / 976562500000000000000) (0 / 1) <
      (50686342234 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X15XP1_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X15 : ℝ) (barrierP2Tail.getD 1 (0, 0)) <
      (50686342234 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X15XP1LogArg).re < _
  have he := (abs_lt.mp barrierCase2X15XP1_error).2
  have ha : ((barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (-4) (0) (1465242111724879988809 / 976562500000000000000) (0 / 1) : ℚ) : ℝ) <
      (50686342234 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X15XP1_approx_upper using 1
    norm_num
  linarith

def barrierCase2X15XP2LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X15 : ℝ) : ℂ) * (barrierP2Tail.getD 2 (0, 0)).1 + (barrierP2Tail.getD 2 (0, 0)).1 ^ 2

private theorem barrierCase2X15XP2_arg_eq :
    barrierCase2X15XP2LogArg = barrierComplex (51 / 100) (-29365970907 / 25000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X15XP2LogArg, Case2PointData.X15, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X15XP2_arg_regular :
    (barrierCase2X15XP2LogArg).im ≠ 0 ∨ 0 < (barrierCase2X15XP2LogArg).re := by
  rw [barrierCase2X15XP2_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X15XP2_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 = barrierComplex (-33138961 / 50000000) (31907569 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X15XP2_error :
    |((2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X15XP2LogArg).re -
      ((barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (0) (-1) (1024922747310770402649 / 625000000000000000000) (-5538656969 / 14038656969) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X15XP2_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-33138961 / 50000000) (31907569 / 100000000)
    barrierCase2X15XP2LogArg (0) (-1) (1024922747310770402649 / 625000000000000000000) (42115970907 / 25000000000) (-16615970907 / 25000000000)
  have hratio : ((-16615970907 / 25000000000) / (42115970907 / 25000000000) : ℚ) = (-5538656969 / 14038656969) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X15XP2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X15XP2_approx_upper :
    barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (0) (-1) (1024922747310770402649 / 625000000000000000000) (-5538656969 / 14038656969) <
      (206591856777 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X15XP2_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X15 : ℝ) (barrierP2Tail.getD 2 (0, 0)) <
      (206591856777 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X15XP2LogArg).re < _
  have he := (abs_lt.mp barrierCase2X15XP2_error).2
  have ha : ((barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (0) (-1) (1024922747310770402649 / 625000000000000000000) (-5538656969 / 14038656969) : ℚ) : ℝ) <
      (206591856777 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X15XP2_approx_upper using 1
    norm_num
  linarith

def barrierCase2X15XP4LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X15 : ℝ) : ℂ) * (barrierP2Tail.getD 4 (0, 0)).1 + (barrierP2Tail.getD 4 (0, 0)).1 ^ 2

private theorem barrierCase2X15XP4_arg_eq :
    barrierCase2X15XP4LogArg = barrierComplex (111 / 400) (-71317357917 / 50000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X15XP4LogArg, Case2PointData.X15, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X15XP4_arg_regular :
    (barrierCase2X15XP4LogArg).im ≠ 0 ∨ 0 < (barrierCase2X15XP4LogArg).re := by
  rw [barrierCase2X15XP4_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X15XP4_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 = barrierComplex (-1231651 / 100000000) (-1200529 / 20000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X15XP4_error :
    |((2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X15XP4LogArg).re -
      ((barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (1) (-2) (5278681165261482578889 / 5000000000000000000000) (4625000000 / 23772452639) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X15XP4_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-1231651 / 100000000) (-1200529 / 20000000)
    barrierCase2X15XP4LogArg (1) (-2) (5278681165261482578889 / 5000000000000000000000) (71317357917 / 25000000000) (111 / 200)
  have hratio : ((111 / 200) / (71317357917 / 25000000000) : ℚ) = (4625000000 / 23772452639) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X15XP4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X15XP4_approx_upper :
    barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (1) (-2) (5278681165261482578889 / 5000000000000000000000) (4625000000 / 23772452639) <
      (-87357683427 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X15XP4_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X15 : ℝ) (barrierP2Tail.getD 4 (0, 0)) <
      (-87357683427 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X15XP4LogArg).re < _
  have he := (abs_lt.mp barrierCase2X15XP4_error).2
  have ha : ((barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (1) (-2) (5278681165261482578889 / 5000000000000000000000) (4625000000 / 23772452639) : ℚ) : ℝ) <
      (-87357683427 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X15XP4_approx_upper using 1
    norm_num
  linarith

def barrierCase2X15XP6LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X15 : ℝ) : ℂ) * (barrierP2Tail.getD 6 (0, 0)).1 + (barrierP2Tail.getD 6 (0, 0)).1 ^ 2

private theorem barrierCase2X15XP6_arg_eq :
    barrierCase2X15XP6LogArg = barrierComplex (4801809877 / 625000000000) (-85908190123 / 62500000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X15XP6LogArg, Case2PointData.X15, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X15XP6_arg_regular :
    (barrierCase2X15XP6LogArg).im ≠ 0 ∨ 0 < (barrierCase2X15XP6LogArg).re := by
  rw [barrierCase2X15XP6_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X15XP6_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 = barrierComplex (-1612959 / 50000000) (-4464117 / 50000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X15XP6_error :
    |((2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 * Complex.log barrierCase2X15XP6LogArg).re -
      ((barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (0) (-2) (738044770399046330268029 / 390625000000000000000000) (4801809877 / 859081901230) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X15XP6_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-1612959 / 50000000) (-4464117 / 50000000)
    barrierCase2X15XP6LogArg (0) (-2) (738044770399046330268029 / 390625000000000000000000) (85908190123 / 31250000000) (4801809877 / 312500000000)
  have hratio : ((4801809877 / 312500000000) / (85908190123 / 31250000000) : ℚ) = (4801809877 / 859081901230) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X15XP6_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X15XP6_approx_upper :
    barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (0) (-2) (738044770399046330268029 / 390625000000000000000000) (4801809877 / 859081901230) <
      (-150007892172 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X15XP6_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X15 : ℝ) (barrierP2Tail.getD 6 (0, 0)) <
      (-150007892172 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 * Complex.log barrierCase2X15XP6LogArg).re < _
  have he := (abs_lt.mp barrierCase2X15XP6_error).2
  have ha : ((barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (0) (-2) (738044770399046330268029 / 390625000000000000000000) (4801809877 / 859081901230) : ℚ) : ℝ) <
      (-150007892172 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X15XP6_approx_upper using 1
    norm_num
  linarith

def barrierCase2X15XP8LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X15 : ℝ) : ℂ) * (barrierP2Tail.getD 8 (0, 0)).1 + (barrierP2Tail.getD 8 (0, 0)).1 ^ 2

private theorem barrierCase2X15XP8_arg_eq :
    barrierCase2X15XP8LogArg = barrierComplex (197778190123 / 625000000000) (-107068190123 / 62500000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X15XP8LogArg, Case2PointData.X15, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X15XP8_arg_regular :
    (barrierCase2X15XP8LogArg).im ≠ 0 ∨ 0 < (barrierCase2X15XP8LogArg).re := by
  rw [barrierCase2X15XP8_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X15XP8_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 = barrierComplex (-32899 / 1562500) (9091287 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X15XP8_error :
    |((2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 * Complex.log barrierCase2X15XP8LogArg).re -
      ((barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (1) (-2) (1185475946109817010268029 / 781250000000000000000000) (197778190123 / 1070681901230) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X15XP8_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-32899 / 1562500) (9091287 / 100000000)
    barrierCase2X15XP8LogArg (1) (-2) (1185475946109817010268029 / 781250000000000000000000) (107068190123 / 31250000000) (197778190123 / 312500000000)
  have hratio : ((197778190123 / 312500000000) / (107068190123 / 31250000000) : ℚ) = (197778190123 / 1070681901230) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X15XP8_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X15XP8_approx_upper :
    barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (1) (-2) (1185475946109817010268029 / 781250000000000000000000) (197778190123 / 1070681901230) <
      (114511893876 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X15XP8_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X15 : ℝ) (barrierP2Tail.getD 8 (0, 0)) <
      (114511893876 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 * Complex.log barrierCase2X15XP8LogArg).re < _
  have he := (abs_lt.mp barrierCase2X15XP8_error).2
  have ha : ((barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (1) (-2) (1185475946109817010268029 / 781250000000000000000000) (197778190123 / 1070681901230) : ℚ) : ℝ) <
      (114511893876 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X15XP8_approx_upper using 1
    norm_num
  linarith

end InternalCatalan

end

end OAI
