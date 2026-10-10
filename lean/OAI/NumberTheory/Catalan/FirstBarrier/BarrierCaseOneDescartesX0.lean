import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.RuleOfSigns
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring
import OAI.NumberTheory.Catalan.Energy.BarrierDescartesCoefficientDegree
import OAI.NumberTheory.Catalan.Energy.BarrierTailPairRational
import OAI.NumberTheory.Catalan.FirstBarrier.BarrierCaseOneRootExistence

namespace OAI

noncomputable section

namespace InternalCatalan

section

open Polynomial
open scoped BigOperators

def barrierFiniteUDerivative (cs : List ℤ) : ℚ[X] :=
  ∑ k ∈ Finset.range cs.length,
    C ((cs.getD k 0 : ℚ) / 100000000) * Chebyshev.U ℚ (k : ℤ)

def barrierFinitePowerDerivative (cs : List ℤ) : ℚ[X] :=
  ∑ k ∈ Finset.range cs.length,
    C ((cs.getD k 0 : ℚ) / 100000000) * X ^ k

def barrierCase1QX : ℚ[X] := X * (1 - X) * (1 + X ^ 2) ^ 2

def barrierCase1QY : ℚ[X] := X * (1 - X)

def barrierCase1AX : ℚ[X] :=
  C (19 / 48) * (1 - X) * (1 + X ^ 2) ^ 2 -
    C (1 / 12) * X * (1 + X ^ 2) ^ 2 -
    C (41 / 24) * X ^ 2 * (1 - X) * (1 + X ^ 2) -
    C (4 * (247405979 / 100000000)) * X ^ 2 * (1 - X) -
    C 2 * barrierCase1QX * barrierFiniteUDerivative barrierP1Finite -
    barrierCase1QX * barrierFinitePowerDerivative barrierV1Finite

def barrierCase1AY : ℚ[X] :=
  C (7 / 48) * (1 - X) - C (1 / 12) * X +
    C 2 * barrierCase1QY * barrierFiniteUDerivative barrierV1Finite

def barrierCase1XDerivativeFormula (x : ℝ) : ℝ :=
  (19 / 48) / x - (1 / 12) / (1 - x) - (41 / 24) * x / (1 + x ^ 2) -
    4 * barrierLambda1 * x / (1 + x ^ 2) ^ 2 -
    2 * (barrierFiniteUDerivative barrierP1Finite).eval₂ (Rat.castHom ℝ) x -
    (barrierFinitePowerDerivative barrierV1Finite).eval₂ (Rat.castHom ℝ) x

def barrierCase1YDerivativeFormula (x : ℝ) : ℝ :=
  (7 / 48) / x - (1 / 12) / (1 - x) +
    2 * (barrierFiniteUDerivative barrierV1Finite).eval₂ (Rat.castHom ℝ) x

theorem barrierCase1QX_eval_ne_zero {x : ℝ} (h0 : x ≠ 0) (h1 : x ≠ 1) :
    barrierCase1QX.eval₂ (Rat.castHom ℝ) x ≠ 0 := by
  have hd : 1 + x ^ 2 ≠ 0 := ne_of_gt (by positivity : (0 : ℝ) < 1 + x ^ 2)
  simpa [barrierCase1QX, eval₂_pow] using
    mul_ne_zero (mul_ne_zero h0 (sub_ne_zero.mpr (Ne.symm h1))) (pow_ne_zero 2 hd)

theorem barrierCase1QY_eval_ne_zero {x : ℝ} (h0 : x ≠ 0) (h1 : x ≠ 1) :
    barrierCase1QY.eval₂ (Rat.castHom ℝ) x ≠ 0 := by
  simpa [barrierCase1QY] using mul_ne_zero h0 (sub_ne_zero.mpr (Ne.symm h1))

theorem barrierCase1AX_clears_denominator {x : ℝ} (h0 : x ≠ 0) (h1 : x ≠ 1) :
    barrierCase1AX.eval₂ (Rat.castHom ℝ) x =
      barrierCase1QX.eval₂ (Rat.castHom ℝ) x * barrierCase1XDerivativeFormula x := by
  have hd : 1 + x ^ 2 ≠ 0 := ne_of_gt (by positivity : (0 : ℝ) < 1 + x ^ 2)
  have ho : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  simp only [barrierCase1AX, barrierCase1QX, barrierCase1XDerivativeFormula,
    barrierLambda1, eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_C, eval₂_X,
    eval₂_one, eval₂_ofNat, map_div₀, map_mul, map_ofNat, map_one]
  field_simp [h0, ho, hd]

theorem barrierCase1AY_clears_denominator {x : ℝ} (h0 : x ≠ 0) (h1 : x ≠ 1) :
    barrierCase1AY.eval₂ (Rat.castHom ℝ) x =
      barrierCase1QY.eval₂ (Rat.castHom ℝ) x * barrierCase1YDerivativeFormula x := by
  have ho : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  simp only [barrierCase1AY, barrierCase1QY, barrierCase1YDerivativeFormula,
    eval₂_sub, eval₂_add, eval₂_mul, eval₂_C, eval₂_X,
    eval₂_one, eval₂_ofNat, map_div₀, map_ofNat, map_one]
  field_simp [h0, ho]

end

section

open Polynomial

def barrierCase1AXExplicit : ℚ[X] :=
  C (19/48) +
    C (-27654673/60000000) * X ^ 1 +
    C (-2660802911/300000000) * X ^ 2 +
    C (246612221/20000000) * X ^ 3 +
    C (198644883/6250000) * X ^ 4 +
    C (-9182425759/300000000) * X ^ 5 +
    C (-320848639/10000000) * X ^ 6 +
    C (252958279/10000000) * X ^ 7 +
    C (-4542019331/50000000) * X ^ 8 +
    C (8873559613/100000000) * X ^ 9 +
    C (3723872963/100000000) * X ^ 10 +
    C (-3407762831/100000000) * X ^ 11 +
    C (3242106693/50000000) * X ^ 12 +
    C (-6401402757/100000000) * X ^ 13

def barrierCase1AYExplicit : ℚ[X] :=
  C (7/48) +
    C (-131721511/37500000) * X ^ 1 +
    C (91528151/6250000) * X ^ 2 +
    C (3975799/2500000) * X ^ 3 +
    C (-208633661/3125000) * X ^ 4 +
    C (1596719/50000) * X ^ 5 +
    C (170059219/1562500) * X ^ 6 +
    C (-29059541/390625) * X ^ 7 +
    C (-43803919/781250) * X ^ 8 +
    C (16992389/390625) * X ^ 9

private theorem barrier_U_3 :
    Chebyshev.U ℚ 3 = 2 * X * Chebyshev.U ℚ 2 - Chebyshev.U ℚ 1 := by
  simpa only [Int.reduceAdd] using Chebyshev.U_add_two ℚ 1

private theorem barrier_U_4 :
    Chebyshev.U ℚ 4 = 2 * X * Chebyshev.U ℚ 3 - Chebyshev.U ℚ 2 := by
  simpa only [Int.reduceAdd] using Chebyshev.U_add_two ℚ 2

private theorem barrier_U_5 :
    Chebyshev.U ℚ 5 = 2 * X * Chebyshev.U ℚ 4 - Chebyshev.U ℚ 3 := by
  simpa only [Int.reduceAdd] using Chebyshev.U_add_two ℚ 3

private theorem barrier_U_6 :
    Chebyshev.U ℚ 6 = 2 * X * Chebyshev.U ℚ 5 - Chebyshev.U ℚ 4 := by
  simpa only [Int.reduceAdd] using Chebyshev.U_add_two ℚ 4

private theorem barrier_U_7 :
    Chebyshev.U ℚ 7 = 2 * X * Chebyshev.U ℚ 6 - Chebyshev.U ℚ 5 := by
  simpa only [Int.reduceAdd] using Chebyshev.U_add_two ℚ 5

theorem barrierCase1AX_eq_explicit : barrierCase1AX = barrierCase1AXExplicit := by
  apply Polynomial.funext
  intro x
  norm_num [barrierCase1AX, barrierCase1AXExplicit, barrierCase1QX,
    barrierCase1QY, barrierFiniteUDerivative, barrierFinitePowerDerivative,
    barrierP1Finite, barrierV1Finite, Finset.sum_range_succ,
    eval_finsetSum, Chebyshev.U_two, barrier_U_3, barrier_U_4,
    barrier_U_5, barrier_U_6, barrier_U_7]
  ring

theorem barrierCase1AX_natDegree : barrierCase1AX.natDegree = 13 := by
  rw [barrierCase1AX_eq_explicit]
  unfold barrierCase1AXExplicit
  compute_degree!

theorem barrierCase1AY_eq_explicit : barrierCase1AY = barrierCase1AYExplicit := by
  apply Polynomial.funext
  intro x
  norm_num [barrierCase1AY, barrierCase1AYExplicit, barrierCase1QX,
    barrierCase1QY, barrierFiniteUDerivative, barrierFinitePowerDerivative,
    barrierP1Finite, barrierV1Finite, Finset.sum_range_succ,
    eval_finsetSum, Chebyshev.U_two, barrier_U_3, barrier_U_4,
    barrier_U_5, barrier_U_6, barrier_U_7]
  ring

theorem barrierCase1AY_natDegree : barrierCase1AY.natDegree = 9 := by
  rw [barrierCase1AY_eq_explicit]
  unfold barrierCase1AYExplicit
  compute_degree!

def barrierBracketLeft (m : ℤ) : ℚ := (m : ℚ) / 10000000000

def barrierBracketRight (m : ℤ) : ℚ := ((m + 2 : ℤ) : ℚ) / 10000000000

def barrierCase1XBrackets : List ℤ :=
  [-9917299785, -2259572153, 2543808026, 4437270259, 6348298970]

theorem barrierCase1AX_bracket_signs (m : ℤ) (hm : m ∈ barrierCase1XBrackets) :
    barrierCase1AX.eval (barrierBracketLeft m) *
      barrierCase1AX.eval (barrierBracketRight m) < 0 := by
  rw [barrierCase1AX_eq_explicit]
  simp only [barrierCase1XBrackets, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl
  <;> norm_num [barrierCase1AXExplicit, barrierBracketLeft, barrierBracketRight, eval_pow]

theorem barrierCase1X_bracket_domain (m : ℤ) (hm : m ∈ barrierCase1XBrackets) :
    -1 < barrierBracketLeft m ∧ barrierBracketRight m < 1 ∧
      (barrierBracketRight m < 0 ∨ 0 < barrierBracketLeft m) := by
  simp only [barrierCase1XBrackets, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl
  <;> norm_num [barrierBracketLeft, barrierBracketRight]

def barrierCase1YBrackets : List ℤ :=
  [532669786, 2504239325, 5701738806, 7966939383, 9454490138]

theorem barrierCase1AY_bracket_signs (m : ℤ) (hm : m ∈ barrierCase1YBrackets) :
    barrierCase1AY.eval (barrierBracketLeft m) *
      barrierCase1AY.eval (barrierBracketRight m) < 0 := by
  rw [barrierCase1AY_eq_explicit]
  simp only [barrierCase1YBrackets, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl
  <;> norm_num [barrierCase1AYExplicit, barrierBracketLeft, barrierBracketRight, eval_pow]

theorem barrierCase1Y_bracket_domain (m : ℤ) (hm : m ∈ barrierCase1YBrackets) :
    0 < barrierBracketLeft m ∧ barrierBracketRight m < 1 := by
  simp only [barrierCase1YBrackets, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl
  <;> norm_num [barrierBracketLeft, barrierBracketRight]

def barrierCase1AYTransformExplicit : ℝ[X] :=
  C (7/48) +
    C (-82502761/37500000) * X ^ 1 +
    C (-153864091/18750000) * X ^ 2 +
    C (674992019/37500000) * X ^ 3 +
    C (337427861/4687500) * X ^ 4 +
    C (52708561/7500000) * X ^ 5 +
    C (-266783927/3750000) * X ^ 6 +
    C (107903701/7500000) * X ^ 7 +
    C (15916019/18750000) * X ^ 8 +
    C (-1/12) * X ^ 9

theorem barrierCase1AY_transform_eq_explicit :
    barrierDescartesTransform (barrierCase1AY.map (Rat.castHom ℝ)) 9 0 1 =
      barrierCase1AYTransformExplicit := by
  apply Polynomial.funext
  intro x
  norm_num [barrierDescartesTransform, barrierCase1AY_eq_explicit,
    barrierCase1AYExplicit, barrierCase1AYTransformExplicit,
    Finset.sum_range_succ, eval_finsetSum, eval_pow, coeff_C_mul, coeff_X_pow, coeff_X]
  ring

theorem barrierCase1AY_transform_signVariations :
    (barrierDescartesTransform (barrierCase1AY.map (Rat.castHom ℝ)) 9 0 1).signVariations = 5 := by
  rw [barrierCase1AY_transform_eq_explicit]
  have hd : barrierCase1AYTransformExplicit.degree = 9 := by
    unfold barrierCase1AYTransformExplicit
    compute_degree!
  rw [signVariations, coeffList, hd]
  norm_num [barrierCase1AYTransformExplicit, List.signVariations,
    List.range_succ, List.destutter, List.destutter', sign_apply,
    coeff_C_mul, coeff_X_pow, coeff_X]

theorem barrierCase1AY_transform_positive_roots_le :
    (barrierDescartesTransform (barrierCase1AY.map (Rat.castHom ℝ)) 9 0 1).roots.countP
      (fun x => 0 < x) ≤ 5 := by
  have h := Polynomial.roots_countP_pos_le_signVariations
    (barrierDescartesTransform (barrierCase1AY.map (Rat.castHom ℝ)) 9 0 1)
  simpa only [barrierCase1AY_transform_signVariations] using h

end

section

theorem barrierCase1AX_subdivision_nonzero :
    barrierCase1AX.eval (-1) ≠ 0 ∧ barrierCase1AX.eval (-1 / 2) ≠ 0 ∧
      barrierCase1AX.eval 0 ≠ 0 ∧ barrierCase1AX.eval (1 / 2) ≠ 0 ∧
      barrierCase1AX.eval 1 ≠ 0 := by
  rw [barrierCase1AX_eq_explicit]
  norm_num [barrierCase1AXExplicit, Polynomial.eval_pow]

theorem barrierCase1AY_endpoint_nonzero :
    barrierCase1AY.eval 0 ≠ 0 ∧ barrierCase1AY.eval 1 ≠ 0 := by
  rw [barrierCase1AY_eq_explicit]
  norm_num [barrierCase1AYExplicit, Polynomial.eval_pow]

open Polynomial
open scoped BigOperators

def barrierCase1AXCoefficient (k : ℕ) : ℚ :=
  ([19/48, -27654673/60000000, -2660802911/300000000, 246612221/20000000, 198644883/6250000, -9182425759/300000000, -320848639/10000000, 252958279/10000000, -4542019331/50000000, 8873559613/100000000, 3723872963/100000000, -3407762831/100000000, 3242106693/50000000, -6401402757/100000000] : List ℚ).getD k 0

theorem barrierCase1AX_coeff_small (k : ℕ) (hk : k < 14) :
    barrierCase1AX.coeff k = barrierCase1AXCoefficient k := by
  interval_cases k
  <;> rw [barrierCase1AX_eq_explicit]
  <;> norm_num [barrierCase1AXExplicit, barrierCase1AXCoefficient,
    coeff_C_mul, coeff_X_pow, coeff_X]

theorem barrierCase1AX_transform_eval (a b x : ℝ) :
    (barrierDescartesTransform (barrierCase1AX.map (Rat.castHom ℝ)) 13 a b).eval x =
      ∑ k ∈ Finset.range 14,
        ((barrierCase1AXCoefficient k : ℚ) : ℝ) * (a + b * x) ^ k * (1 + x) ^ (13 - k) := by
  unfold barrierDescartesTransform
  rw [eval_finsetSum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Polynomial.coeff_map, barrierCase1AX_coeff_small k (Finset.mem_range.mp hk)]
  simp only [eval_mul, eval_C, eval_pow, eval_add, eval_X, eval_one]
  rfl

end

theorem barrierBracketLeft_lt_right (m : ℤ) :
    barrierBracketLeft m < barrierBracketRight m := by
  unfold barrierBracketLeft barrierBracketRight
  apply div_lt_div_of_pos_right _ (by norm_num : (0 : ℚ) < 10000000000)
  push_cast
  linarith

theorem barrierCase1AX_root_in_each_bracket (m : ℤ) (hm : m ∈ barrierCase1XBrackets) :
    ∃ x : ℝ, x ∈ Set.Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ) ∧
      (barrierCase1AX.map (Rat.castHom ℝ)).eval x = 0 := by
  exact rationalPolynomial_root_mem_Ioo_of_eval_mul_neg barrierCase1AX
    (barrierBracketLeft_lt_right m) (barrierCase1AX_bracket_signs m hm)

theorem barrierCase1AY_root_in_each_bracket (m : ℤ) (hm : m ∈ barrierCase1YBrackets) :
    ∃ x : ℝ, x ∈ Set.Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ) ∧
      (barrierCase1AY.map (Rat.castHom ℝ)).eval x = 0 := by
  exact rationalPolynomial_root_mem_Ioo_of_eval_mul_neg barrierCase1AY
    (barrierBracketLeft_lt_right m) (barrierCase1AY_bracket_signs m hm)

open Polynomial

def barrierCase1AXTransform0Explicit : ℝ[X] :=
  C (197396341 / 37500000) +
    C (-41373586421 / 150000000) * X ^ 1 +
    C (-7836353153 / 3750000) * X ^ 2 +
    C (-828479578847 / 120000000) * X ^ 3 +
    C (-3279246739423 / 240000000) * X ^ 4 +
    C (-87449292655397 / 4800000000) * X ^ 5 +
    C (-41679500981699 / 2400000000) * X ^ 6 +
    C (-58739170281629 / 4800000000) * X ^ 7 +
    C (-7786668227467 / 1200000000) * X ^ 8 +
    C (-133002937907977 / 51200000000) * X ^ 9 +
    C (-118601317890961 / 153600000000) * X ^ 10 +
    C (-33203272271481 / 204800000000) * X ^ 11 +
    C (-8794089445937 / 409600000000) * X ^ 12 +
    C (-3292884383081 / 2457600000000) * X ^ 13

theorem barrierCase1AX_transform0_eq_explicit :
    barrierDescartesTransform (barrierCase1AX.map (Rat.castHom ℝ)) 13 (-1) (-1 / 2) =
      barrierCase1AXTransform0Explicit := by
  apply Polynomial.funext
  intro x
  rw [barrierCase1AX_transform_eval]
  norm_num [barrierCase1AXCoefficient, barrierCase1AXTransform0Explicit,
    Finset.sum_range_succ, eval_pow]
  ring

open Polynomial

def barrierCase1AXTransform1Explicit : ℝ[X] :=
  C (-3292884383081 / 2457600000000) +
    C (-8212614321121 / 614400000000) * X ^ 1 +
    C (-13289192880343 / 204800000000) * X ^ 2 +
    C (-19680190814197 / 102400000000) * X ^ 3 +
    C (-18611893427857 / 51200000000) * X ^ 4 +
    C (-16476547481449 / 38400000000) * X ^ 5 +
    C (-5106428303839 / 19200000000) * X ^ 6 +
    C (9121431887 / 384000000) * X ^ 7 +
    C (1988423816251 / 9600000000) * X ^ 8 +
    C (19834078543 / 100000000) * X ^ 9 +
    C (81989107001 / 800000000) * X ^ 10 +
    C (37707757849 / 1200000000) * X ^ 11 +
    C (645154673 / 120000000) * X ^ 12 +
    C (19 / 48) * X ^ 13

theorem barrierCase1AX_transform1_eq_explicit :
    barrierDescartesTransform (barrierCase1AX.map (Rat.castHom ℝ)) 13 (-1 / 2) (0) =
      barrierCase1AXTransform1Explicit := by
  apply Polynomial.funext
  intro x
  rw [barrierCase1AX_transform_eval]
  norm_num [barrierCase1AXCoefficient, barrierCase1AXTransform1Explicit,
    Finset.sum_range_succ, eval_pow]
  ring

def barrierCase1AXTransform2Explicit : ℝ[X] :=
  C (19 / 48) +
    C (196615109 / 40000000) * X ^ 1 +
    C (31070636329 / 1200000000) * X ^ 2 +
    C (60119116971 / 800000000) * X ^ 3 +
    C (76660107233 / 600000000) * X ^ 4 +
    C (1111514856533 / 9600000000) * X ^ 5 +
    C (127932804871 / 9600000000) * X ^ 6 +
    C (-1874949014717 / 19200000000) * X ^ 7 +
    C (-4686595639121 / 38400000000) * X ^ 8 +
    C (-11050376940053 / 153600000000) * X ^ 9 +
    C (-6607368253423 / 307200000000) * X ^ 10 +
    C (-1338397959119 / 614400000000) * X ^ 11 +
    C (194202312139 / 614400000000) * X ^ 12 +
    C (151932441073 / 2457600000000) * X ^ 13

theorem barrierCase1AX_transform2_eq_explicit :
    barrierDescartesTransform (barrierCase1AX.map (Rat.castHom ℝ)) 13 (0) (1 / 2) =
      barrierCase1AXTransform2Explicit := by
  apply Polynomial.funext
  intro x
  rw [barrierCase1AX_transform_eval]
  norm_num [barrierCase1AXCoefficient, barrierCase1AXTransform2Explicit,
    Finset.sum_range_succ, eval_pow]
  ring

def barrierCase1AXTransform3Explicit : ℝ[X] :=
  C (151932441073 / 2457600000000) +
    C (1586717109671 / 1228800000000) * X ^ 1 +
    C (5851476953239 / 614400000000) * X ^ 2 +
    C (2425740911911 / 76800000000) * X ^ 3 +
    C (4594095868667 / 153600000000) * X ^ 4 +
    C (-5153765194747 / 38400000000) * X ^ 5 +
    C (-2783183411353 / 4800000000) * X ^ 6 +
    C (-2656223354401 / 2400000000) * X ^ 7 +
    C (-5991394151383 / 4800000000) * X ^ 8 +
    C (-42883475647 / 50000000) * X ^ 9 +
    C (-8021241613 / 24000000) * X ^ 10 +
    C (-2870130291 / 50000000) * X ^ 11 +
    C (-36667881 / 50000000) * X ^ 12 +
    C (-1 / 3) * X ^ 13

theorem barrierCase1AX_transform3_eq_explicit :
    barrierDescartesTransform (barrierCase1AX.map (Rat.castHom ℝ)) 13 (1 / 2) (1) =
      barrierCase1AXTransform3Explicit := by
  apply Polynomial.funext
  intro x
  rw [barrierCase1AX_transform_eval]
  norm_num [barrierCase1AXCoefficient, barrierCase1AXTransform3Explicit,
    Finset.sum_range_succ, eval_pow]
  ring

theorem barrierCase1AY_interval_roots_card_le (s : Finset ℝ)
    (hs : ∀ x ∈ s, x ∈ Set.Ioo (0 : ℝ) 1 ∧
      (barrierCase1AY.map (Rat.castHom ℝ)).eval x = 0) :
    s.card ≤ 5 := by
  have hd : (barrierCase1AY.map (Rat.castHom ℝ)).natDegree ≤ 9 := by
    calc
      _ ≤ barrierCase1AY.natDegree := Polynomial.natDegree_map_le
      _ = 9 := barrierCase1AY_natDegree
  have hne : barrierDescartesTransform
      (barrierCase1AY.map (Rat.castHom ℝ)) 9 0 1 ≠ 0 := by
    intro hz
    have h := barrierCase1AY_transform_signVariations
    rw [hz, Polynomial.signVariations_zero] at h
    norm_num at h
  simpa only [barrierCase1AY_transform_signVariations] using
    barrierDescartes_interval_roots_card_le
      (barrierCase1AY.map (Rat.castHom ℝ)) 9 0 1 hd hne s hs

private theorem barrierCase1Y_bracket_subset_interval {m : ℤ}
    (hm : m ∈ barrierCase1YBrackets) {x : ℝ}
    (hx : x ∈ Set.Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ)) :
    x ∈ Set.Ioo (0 : ℝ) 1 := by
  obtain ⟨ha, hb⟩ := barrierCase1Y_bracket_domain m hm
  have ha' : (0 : ℝ) < (barrierBracketLeft m : ℝ) := by exact_mod_cast ha
  have hb' : (barrierBracketRight m : ℝ) < (1 : ℝ) := by exact_mod_cast hb
  exact ⟨ha'.trans hx.1, hx.2.trans hb'⟩

private theorem barrierCase1Y_brackets_disjoint {m n : ℤ}
    (hm : m ∈ barrierCase1YBrackets) (hn : n ∈ barrierCase1YBrackets)
    (hmn : m ≠ n) {x : ℝ}
    (hx : x ∈ Set.Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ))
    (hy : x ∈ Set.Ioo (barrierBracketLeft n : ℝ) (barrierBracketRight n : ℝ)) :
    False := by
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hy0, hy1⟩ := hy
  simp only [barrierCase1YBrackets, List.mem_cons, List.not_mem_nil, or_false] at hm hn
  rcases hm with rfl | rfl | rfl | rfl | rfl
  <;> rcases hn with rfl | rfl | rfl | rfl | rfl
  all_goals try exact hmn rfl
  all_goals norm_num [barrierBracketLeft, barrierBracketRight] at hx0 hx1 hy0 hy1
  all_goals linarith

private def barrierCase1YChosenRoot (m : ℤ) : ℝ :=
  if hm : m ∈ barrierCase1YBrackets then
    Classical.choose (barrierCase1AY_root_in_each_bracket m hm)
  else 0

private theorem barrierCase1YChosenRoot_spec (m : ℤ)
    (hm : m ∈ barrierCase1YBrackets) :
    barrierCase1YChosenRoot m ∈
        Set.Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ) ∧
      (barrierCase1AY.map (Rat.castHom ℝ)).eval (barrierCase1YChosenRoot m) = 0 := by
  simpa only [barrierCase1YChosenRoot, dite_eq_left hm] using
    Classical.choose_spec (barrierCase1AY_root_in_each_bracket m hm)

private def barrierCase1YChosenRoots : Finset ℝ := by
  classical
  exact barrierCase1YBrackets.toFinset.image barrierCase1YChosenRoot

private theorem barrierCase1YChosenRoots_card : barrierCase1YChosenRoots.card = 5 := by
  classical
  have hinj : Set.InjOn barrierCase1YChosenRoot
      (↑barrierCase1YBrackets.toFinset : Set ℤ) := by
    intro m hm n hn heq
    have hm' : m ∈ barrierCase1YBrackets := List.mem_toFinset.mp hm
    have hn' : n ∈ barrierCase1YBrackets := List.mem_toFinset.mp hn
    by_contra hmn
    exact barrierCase1Y_brackets_disjoint hm' hn' hmn
      (barrierCase1YChosenRoot_spec m hm').1
      (by simpa only [heq] using (barrierCase1YChosenRoot_spec n hn').1)
  unfold barrierCase1YChosenRoots
  rw [Finset.card_image_of_injOn hinj]
  norm_num [barrierCase1YBrackets]

private theorem barrierCase1YChosenRoots_spec {x : ℝ}
    (hx : x ∈ barrierCase1YChosenRoots) :
    x ∈ Set.Ioo (0 : ℝ) 1 ∧ (barrierCase1AY.map (Rat.castHom ℝ)).eval x = 0 := by
  classical
  change x ∈ barrierCase1YBrackets.toFinset.image barrierCase1YChosenRoot at hx
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hx
  have hm' : m ∈ barrierCase1YBrackets := List.mem_toFinset.mp hm
  have hr := barrierCase1YChosenRoot_spec m hm'
  exact ⟨barrierCase1Y_bracket_subset_interval hm' hr.1, hr.2⟩

private theorem barrierCase1AY_root_mem_chosen {x : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (hr : (barrierCase1AY.map (Rat.castHom ℝ)).eval x = 0) :
    x ∈ barrierCase1YChosenRoots := by
  classical
  by_contra hnot
  have hb : (insert x barrierCase1YChosenRoots).card ≤ 5 := by
    apply barrierCase1AY_interval_roots_card_le
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact ⟨hx, hr⟩
    · exact barrierCase1YChosenRoots_spec hy
  rw [Finset.card_insert_of_notMem hnot, barrierCase1YChosenRoots_card] at hb
  norm_num at hb

theorem barrierCase1AY_roots_exhausted {x : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (hr : (barrierCase1AY.map (Rat.castHom ℝ)).eval x = 0) :
    ∃ m ∈ barrierCase1YBrackets,
      x ∈ Set.Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ) := by
  classical
  have hmem := barrierCase1AY_root_mem_chosen hx hr
  change x ∈ barrierCase1YBrackets.toFinset.image barrierCase1YChosenRoot at hmem
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hmem
  have hm' : m ∈ barrierCase1YBrackets := List.mem_toFinset.mp hm
  exact ⟨m, hm', (barrierCase1YChosenRoot_spec m hm').1⟩

theorem barrierCase1AY_unique_root_in_bracket (m : ℤ)
    (hm : m ∈ barrierCase1YBrackets) :
    ∃! x : ℝ, x ∈ Set.Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ) ∧
      (barrierCase1AY.map (Rat.castHom ℝ)).eval x = 0 := by
  classical
  refine ⟨barrierCase1YChosenRoot m, barrierCase1YChosenRoot_spec m hm, ?_⟩
  intro y hy
  have hmem := barrierCase1AY_root_mem_chosen
    (barrierCase1Y_bracket_subset_interval hm hy.1) hy.2
  change y ∈ barrierCase1YBrackets.toFinset.image barrierCase1YChosenRoot at hmem
  obtain ⟨n, hn, heq⟩ := Finset.mem_image.mp hmem
  have hn' : n ∈ barrierCase1YBrackets := List.mem_toFinset.mp hn
  by_cases hnm : n = m
  · subst n
    exact heq.symm
  · exact False.elim (barrierCase1Y_brackets_disjoint hn' hm hnm
      (barrierCase1YChosenRoot_spec n hn').1 (by simpa only [heq] using hy.1))

theorem barrierCase1AX_transform0_signVariations :
    (barrierDescartesTransform (barrierCase1AX.map (Rat.castHom ℝ)) 13 (-1) (-1 / 2)).signVariations = 1 := by
  rw [barrierCase1AX_transform0_eq_explicit]
  have hd : barrierCase1AXTransform0Explicit.degree = 13 := by
    unfold barrierCase1AXTransform0Explicit
    compute_degree!
  rw [signVariations, coeffList, hd]
  norm_num [barrierCase1AXTransform0Explicit, List.signVariations,
    List.range_succ, List.destutter, List.destutter', sign_apply,
    coeff_C_mul, coeff_X_pow, coeff_X]

theorem barrierCase1AX_transform0_positive_roots_le :
    (barrierDescartesTransform (barrierCase1AX.map (Rat.castHom ℝ)) 13 (-1) (-1 / 2)).roots.countP
      (fun x => 0 < x) ≤ 1 := by
  have h := Polynomial.roots_countP_pos_le_signVariations
    (barrierDescartesTransform (barrierCase1AX.map (Rat.castHom ℝ)) 13 (-1) (-1 / 2))
  simpa only [barrierCase1AX_transform0_signVariations] using h

end InternalCatalan

end

end OAI
