import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.List.GetD
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.IntervalCases
import OAI.NumberTheory.Catalan.Energy.BarrierFractionAlgebra

namespace OAI

noncomputable section

namespace InternalCatalan
open Polynomial

def barrierCase2VTailNumeratorExplicit : ℚ[X] :=
  C (-37299120109/50000000000) +
  C (57077222972893/50000000000000) * X ^ 1 +
  C (-3015697796249587/2500000000000000) * X ^ 2 +
  C (1903374555313940637/1250000000000000000) * X ^ 3 +
  C (6401582921755134889/62500000000000000000) * X ^ 4 +
  C (-2107925339418386175807/3125000000000000000000) * X ^ 5 +
  C (26392524978815695479879/31250000000000000000000) * X ^ 6 +
  C (-5289414969008072326466637/3906250000000000000000000) * X ^ 7 +
  C (25472189400411520051226379/97656250000000000000000000) * X ^ 8 +
  C (-31165297145766469289445579/244140625000000000000000000) * X ^ 9 +
  C (11777948990802686139931413/305175781250000000000000000) * X ^ 10 +
  C (20103852089848325076621603/122070312500000000000000000) * X ^ 11 +
  C (21124036836699354417939651/381469726562500000000000000) * X ^ 12

def barrierCase2VTailProductExplicit : ℚ[X] :=
  C (1) +
  C (-527/500) * X ^ 1 +
  C (1750761/1000000) * X ^ 2 +
  C (-909979287/500000000) * X ^ 3 +
  C (-6075541559/12500000000) * X ^ 4 +
  C (71558150879/125000000000) * X ^ 5 +
  C (-67966663885113/31250000000000) * X ^ 6 +
  C (7242405375152601/3125000000000000) * X ^ 7 +
  C (-47227503939133689/78125000000000000) * X ^ 8 +
  C (1167344873752127031/1953125000000000000) * X ^ 9 +
  C (5704562351214682263/9765625000000000000) * X ^ 10 +
  C (-3201700060905414417/4882812500000000000) * X ^ 11 +
  C (7665395189269475619/30517578125000000000) * X ^ 12 +
  C (-5244014001398472729/19073486328125000000) * X ^ 13

theorem barrierCase2VTailNumerator_eq_explicit :
    barrierFractionNumerator (barrierLinearFractions barrierV2RealRows barrierV2PairRows) = barrierCase2VTailNumeratorExplicit := by
  apply Polynomial.funext
  intro x
  norm_num [barrierCase2VTailNumeratorExplicit, barrierFractionNumerator, barrierFractionProduct,
    barrierLinearFractions, barrierQuadraticFractions,
    barrierRealLinearQ, barrierRealQuadraticQ,
    barrierPairLinearA, barrierPairLinearQ, barrierPairQuadraticA, barrierPairQuadraticQ,
    barrierP2RealRows, barrierP2PairRows, barrierV2RealRows, barrierV2PairRows,
    eval_list_prod]
  ring

theorem barrierCase2VTailProduct_eq_explicit :
    barrierFractionProduct (barrierLinearFractions barrierV2RealRows barrierV2PairRows) = barrierCase2VTailProductExplicit := by
  apply Polynomial.funext
  intro x
  norm_num [barrierCase2VTailProductExplicit, barrierFractionNumerator, barrierFractionProduct,
    barrierLinearFractions, barrierQuadraticFractions,
    barrierRealLinearQ, barrierRealQuadraticQ,
    barrierPairLinearA, barrierPairLinearQ, barrierPairQuadraticA, barrierPairQuadraticQ,
    barrierP2RealRows, barrierP2PairRows, barrierV2RealRows, barrierV2PairRows,
    eval_list_prod]
  ring

def barrierCase2VTailNumeratorCoefficient (k : ℕ) : ℚ :=
  ([-37299120109/50000000000,
    57077222972893/50000000000000,
    -3015697796249587/2500000000000000,
    1903374555313940637/1250000000000000000,
    6401582921755134889/62500000000000000000,
    -2107925339418386175807/3125000000000000000000,
    26392524978815695479879/31250000000000000000000,
    -5289414969008072326466637/3906250000000000000000000,
    25472189400411520051226379/97656250000000000000000000,
    -31165297145766469289445579/244140625000000000000000000,
    11777948990802686139931413/305175781250000000000000000,
    20103852089848325076621603/122070312500000000000000000,
    21124036836699354417939651/381469726562500000000000000] : List ℚ).getD k 0

private theorem barrierCase2VTailNumeratorExplicit_coeff_00 :
    barrierCase2VTailNumeratorExplicit.coeff 0 = barrierCase2VTailNumeratorCoefficient 0 := by
  simp only [barrierCase2VTailNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero]
  simp only [barrierCase2VTailNumeratorCoefficient, List.getD_cons_zero]

private theorem barrierCase2VTailNumeratorExplicit_coeff_01 :
    barrierCase2VTailNumeratorExplicit.coeff 1 = barrierCase2VTailNumeratorCoefficient 1 := by
  simp only [barrierCase2VTailNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2VTailNumeratorCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2VTailNumeratorExplicit_coeff_02 :
    barrierCase2VTailNumeratorExplicit.coeff 2 = barrierCase2VTailNumeratorCoefficient 2 := by
  simp only [barrierCase2VTailNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2VTailNumeratorCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2VTailNumeratorExplicit_coeff_03 :
    barrierCase2VTailNumeratorExplicit.coeff 3 = barrierCase2VTailNumeratorCoefficient 3 := by
  simp only [barrierCase2VTailNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2VTailNumeratorCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2VTailNumeratorExplicit_coeff_04 :
    barrierCase2VTailNumeratorExplicit.coeff 4 = barrierCase2VTailNumeratorCoefficient 4 := by
  simp only [barrierCase2VTailNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2VTailNumeratorCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2VTailNumeratorExplicit_coeff_05 :
    barrierCase2VTailNumeratorExplicit.coeff 5 = barrierCase2VTailNumeratorCoefficient 5 := by
  simp only [barrierCase2VTailNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2VTailNumeratorCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2VTailNumeratorExplicit_coeff_06 :
    barrierCase2VTailNumeratorExplicit.coeff 6 = barrierCase2VTailNumeratorCoefficient 6 := by
  simp only [barrierCase2VTailNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2VTailNumeratorCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2VTailNumeratorExplicit_coeff_07 :
    barrierCase2VTailNumeratorExplicit.coeff 7 = barrierCase2VTailNumeratorCoefficient 7 := by
  simp only [barrierCase2VTailNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2VTailNumeratorCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2VTailNumeratorExplicit_coeff_08 :
    barrierCase2VTailNumeratorExplicit.coeff 8 = barrierCase2VTailNumeratorCoefficient 8 := by
  simp only [barrierCase2VTailNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2VTailNumeratorCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2VTailNumeratorExplicit_coeff_09 :
    barrierCase2VTailNumeratorExplicit.coeff 9 = barrierCase2VTailNumeratorCoefficient 9 := by
  simp only [barrierCase2VTailNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2VTailNumeratorCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2VTailNumeratorExplicit_coeff_10 :
    barrierCase2VTailNumeratorExplicit.coeff 10 = barrierCase2VTailNumeratorCoefficient 10 := by
  simp only [barrierCase2VTailNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2VTailNumeratorCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2VTailNumeratorExplicit_coeff_11 :
    barrierCase2VTailNumeratorExplicit.coeff 11 = barrierCase2VTailNumeratorCoefficient 11 := by
  simp only [barrierCase2VTailNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2VTailNumeratorCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2VTailNumeratorExplicit_coeff_12 :
    barrierCase2VTailNumeratorExplicit.coeff 12 = barrierCase2VTailNumeratorCoefficient 12 := by
  simp only [barrierCase2VTailNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2VTailNumeratorCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2VTailNumeratorExplicit_natDegree :
    barrierCase2VTailNumeratorExplicit.natDegree = 12 := by
  unfold barrierCase2VTailNumeratorExplicit
  compute_degree!

theorem barrierCase2VTailNumeratorExplicit_coeff (k : ℕ) :
    barrierCase2VTailNumeratorExplicit.coeff k = barrierCase2VTailNumeratorCoefficient k := by
  by_cases hk : k < 13
  · interval_cases k
    · exact barrierCase2VTailNumeratorExplicit_coeff_00
    · exact barrierCase2VTailNumeratorExplicit_coeff_01
    · exact barrierCase2VTailNumeratorExplicit_coeff_02
    · exact barrierCase2VTailNumeratorExplicit_coeff_03
    · exact barrierCase2VTailNumeratorExplicit_coeff_04
    · exact barrierCase2VTailNumeratorExplicit_coeff_05
    · exact barrierCase2VTailNumeratorExplicit_coeff_06
    · exact barrierCase2VTailNumeratorExplicit_coeff_07
    · exact barrierCase2VTailNumeratorExplicit_coeff_08
    · exact barrierCase2VTailNumeratorExplicit_coeff_09
    · exact barrierCase2VTailNumeratorExplicit_coeff_10
    · exact barrierCase2VTailNumeratorExplicit_coeff_11
    · exact barrierCase2VTailNumeratorExplicit_coeff_12
  · have hlen : 13 ≤ k := Nat.le_of_not_gt hk
    have hlookup : barrierCase2VTailNumeratorCoefficient k = 0 := by
      unfold barrierCase2VTailNumeratorCoefficient
      apply List.getD_eq_default
      simpa only [List.length_cons, List.length_nil] using hlen
    rw [hlookup]
    apply coeff_eq_zero_of_natDegree_lt
    rw [barrierCase2VTailNumeratorExplicit_natDegree]
    exact lt_of_lt_of_le (by decide : 12 < 13) hlen

def barrierCase2VTailProductCoefficient (k : ℕ) : ℚ :=
  ([1,
    -527/500,
    1750761/1000000,
    -909979287/500000000,
    -6075541559/12500000000,
    71558150879/125000000000,
    -67966663885113/31250000000000,
    7242405375152601/3125000000000000,
    -47227503939133689/78125000000000000,
    1167344873752127031/1953125000000000000,
    5704562351214682263/9765625000000000000,
    -3201700060905414417/4882812500000000000,
    7665395189269475619/30517578125000000000,
    -5244014001398472729/19073486328125000000] : List ℚ).getD k 0

private theorem barrierCase2VTailProductExplicit_coeff_00 :
    barrierCase2VTailProductExplicit.coeff 0 = barrierCase2VTailProductCoefficient 0 := by
  simp only [barrierCase2VTailProductExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero]
  simp only [barrierCase2VTailProductCoefficient, List.getD_cons_zero]

private theorem barrierCase2VTailProductExplicit_coeff_01 :
    barrierCase2VTailProductExplicit.coeff 1 = barrierCase2VTailProductCoefficient 1 := by
  simp only [barrierCase2VTailProductExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2VTailProductCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2VTailProductExplicit_coeff_02 :
    barrierCase2VTailProductExplicit.coeff 2 = barrierCase2VTailProductCoefficient 2 := by
  simp only [barrierCase2VTailProductExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2VTailProductCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2VTailProductExplicit_coeff_03 :
    barrierCase2VTailProductExplicit.coeff 3 = barrierCase2VTailProductCoefficient 3 := by
  simp only [barrierCase2VTailProductExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2VTailProductCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2VTailProductExplicit_coeff_04 :
    barrierCase2VTailProductExplicit.coeff 4 = barrierCase2VTailProductCoefficient 4 := by
  simp only [barrierCase2VTailProductExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2VTailProductCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2VTailProductExplicit_coeff_05 :
    barrierCase2VTailProductExplicit.coeff 5 = barrierCase2VTailProductCoefficient 5 := by
  simp only [barrierCase2VTailProductExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2VTailProductCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2VTailProductExplicit_coeff_06 :
    barrierCase2VTailProductExplicit.coeff 6 = barrierCase2VTailProductCoefficient 6 := by
  simp only [barrierCase2VTailProductExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2VTailProductCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2VTailProductExplicit_coeff_07 :
    barrierCase2VTailProductExplicit.coeff 7 = barrierCase2VTailProductCoefficient 7 := by
  simp only [barrierCase2VTailProductExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2VTailProductCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2VTailProductExplicit_coeff_08 :
    barrierCase2VTailProductExplicit.coeff 8 = barrierCase2VTailProductCoefficient 8 := by
  simp only [barrierCase2VTailProductExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2VTailProductCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2VTailProductExplicit_coeff_09 :
    barrierCase2VTailProductExplicit.coeff 9 = barrierCase2VTailProductCoefficient 9 := by
  simp only [barrierCase2VTailProductExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2VTailProductCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2VTailProductExplicit_coeff_10 :
    barrierCase2VTailProductExplicit.coeff 10 = barrierCase2VTailProductCoefficient 10 := by
  simp only [barrierCase2VTailProductExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2VTailProductCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2VTailProductExplicit_coeff_11 :
    barrierCase2VTailProductExplicit.coeff 11 = barrierCase2VTailProductCoefficient 11 := by
  simp only [barrierCase2VTailProductExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2VTailProductCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2VTailProductExplicit_coeff_12 :
    barrierCase2VTailProductExplicit.coeff 12 = barrierCase2VTailProductCoefficient 12 := by
  simp only [barrierCase2VTailProductExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2VTailProductCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2VTailProductExplicit_coeff_13 :
    barrierCase2VTailProductExplicit.coeff 13 = barrierCase2VTailProductCoefficient 13 := by
  simp only [barrierCase2VTailProductExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2VTailProductCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2VTailProductExplicit_natDegree :
    barrierCase2VTailProductExplicit.natDegree = 13 := by
  unfold barrierCase2VTailProductExplicit
  compute_degree!

theorem barrierCase2VTailProductExplicit_coeff (k : ℕ) :
    barrierCase2VTailProductExplicit.coeff k = barrierCase2VTailProductCoefficient k := by
  by_cases hk : k < 14
  · interval_cases k
    · exact barrierCase2VTailProductExplicit_coeff_00
    · exact barrierCase2VTailProductExplicit_coeff_01
    · exact barrierCase2VTailProductExplicit_coeff_02
    · exact barrierCase2VTailProductExplicit_coeff_03
    · exact barrierCase2VTailProductExplicit_coeff_04
    · exact barrierCase2VTailProductExplicit_coeff_05
    · exact barrierCase2VTailProductExplicit_coeff_06
    · exact barrierCase2VTailProductExplicit_coeff_07
    · exact barrierCase2VTailProductExplicit_coeff_08
    · exact barrierCase2VTailProductExplicit_coeff_09
    · exact barrierCase2VTailProductExplicit_coeff_10
    · exact barrierCase2VTailProductExplicit_coeff_11
    · exact barrierCase2VTailProductExplicit_coeff_12
    · exact barrierCase2VTailProductExplicit_coeff_13
  · have hlen : 14 ≤ k := Nat.le_of_not_gt hk
    have hlookup : barrierCase2VTailProductCoefficient k = 0 := by
      unfold barrierCase2VTailProductCoefficient
      apply List.getD_eq_default
      simpa only [List.length_cons, List.length_nil] using hlen
    rw [hlookup]
    apply coeff_eq_zero_of_natDegree_lt
    rw [barrierCase2VTailProductExplicit_natDegree]
    exact lt_of_lt_of_le (by decide : 13 < 14) hlen

def barrierCase2XBaseFractions : List (ℚ[X] × ℚ[X]) :=
  [(C (19 / 48), X), (-C (1 / 12), 1 - X), (-C (65 / 24) * X, 1 + X ^ 2),
   (-(C 4 * barrierFiniteUDerivative barrierP2Finite +
       barrierFinitePowerDerivative barrierV2Finite), 1)]

def barrierCase2XBaseNumeratorExplicit : ℚ[X] :=
  C (19/48) +
  C (-385043839/150000000) * X ^ 1 +
  C (372377653/50000000) * X ^ 2 +
  C (-189294451/75000000) * X ^ 3 +
  C (-1151057621/100000000) * X ^ 4 +
  C (108894531/50000000) * X ^ 5 +
  C (300309089/20000000) * X ^ 6 +
  C (-129850079/20000000) * X ^ 7 +
  C (4681561/2500000) * X ^ 8 +
  C (264361599/100000000) * X ^ 9 +
  C (-510055997/25000000) * X ^ 10 +
  C (6872329/1000000) * X ^ 11 +
  C (175140243/12500000) * X ^ 12 +
  C (-355349099/50000000) * X ^ 13

def barrierCase2XBaseProductExplicit : ℚ[X] :=
  C (0) +
  C (1) * X ^ 1 +
  C (-1) * X ^ 2 +
  C (1) * X ^ 3 +
  C (-1) * X ^ 4

private theorem barrier_case2_U_3 :
    Chebyshev.U ℚ 3 = 2 * X * Chebyshev.U ℚ 2 - Chebyshev.U ℚ 1 := by
  simpa only [Int.reduceAdd] using Chebyshev.U_add_two ℚ 1

private theorem barrier_case2_U_4 :
    Chebyshev.U ℚ 4 = 2 * X * Chebyshev.U ℚ 3 - Chebyshev.U ℚ 2 := by
  simpa only [Int.reduceAdd] using Chebyshev.U_add_two ℚ 2

private theorem barrier_case2_U_5 :
    Chebyshev.U ℚ 5 = 2 * X * Chebyshev.U ℚ 4 - Chebyshev.U ℚ 3 := by
  simpa only [Int.reduceAdd] using Chebyshev.U_add_two ℚ 3

private theorem barrier_case2_U_6 :
    Chebyshev.U ℚ 6 = 2 * X * Chebyshev.U ℚ 5 - Chebyshev.U ℚ 4 := by
  simpa only [Int.reduceAdd] using Chebyshev.U_add_two ℚ 4

private theorem barrier_case2_U_7 :
    Chebyshev.U ℚ 7 = 2 * X * Chebyshev.U ℚ 6 - Chebyshev.U ℚ 5 := by
  simpa only [Int.reduceAdd] using Chebyshev.U_add_two ℚ 5

private theorem barrier_case2_U_8 :
    Chebyshev.U ℚ 8 = 2 * X * Chebyshev.U ℚ 7 - Chebyshev.U ℚ 6 := by
  simpa only [Int.reduceAdd] using Chebyshev.U_add_two ℚ 6

private theorem barrier_case2_U_9 :
    Chebyshev.U ℚ 9 = 2 * X * Chebyshev.U ℚ 8 - Chebyshev.U ℚ 7 := by
  simpa only [Int.reduceAdd] using Chebyshev.U_add_two ℚ 7

theorem barrierCase2XBaseNumerator_eq_explicit :
    barrierFractionNumerator barrierCase2XBaseFractions =
      barrierCase2XBaseNumeratorExplicit := by
  apply Polynomial.funext
  intro x
  norm_num [barrierCase2XBaseFractions, barrierCase2XBaseNumeratorExplicit,
    barrierFractionNumerator, barrierFractionProduct, barrierFiniteUDerivative,
    barrierFinitePowerDerivative, barrierP2Finite, barrierV2Finite,
    Finset.sum_range_succ, eval_finsetSum, eval_list_prod,
    Chebyshev.U_two, barrier_case2_U_3, barrier_case2_U_4,
    barrier_case2_U_5, barrier_case2_U_6, barrier_case2_U_7,
    barrier_case2_U_8, barrier_case2_U_9]
  ring

theorem barrierCase2XBaseProduct_eq_explicit :
    barrierFractionProduct barrierCase2XBaseFractions =
      barrierCase2XBaseProductExplicit := by
  apply Polynomial.funext
  intro x
  norm_num [barrierCase2XBaseFractions, barrierCase2XBaseProductExplicit,
    barrierFractionProduct, eval_list_prod]
  ring

theorem barrierCase2AX_eq_factored :
    barrierCase2AX =
      barrierCase2XBaseNumeratorExplicit * barrierCase2PTailProductExplicit *
          barrierCase2VTailProductExplicit -
        C 4 * barrierCase2XBaseProductExplicit * barrierCase2PTailNumeratorExplicit *
          barrierCase2VTailProductExplicit -
        barrierCase2XBaseProductExplicit * barrierCase2PTailProductExplicit *
          barrierCase2VTailNumeratorExplicit := by
  unfold barrierCase2AX
  change barrierFractionNumerator
    (barrierCase2XBaseFractions ++
      barrierScaleFractions (-4)
        (barrierQuadraticFractions barrierP2RealRows barrierP2PairRows) ++
      barrierScaleFractions (-1)
        (barrierLinearFractions barrierV2RealRows barrierV2PairRows)) = _
  simp only [barrierFractionNumerator_append_exact, barrierFractionProduct_append_exact,
    barrierFractionNumerator_scale_exact, barrierFractionProduct_scale_exact,
    barrierCase2XBaseNumerator_eq_explicit, barrierCase2XBaseProduct_eq_explicit,
    barrierCase2PTailNumerator_eq_explicit, barrierCase2PTailProduct_eq_explicit,
    barrierCase2VTailNumerator_eq_explicit, barrierCase2VTailProduct_eq_explicit,
    map_neg, map_ofNat, map_one]
  ring

def barrierCase2XBaseNumeratorCoefficient (k : ℕ) : ℚ :=
  ([19/48, -385043839/150000000, 372377653/50000000, -189294451/75000000, -1151057621/100000000, 108894531/50000000, 300309089/20000000, -129850079/20000000, 4681561/2500000, 264361599/100000000, -510055997/25000000, 6872329/1000000, 175140243/12500000, -355349099/50000000] : List ℚ).getD k 0

def barrierCase2XBaseProductCoefficient (k : ℕ) : ℚ :=
  ([0, 1, -1, 1, -1] : List ℚ).getD k 0

end InternalCatalan

end

end OAI
