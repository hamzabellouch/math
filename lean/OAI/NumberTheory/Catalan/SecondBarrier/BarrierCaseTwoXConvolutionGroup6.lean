import OAI.NumberTheory.Catalan.Energy.BarrierCoefficientConvolution
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoXBaseProductCoefficientsData
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoXExplicit
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoXTailCoefficientsP

namespace OAI

namespace InternalCatalan

section
open Polynomial

theorem barrierCase2XBaseNumeratorExplicit_coeff_0 :
    barrierCase2XBaseNumeratorExplicit.coeff 0 = barrierCase2XBaseNumeratorCoefficient 0 := by
  simp only [barrierCase2XBaseNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero]
  simp only [barrierCase2XBaseNumeratorCoefficient, List.getD_cons_zero]

theorem barrierCase2XBaseNumeratorExplicit_coeff_1 :
    barrierCase2XBaseNumeratorExplicit.coeff 1 = barrierCase2XBaseNumeratorCoefficient 1 := by
  simp only [barrierCase2XBaseNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2XBaseNumeratorCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2XBaseNumeratorExplicit_coeff_2 :
    barrierCase2XBaseNumeratorExplicit.coeff 2 = barrierCase2XBaseNumeratorCoefficient 2 := by
  simp only [barrierCase2XBaseNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2XBaseNumeratorCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2XBaseNumeratorExplicit_coeff_3 :
    barrierCase2XBaseNumeratorExplicit.coeff 3 = barrierCase2XBaseNumeratorCoefficient 3 := by
  simp only [barrierCase2XBaseNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2XBaseNumeratorCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2XBaseNumeratorExplicit_coeff_4 :
    barrierCase2XBaseNumeratorExplicit.coeff 4 = barrierCase2XBaseNumeratorCoefficient 4 := by
  simp only [barrierCase2XBaseNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2XBaseNumeratorCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2XBaseNumeratorExplicit_coeff_5 :
    barrierCase2XBaseNumeratorExplicit.coeff 5 = barrierCase2XBaseNumeratorCoefficient 5 := by
  simp only [barrierCase2XBaseNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2XBaseNumeratorCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2XBaseNumeratorExplicit_coeff_6 :
    barrierCase2XBaseNumeratorExplicit.coeff 6 = barrierCase2XBaseNumeratorCoefficient 6 := by
  simp only [barrierCase2XBaseNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2XBaseNumeratorCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2XBaseNumeratorExplicit_coeff_7 :
    barrierCase2XBaseNumeratorExplicit.coeff 7 = barrierCase2XBaseNumeratorCoefficient 7 := by
  simp only [barrierCase2XBaseNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2XBaseNumeratorCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2XBaseNumeratorExplicit_coeff_8 :
    barrierCase2XBaseNumeratorExplicit.coeff 8 = barrierCase2XBaseNumeratorCoefficient 8 := by
  simp only [barrierCase2XBaseNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2XBaseNumeratorCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2XBaseNumeratorExplicit_coeff_9 :
    barrierCase2XBaseNumeratorExplicit.coeff 9 = barrierCase2XBaseNumeratorCoefficient 9 := by
  simp only [barrierCase2XBaseNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2XBaseNumeratorCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2XBaseNumeratorExplicit_coeff_10 :
    barrierCase2XBaseNumeratorExplicit.coeff 10 = barrierCase2XBaseNumeratorCoefficient 10 := by
  simp only [barrierCase2XBaseNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2XBaseNumeratorCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2XBaseNumeratorExplicit_coeff_11 :
    barrierCase2XBaseNumeratorExplicit.coeff 11 = barrierCase2XBaseNumeratorCoefficient 11 := by
  simp only [barrierCase2XBaseNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2XBaseNumeratorCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2XBaseNumeratorExplicit_coeff_12 :
    barrierCase2XBaseNumeratorExplicit.coeff 12 = barrierCase2XBaseNumeratorCoefficient 12 := by
  simp only [barrierCase2XBaseNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2XBaseNumeratorCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2XBaseNumeratorExplicit_coeff_13 :
    barrierCase2XBaseNumeratorExplicit.coeff 13 = barrierCase2XBaseNumeratorCoefficient 13 := by
  simp only [barrierCase2XBaseNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2XBaseNumeratorCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2XBaseProductExplicit_coeff_0 :
    barrierCase2XBaseProductExplicit.coeff 0 = barrierCase2XBaseProductCoefficient 0 := by
  norm_num [barrierCase2XBaseProductExplicit, barrierCase2XBaseProductCoefficient, coeff_C_mul, coeff_X_pow, coeff_X]

theorem barrierCase2XBaseProductExplicit_coeff_1 :
    barrierCase2XBaseProductExplicit.coeff 1 = barrierCase2XBaseProductCoefficient 1 := by
  norm_num [barrierCase2XBaseProductExplicit, barrierCase2XBaseProductCoefficient, coeff_C_mul, coeff_X_pow, coeff_X]

theorem barrierCase2XBaseProductExplicit_coeff_2 :
    barrierCase2XBaseProductExplicit.coeff 2 = barrierCase2XBaseProductCoefficient 2 := by
  norm_num [barrierCase2XBaseProductExplicit, barrierCase2XBaseProductCoefficient, coeff_C_mul, coeff_X_pow, coeff_X]

theorem barrierCase2XBaseProductExplicit_coeff_3 :
    barrierCase2XBaseProductExplicit.coeff 3 = barrierCase2XBaseProductCoefficient 3 := by
  norm_num [barrierCase2XBaseProductExplicit, barrierCase2XBaseProductCoefficient, coeff_C_mul, coeff_X_pow, coeff_X]

theorem barrierCase2XBaseProductExplicit_coeff_4 :
    barrierCase2XBaseProductExplicit.coeff 4 = barrierCase2XBaseProductCoefficient 4 := by
  norm_num [barrierCase2XBaseProductExplicit, barrierCase2XBaseProductCoefficient, coeff_C_mul, coeff_X_pow, coeff_X]

theorem barrierCase2XBaseNumeratorExplicit_natDegree : barrierCase2XBaseNumeratorExplicit.natDegree = 13 := by
  unfold barrierCase2XBaseNumeratorExplicit
  compute_degree!

theorem barrierCase2XBaseNumeratorExplicit_coeff (k : ℕ) :
    barrierCase2XBaseNumeratorExplicit.coeff k = barrierCase2XBaseNumeratorCoefficient k := by
  by_cases hk : k < 14
  · interval_cases k
    · exact barrierCase2XBaseNumeratorExplicit_coeff_0
    · exact barrierCase2XBaseNumeratorExplicit_coeff_1
    · exact barrierCase2XBaseNumeratorExplicit_coeff_2
    · exact barrierCase2XBaseNumeratorExplicit_coeff_3
    · exact barrierCase2XBaseNumeratorExplicit_coeff_4
    · exact barrierCase2XBaseNumeratorExplicit_coeff_5
    · exact barrierCase2XBaseNumeratorExplicit_coeff_6
    · exact barrierCase2XBaseNumeratorExplicit_coeff_7
    · exact barrierCase2XBaseNumeratorExplicit_coeff_8
    · exact barrierCase2XBaseNumeratorExplicit_coeff_9
    · exact barrierCase2XBaseNumeratorExplicit_coeff_10
    · exact barrierCase2XBaseNumeratorExplicit_coeff_11
    · exact barrierCase2XBaseNumeratorExplicit_coeff_12
    · exact barrierCase2XBaseNumeratorExplicit_coeff_13
  · rw [coeff_eq_zero_of_natDegree_lt (by rw [barrierCase2XBaseNumeratorExplicit_natDegree]; omega)]
    unfold barrierCase2XBaseNumeratorCoefficient
    symm
    apply List.getD_eq_default
    simpa only [List.length_cons, List.length_nil] using (Nat.le_of_not_gt hk)

theorem barrierCase2XBaseProductExplicit_natDegree : barrierCase2XBaseProductExplicit.natDegree = 4 := by
  unfold barrierCase2XBaseProductExplicit
  compute_degree!

theorem barrierCase2XBaseProductExplicit_coeff (k : ℕ) :
    barrierCase2XBaseProductExplicit.coeff k = barrierCase2XBaseProductCoefficient k := by
  by_cases hk : k < 5
  · interval_cases k
    · exact barrierCase2XBaseProductExplicit_coeff_0
    · exact barrierCase2XBaseProductExplicit_coeff_1
    · exact barrierCase2XBaseProductExplicit_coeff_2
    · exact barrierCase2XBaseProductExplicit_coeff_3
    · exact barrierCase2XBaseProductExplicit_coeff_4
  · rw [coeff_eq_zero_of_natDegree_lt (by rw [barrierCase2XBaseProductExplicit_natDegree]; omega)]
    unfold barrierCase2XBaseProductCoefficient
    symm
    apply List.getD_eq_default
    simpa only [List.length_cons, List.length_nil] using (Nat.le_of_not_gt hk)

end

noncomputable section
open Polynomial

def barrierCase2AXComputedCoefficient (k : ℕ) : ℚ :=
  barrierCoeffConv
      (barrierCoeffConv barrierCase2XBaseNumeratorCoefficient
        barrierCase2PTailProductCoefficient) barrierCase2VTailProductCoefficient k -
    barrierCoeffConv
      (barrierCoeffConv (fun i => 4 * barrierCase2XBaseProductCoefficient i)
        barrierCase2PTailNumeratorCoefficient) barrierCase2VTailProductCoefficient k -
    barrierCoeffConv
      (barrierCoeffConv barrierCase2XBaseProductCoefficient
        barrierCase2PTailProductCoefficient) barrierCase2VTailNumeratorCoefficient k

end

theorem barrierCase2AX_computed_coeff_0 :
    barrierCase2AXComputedCoefficient 0 = barrierCase2AXCoefficient 0 := by
  decide +kernel

theorem barrierCase2AX_computed_coeff_1 :
    barrierCase2AXComputedCoefficient 1 = barrierCase2AXCoefficient 1 := by
  decide +kernel

theorem barrierCase2AX_computed_coeff_2 :
    barrierCase2AXComputedCoefficient 2 = barrierCase2AXCoefficient 2 := by
  decide +kernel

theorem barrierCase2AX_computed_coeff_3 :
    barrierCase2AXComputedCoefficient 3 = barrierCase2AXCoefficient 3 := by
  decide +kernel

theorem barrierCase2AX_computed_coeff_4 :
    barrierCase2AXComputedCoefficient 4 = barrierCase2AXCoefficient 4 := by
  decide +kernel

theorem barrierCase2AX_computed_coeff_5 :
    barrierCase2AXComputedCoefficient 5 = barrierCase2AXCoefficient 5 := by
  decide +kernel

theorem barrierCase2AX_computed_coeff_6 :
    barrierCase2AXComputedCoefficient 6 = barrierCase2AXCoefficient 6 := by
  decide +kernel

theorem barrierCase2AX_computed_coeff_7 :
    barrierCase2AXComputedCoefficient 7 = barrierCase2AXCoefficient 7 := by
  decide +kernel

theorem barrierCase2AX_computed_coeff_8 :
    barrierCase2AXComputedCoefficient 8 = barrierCase2AXCoefficient 8 := by
  decide +kernel

theorem barrierCase2AX_computed_coeff_9 :
    barrierCase2AXComputedCoefficient 9 = barrierCase2AXCoefficient 9 := by
  decide +kernel

theorem barrierCase2AX_computed_coeff_10 :
    barrierCase2AXComputedCoefficient 10 = barrierCase2AXCoefficient 10 := by
  decide +kernel

theorem barrierCase2AX_computed_coeff_11 :
    barrierCase2AXComputedCoefficient 11 = barrierCase2AXCoefficient 11 := by
  decide +kernel

theorem barrierCase2AX_computed_coeff_12 :
    barrierCase2AXComputedCoefficient 12 = barrierCase2AXCoefficient 12 := by
  decide +kernel

theorem barrierCase2AX_computed_coeff_13 :
    barrierCase2AXComputedCoefficient 13 = barrierCase2AXCoefficient 13 := by
  decide +kernel

theorem barrierCase2AX_computed_coeff_14 :
    barrierCase2AXComputedCoefficient 14 = barrierCase2AXCoefficient 14 := by
  decide +kernel

theorem barrierCase2AX_computed_coeff_15 :
    barrierCase2AXComputedCoefficient 15 = barrierCase2AXCoefficient 15 := by
  decide +kernel

theorem barrierCase2AX_computed_coeff_16 :
    barrierCase2AXComputedCoefficient 16 = barrierCase2AXCoefficient 16 := by
  decide +kernel

theorem barrierCase2AX_computed_coeff_17 :
    barrierCase2AXComputedCoefficient 17 = barrierCase2AXCoefficient 17 := by
  decide +kernel

theorem barrierCase2AX_computed_coeff_18 :
    barrierCase2AXComputedCoefficient 18 = barrierCase2AXCoefficient 18 := by
  decide +kernel

theorem barrierCase2AX_computed_coeff_19 :
    barrierCase2AXComputedCoefficient 19 = barrierCase2AXCoefficient 19 := by
  decide +kernel

theorem barrierCase2AX_computed_coeff_20 :
    barrierCase2AXComputedCoefficient 20 = barrierCase2AXCoefficient 20 := by
  decide +kernel

theorem barrierCase2AX_computed_coeff_21 :
    barrierCase2AXComputedCoefficient 21 = barrierCase2AXCoefficient 21 := by
  decide +kernel

theorem barrierCase2AX_computed_coeff_22 :
    barrierCase2AXComputedCoefficient 22 = barrierCase2AXCoefficient 22 := by
  decide +kernel

theorem barrierCase2AX_computed_coeff_23 :
    barrierCase2AXComputedCoefficient 23 = barrierCase2AXCoefficient 23 := by
  decide +kernel

theorem barrierCase2AX_computed_coeff_24 :
    barrierCase2AXComputedCoefficient 24 = barrierCase2AXCoefficient 24 := by
  decide +kernel

theorem barrierCase2AX_computed_coeff_25 :
    barrierCase2AXComputedCoefficient 25 = barrierCase2AXCoefficient 25 := by
  decide +kernel

theorem barrierCase2AX_computed_coeff_26 :
    barrierCase2AXComputedCoefficient 26 = barrierCase2AXCoefficient 26 := by
  decide +kernel

theorem barrierCase2AX_computed_coeff_27 :
    barrierCase2AXComputedCoefficient 27 = barrierCase2AXCoefficient 27 := by
  decide +kernel

theorem barrierCase2AX_computed_coeff_28 :
    barrierCase2AXComputedCoefficient 28 = barrierCase2AXCoefficient 28 := by
  decide +kernel

theorem barrierCase2AX_computed_coeff_29 :
    barrierCase2AXComputedCoefficient 29 = barrierCase2AXCoefficient 29 := by
  decide +kernel

theorem barrierCase2AX_computed_coeff_30 :
    barrierCase2AXComputedCoefficient 30 = barrierCase2AXCoefficient 30 := by
  decide +kernel

theorem barrierCase2AX_computed_coeff_31 :
    barrierCase2AXComputedCoefficient 31 = barrierCase2AXCoefficient 31 := by
  decide +kernel

theorem barrierCase2AX_computed_coeff_32 :
    barrierCase2AXComputedCoefficient 32 = barrierCase2AXCoefficient 32 := by
  decide +kernel

theorem barrierCase2AX_computed_coeff_33 :
    barrierCase2AXComputedCoefficient 33 = barrierCase2AXCoefficient 33 := by
  decide +kernel

theorem barrierCase2AX_computed_coeff_34 :
    barrierCase2AXComputedCoefficient 34 = barrierCase2AXCoefficient 34 := by
  decide +kernel

end InternalCatalan

end OAI
