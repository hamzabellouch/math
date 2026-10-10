import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoBracketYGroup0

namespace OAI

namespace InternalCatalan
open Polynomial

theorem barrierCase2AX_transform0_ratCoeff_10 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (-1) (0) 10 =
      barrierCase2AXTransform0Coefficient 10 := by decide +kernel

theorem barrierCase2AXTransform0Explicit_coeff_10 :
    barrierCase2AXTransform0Explicit.coeff 10 = (barrierCase2AXTransform0Coefficient 10 : ℝ) := by
  simp only [barrierCase2AXTransform0Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform0Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AX_transform0_ratCoeff_11 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (-1) (0) 11 =
      barrierCase2AXTransform0Coefficient 11 := by decide +kernel

theorem barrierCase2AXTransform0Explicit_coeff_11 :
    barrierCase2AXTransform0Explicit.coeff 11 = (barrierCase2AXTransform0Coefficient 11 : ℝ) := by
  simp only [barrierCase2AXTransform0Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform0Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AX_transform0_ratCoeff_12 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (-1) (0) 12 =
      barrierCase2AXTransform0Coefficient 12 := by decide +kernel

theorem barrierCase2AXTransform0Explicit_coeff_12 :
    barrierCase2AXTransform0Explicit.coeff 12 = (barrierCase2AXTransform0Coefficient 12 : ℝ) := by
  simp only [barrierCase2AXTransform0Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform0Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AX_transform0_ratCoeff_13 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (-1) (0) 13 =
      barrierCase2AXTransform0Coefficient 13 := by decide +kernel

theorem barrierCase2AXTransform0Explicit_coeff_13 :
    barrierCase2AXTransform0Explicit.coeff 13 = (barrierCase2AXTransform0Coefficient 13 : ℝ) := by
  simp only [barrierCase2AXTransform0Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform0Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AX_transform0_ratCoeff_14 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (-1) (0) 14 =
      barrierCase2AXTransform0Coefficient 14 := by decide +kernel

theorem barrierCase2AXTransform0Explicit_coeff_14 :
    barrierCase2AXTransform0Explicit.coeff 14 = (barrierCase2AXTransform0Coefficient 14 : ℝ) := by
  simp only [barrierCase2AXTransform0Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform0Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

end InternalCatalan

end OAI
