import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoBracketYGroup0

namespace OAI

namespace InternalCatalan
open Polynomial

theorem barrierCase2AX_transform0_ratCoeff_0 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (-1) (0) 0 =
      barrierCase2AXTransform0Coefficient 0 := by decide +kernel

theorem barrierCase2AXTransform0Explicit_coeff_0 :
    barrierCase2AXTransform0Explicit.coeff 0 = (barrierCase2AXTransform0Coefficient 0 : ℝ) := by
  simp only [barrierCase2AXTransform0Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero]
  simp only [barrierCase2AXTransform0Coefficient, List.getD_cons_zero]
  norm_num

theorem barrierCase2AX_transform0_ratCoeff_1 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (-1) (0) 1 =
      barrierCase2AXTransform0Coefficient 1 := by decide +kernel

theorem barrierCase2AXTransform0Explicit_coeff_1 :
    barrierCase2AXTransform0Explicit.coeff 1 = (barrierCase2AXTransform0Coefficient 1 : ℝ) := by
  simp only [barrierCase2AXTransform0Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform0Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AX_transform0_ratCoeff_2 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (-1) (0) 2 =
      barrierCase2AXTransform0Coefficient 2 := by decide +kernel

theorem barrierCase2AXTransform0Explicit_coeff_2 :
    barrierCase2AXTransform0Explicit.coeff 2 = (barrierCase2AXTransform0Coefficient 2 : ℝ) := by
  simp only [barrierCase2AXTransform0Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform0Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AX_transform0_ratCoeff_3 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (-1) (0) 3 =
      barrierCase2AXTransform0Coefficient 3 := by decide +kernel

theorem barrierCase2AXTransform0Explicit_coeff_3 :
    barrierCase2AXTransform0Explicit.coeff 3 = (barrierCase2AXTransform0Coefficient 3 : ℝ) := by
  simp only [barrierCase2AXTransform0Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform0Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AX_transform0_ratCoeff_4 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (-1) (0) 4 =
      barrierCase2AXTransform0Coefficient 4 := by decide +kernel

theorem barrierCase2AXTransform0Explicit_coeff_4 :
    barrierCase2AXTransform0Explicit.coeff 4 = (barrierCase2AXTransform0Coefficient 4 : ℝ) := by
  simp only [barrierCase2AXTransform0Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform0Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

end InternalCatalan

end OAI
