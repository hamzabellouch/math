import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoBracketYGroup0

namespace OAI

namespace InternalCatalan
open Polynomial

theorem barrierCase2AX_transform1_ratCoeff_5 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (0) (1) 5 =
      barrierCase2AXTransform1Coefficient 5 := by decide +kernel

theorem barrierCase2AXTransform1Explicit_coeff_5 :
    barrierCase2AXTransform1Explicit.coeff 5 = (barrierCase2AXTransform1Coefficient 5 : ℝ) := by
  simp only [barrierCase2AXTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AX_transform1_ratCoeff_6 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (0) (1) 6 =
      barrierCase2AXTransform1Coefficient 6 := by decide +kernel

theorem barrierCase2AXTransform1Explicit_coeff_6 :
    barrierCase2AXTransform1Explicit.coeff 6 = (barrierCase2AXTransform1Coefficient 6 : ℝ) := by
  simp only [barrierCase2AXTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AX_transform1_ratCoeff_7 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (0) (1) 7 =
      barrierCase2AXTransform1Coefficient 7 := by decide +kernel

theorem barrierCase2AXTransform1Explicit_coeff_7 :
    barrierCase2AXTransform1Explicit.coeff 7 = (barrierCase2AXTransform1Coefficient 7 : ℝ) := by
  simp only [barrierCase2AXTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AX_transform1_ratCoeff_8 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (0) (1) 8 =
      barrierCase2AXTransform1Coefficient 8 := by decide +kernel

theorem barrierCase2AXTransform1Explicit_coeff_8 :
    barrierCase2AXTransform1Explicit.coeff 8 = (barrierCase2AXTransform1Coefficient 8 : ℝ) := by
  simp only [barrierCase2AXTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AX_transform1_ratCoeff_9 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (0) (1) 9 =
      barrierCase2AXTransform1Coefficient 9 := by decide +kernel

theorem barrierCase2AXTransform1Explicit_coeff_9 :
    barrierCase2AXTransform1Explicit.coeff 9 = (barrierCase2AXTransform1Coefficient 9 : ℝ) := by
  simp only [barrierCase2AXTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

end InternalCatalan

end OAI
