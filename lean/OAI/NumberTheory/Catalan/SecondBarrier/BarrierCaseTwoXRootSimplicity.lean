import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.RuleOfSigns
import Mathlib.Data.List.Pairwise
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoDescartesX0
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoDescartesX1Group0
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoDescartesX1Group1
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoDescartesX1Group2
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoYRootSimplicity

namespace OAI

noncomputable section

namespace InternalCatalan
open Polynomial

theorem barrierCase2AX_transform1_ratCoeff_15 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (0) (1) 15 =
      barrierCase2AXTransform1Coefficient 15 := by decide +kernel

theorem barrierCase2AXTransform1Explicit_coeff_15 :
    barrierCase2AXTransform1Explicit.coeff 15 = (barrierCase2AXTransform1Coefficient 15 : ℝ) := by
  simp only [barrierCase2AXTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AX_transform1_ratCoeff_16 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (0) (1) 16 =
      barrierCase2AXTransform1Coefficient 16 := by decide +kernel

theorem barrierCase2AXTransform1Explicit_coeff_16 :
    barrierCase2AXTransform1Explicit.coeff 16 = (barrierCase2AXTransform1Coefficient 16 : ℝ) := by
  simp only [barrierCase2AXTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AX_transform1_ratCoeff_17 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (0) (1) 17 =
      barrierCase2AXTransform1Coefficient 17 := by decide +kernel

theorem barrierCase2AXTransform1Explicit_coeff_17 :
    barrierCase2AXTransform1Explicit.coeff 17 = (barrierCase2AXTransform1Coefficient 17 : ℝ) := by
  simp only [barrierCase2AXTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AX_transform1_ratCoeff_18 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (0) (1) 18 =
      barrierCase2AXTransform1Coefficient 18 := by decide +kernel

theorem barrierCase2AXTransform1Explicit_coeff_18 :
    barrierCase2AXTransform1Explicit.coeff 18 = (barrierCase2AXTransform1Coefficient 18 : ℝ) := by
  simp only [barrierCase2AXTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AX_transform1_ratCoeff_19 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (0) (1) 19 =
      barrierCase2AXTransform1Coefficient 19 := by decide +kernel

theorem barrierCase2AXTransform1Explicit_coeff_19 :
    barrierCase2AXTransform1Explicit.coeff 19 = (barrierCase2AXTransform1Coefficient 19 : ℝ) := by
  simp only [barrierCase2AXTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AX_transform1_ratCoeff_20 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (0) (1) 20 =
      barrierCase2AXTransform1Coefficient 20 := by decide +kernel

theorem barrierCase2AXTransform1Explicit_coeff_20 :
    barrierCase2AXTransform1Explicit.coeff 20 = (barrierCase2AXTransform1Coefficient 20 : ℝ) := by
  simp only [barrierCase2AXTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AX_transform1_ratCoeff_21 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (0) (1) 21 =
      barrierCase2AXTransform1Coefficient 21 := by decide +kernel

theorem barrierCase2AXTransform1Explicit_coeff_21 :
    barrierCase2AXTransform1Explicit.coeff 21 = (barrierCase2AXTransform1Coefficient 21 : ℝ) := by
  simp only [barrierCase2AXTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AX_transform1_ratCoeff_22 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (0) (1) 22 =
      barrierCase2AXTransform1Coefficient 22 := by decide +kernel

theorem barrierCase2AXTransform1Explicit_coeff_22 :
    barrierCase2AXTransform1Explicit.coeff 22 = (barrierCase2AXTransform1Coefficient 22 : ℝ) := by
  simp only [barrierCase2AXTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AX_transform1_ratCoeff_23 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (0) (1) 23 =
      barrierCase2AXTransform1Coefficient 23 := by decide +kernel

theorem barrierCase2AXTransform1Explicit_coeff_23 :
    barrierCase2AXTransform1Explicit.coeff 23 = (barrierCase2AXTransform1Coefficient 23 : ℝ) := by
  simp only [barrierCase2AXTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AX_transform1_ratCoeff_24 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (0) (1) 24 =
      barrierCase2AXTransform1Coefficient 24 := by decide +kernel

theorem barrierCase2AXTransform1Explicit_coeff_24 :
    barrierCase2AXTransform1Explicit.coeff 24 = (barrierCase2AXTransform1Coefficient 24 : ℝ) := by
  simp only [barrierCase2AXTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AX_transform1_ratCoeff_25 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (0) (1) 25 =
      barrierCase2AXTransform1Coefficient 25 := by decide +kernel

theorem barrierCase2AXTransform1Explicit_coeff_25 :
    barrierCase2AXTransform1Explicit.coeff 25 = (barrierCase2AXTransform1Coefficient 25 : ℝ) := by
  simp only [barrierCase2AXTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AX_transform1_ratCoeff_26 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (0) (1) 26 =
      barrierCase2AXTransform1Coefficient 26 := by decide +kernel

theorem barrierCase2AXTransform1Explicit_coeff_26 :
    barrierCase2AXTransform1Explicit.coeff 26 = (barrierCase2AXTransform1Coefficient 26 : ℝ) := by
  simp only [barrierCase2AXTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AX_transform1_ratCoeff_27 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (0) (1) 27 =
      barrierCase2AXTransform1Coefficient 27 := by decide +kernel

theorem barrierCase2AXTransform1Explicit_coeff_27 :
    barrierCase2AXTransform1Explicit.coeff 27 = (barrierCase2AXTransform1Coefficient 27 : ℝ) := by
  simp only [barrierCase2AXTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AX_transform1_ratCoeff_28 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (0) (1) 28 =
      barrierCase2AXTransform1Coefficient 28 := by decide +kernel

theorem barrierCase2AXTransform1Explicit_coeff_28 :
    barrierCase2AXTransform1Explicit.coeff 28 = (barrierCase2AXTransform1Coefficient 28 : ℝ) := by
  simp only [barrierCase2AXTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AX_transform1_ratCoeff_29 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (0) (1) 29 =
      barrierCase2AXTransform1Coefficient 29 := by decide +kernel

theorem barrierCase2AXTransform1Explicit_coeff_29 :
    barrierCase2AXTransform1Explicit.coeff 29 = (barrierCase2AXTransform1Coefficient 29 : ℝ) := by
  simp only [barrierCase2AXTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AX_transform1_ratCoeff_30 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (0) (1) 30 =
      barrierCase2AXTransform1Coefficient 30 := by decide +kernel

theorem barrierCase2AXTransform1Explicit_coeff_30 :
    barrierCase2AXTransform1Explicit.coeff 30 = (barrierCase2AXTransform1Coefficient 30 : ℝ) := by
  simp only [barrierCase2AXTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AX_transform1_ratCoeff_31 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (0) (1) 31 =
      barrierCase2AXTransform1Coefficient 31 := by decide +kernel

theorem barrierCase2AXTransform1Explicit_coeff_31 :
    barrierCase2AXTransform1Explicit.coeff 31 = (barrierCase2AXTransform1Coefficient 31 : ℝ) := by
  simp only [barrierCase2AXTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AX_transform1_ratCoeff_32 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (0) (1) 32 =
      barrierCase2AXTransform1Coefficient 32 := by decide +kernel

theorem barrierCase2AXTransform1Explicit_coeff_32 :
    barrierCase2AXTransform1Explicit.coeff 32 = (barrierCase2AXTransform1Coefficient 32 : ℝ) := by
  simp only [barrierCase2AXTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AX_transform1_ratCoeff_33 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (0) (1) 33 =
      barrierCase2AXTransform1Coefficient 33 := by decide +kernel

theorem barrierCase2AXTransform1Explicit_coeff_33 :
    barrierCase2AXTransform1Explicit.coeff 33 = (barrierCase2AXTransform1Coefficient 33 : ℝ) := by
  simp only [barrierCase2AXTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AX_transform1_ratCoeff_34 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (0) (1) 34 =
      barrierCase2AXTransform1Coefficient 34 := by decide +kernel

theorem barrierCase2AXTransform1Explicit_coeff_34 :
    barrierCase2AXTransform1Explicit.coeff 34 = (barrierCase2AXTransform1Coefficient 34 : ℝ) := by
  simp only [barrierCase2AXTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AX_transform1_ratCoeff_35 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (0) (1) 35 =
      barrierCase2AXTransform1Coefficient 35 := by decide +kernel

theorem barrierCase2AXTransform1Explicit_coeff_35 :
    barrierCase2AXTransform1Explicit.coeff 35 = (barrierCase2AXTransform1Coefficient 35 : ℝ) := by
  simp only [barrierCase2AXTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AX_transform1_ratCoeff_36 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (0) (1) 36 =
      barrierCase2AXTransform1Coefficient 36 := by decide +kernel

theorem barrierCase2AXTransform1Explicit_coeff_36 :
    barrierCase2AXTransform1Explicit.coeff 36 = (barrierCase2AXTransform1Coefficient 36 : ℝ) := by
  simp only [barrierCase2AXTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AX_transform1_all_coeff_rat (h : Fin 37) :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (0) (1) h.val =
      barrierCase2AXTransform1Coefficient h.val := by
  rcases h with ⟨h, hh⟩
  change barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (0) (1) h =
    barrierCase2AXTransform1Coefficient h
  interval_cases h
  · exact barrierCase2AX_transform1_ratCoeff_0
  · exact barrierCase2AX_transform1_ratCoeff_1
  · exact barrierCase2AX_transform1_ratCoeff_2
  · exact barrierCase2AX_transform1_ratCoeff_3
  · exact barrierCase2AX_transform1_ratCoeff_4
  · exact barrierCase2AX_transform1_ratCoeff_5
  · exact barrierCase2AX_transform1_ratCoeff_6
  · exact barrierCase2AX_transform1_ratCoeff_7
  · exact barrierCase2AX_transform1_ratCoeff_8
  · exact barrierCase2AX_transform1_ratCoeff_9
  · exact barrierCase2AX_transform1_ratCoeff_10
  · exact barrierCase2AX_transform1_ratCoeff_11
  · exact barrierCase2AX_transform1_ratCoeff_12
  · exact barrierCase2AX_transform1_ratCoeff_13
  · exact barrierCase2AX_transform1_ratCoeff_14
  · exact barrierCase2AX_transform1_ratCoeff_15
  · exact barrierCase2AX_transform1_ratCoeff_16
  · exact barrierCase2AX_transform1_ratCoeff_17
  · exact barrierCase2AX_transform1_ratCoeff_18
  · exact barrierCase2AX_transform1_ratCoeff_19
  · exact barrierCase2AX_transform1_ratCoeff_20
  · exact barrierCase2AX_transform1_ratCoeff_21
  · exact barrierCase2AX_transform1_ratCoeff_22
  · exact barrierCase2AX_transform1_ratCoeff_23
  · exact barrierCase2AX_transform1_ratCoeff_24
  · exact barrierCase2AX_transform1_ratCoeff_25
  · exact barrierCase2AX_transform1_ratCoeff_26
  · exact barrierCase2AX_transform1_ratCoeff_27
  · exact barrierCase2AX_transform1_ratCoeff_28
  · exact barrierCase2AX_transform1_ratCoeff_29
  · exact barrierCase2AX_transform1_ratCoeff_30
  · exact barrierCase2AX_transform1_ratCoeff_31
  · exact barrierCase2AX_transform1_ratCoeff_32
  · exact barrierCase2AX_transform1_ratCoeff_33
  · exact barrierCase2AX_transform1_ratCoeff_34
  · exact barrierCase2AX_transform1_ratCoeff_35
  · exact barrierCase2AX_transform1_ratCoeff_36

theorem barrierCase2AXTransform1Explicit_coeff (h : ℕ) (hh : h < 37) :
    barrierCase2AXTransform1Explicit.coeff h = (barrierCase2AXTransform1Coefficient h : ℝ) := by
  interval_cases h
  · exact barrierCase2AXTransform1Explicit_coeff_0
  · exact barrierCase2AXTransform1Explicit_coeff_1
  · exact barrierCase2AXTransform1Explicit_coeff_2
  · exact barrierCase2AXTransform1Explicit_coeff_3
  · exact barrierCase2AXTransform1Explicit_coeff_4
  · exact barrierCase2AXTransform1Explicit_coeff_5
  · exact barrierCase2AXTransform1Explicit_coeff_6
  · exact barrierCase2AXTransform1Explicit_coeff_7
  · exact barrierCase2AXTransform1Explicit_coeff_8
  · exact barrierCase2AXTransform1Explicit_coeff_9
  · exact barrierCase2AXTransform1Explicit_coeff_10
  · exact barrierCase2AXTransform1Explicit_coeff_11
  · exact barrierCase2AXTransform1Explicit_coeff_12
  · exact barrierCase2AXTransform1Explicit_coeff_13
  · exact barrierCase2AXTransform1Explicit_coeff_14
  · exact barrierCase2AXTransform1Explicit_coeff_15
  · exact barrierCase2AXTransform1Explicit_coeff_16
  · exact barrierCase2AXTransform1Explicit_coeff_17
  · exact barrierCase2AXTransform1Explicit_coeff_18
  · exact barrierCase2AXTransform1Explicit_coeff_19
  · exact barrierCase2AXTransform1Explicit_coeff_20
  · exact barrierCase2AXTransform1Explicit_coeff_21
  · exact barrierCase2AXTransform1Explicit_coeff_22
  · exact barrierCase2AXTransform1Explicit_coeff_23
  · exact barrierCase2AXTransform1Explicit_coeff_24
  · exact barrierCase2AXTransform1Explicit_coeff_25
  · exact barrierCase2AXTransform1Explicit_coeff_26
  · exact barrierCase2AXTransform1Explicit_coeff_27
  · exact barrierCase2AXTransform1Explicit_coeff_28
  · exact barrierCase2AXTransform1Explicit_coeff_29
  · exact barrierCase2AXTransform1Explicit_coeff_30
  · exact barrierCase2AXTransform1Explicit_coeff_31
  · exact barrierCase2AXTransform1Explicit_coeff_32
  · exact barrierCase2AXTransform1Explicit_coeff_33
  · exact barrierCase2AXTransform1Explicit_coeff_34
  · exact barrierCase2AXTransform1Explicit_coeff_35
  · exact barrierCase2AXTransform1Explicit_coeff_36

theorem barrierCase2AX_transform1_eq_explicit :
    barrierDescartesTransform (barrierCase2AX.map (Rat.castHom ℝ)) 36 (0) (1) =
      barrierCase2AXTransform1Explicit := by
  apply Polynomial.ext
  intro h
  by_cases hh : h < 37
  · have hc := barrierDescartesTransform_coeff_rat barrierCase2AX
      barrierCase2AXCoefficient 36 (0) (1) h barrierCase2AX_coeff_small
    have hr := barrierCase2AX_transform1_all_coeff_rat ⟨h, hh⟩
    change barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (0) (1) h =
      barrierCase2AXTransform1Coefficient h at hr
    rw [hr] at hc
    have ha : ((0 : ℚ) : ℝ) = (0 : ℝ) := by norm_num
    have hb : ((1 : ℚ) : ℝ) = (1 : ℝ) := by norm_num
    rw [ha, hb] at hc
    exact hc.trans (barrierCase2AXTransform1Explicit_coeff h hh).symm
  · rw [barrierDescartesTransform_coeff_zero_above _ _ _ _ (by omega)]
    symm
    apply coeff_eq_zero_of_natDegree_lt
    rw [barrierCase2AXTransform1Explicit_natDegree]
    omega

theorem barrierCase2AX_transform1_signVariations :
    (barrierDescartesTransform (barrierCase2AX.map (Rat.castHom ℝ))
      36 (0) (1)).signVariations = 9 := by
  rw [barrierCase2AX_transform1_eq_explicit]
  have hd : barrierCase2AXTransform1Explicit.degree = 36 :=
    (degree_eq_iff_natDegree_eq_of_pos (show 0 < (36 : ℕ) by decide)).mpr
      barrierCase2AXTransform1Explicit_natDegree
  rw [signVariations, coeffList, hd]
  norm_num [barrierCase2AXTransform1Explicit_coeff, barrierCase2AXTransform1Coefficient,
    List.signVariations, List.range_succ, List.destutter, List.destutter', sign_apply,
    coeff_C_mul, coeff_X_pow, coeff_X]

theorem barrierCase2AX_transform1_positive_roots_le :
    (barrierDescartesTransform (barrierCase2AX.map (Rat.castHom ℝ))
      36 (0) (1)).roots.countP (fun x => 0 < x) ≤ 9 := by
  have h := Polynomial.roots_countP_pos_le_signVariations
    (barrierDescartesTransform (barrierCase2AX.map (Rat.castHom ℝ)) 36 (0) (1))
  simpa only [barrierCase2AX_transform1_signVariations] using h

private theorem barrierCase2AX_mapped_natDegree_le :
    (barrierCase2AX.map (Rat.castHom ℝ)).natDegree ≤ 36 := by
  calc
    _ ≤ barrierCase2AX.natDegree := Polynomial.natDegree_map_le
    _ = 36 := barrierCase2AX_natDegree

theorem barrierCase2AX_interval0_roots_card_le (s : Finset ℝ)
    (hs : ∀ x ∈ s, x ∈ Set.Ioo (-1 : ℝ) 0 ∧
      (barrierCase2AX.map (Rat.castHom ℝ)).eval x = 0) : s.card ≤ 9 := by
  have hne : barrierDescartesTransform
      (barrierCase2AX.map (Rat.castHom ℝ)) 36 (-1) 0 ≠ 0 := by
    intro hz
    have h := barrierCase2AX_transform0_signVariations
    rw [hz, Polynomial.signVariations_zero] at h
    norm_num at h
  simpa only [barrierCase2AX_transform0_signVariations] using
    barrierDescartes_interval_roots_card_le
      (barrierCase2AX.map (Rat.castHom ℝ)) 36 (-1) 0
      barrierCase2AX_mapped_natDegree_le hne s hs

theorem barrierCase2AX_interval1_roots_card_le (s : Finset ℝ)
    (hs : ∀ x ∈ s, x ∈ Set.Ioo (0 : ℝ) 1 ∧
      (barrierCase2AX.map (Rat.castHom ℝ)).eval x = 0) : s.card ≤ 9 := by
  have hne : barrierDescartesTransform
      (barrierCase2AX.map (Rat.castHom ℝ)) 36 0 1 ≠ 0 := by
    intro hz
    have h := barrierCase2AX_transform1_signVariations
    rw [hz, Polynomial.signVariations_zero] at h
    norm_num at h
  simpa only [barrierCase2AX_transform1_signVariations] using
    barrierDescartes_interval_roots_card_le
      (barrierCase2AX.map (Rat.castHom ℝ)) 36 0 1
      barrierCase2AX_mapped_natDegree_le hne s hs

theorem barrierCase2AX_domain_roots_card_le (s : Finset ℝ)
    (hs : ∀ x ∈ s, x ∈ Set.Ioo (-1 : ℝ) 0 ∪ Set.Ioo (0 : ℝ) 1 ∧
      (barrierCase2AX.map (Rat.castHom ℝ)).eval x = 0) : s.card ≤ 18 := by
  classical
  let s0 := s.filter (fun x => x ∈ Set.Ioo (-1 : ℝ) 0)
  let s1 := s.filter (fun x => x ∈ Set.Ioo (0 : ℝ) 1)
  have h0 : s0.card ≤ 9 := by
    apply barrierCase2AX_interval0_roots_card_le
    intro x hx
    have hh := Finset.mem_filter.mp hx
    exact ⟨hh.2, (hs x hh.1).2⟩
  have h1 : s1.card ≤ 9 := by
    apply barrierCase2AX_interval1_roots_card_le
    intro x hx
    have hh := Finset.mem_filter.mp hx
    exact ⟨hh.2, (hs x hh.1).2⟩
  have hcover : s ⊆ s0 ∪ s1 := by
    intro x hx
    rcases (hs x hx).1 with hn | hp
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hx, hn⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hx, hp⟩))
  calc
    s.card ≤ (s0 ∪ s1).card := Finset.card_le_card hcover
    _ ≤ s0.card + s1.card := Finset.card_union_le _ _
    _ ≤ 9 + 9 := Nat.add_le_add h0 h1
    _ = 18 := rfl

private theorem barrierCase2X_bracket_subset_domain {m : ℤ}
    (hm : m ∈ barrierCase2XBrackets) {x : ℝ}
    (hx : x ∈ Set.Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ)) :
    x ∈ Set.Ioo (-1 : ℝ) 0 ∪ Set.Ioo (0 : ℝ) 1 := by
  obtain ⟨ha, _, hb, hzero⟩ := barrierCase2X_bracket_domain m hm
  have ha' : (-1 : ℝ) < (barrierBracketLeft m : ℝ) := by exact_mod_cast ha
  have hb' : (barrierBracketRight m : ℝ) < (1 : ℝ) := by exact_mod_cast hb
  rcases hzero with hn | hp
  · have hn' : (barrierBracketRight m : ℝ) < (0 : ℝ) := by exact_mod_cast hn
    exact Or.inl ⟨ha'.trans hx.1, hx.2.trans hn'⟩
  · have hp' : (0 : ℝ) < (barrierBracketLeft m : ℝ) := by exact_mod_cast hp
    exact Or.inr ⟨hp'.trans hx.1, hx.2.trans hb'⟩

private theorem barrierCase2X_brackets_disjoint {m n : ℤ}
    (hm : m ∈ barrierCase2XBrackets) (hn : n ∈ barrierCase2XBrackets)
    (hmn : m ≠ n) {x : ℝ}
    (hx : x ∈ Set.Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ))
    (hy : x ∈ Set.Ioo (barrierBracketLeft n : ℝ) (barrierBracketRight n : ℝ)) :
    False := by
  have : Std.Symm (fun a b : ℤ => a + 2 ≤ b ∨ b + 2 ≤ a) :=
    ⟨fun _ _ h => h.symm⟩
  have hp : barrierCase2XBrackets.Pairwise
      (fun a b : ℤ => a + 2 ≤ b ∨ b + 2 ≤ a) := by decide
  rcases hp.forall hm hn hmn with hmn' | hnm'
  · have hq : barrierBracketRight m ≤ barrierBracketLeft n := by
      unfold barrierBracketRight barrierBracketLeft
      exact div_le_div_of_nonneg_right (by exact_mod_cast hmn') (by norm_num)
    have hr : (barrierBracketRight m : ℝ) ≤ (barrierBracketLeft n : ℝ) := by
      exact_mod_cast hq
    exact (not_lt_of_ge hr) (hy.1.trans hx.2)
  · have hq : barrierBracketRight n ≤ barrierBracketLeft m := by
      unfold barrierBracketRight barrierBracketLeft
      exact div_le_div_of_nonneg_right (by exact_mod_cast hnm') (by norm_num)
    have hr : (barrierBracketRight n : ℝ) ≤ (barrierBracketLeft m : ℝ) := by
      exact_mod_cast hq
    exact (not_lt_of_ge hr) (hx.1.trans hy.2)

private def barrierCase2XChosenRoot (m : ℤ) : ℝ :=
  if hm : m ∈ barrierCase2XBrackets then
    Classical.choose (barrierCase2AX_bracket_root m hm)
  else 0

private theorem barrierCase2XChosenRoot_spec (m : ℤ)
    (hm : m ∈ barrierCase2XBrackets) :
    barrierCase2XChosenRoot m ∈
        Set.Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ) ∧
      (barrierCase2AX.map (Rat.castHom ℝ)).eval (barrierCase2XChosenRoot m) = 0 := by
  simpa only [barrierCase2XChosenRoot, dite_eq_left hm] using
    Classical.choose_spec (barrierCase2AX_bracket_root m hm)

private def barrierCase2XChosenRoots : Finset ℝ := by
  classical
  exact barrierCase2XBrackets.toFinset.image barrierCase2XChosenRoot

private theorem barrierCase2XChosenRoots_card : barrierCase2XChosenRoots.card = 18 := by
  classical
  have hinj : Set.InjOn barrierCase2XChosenRoot
      (↑barrierCase2XBrackets.toFinset : Set ℤ) := by
    intro m hm n hn heq
    have hm' : m ∈ barrierCase2XBrackets := List.mem_toFinset.mp hm
    have hn' : n ∈ barrierCase2XBrackets := List.mem_toFinset.mp hn
    by_contra hmn
    exact barrierCase2X_brackets_disjoint hm' hn' hmn
      (barrierCase2XChosenRoot_spec m hm').1
      (by simpa only [heq] using (barrierCase2XChosenRoot_spec n hn').1)
  unfold barrierCase2XChosenRoots
  rw [Finset.card_image_of_injOn hinj]
  norm_num [barrierCase2XBrackets]

private theorem barrierCase2XChosenRoots_spec {x : ℝ}
    (hx : x ∈ barrierCase2XChosenRoots) :
    x ∈ Set.Ioo (-1 : ℝ) 0 ∪ Set.Ioo (0 : ℝ) 1 ∧
      (barrierCase2AX.map (Rat.castHom ℝ)).eval x = 0 := by
  classical
  change x ∈ barrierCase2XBrackets.toFinset.image barrierCase2XChosenRoot at hx
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hx
  have hm' : m ∈ barrierCase2XBrackets := List.mem_toFinset.mp hm
  have hr := barrierCase2XChosenRoot_spec m hm'
  exact ⟨barrierCase2X_bracket_subset_domain hm' hr.1, hr.2⟩

private theorem barrierCase2AX_root_mem_chosen {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 0 ∪ Set.Ioo (0 : ℝ) 1)
    (hr : (barrierCase2AX.map (Rat.castHom ℝ)).eval x = 0) :
    x ∈ barrierCase2XChosenRoots := by
  classical
  by_contra hnot
  have hb : (insert x barrierCase2XChosenRoots).card ≤ 18 := by
    apply barrierCase2AX_domain_roots_card_le
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact ⟨hx, hr⟩
    · exact barrierCase2XChosenRoots_spec hy
  rw [Finset.card_insert_of_notMem hnot, barrierCase2XChosenRoots_card] at hb
  norm_num at hb

theorem barrierCase2AX_roots_exhausted {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 0 ∪ Set.Ioo (0 : ℝ) 1)
    (hr : (barrierCase2AX.map (Rat.castHom ℝ)).eval x = 0) :
    ∃ m ∈ barrierCase2XBrackets,
      x ∈ Set.Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ) := by
  classical
  have hmem := barrierCase2AX_root_mem_chosen hx hr
  change x ∈ barrierCase2XBrackets.toFinset.image barrierCase2XChosenRoot at hmem
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hmem
  have hm' : m ∈ barrierCase2XBrackets := List.mem_toFinset.mp hm
  exact ⟨m, hm', (barrierCase2XChosenRoot_spec m hm').1⟩

private def case2XSimplicityNegativeBrackets : List ℤ :=
  [-9601109148, -8942317572, -7608305633,
   -6503394794, -5185864065, -4015634158,
   -3108806646, -2067921826, -1589849496]

private def case2XSimplicityPositiveBrackets : List ℤ :=
  [1531948062, 2072448179, 3208186484,
   4381119427, 5851354199, 7269030693,
   8390277402, 9332614564, 9709786219]

private theorem case2XSimplicity_degree_le :
    (barrierCase2AX.map (Rat.castHom ℝ)).natDegree ≤ 36 := by
  calc
    _ ≤ barrierCase2AX.natDegree := Polynomial.natDegree_map_le
    _ = 36 := barrierCase2AX_natDegree

private theorem case2XSimplicity_negative {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 0)
    (hp : (barrierCase2AX.map (Rat.castHom ℝ)).eval x = 0) :
    (barrierCase2AX.map (Rat.castHom ℝ)).rootMultiplicity x = 1 := by
  have hne : barrierDescartesTransform
      (barrierCase2AX.map (Rat.castHom ℝ)) 36 (-1) 0 ≠ 0 := by
    intro hz
    have h := barrierCase2AX_transform0_signVariations
    rw [hz, Polynomial.signVariations_zero] at h
    norm_num at h
  have hsep : ∀ m ∈ case2XSimplicityNegativeBrackets,
      ∀ n ∈ case2XSimplicityNegativeBrackets,
        m ≠ n → m + 2 ≤ n ∨ n + 2 ≤ m := by decide +kernel
  have hinside : ∀ m ∈ case2XSimplicityNegativeBrackets,
      (-1 : ℚ) ≤ barrierBracketLeft m ∧ barrierBracketRight m ≤ 0 := by decide +kernel
  have hsub : ∀ m ∈ case2XSimplicityNegativeBrackets,
      m ∈ barrierCase2XBrackets := by decide +kernel
  have hex : ∀ m ∈ case2XSimplicityNegativeBrackets, ∃ y : ℝ,
      y ∈ Set.Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ) ∧
        (barrierCase2AX.map (Rat.castHom ℝ)).eval y = 0 := by
    intro m hm
    exact barrierCase2AX_bracket_root m (hsub m hm)
  have hcount : (barrierDescartesTransform
      (barrierCase2AX.map (Rat.castHom ℝ)) 36 (-1) 0).signVariations ≤
        case2XSimplicityNegativeBrackets.toFinset.card := by
    rw [barrierCase2AX_transform0_signVariations]
    decide +kernel
  exact barrierDescartes_root_simple_of_brackets
    (barrierCase2AX.map (Rat.castHom ℝ)) 36 (-1) 0
    case2XSimplicityNegativeBrackets case2XSimplicity_degree_le
    (by simpa using hne) hsep hinside hex
    (by simpa using hcount) (by simpa using hx) hp

private theorem case2XSimplicity_positive {x : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (hp : (barrierCase2AX.map (Rat.castHom ℝ)).eval x = 0) :
    (barrierCase2AX.map (Rat.castHom ℝ)).rootMultiplicity x = 1 := by
  have hne : barrierDescartesTransform
      (barrierCase2AX.map (Rat.castHom ℝ)) 36 0 1 ≠ 0 := by
    intro hz
    have h := barrierCase2AX_transform1_signVariations
    rw [hz, Polynomial.signVariations_zero] at h
    norm_num at h
  have hsep : ∀ m ∈ case2XSimplicityPositiveBrackets,
      ∀ n ∈ case2XSimplicityPositiveBrackets,
        m ≠ n → m + 2 ≤ n ∨ n + 2 ≤ m := by decide +kernel
  have hinside : ∀ m ∈ case2XSimplicityPositiveBrackets,
      (0 : ℚ) ≤ barrierBracketLeft m ∧ barrierBracketRight m ≤ 1 := by decide +kernel
  have hsub : ∀ m ∈ case2XSimplicityPositiveBrackets,
      m ∈ barrierCase2XBrackets := by decide +kernel
  have hex : ∀ m ∈ case2XSimplicityPositiveBrackets, ∃ y : ℝ,
      y ∈ Set.Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ) ∧
        (barrierCase2AX.map (Rat.castHom ℝ)).eval y = 0 := by
    intro m hm
    exact barrierCase2AX_bracket_root m (hsub m hm)
  have hcount : (barrierDescartesTransform
      (barrierCase2AX.map (Rat.castHom ℝ)) 36 0 1).signVariations ≤
        case2XSimplicityPositiveBrackets.toFinset.card := by
    rw [barrierCase2AX_transform1_signVariations]
    decide +kernel
  exact barrierDescartes_root_simple_of_brackets
    (barrierCase2AX.map (Rat.castHom ℝ)) 36 0 1
    case2XSimplicityPositiveBrackets case2XSimplicity_degree_le
    (by simpa using hne) hsep hinside hex
    (by simpa using hcount) (by simpa using hx) hp

theorem barrierCase2AX_rootMultiplicity_eq_one {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 0 ∪ Set.Ioo (0 : ℝ) 1)
    (hp : (barrierCase2AX.map (Rat.castHom ℝ)).eval x = 0) :
    (barrierCase2AX.map (Rat.castHom ℝ)).rootMultiplicity x = 1 := by
  rcases hx with hn | hp'
  · exact case2XSimplicity_negative hn hp
  · exact case2XSimplicity_positive hp' hp

theorem barrierCase2AX_derivative_ne_zero_at_root {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 0 ∪ Set.Ioo (0 : ℝ) 1)
    (hp : (barrierCase2AX.map (Rat.castHom ℝ)).eval x = 0) :
    (barrierCase2AX.map (Rat.castHom ℝ)).derivative.eval x ≠ 0 := by
  have hs := barrierCase2AX_rootMultiplicity_eq_one hx hp
  have hne : barrierCase2AX.map (Rat.castHom ℝ) ≠ 0 := by
    intro hz
    rw [hz, Polynomial.rootMultiplicity_zero] at hs
    norm_num at hs
  intro hd
  have hgt := (Polynomial.one_lt_rootMultiplicity_iff_isRoot hne).mpr ⟨hp, hd⟩
  rw [hs] at hgt
  exact (lt_irrefl (1 : ℕ)) hgt

private theorem case2XSimplicity_bracket_subset_domain {m : ℤ}
    (hm : m ∈ barrierCase2XBrackets) {x : ℝ}
    (hx : x ∈ Set.Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ)) :
    x ∈ Set.Ioo (-1 : ℝ) 0 ∪ Set.Ioo (0 : ℝ) 1 := by
  obtain ⟨ha, _, hb, hzero⟩ := barrierCase2X_bracket_domain m hm
  have ha' : (-1 : ℝ) < (barrierBracketLeft m : ℝ) := by exact_mod_cast ha
  have hb' : (barrierBracketRight m : ℝ) < (1 : ℝ) := by exact_mod_cast hb
  rcases hzero with hn | hp
  · have hn' : (barrierBracketRight m : ℝ) < (0 : ℝ) := by exact_mod_cast hn
    exact Or.inl ⟨ha'.trans hx.1, hx.2.trans hn'⟩
  · have hp' : (0 : ℝ) < (barrierBracketLeft m : ℝ) := by exact_mod_cast hp
    exact Or.inr ⟨hp'.trans hx.1, hx.2.trans hb'⟩

private theorem case2XSimplicity_brackets_disjoint {m n : ℤ}
    (hm : m ∈ barrierCase2XBrackets) (hn : n ∈ barrierCase2XBrackets)
    (hmn : m ≠ n) {x : ℝ}
    (hx : x ∈ Set.Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ))
    (hy : x ∈ Set.Ioo (barrierBracketLeft n : ℝ) (barrierBracketRight n : ℝ)) :
    False := by
  have : Std.Symm (fun a b : ℤ => a + 2 ≤ b ∨ b + 2 ≤ a) :=
    ⟨fun _ _ h => h.symm⟩
  have hp : barrierCase2XBrackets.Pairwise
      (fun a b : ℤ => a + 2 ≤ b ∨ b + 2 ≤ a) := by decide
  rcases hp.forall hm hn hmn with hmn' | hnm'
  · have hq : barrierBracketRight m ≤ barrierBracketLeft n := by
      unfold barrierBracketRight barrierBracketLeft
      exact div_le_div_of_nonneg_right (by exact_mod_cast hmn') (by norm_num)
    have hr : (barrierBracketRight m : ℝ) ≤ (barrierBracketLeft n : ℝ) := by
      exact_mod_cast hq
    exact (not_lt_of_ge hr) (hy.1.trans hx.2)
  · have hq : barrierBracketRight n ≤ barrierBracketLeft m := by
      unfold barrierBracketRight barrierBracketLeft
      exact div_le_div_of_nonneg_right (by exact_mod_cast hnm') (by norm_num)
    have hr : (barrierBracketRight n : ℝ) ≤ (barrierBracketLeft m : ℝ) := by
      exact_mod_cast hq
    exact (not_lt_of_ge hr) (hx.1.trans hy.2)

private def case2XSimplicityChosenRoot (m : ℤ) : ℝ :=
  if hm : m ∈ barrierCase2XBrackets then
    Classical.choose (barrierCase2AX_bracket_root m hm)
  else 0

private theorem case2XSimplicityChosenRoot_spec (m : ℤ)
    (hm : m ∈ barrierCase2XBrackets) :
    case2XSimplicityChosenRoot m ∈
        Set.Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ) ∧
      (barrierCase2AX.map (Rat.castHom ℝ)).eval (case2XSimplicityChosenRoot m) = 0 := by
  simpa only [case2XSimplicityChosenRoot, dite_eq_left hm] using
    Classical.choose_spec (barrierCase2AX_bracket_root m hm)

private def case2XSimplicityChosenRoots : Finset ℝ := by
  classical
  exact barrierCase2XBrackets.toFinset.image case2XSimplicityChosenRoot

private theorem case2XSimplicityChosenRoots_card : case2XSimplicityChosenRoots.card = 18 := by
  classical
  have hinj : Set.InjOn case2XSimplicityChosenRoot
      (↑barrierCase2XBrackets.toFinset : Set ℤ) := by
    intro m hm n hn heq
    have hm' : m ∈ barrierCase2XBrackets := List.mem_toFinset.mp hm
    have hn' : n ∈ barrierCase2XBrackets := List.mem_toFinset.mp hn
    by_contra hmn
    exact case2XSimplicity_brackets_disjoint hm' hn' hmn
      (case2XSimplicityChosenRoot_spec m hm').1
      (by simpa only [heq] using (case2XSimplicityChosenRoot_spec n hn').1)
  unfold case2XSimplicityChosenRoots
  rw [Finset.card_image_of_injOn hinj]
  norm_num [barrierCase2XBrackets]

private theorem case2XSimplicityChosenRoots_spec {x : ℝ}
    (hx : x ∈ case2XSimplicityChosenRoots) :
    x ∈ Set.Ioo (-1 : ℝ) 0 ∪ Set.Ioo (0 : ℝ) 1 ∧
      (barrierCase2AX.map (Rat.castHom ℝ)).eval x = 0 := by
  classical
  change x ∈ barrierCase2XBrackets.toFinset.image case2XSimplicityChosenRoot at hx
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hx
  have hm' : m ∈ barrierCase2XBrackets := List.mem_toFinset.mp hm
  have hr := case2XSimplicityChosenRoot_spec m hm'
  exact ⟨case2XSimplicity_bracket_subset_domain hm' hr.1, hr.2⟩

private theorem case2XSimplicity_root_mem_chosen {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 0 ∪ Set.Ioo (0 : ℝ) 1)
    (hr : (barrierCase2AX.map (Rat.castHom ℝ)).eval x = 0) :
    x ∈ case2XSimplicityChosenRoots := by
  classical
  by_contra hnot
  have hb : (insert x case2XSimplicityChosenRoots).card ≤ 18 := by
    apply barrierCase2AX_domain_roots_card_le
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact ⟨hx, hr⟩
    · exact case2XSimplicityChosenRoots_spec hy
  rw [Finset.card_insert_of_notMem hnot, case2XSimplicityChosenRoots_card] at hb
  norm_num at hb

theorem barrierCase2AX_unique_root_in_bracket (m : ℤ)
    (hm : m ∈ barrierCase2XBrackets) :
    ∃! x : ℝ, x ∈ Set.Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ) ∧
      (barrierCase2AX.map (Rat.castHom ℝ)).eval x = 0 := by
  classical
  refine ⟨case2XSimplicityChosenRoot m, case2XSimplicityChosenRoot_spec m hm, ?_⟩
  intro y hy
  have hmem := case2XSimplicity_root_mem_chosen
    (case2XSimplicity_bracket_subset_domain hm hy.1) hy.2
  change y ∈ barrierCase2XBrackets.toFinset.image case2XSimplicityChosenRoot at hmem
  obtain ⟨n, hn, heq⟩ := Finset.mem_image.mp hmem
  have hn' : n ∈ barrierCase2XBrackets := List.mem_toFinset.mp hn
  by_cases hnm : n = m
  · subst n
    exact heq.symm
  · exact False.elim (case2XSimplicity_brackets_disjoint hn' hm hnm
      (case2XSimplicityChosenRoot_spec n hn').1 (by simpa only [heq] using hy.1))

theorem barrierCase2AX_simple_root_in_bracket (m : ℤ)
    (hm : m ∈ barrierCase2XBrackets) :
    ∃ x : ℝ, x ∈ Set.Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ) ∧
      (barrierCase2AX.map (Rat.castHom ℝ)).eval x = 0 ∧
      (barrierCase2AX.map (Rat.castHom ℝ)).rootMultiplicity x = 1 := by
  obtain ⟨x, hx, hp⟩ := barrierCase2AX_bracket_root m hm
  exact ⟨x, hx, hp, barrierCase2AX_rootMultiplicity_eq_one
    (case2XSimplicity_bracket_subset_domain hm hx) hp⟩

theorem barrierCase2AX_unique_simple_root_in_bracket (m : ℤ)
    (hm : m ∈ barrierCase2XBrackets) :
    ∃! x : ℝ, x ∈ Set.Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ) ∧
      (barrierCase2AX.map (Rat.castHom ℝ)).eval x = 0 ∧
      (barrierCase2AX.map (Rat.castHom ℝ)).rootMultiplicity x = 1 := by
  obtain ⟨x, hx, huniq⟩ := barrierCase2AX_unique_root_in_bracket m hm
  refine ⟨x, ⟨hx.1, hx.2, barrierCase2AX_rootMultiplicity_eq_one
    (case2XSimplicity_bracket_subset_domain hm hx.1) hx.2⟩, ?_⟩
  intro y hy
  exact huniq y ⟨hy.1, hy.2.1⟩

end InternalCatalan

end

end OAI
