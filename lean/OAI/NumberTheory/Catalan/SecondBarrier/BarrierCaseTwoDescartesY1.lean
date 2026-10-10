import Mathlib.Algebra.Polynomial.RuleOfSigns
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoDescartesY0Group0

namespace OAI

namespace InternalCatalan

section

open Polynomial

theorem barrierCase2AY_transform1_ratCoeff_0 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1/4) (1/2) 0 =
      barrierCase2AYTransform1Coefficient 0 := by decide +kernel

theorem barrierCase2AY_transform1_ratCoeff_1 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1/4) (1/2) 1 =
      barrierCase2AYTransform1Coefficient 1 := by decide +kernel

theorem barrierCase2AY_transform1_ratCoeff_2 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1/4) (1/2) 2 =
      barrierCase2AYTransform1Coefficient 2 := by decide +kernel

theorem barrierCase2AY_transform1_ratCoeff_3 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1/4) (1/2) 3 =
      barrierCase2AYTransform1Coefficient 3 := by decide +kernel

theorem barrierCase2AY_transform1_ratCoeff_4 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1/4) (1/2) 4 =
      barrierCase2AYTransform1Coefficient 4 := by decide +kernel

theorem barrierCase2AYTransform1Explicit_coeff_0 :
    barrierCase2AYTransform1Explicit.coeff 0 = (barrierCase2AYTransform1Coefficient 0 : ℝ) := by
  simp only [barrierCase2AYTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero]
  simp only [barrierCase2AYTransform1Coefficient, List.getD_cons_zero]
  norm_num

theorem barrierCase2AYTransform1Explicit_coeff_1 :
    barrierCase2AYTransform1Explicit.coeff 1 = (barrierCase2AYTransform1Coefficient 1 : ℝ) := by
  simp only [barrierCase2AYTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AYTransform1Explicit_coeff_2 :
    barrierCase2AYTransform1Explicit.coeff 2 = (barrierCase2AYTransform1Coefficient 2 : ℝ) := by
  simp only [barrierCase2AYTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AYTransform1Explicit_coeff_3 :
    barrierCase2AYTransform1Explicit.coeff 3 = (barrierCase2AYTransform1Coefficient 3 : ℝ) := by
  simp only [barrierCase2AYTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AYTransform1Explicit_coeff_4 :
    barrierCase2AYTransform1Explicit.coeff 4 = (barrierCase2AYTransform1Coefficient 4 : ℝ) := by
  simp only [barrierCase2AYTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AY_transform1_ratCoeff_5 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1/4) (1/2) 5 =
      barrierCase2AYTransform1Coefficient 5 := by decide +kernel

theorem barrierCase2AY_transform1_ratCoeff_6 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1/4) (1/2) 6 =
      barrierCase2AYTransform1Coefficient 6 := by decide +kernel

theorem barrierCase2AY_transform1_ratCoeff_7 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1/4) (1/2) 7 =
      barrierCase2AYTransform1Coefficient 7 := by decide +kernel

theorem barrierCase2AY_transform1_ratCoeff_8 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1/4) (1/2) 8 =
      barrierCase2AYTransform1Coefficient 8 := by decide +kernel

theorem barrierCase2AY_transform1_ratCoeff_9 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1/4) (1/2) 9 =
      barrierCase2AYTransform1Coefficient 9 := by decide +kernel

theorem barrierCase2AYTransform1Explicit_coeff_5 :
    barrierCase2AYTransform1Explicit.coeff 5 = (barrierCase2AYTransform1Coefficient 5 : ℝ) := by
  simp only [barrierCase2AYTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AYTransform1Explicit_coeff_6 :
    barrierCase2AYTransform1Explicit.coeff 6 = (barrierCase2AYTransform1Coefficient 6 : ℝ) := by
  simp only [barrierCase2AYTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AYTransform1Explicit_coeff_7 :
    barrierCase2AYTransform1Explicit.coeff 7 = (barrierCase2AYTransform1Coefficient 7 : ℝ) := by
  simp only [barrierCase2AYTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AYTransform1Explicit_coeff_8 :
    barrierCase2AYTransform1Explicit.coeff 8 = (barrierCase2AYTransform1Coefficient 8 : ℝ) := by
  simp only [barrierCase2AYTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AYTransform1Explicit_coeff_9 :
    barrierCase2AYTransform1Explicit.coeff 9 = (barrierCase2AYTransform1Coefficient 9 : ℝ) := by
  simp only [barrierCase2AYTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AY_transform1_ratCoeff_10 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1/4) (1/2) 10 =
      barrierCase2AYTransform1Coefficient 10 := by decide +kernel

theorem barrierCase2AY_transform1_ratCoeff_11 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1/4) (1/2) 11 =
      barrierCase2AYTransform1Coefficient 11 := by decide +kernel

theorem barrierCase2AY_transform1_ratCoeff_12 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1/4) (1/2) 12 =
      barrierCase2AYTransform1Coefficient 12 := by decide +kernel

theorem barrierCase2AY_transform1_ratCoeff_13 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1/4) (1/2) 13 =
      barrierCase2AYTransform1Coefficient 13 := by decide +kernel

theorem barrierCase2AY_transform1_ratCoeff_14 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1/4) (1/2) 14 =
      barrierCase2AYTransform1Coefficient 14 := by decide +kernel

theorem barrierCase2AYTransform1Explicit_coeff_10 :
    barrierCase2AYTransform1Explicit.coeff 10 = (barrierCase2AYTransform1Coefficient 10 : ℝ) := by
  simp only [barrierCase2AYTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AYTransform1Explicit_coeff_11 :
    barrierCase2AYTransform1Explicit.coeff 11 = (barrierCase2AYTransform1Coefficient 11 : ℝ) := by
  simp only [barrierCase2AYTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AYTransform1Explicit_coeff_12 :
    barrierCase2AYTransform1Explicit.coeff 12 = (barrierCase2AYTransform1Coefficient 12 : ℝ) := by
  simp only [barrierCase2AYTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AYTransform1Explicit_coeff_13 :
    barrierCase2AYTransform1Explicit.coeff 13 = (barrierCase2AYTransform1Coefficient 13 : ℝ) := by
  simp only [barrierCase2AYTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AYTransform1Explicit_coeff_14 :
    barrierCase2AYTransform1Explicit.coeff 14 = (barrierCase2AYTransform1Coefficient 14 : ℝ) := by
  simp only [barrierCase2AYTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AY_transform1_ratCoeff_15 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1/4) (1/2) 15 =
      barrierCase2AYTransform1Coefficient 15 := by decide +kernel

theorem barrierCase2AY_transform1_ratCoeff_16 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1/4) (1/2) 16 =
      barrierCase2AYTransform1Coefficient 16 := by decide +kernel

theorem barrierCase2AY_transform1_ratCoeff_17 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1/4) (1/2) 17 =
      barrierCase2AYTransform1Coefficient 17 := by decide +kernel

theorem barrierCase2AY_transform1_ratCoeff_18 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1/4) (1/2) 18 =
      barrierCase2AYTransform1Coefficient 18 := by decide +kernel

theorem barrierCase2AY_transform1_ratCoeff_19 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1/4) (1/2) 19 =
      barrierCase2AYTransform1Coefficient 19 := by decide +kernel

theorem barrierCase2AYTransform1Explicit_coeff_15 :
    barrierCase2AYTransform1Explicit.coeff 15 = (barrierCase2AYTransform1Coefficient 15 : ℝ) := by
  simp only [barrierCase2AYTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AYTransform1Explicit_coeff_16 :
    barrierCase2AYTransform1Explicit.coeff 16 = (barrierCase2AYTransform1Coefficient 16 : ℝ) := by
  simp only [barrierCase2AYTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AYTransform1Explicit_coeff_17 :
    barrierCase2AYTransform1Explicit.coeff 17 = (barrierCase2AYTransform1Coefficient 17 : ℝ) := by
  simp only [barrierCase2AYTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AYTransform1Explicit_coeff_18 :
    barrierCase2AYTransform1Explicit.coeff 18 = (barrierCase2AYTransform1Coefficient 18 : ℝ) := by
  simp only [barrierCase2AYTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AYTransform1Explicit_coeff_19 :
    barrierCase2AYTransform1Explicit.coeff 19 = (barrierCase2AYTransform1Coefficient 19 : ℝ) := by
  simp only [barrierCase2AYTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AY_transform1_ratCoeff_20 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1/4) (1/2) 20 =
      barrierCase2AYTransform1Coefficient 20 := by decide +kernel

theorem barrierCase2AY_transform1_ratCoeff_21 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1/4) (1/2) 21 =
      barrierCase2AYTransform1Coefficient 21 := by decide +kernel

theorem barrierCase2AY_transform1_ratCoeff_22 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1/4) (1/2) 22 =
      barrierCase2AYTransform1Coefficient 22 := by decide +kernel

theorem barrierCase2AY_transform1_ratCoeff_23 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1/4) (1/2) 23 =
      barrierCase2AYTransform1Coefficient 23 := by decide +kernel

theorem barrierCase2AY_transform1_ratCoeff_24 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1/4) (1/2) 24 =
      barrierCase2AYTransform1Coefficient 24 := by decide +kernel

theorem barrierCase2AYTransform1Explicit_coeff_20 :
    barrierCase2AYTransform1Explicit.coeff 20 = (barrierCase2AYTransform1Coefficient 20 : ℝ) := by
  simp only [barrierCase2AYTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AYTransform1Explicit_coeff_21 :
    barrierCase2AYTransform1Explicit.coeff 21 = (barrierCase2AYTransform1Coefficient 21 : ℝ) := by
  simp only [barrierCase2AYTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AYTransform1Explicit_coeff_22 :
    barrierCase2AYTransform1Explicit.coeff 22 = (barrierCase2AYTransform1Coefficient 22 : ℝ) := by
  simp only [barrierCase2AYTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AYTransform1Explicit_coeff_23 :
    barrierCase2AYTransform1Explicit.coeff 23 = (barrierCase2AYTransform1Coefficient 23 : ℝ) := by
  simp only [barrierCase2AYTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AYTransform1Explicit_coeff_24 :
    barrierCase2AYTransform1Explicit.coeff 24 = (barrierCase2AYTransform1Coefficient 24 : ℝ) := by
  simp only [barrierCase2AYTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AY_transform1_all_coeff_rat (h : Fin 25) :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1/4) (1/2) h.val =
      barrierCase2AYTransform1Coefficient h.val := by
  rcases h with ⟨h, hh⟩
  change barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1/4) (1/2) h =
    barrierCase2AYTransform1Coefficient h
  interval_cases h
  · exact barrierCase2AY_transform1_ratCoeff_0
  · exact barrierCase2AY_transform1_ratCoeff_1
  · exact barrierCase2AY_transform1_ratCoeff_2
  · exact barrierCase2AY_transform1_ratCoeff_3
  · exact barrierCase2AY_transform1_ratCoeff_4
  · exact barrierCase2AY_transform1_ratCoeff_5
  · exact barrierCase2AY_transform1_ratCoeff_6
  · exact barrierCase2AY_transform1_ratCoeff_7
  · exact barrierCase2AY_transform1_ratCoeff_8
  · exact barrierCase2AY_transform1_ratCoeff_9
  · exact barrierCase2AY_transform1_ratCoeff_10
  · exact barrierCase2AY_transform1_ratCoeff_11
  · exact barrierCase2AY_transform1_ratCoeff_12
  · exact barrierCase2AY_transform1_ratCoeff_13
  · exact barrierCase2AY_transform1_ratCoeff_14
  · exact barrierCase2AY_transform1_ratCoeff_15
  · exact barrierCase2AY_transform1_ratCoeff_16
  · exact barrierCase2AY_transform1_ratCoeff_17
  · exact barrierCase2AY_transform1_ratCoeff_18
  · exact barrierCase2AY_transform1_ratCoeff_19
  · exact barrierCase2AY_transform1_ratCoeff_20
  · exact barrierCase2AY_transform1_ratCoeff_21
  · exact barrierCase2AY_transform1_ratCoeff_22
  · exact barrierCase2AY_transform1_ratCoeff_23
  · exact barrierCase2AY_transform1_ratCoeff_24

theorem barrierCase2AYTransform1Explicit_coeff (h : ℕ) (hh : h < 25) :
    barrierCase2AYTransform1Explicit.coeff h = (barrierCase2AYTransform1Coefficient h : ℝ) := by
  interval_cases h
  · exact barrierCase2AYTransform1Explicit_coeff_0
  · exact barrierCase2AYTransform1Explicit_coeff_1
  · exact barrierCase2AYTransform1Explicit_coeff_2
  · exact barrierCase2AYTransform1Explicit_coeff_3
  · exact barrierCase2AYTransform1Explicit_coeff_4
  · exact barrierCase2AYTransform1Explicit_coeff_5
  · exact barrierCase2AYTransform1Explicit_coeff_6
  · exact barrierCase2AYTransform1Explicit_coeff_7
  · exact barrierCase2AYTransform1Explicit_coeff_8
  · exact barrierCase2AYTransform1Explicit_coeff_9
  · exact barrierCase2AYTransform1Explicit_coeff_10
  · exact barrierCase2AYTransform1Explicit_coeff_11
  · exact barrierCase2AYTransform1Explicit_coeff_12
  · exact barrierCase2AYTransform1Explicit_coeff_13
  · exact barrierCase2AYTransform1Explicit_coeff_14
  · exact barrierCase2AYTransform1Explicit_coeff_15
  · exact barrierCase2AYTransform1Explicit_coeff_16
  · exact barrierCase2AYTransform1Explicit_coeff_17
  · exact barrierCase2AYTransform1Explicit_coeff_18
  · exact barrierCase2AYTransform1Explicit_coeff_19
  · exact barrierCase2AYTransform1Explicit_coeff_20
  · exact barrierCase2AYTransform1Explicit_coeff_21
  · exact barrierCase2AYTransform1Explicit_coeff_22
  · exact barrierCase2AYTransform1Explicit_coeff_23
  · exact barrierCase2AYTransform1Explicit_coeff_24

theorem barrierCase2AY_transform1_eq_explicit :
    barrierDescartesTransform (barrierCase2AY.map (Rat.castHom ℝ)) 24 (1/4) (1/2) =
      barrierCase2AYTransform1Explicit := by
  apply Polynomial.ext
  intro h
  by_cases hh : h < 25
  · have hc := barrierDescartesTransform_coeff_rat barrierCase2AY
      barrierCase2AYCoefficient 24 (1/4) (1/2) h barrierCase2AY_coeff_small
    have hr := barrierCase2AY_transform1_all_coeff_rat ⟨h, hh⟩
    change barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1/4) (1/2) h =
      barrierCase2AYTransform1Coefficient h at hr
    rw [hr] at hc
    have ha : ((1/4 : ℚ) : ℝ) = (1/4 : ℝ) := by norm_num
    have hb : ((1/2 : ℚ) : ℝ) = (1/2 : ℝ) := by norm_num
    rw [ha, hb] at hc
    exact hc.trans (barrierCase2AYTransform1Explicit_coeff h hh).symm
  · rw [barrierDescartesTransform_coeff_zero_above _ _ _ _ (by omega)]
    symm
    apply coeff_eq_zero_of_natDegree_lt
    rw [barrierCase2AYTransform1Explicit_natDegree]
    omega

end

noncomputable section

open Polynomial

theorem barrierCase2AY_transform1_signVariations :
    (barrierDescartesTransform (barrierCase2AY.map (Rat.castHom ℝ))
      24 (1/4) (1/2)).signVariations = 2 := by
  rw [barrierCase2AY_transform1_eq_explicit]
  have hd : barrierCase2AYTransform1Explicit.degree = 24 := by
    unfold barrierCase2AYTransform1Explicit
    compute_degree!
  rw [signVariations, coeffList, hd]
  norm_num [barrierCase2AYTransform1Explicit_coeff, barrierCase2AYTransform1Coefficient,
    List.range_succ, List.signVariations, List.destutter, List.destutter', sign_apply,
    coeff_C_mul, coeff_X_pow, coeff_X]

theorem barrierCase2AY_transform1_positive_roots_le :
    (barrierDescartesTransform (barrierCase2AY.map (Rat.castHom ℝ))
      24 (1/4) (1/2)).roots.countP (fun x => 0 < x) ≤ 2 := by
  have h := Polynomial.roots_countP_pos_le_signVariations
    (barrierDescartesTransform (barrierCase2AY.map (Rat.castHom ℝ)) 24 (1/4) (1/2))
  simpa only [barrierCase2AY_transform1_signVariations] using h

end

end InternalCatalan

end OAI
