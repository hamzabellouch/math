import Mathlib.Algebra.Polynomial.RuleOfSigns
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoDescartesY2Group3

namespace OAI

namespace InternalCatalan

section

open Polynomial

theorem barrier_case2_AY_transform2_coeff_rat_20 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1 / 2) (3 / 4) 20 =
      barrierCase2AYTransform2Coefficient 20 := by decide +kernel

theorem barrier_case2_AY_transform2_coeff_rat_21 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1 / 2) (3 / 4) 21 =
      barrierCase2AYTransform2Coefficient 21 := by decide +kernel

theorem barrier_case2_AY_transform2_coeff_rat_22 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1 / 2) (3 / 4) 22 =
      barrierCase2AYTransform2Coefficient 22 := by decide +kernel

theorem barrier_case2_AY_transform2_coeff_rat_23 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1 / 2) (3 / 4) 23 =
      barrierCase2AYTransform2Coefficient 23 := by decide +kernel

theorem barrier_case2_AY_transform2_coeff_rat_24 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1 / 2) (3 / 4) 24 =
      barrierCase2AYTransform2Coefficient 24 := by decide +kernel

theorem barrier_case2_AY_transform2_explicit_coeff_20 :
    barrierCase2AYTransform2Explicit.coeff 20 =
      (barrierCase2AYTransform2Coefficient 20 : ℝ) := by
  simp only [barrierCase2AYTransform2Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform2Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform2_explicit_coeff_21 :
    barrierCase2AYTransform2Explicit.coeff 21 =
      (barrierCase2AYTransform2Coefficient 21 : ℝ) := by
  simp only [barrierCase2AYTransform2Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform2Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform2_explicit_coeff_22 :
    barrierCase2AYTransform2Explicit.coeff 22 =
      (barrierCase2AYTransform2Coefficient 22 : ℝ) := by
  simp only [barrierCase2AYTransform2Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform2Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform2_explicit_coeff_23 :
    barrierCase2AYTransform2Explicit.coeff 23 =
      (barrierCase2AYTransform2Coefficient 23 : ℝ) := by
  simp only [barrierCase2AYTransform2Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform2Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform2_explicit_coeff_24 :
    barrierCase2AYTransform2Explicit.coeff 24 =
      (barrierCase2AYTransform2Coefficient 24 : ℝ) := by
  simp only [barrierCase2AYTransform2Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform2Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AY_transform2_all_coeff_rat (h : Fin 25) :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1 / 2) (3 / 4) h.val =
      barrierCase2AYTransform2Coefficient h.val := by
  rcases h with ⟨h, hh⟩
  change barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1 / 2) (3 / 4) h =
    barrierCase2AYTransform2Coefficient h
  interval_cases h
  · exact barrier_case2_AY_transform2_coeff_rat_0
  · exact barrier_case2_AY_transform2_coeff_rat_1
  · exact barrier_case2_AY_transform2_coeff_rat_2
  · exact barrier_case2_AY_transform2_coeff_rat_3
  · exact barrier_case2_AY_transform2_coeff_rat_4
  · exact barrier_case2_AY_transform2_coeff_rat_5
  · exact barrier_case2_AY_transform2_coeff_rat_6
  · exact barrier_case2_AY_transform2_coeff_rat_7
  · exact barrier_case2_AY_transform2_coeff_rat_8
  · exact barrier_case2_AY_transform2_coeff_rat_9
  · exact barrier_case2_AY_transform2_coeff_rat_10
  · exact barrier_case2_AY_transform2_coeff_rat_11
  · exact barrier_case2_AY_transform2_coeff_rat_12
  · exact barrier_case2_AY_transform2_coeff_rat_13
  · exact barrier_case2_AY_transform2_coeff_rat_14
  · exact barrier_case2_AY_transform2_coeff_rat_15
  · exact barrier_case2_AY_transform2_coeff_rat_16
  · exact barrier_case2_AY_transform2_coeff_rat_17
  · exact barrier_case2_AY_transform2_coeff_rat_18
  · exact barrier_case2_AY_transform2_coeff_rat_19
  · exact barrier_case2_AY_transform2_coeff_rat_20
  · exact barrier_case2_AY_transform2_coeff_rat_21
  · exact barrier_case2_AY_transform2_coeff_rat_22
  · exact barrier_case2_AY_transform2_coeff_rat_23
  · exact barrier_case2_AY_transform2_coeff_rat_24

theorem barrierCase2AYTransform2Explicit_coeff (h : ℕ) (hh : h < 25) :
    barrierCase2AYTransform2Explicit.coeff h =
      (barrierCase2AYTransform2Coefficient h : ℝ) := by
  interval_cases h
  · exact barrier_case2_AY_transform2_explicit_coeff_0
  · exact barrier_case2_AY_transform2_explicit_coeff_1
  · exact barrier_case2_AY_transform2_explicit_coeff_2
  · exact barrier_case2_AY_transform2_explicit_coeff_3
  · exact barrier_case2_AY_transform2_explicit_coeff_4
  · exact barrier_case2_AY_transform2_explicit_coeff_5
  · exact barrier_case2_AY_transform2_explicit_coeff_6
  · exact barrier_case2_AY_transform2_explicit_coeff_7
  · exact barrier_case2_AY_transform2_explicit_coeff_8
  · exact barrier_case2_AY_transform2_explicit_coeff_9
  · exact barrier_case2_AY_transform2_explicit_coeff_10
  · exact barrier_case2_AY_transform2_explicit_coeff_11
  · exact barrier_case2_AY_transform2_explicit_coeff_12
  · exact barrier_case2_AY_transform2_explicit_coeff_13
  · exact barrier_case2_AY_transform2_explicit_coeff_14
  · exact barrier_case2_AY_transform2_explicit_coeff_15
  · exact barrier_case2_AY_transform2_explicit_coeff_16
  · exact barrier_case2_AY_transform2_explicit_coeff_17
  · exact barrier_case2_AY_transform2_explicit_coeff_18
  · exact barrier_case2_AY_transform2_explicit_coeff_19
  · exact barrier_case2_AY_transform2_explicit_coeff_20
  · exact barrier_case2_AY_transform2_explicit_coeff_21
  · exact barrier_case2_AY_transform2_explicit_coeff_22
  · exact barrier_case2_AY_transform2_explicit_coeff_23
  · exact barrier_case2_AY_transform2_explicit_coeff_24

theorem barrierCase2AY_transform2_eq_explicit :
    barrierDescartesTransform (barrierCase2AY.map (Rat.castHom ℝ)) 24 (1 / 2) (3 / 4) =
      barrierCase2AYTransform2Explicit := by
  apply Polynomial.ext
  intro h
  by_cases hh : h < 25
  · have hc := barrierDescartesTransform_coeff_rat barrierCase2AY
      barrierCase2AYCoefficient 24 (1 / 2) (3 / 4) h barrierCase2AY_coeff_small
    have hr := barrierCase2AY_transform2_all_coeff_rat ⟨h, hh⟩
    change barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1 / 2) (3 / 4) h =
      barrierCase2AYTransform2Coefficient h at hr
    rw [hr] at hc
    have ha : ((1 / 2 : ℚ) : ℝ) = (1 / 2 : ℝ) := by norm_num
    have hb : ((3 / 4 : ℚ) : ℝ) = (3 / 4 : ℝ) := by norm_num
    rw [ha, hb] at hc
    exact hc.trans (barrierCase2AYTransform2Explicit_coeff h hh).symm
  · rw [barrierDescartesTransform_coeff_zero_above _ _ _ _ (by omega)]
    symm
    apply coeff_eq_zero_of_natDegree_lt
    rw [barrierCase2AYTransform2Explicit_natDegree]
    omega

end

noncomputable section

open Polynomial

theorem barrierCase2AY_transform2_signVariations :
    (barrierDescartesTransform (barrierCase2AY.map (Rat.castHom ℝ)) 24 (1 / 2) (3 / 4)).signVariations =
      2 := by
  rw [barrierCase2AY_transform2_eq_explicit]
  have hd : barrierCase2AYTransform2Explicit.degree = 24 := by
    unfold barrierCase2AYTransform2Explicit
    compute_degree!
  rw [signVariations, coeffList, hd]
  norm_num [barrierCase2AYTransform2Explicit_coeff, barrierCase2AYTransform2Coefficient,
    List.range_succ, List.signVariations, List.destutter, List.destutter', sign_apply,
    coeff_C_mul, coeff_X_pow, coeff_X]

theorem barrierCase2AY_transform2_positive_roots_le :
    (barrierDescartesTransform (barrierCase2AY.map (Rat.castHom ℝ)) 24 (1 / 2) (3 / 4)).roots.countP
      (fun x => 0 < x) ≤ 2 := by
  have h := Polynomial.roots_countP_pos_le_signVariations
    (barrierDescartesTransform (barrierCase2AY.map (Rat.castHom ℝ)) 24 (1 / 2) (3 / 4))
  simpa only [barrierCase2AY_transform2_signVariations] using h

end

end InternalCatalan

end OAI
