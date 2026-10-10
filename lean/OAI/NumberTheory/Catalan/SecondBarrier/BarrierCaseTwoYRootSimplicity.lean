import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.RuleOfSigns
import OAI.NumberTheory.Catalan.Energy.BarrierBracketRootSimplicity
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoBracketYGroup0
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoDescartesY0
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoDescartesY1
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoDescartesY2
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoDescartesY3Group3

namespace OAI

noncomputable section

namespace InternalCatalan

section

open Polynomial

theorem barrier_case2_AY_transform3_coeff_rat_20 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (3 / 4) (1) 20 =
      barrierCase2AYTransform3Coefficient 20 := by decide +kernel

theorem barrier_case2_AY_transform3_coeff_rat_21 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (3 / 4) (1) 21 =
      barrierCase2AYTransform3Coefficient 21 := by decide +kernel

theorem barrier_case2_AY_transform3_coeff_rat_22 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (3 / 4) (1) 22 =
      barrierCase2AYTransform3Coefficient 22 := by decide +kernel

theorem barrier_case2_AY_transform3_coeff_rat_23 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (3 / 4) (1) 23 =
      barrierCase2AYTransform3Coefficient 23 := by decide +kernel

theorem barrier_case2_AY_transform3_coeff_rat_24 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (3 / 4) (1) 24 =
      barrierCase2AYTransform3Coefficient 24 := by decide +kernel

theorem barrier_case2_AY_transform3_explicit_coeff_20 :
    barrierCase2AYTransform3Explicit.coeff 20 =
      (barrierCase2AYTransform3Coefficient 20 : ℝ) := by
  simp only [barrierCase2AYTransform3Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform3Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform3_explicit_coeff_21 :
    barrierCase2AYTransform3Explicit.coeff 21 =
      (barrierCase2AYTransform3Coefficient 21 : ℝ) := by
  simp only [barrierCase2AYTransform3Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform3Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform3_explicit_coeff_22 :
    barrierCase2AYTransform3Explicit.coeff 22 =
      (barrierCase2AYTransform3Coefficient 22 : ℝ) := by
  simp only [barrierCase2AYTransform3Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform3Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform3_explicit_coeff_23 :
    barrierCase2AYTransform3Explicit.coeff 23 =
      (barrierCase2AYTransform3Coefficient 23 : ℝ) := by
  simp only [barrierCase2AYTransform3Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform3Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform3_explicit_coeff_24 :
    barrierCase2AYTransform3Explicit.coeff 24 =
      (barrierCase2AYTransform3Coefficient 24 : ℝ) := by
  simp only [barrierCase2AYTransform3Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform3Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AY_transform3_all_coeff_rat (h : Fin 25) :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (3 / 4) (1) h.val =
      barrierCase2AYTransform3Coefficient h.val := by
  rcases h with ⟨h, hh⟩
  change barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (3 / 4) (1) h =
    barrierCase2AYTransform3Coefficient h
  interval_cases h
  · exact barrier_case2_AY_transform3_coeff_rat_0
  · exact barrier_case2_AY_transform3_coeff_rat_1
  · exact barrier_case2_AY_transform3_coeff_rat_2
  · exact barrier_case2_AY_transform3_coeff_rat_3
  · exact barrier_case2_AY_transform3_coeff_rat_4
  · exact barrier_case2_AY_transform3_coeff_rat_5
  · exact barrier_case2_AY_transform3_coeff_rat_6
  · exact barrier_case2_AY_transform3_coeff_rat_7
  · exact barrier_case2_AY_transform3_coeff_rat_8
  · exact barrier_case2_AY_transform3_coeff_rat_9
  · exact barrier_case2_AY_transform3_coeff_rat_10
  · exact barrier_case2_AY_transform3_coeff_rat_11
  · exact barrier_case2_AY_transform3_coeff_rat_12
  · exact barrier_case2_AY_transform3_coeff_rat_13
  · exact barrier_case2_AY_transform3_coeff_rat_14
  · exact barrier_case2_AY_transform3_coeff_rat_15
  · exact barrier_case2_AY_transform3_coeff_rat_16
  · exact barrier_case2_AY_transform3_coeff_rat_17
  · exact barrier_case2_AY_transform3_coeff_rat_18
  · exact barrier_case2_AY_transform3_coeff_rat_19
  · exact barrier_case2_AY_transform3_coeff_rat_20
  · exact barrier_case2_AY_transform3_coeff_rat_21
  · exact barrier_case2_AY_transform3_coeff_rat_22
  · exact barrier_case2_AY_transform3_coeff_rat_23
  · exact barrier_case2_AY_transform3_coeff_rat_24

theorem barrierCase2AYTransform3Explicit_coeff (h : ℕ) (hh : h < 25) :
    barrierCase2AYTransform3Explicit.coeff h =
      (barrierCase2AYTransform3Coefficient h : ℝ) := by
  interval_cases h
  · exact barrier_case2_AY_transform3_explicit_coeff_0
  · exact barrier_case2_AY_transform3_explicit_coeff_1
  · exact barrier_case2_AY_transform3_explicit_coeff_2
  · exact barrier_case2_AY_transform3_explicit_coeff_3
  · exact barrier_case2_AY_transform3_explicit_coeff_4
  · exact barrier_case2_AY_transform3_explicit_coeff_5
  · exact barrier_case2_AY_transform3_explicit_coeff_6
  · exact barrier_case2_AY_transform3_explicit_coeff_7
  · exact barrier_case2_AY_transform3_explicit_coeff_8
  · exact barrier_case2_AY_transform3_explicit_coeff_9
  · exact barrier_case2_AY_transform3_explicit_coeff_10
  · exact barrier_case2_AY_transform3_explicit_coeff_11
  · exact barrier_case2_AY_transform3_explicit_coeff_12
  · exact barrier_case2_AY_transform3_explicit_coeff_13
  · exact barrier_case2_AY_transform3_explicit_coeff_14
  · exact barrier_case2_AY_transform3_explicit_coeff_15
  · exact barrier_case2_AY_transform3_explicit_coeff_16
  · exact barrier_case2_AY_transform3_explicit_coeff_17
  · exact barrier_case2_AY_transform3_explicit_coeff_18
  · exact barrier_case2_AY_transform3_explicit_coeff_19
  · exact barrier_case2_AY_transform3_explicit_coeff_20
  · exact barrier_case2_AY_transform3_explicit_coeff_21
  · exact barrier_case2_AY_transform3_explicit_coeff_22
  · exact barrier_case2_AY_transform3_explicit_coeff_23
  · exact barrier_case2_AY_transform3_explicit_coeff_24

theorem barrierCase2AY_transform3_eq_explicit :
    barrierDescartesTransform (barrierCase2AY.map (Rat.castHom ℝ)) 24 (3 / 4) (1) =
      barrierCase2AYTransform3Explicit := by
  apply Polynomial.ext
  intro h
  by_cases hh : h < 25
  · have hc := barrierDescartesTransform_coeff_rat barrierCase2AY
      barrierCase2AYCoefficient 24 (3 / 4) (1) h barrierCase2AY_coeff_small
    have hr := barrierCase2AY_transform3_all_coeff_rat ⟨h, hh⟩
    change barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (3 / 4) (1) h =
      barrierCase2AYTransform3Coefficient h at hr
    rw [hr] at hc
    have ha : ((3 / 4 : ℚ) : ℝ) = (3 / 4 : ℝ) := by norm_num
    have hb : ((1 : ℚ) : ℝ) = (1 : ℝ) := by norm_num
    rw [ha, hb] at hc
    exact hc.trans (barrierCase2AYTransform3Explicit_coeff h hh).symm
  · rw [barrierDescartesTransform_coeff_zero_above _ _ _ _ (by omega)]
    symm
    apply coeff_eq_zero_of_natDegree_lt
    rw [barrierCase2AYTransform3Explicit_natDegree]
    omega

theorem barrierCase2AY_transform3_signVariations :
    (barrierDescartesTransform (barrierCase2AY.map (Rat.castHom ℝ)) 24 (3 / 4) (1)).signVariations =
      6 := by
  rw [barrierCase2AY_transform3_eq_explicit]
  have hd : barrierCase2AYTransform3Explicit.degree = 24 := by
    unfold barrierCase2AYTransform3Explicit
    compute_degree!
  rw [signVariations, coeffList, hd]
  norm_num [barrierCase2AYTransform3Explicit_coeff, barrierCase2AYTransform3Coefficient,
    List.signVariations, List.range_succ, List.destutter, List.destutter', sign_apply,
    coeff_C_mul, coeff_X_pow, coeff_X]

theorem barrierCase2AY_transform3_positive_roots_le :
    (barrierDescartesTransform (barrierCase2AY.map (Rat.castHom ℝ)) 24 (3 / 4) (1)).roots.countP
      (fun x => 0 < x) ≤ 6 := by
  have h := Polynomial.roots_countP_pos_le_signVariations
    (barrierDescartesTransform (barrierCase2AY.map (Rat.castHom ℝ)) 24 (3 / 4) (1))
  simpa only [barrierCase2AY_transform3_signVariations] using h

end

section

theorem barrierCase2AY_bracket_sign_03 :
    barrierCase2AY.eval (barrierBracketLeft (1227250753)) *
      barrierCase2AY.eval (barrierBracketRight (1227250753)) < 0 := by
  rw [barrierCase2AY_eval_finite (barrierBracketLeft (1227250753)),
    barrierCase2AY_eval_finite (barrierBracketRight (1227250753))]
  decide +kernel

theorem barrierCase2AY_bracket_sign_04 :
    barrierCase2AY.eval (barrierBracketLeft (2149465998)) *
      barrierCase2AY.eval (barrierBracketRight (2149465998)) < 0 := by
  rw [barrierCase2AY_eval_finite (barrierBracketLeft (2149465998)),
    barrierCase2AY_eval_finite (barrierBracketRight (2149465998))]
  decide +kernel

theorem barrierCase2AY_bracket_sign_05 :
    barrierCase2AY.eval (barrierBracketLeft (3048189112)) *
      barrierCase2AY.eval (barrierBracketRight (3048189112)) < 0 := by
  rw [barrierCase2AY_eval_finite (barrierBracketLeft (3048189112)),
    barrierCase2AY_eval_finite (barrierBracketRight (3048189112))]
  decide +kernel

theorem barrierCase2AY_bracket_sign_06 :
    barrierCase2AY.eval (barrierBracketLeft (4322699096)) *
      barrierCase2AY.eval (barrierBracketRight (4322699096)) < 0 := by
  rw [barrierCase2AY_eval_finite (barrierBracketLeft (4322699096)),
    barrierCase2AY_eval_finite (barrierBracketRight (4322699096))]
  decide +kernel

theorem barrierCase2AY_bracket_sign_07 :
    barrierCase2AY.eval (barrierBracketLeft (5564757994)) *
      barrierCase2AY.eval (barrierBracketRight (5564757994)) < 0 := by
  rw [barrierCase2AY_eval_finite (barrierBracketLeft (5564757994)),
    barrierCase2AY_eval_finite (barrierBracketRight (5564757994))]
  decide +kernel

theorem barrierCase2AY_bracket_sign_08 :
    barrierCase2AY.eval (barrierBracketLeft (6801929373)) *
      barrierCase2AY.eval (barrierBracketRight (6801929373)) < 0 := by
  rw [barrierCase2AY_eval_finite (barrierBracketLeft (6801929373)),
    barrierCase2AY_eval_finite (barrierBracketRight (6801929373))]
  decide +kernel

theorem barrierCase2AY_bracket_sign_09 :
    barrierCase2AY.eval (barrierBracketLeft (8031988371)) *
      barrierCase2AY.eval (barrierBracketRight (8031988371)) < 0 := by
  rw [barrierCase2AY_eval_finite (barrierBracketLeft (8031988371)),
    barrierCase2AY_eval_finite (barrierBracketRight (8031988371))]
  decide +kernel

theorem barrierCase2AY_bracket_sign_10 :
    barrierCase2AY.eval (barrierBracketLeft (8877037851)) *
      barrierCase2AY.eval (barrierBracketRight (8877037851)) < 0 := by
  rw [barrierCase2AY_eval_finite (barrierBracketLeft (8877037851)),
    barrierCase2AY_eval_finite (barrierBracketRight (8877037851))]
  decide +kernel

theorem barrierCase2AY_bracket_sign_11 :
    barrierCase2AY.eval (barrierBracketLeft (9577761832)) *
      barrierCase2AY.eval (barrierBracketRight (9577761832)) < 0 := by
  rw [barrierCase2AY_eval_finite (barrierBracketLeft (9577761832)),
    barrierCase2AY_eval_finite (barrierBracketRight (9577761832))]
  decide +kernel

theorem barrierCase2AY_bracket_sign_12 :
    barrierCase2AY.eval (barrierBracketLeft (9838463999)) *
      barrierCase2AY.eval (barrierBracketRight (9838463999)) < 0 := by
  rw [barrierCase2AY_eval_finite (barrierBracketLeft (9838463999)),
    barrierCase2AY_eval_finite (barrierBracketRight (9838463999))]
  decide +kernel

theorem barrierCase2AY_bracket_sign_13 :
    barrierCase2AY.eval (barrierBracketLeft (9972727815)) *
      barrierCase2AY.eval (barrierBracketRight (9972727815)) < 0 := by
  rw [barrierCase2AY_eval_finite (barrierBracketLeft (9972727815)),
    barrierCase2AY_eval_finite (barrierBracketRight (9972727815))]
  decide +kernel

theorem barrierCase2AY_bracket_sign_14 :
    barrierCase2AY.eval (barrierBracketLeft (9992037196)) *
      barrierCase2AY.eval (barrierBracketRight (9992037196)) < 0 := by
  rw [barrierCase2AY_eval_finite (barrierBracketLeft (9992037196)),
    barrierCase2AY_eval_finite (barrierBracketRight (9992037196))]
  decide +kernel

open Polynomial

def barrierCase2XBrackets : List ℤ :=
  [-9601109148, -8942317572, -7608305633,
   -6503394794, -5185864065, -4015634158,
   -3108806646, -2067921826, -1589849496,
   1531948062, 2072448179, 3208186484,
   4381119427, 5851354199, 7269030693,
   8390277402, 9332614564, 9709786219]

theorem barrierCase2AX_bracket_signs (m : ℤ) (hm : m ∈ barrierCase2XBrackets) :
    barrierCase2AX.eval (barrierBracketLeft m) *
      barrierCase2AX.eval (barrierBracketRight m) < 0 := by
  simp only [barrierCase2XBrackets, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact barrierCase2AX_bracket_sign_00
  · exact barrierCase2AX_bracket_sign_01
  · exact barrierCase2AX_bracket_sign_02
  · exact barrierCase2AX_bracket_sign_03
  · exact barrierCase2AX_bracket_sign_04
  · exact barrierCase2AX_bracket_sign_05
  · exact barrierCase2AX_bracket_sign_06
  · exact barrierCase2AX_bracket_sign_07
  · exact barrierCase2AX_bracket_sign_08
  · exact barrierCase2AX_bracket_sign_09
  · exact barrierCase2AX_bracket_sign_10
  · exact barrierCase2AX_bracket_sign_11
  · exact barrierCase2AX_bracket_sign_12
  · exact barrierCase2AX_bracket_sign_13
  · exact barrierCase2AX_bracket_sign_14
  · exact barrierCase2AX_bracket_sign_15
  · exact barrierCase2AX_bracket_sign_16
  · exact barrierCase2AX_bracket_sign_17

theorem barrierCase2X_bracket_domain (m : ℤ) (hm : m ∈ barrierCase2XBrackets) :
    -1 < barrierBracketLeft m ∧
      barrierBracketLeft m < barrierBracketRight m ∧
      barrierBracketRight m < 1 ∧
      (barrierBracketRight m < 0 ∨ 0 < barrierBracketLeft m) := by
  simp only [barrierCase2XBrackets, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  <;> norm_num [barrierBracketLeft, barrierBracketRight]

def barrierCase2YBrackets : List ℤ :=
  [176402802, 330649406, 764952882,
   1227250753, 2149465998, 3048189112,
   4322699096, 5564757994, 6801929373,
   8031988371, 8877037851, 9577761832,
   9838463999, 9972727815, 9992037196]

theorem barrierCase2AY_bracket_signs (m : ℤ) (hm : m ∈ barrierCase2YBrackets) :
    barrierCase2AY.eval (barrierBracketLeft m) *
      barrierCase2AY.eval (barrierBracketRight m) < 0 := by
  simp only [barrierCase2YBrackets, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact barrierCase2AY_bracket_sign_00
  · exact barrierCase2AY_bracket_sign_01
  · exact barrierCase2AY_bracket_sign_02
  · exact barrierCase2AY_bracket_sign_03
  · exact barrierCase2AY_bracket_sign_04
  · exact barrierCase2AY_bracket_sign_05
  · exact barrierCase2AY_bracket_sign_06
  · exact barrierCase2AY_bracket_sign_07
  · exact barrierCase2AY_bracket_sign_08
  · exact barrierCase2AY_bracket_sign_09
  · exact barrierCase2AY_bracket_sign_10
  · exact barrierCase2AY_bracket_sign_11
  · exact barrierCase2AY_bracket_sign_12
  · exact barrierCase2AY_bracket_sign_13
  · exact barrierCase2AY_bracket_sign_14

theorem barrierCase2Y_bracket_domain (m : ℤ) (hm : m ∈ barrierCase2YBrackets) :
    0 < barrierBracketLeft m ∧
      barrierBracketLeft m < barrierBracketRight m ∧
      barrierBracketRight m < 1 := by
  simp only [barrierCase2YBrackets, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  <;> norm_num [barrierBracketLeft, barrierBracketRight]

end

theorem barrierCase2AX_bracket_root (m : ℤ)
    (hm : m ∈ barrierCase2XBrackets) :
    ∃ x : ℝ, x ∈ Set.Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ) ∧
      (barrierCase2AX.map (Rat.castHom ℝ)).eval x = 0 := by
  exact rationalPolynomial_root_mem_Ioo_of_eval_mul_neg barrierCase2AX
    (barrierCase2X_bracket_domain m hm).2.1 (barrierCase2AX_bracket_signs m hm)

theorem barrierCase2AY_bracket_root (m : ℤ)
    (hm : m ∈ barrierCase2YBrackets) :
    ∃ x : ℝ, x ∈ Set.Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ) ∧
      (barrierCase2AY.map (Rat.castHom ℝ)).eval x = 0 := by
  exact rationalPolynomial_root_mem_Ioo_of_eval_mul_neg barrierCase2AY
    (barrierCase2Y_bracket_domain m hm).2.1 (barrierCase2AY_bracket_signs m hm)

open Polynomial

private theorem barrierCase2AY_mapped_natDegree_le :
    (barrierCase2AY.map (Rat.castHom ℝ)).natDegree ≤ 24 := by
  calc
    _ ≤ barrierCase2AY.natDegree := Polynomial.natDegree_map_le
    _ = 24 := barrierCase2AY_natDegree

theorem barrierCase2AY_interval0_roots_card_le (s : Finset ℝ)
    (hs : ∀ x ∈ s, x ∈ Set.Ioo (0 : ℝ) (1 / 4) ∧
      (barrierCase2AY.map (Rat.castHom ℝ)).eval x = 0) :
    s.card ≤ 5 := by
  have hne : barrierDescartesTransform
      (barrierCase2AY.map (Rat.castHom ℝ)) 24 (0) (1 / 4) ≠ 0 := by
    intro hz
    have h := barrierCase2AY_transform0_signVariations
    rw [hz, Polynomial.signVariations_zero] at h
    norm_num at h
  simpa only [barrierCase2AY_transform0_signVariations] using
    barrierDescartes_interval_roots_card_le
      (barrierCase2AY.map (Rat.castHom ℝ)) 24 (0) (1 / 4)
      barrierCase2AY_mapped_natDegree_le hne s hs

theorem barrierCase2AY_interval1_roots_card_le (s : Finset ℝ)
    (hs : ∀ x ∈ s, x ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2) ∧
      (barrierCase2AY.map (Rat.castHom ℝ)).eval x = 0) :
    s.card ≤ 2 := by
  have hne : barrierDescartesTransform
      (barrierCase2AY.map (Rat.castHom ℝ)) 24 (1 / 4) (1 / 2) ≠ 0 := by
    intro hz
    have h := barrierCase2AY_transform1_signVariations
    rw [hz, Polynomial.signVariations_zero] at h
    norm_num at h
  simpa only [barrierCase2AY_transform1_signVariations] using
    barrierDescartes_interval_roots_card_le
      (barrierCase2AY.map (Rat.castHom ℝ)) 24 (1 / 4) (1 / 2)
      barrierCase2AY_mapped_natDegree_le hne s hs

theorem barrierCase2AY_interval2_roots_card_le (s : Finset ℝ)
    (hs : ∀ x ∈ s, x ∈ Set.Ioo (1 / 2 : ℝ) (3 / 4) ∧
      (barrierCase2AY.map (Rat.castHom ℝ)).eval x = 0) :
    s.card ≤ 2 := by
  have hne : barrierDescartesTransform
      (barrierCase2AY.map (Rat.castHom ℝ)) 24 (1 / 2) (3 / 4) ≠ 0 := by
    intro hz
    have h := barrierCase2AY_transform2_signVariations
    rw [hz, Polynomial.signVariations_zero] at h
    norm_num at h
  simpa only [barrierCase2AY_transform2_signVariations] using
    barrierDescartes_interval_roots_card_le
      (barrierCase2AY.map (Rat.castHom ℝ)) 24 (1 / 2) (3 / 4)
      barrierCase2AY_mapped_natDegree_le hne s hs

theorem barrierCase2AY_interval3_roots_card_le (s : Finset ℝ)
    (hs : ∀ x ∈ s, x ∈ Set.Ioo (3 / 4 : ℝ) (1) ∧
      (barrierCase2AY.map (Rat.castHom ℝ)).eval x = 0) :
    s.card ≤ 6 := by
  have hne : barrierDescartesTransform
      (barrierCase2AY.map (Rat.castHom ℝ)) 24 (3 / 4) (1) ≠ 0 := by
    intro hz
    have h := barrierCase2AY_transform3_signVariations
    rw [hz, Polynomial.signVariations_zero] at h
    norm_num at h
  simpa only [barrierCase2AY_transform3_signVariations] using
    barrierDescartes_interval_roots_card_le
      (barrierCase2AY.map (Rat.castHom ℝ)) 24 (3 / 4) (1)
      barrierCase2AY_mapped_natDegree_le hne s hs

private theorem barrierCase2AY_map_eval_rat_ne_zero (q : ℚ)
    (hq : barrierCase2AY.eval q ≠ 0) :
    (barrierCase2AY.map (Rat.castHom ℝ)).eval (q : ℝ) ≠ 0 := by
  have heval : (barrierCase2AY.map (Rat.castHom ℝ)).eval (q : ℝ) =
      ((barrierCase2AY.eval q : ℚ) : ℝ) := by
    change (barrierCase2AY.map (Rat.castHom ℝ)).eval ((Rat.castHom ℝ) q) =
      (Rat.castHom ℝ) (barrierCase2AY.eval q)
    exact Polynomial.eval_map_apply (Rat.castHom ℝ) q
  rw [heval]
  exact_mod_cast hq

private theorem barrierCase2AY_root_subdivision {x : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (hr : (barrierCase2AY.map (Rat.castHom ℝ)).eval x = 0) :
    x ∈ Set.Ioo (0 : ℝ) (1 / 4) ∨ x ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2) ∨
      x ∈ Set.Ioo (1 / 2 : ℝ) (3 / 4) ∨ x ∈ Set.Ioo (3 / 4 : ℝ) 1 := by
  have hq1 : (barrierCase2AY.map (Rat.castHom ℝ)).eval (1 / 4 : ℝ) ≠ 0 := by
    simpa using barrierCase2AY_map_eval_rat_ne_zero (1 / 4)
      barrierCase2AY_quarter_nonzero.1
  have hq2 : (barrierCase2AY.map (Rat.castHom ℝ)).eval (1 / 2 : ℝ) ≠ 0 := by
    simpa using barrierCase2AY_map_eval_rat_ne_zero (1 / 2)
      barrierCase2AY_quarter_nonzero.2.1
  have hq3 : (barrierCase2AY.map (Rat.castHom ℝ)).eval (3 / 4 : ℝ) ≠ 0 := by
    simpa using barrierCase2AY_map_eval_rat_ne_zero (3 / 4)
      barrierCase2AY_quarter_nonzero.2.2
  have hn1 : x ≠ (1 / 4 : ℝ) := by
    intro heq
    exact hq1 (by simpa only [heq] using hr)
  have hn2 : x ≠ (1 / 2 : ℝ) := by
    intro heq
    exact hq2 (by simpa only [heq] using hr)
  have hn3 : x ≠ (3 / 4 : ℝ) := by
    intro heq
    exact hq3 (by simpa only [heq] using hr)
  rcases lt_or_gt_of_ne hn1 with hlt1 | hgt1
  · exact Or.inl ⟨hx.1, hlt1⟩
  · rcases lt_or_gt_of_ne hn2 with hlt2 | hgt2
    · exact Or.inr (Or.inl ⟨hgt1, hlt2⟩)
    · rcases lt_or_gt_of_ne hn3 with hlt3 | hgt3
      · exact Or.inr (Or.inr (Or.inl ⟨hgt2, hlt3⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨hgt3, hx.2⟩))

theorem barrierCase2AY_interval_roots_card_le (s : Finset ℝ)
    (hs : ∀ x ∈ s, x ∈ Set.Ioo (0 : ℝ) 1 ∧
      (barrierCase2AY.map (Rat.castHom ℝ)).eval x = 0) :
    s.card ≤ 15 := by
  classical
  let s0 := s.filter (fun x => x ∈ Set.Ioo (0 : ℝ) (1 / 4))
  let s1 := s.filter (fun x => x ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2))
  let s2 := s.filter (fun x => x ∈ Set.Ioo (1 / 2 : ℝ) (3 / 4))
  let s3 := s.filter (fun x => x ∈ Set.Ioo (3 / 4 : ℝ) 1)
  have h0 : s0.card ≤ 5 := by
    apply barrierCase2AY_interval0_roots_card_le
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    exact ⟨hx'.2, (hs x hx'.1).2⟩
  have h1 : s1.card ≤ 2 := by
    apply barrierCase2AY_interval1_roots_card_le
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    exact ⟨hx'.2, (hs x hx'.1).2⟩
  have h2 : s2.card ≤ 2 := by
    apply barrierCase2AY_interval2_roots_card_le
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    exact ⟨hx'.2, (hs x hx'.1).2⟩
  have h3 : s3.card ≤ 6 := by
    apply barrierCase2AY_interval3_roots_card_le
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    exact ⟨hx'.2, (hs x hx'.1).2⟩
  have hcover : s ⊆ s0 ∪ (s1 ∪ (s2 ∪ s3)) := by
    intro x hx
    have hparts := barrierCase2AY_root_subdivision (hs x hx).1 (hs x hx).2
    simp only [Finset.mem_union]
    rcases hparts with hx0 | hx1 | hx2 | hx3
    · exact Or.inl (Finset.mem_filter.mpr ⟨hx, hx0⟩)
    · exact Or.inr (Or.inl (Finset.mem_filter.mpr ⟨hx, hx1⟩))
    · exact Or.inr (Or.inr (Or.inl (Finset.mem_filter.mpr ⟨hx, hx2⟩)))
    · exact Or.inr (Or.inr (Or.inr (Finset.mem_filter.mpr ⟨hx, hx3⟩)))
  calc
    s.card ≤ (s0 ∪ (s1 ∪ (s2 ∪ s3))).card := Finset.card_le_card hcover
    _ ≤ s0.card + (s1 ∪ (s2 ∪ s3)).card := Finset.card_union_le _ _
    _ ≤ s0.card + (s1.card + (s2 ∪ s3).card) :=
      Nat.add_le_add_left (Finset.card_union_le _ _) _
    _ ≤ s0.card + (s1.card + (s2.card + s3.card)) :=
      Nat.add_le_add_left (Nat.add_le_add_left (Finset.card_union_le _ _) _) _
    _ ≤ 5 + (2 + (2 + 6)) := Nat.add_le_add h0 (Nat.add_le_add h1 (Nat.add_le_add h2 h3))
    _ = 15 := rfl

private theorem barrierCase2Y_bracket_subset_interval {m : ℤ}
    (hm : m ∈ barrierCase2YBrackets) {x : ℝ}
    (hx : x ∈ Set.Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ)) :
    x ∈ Set.Ioo (0 : ℝ) 1 := by
  obtain ⟨ha, _, hb⟩ := barrierCase2Y_bracket_domain m hm
  have ha' : (0 : ℝ) < (barrierBracketLeft m : ℝ) := by exact_mod_cast ha
  have hb' : (barrierBracketRight m : ℝ) < (1 : ℝ) := by exact_mod_cast hb
  exact ⟨ha'.trans hx.1, hx.2.trans hb'⟩

private theorem barrierCase2Y_bracket_separation :
    ∀ m ∈ barrierCase2YBrackets, ∀ n ∈ barrierCase2YBrackets,
      m ≠ n → m + 2 ≤ n ∨ n + 2 ≤ m := by decide +kernel

private theorem barrierBracketRight_le_left_of_separated {m n : ℤ}
    (h : m + 2 ≤ n) :
    (barrierBracketRight m : ℝ) ≤ (barrierBracketLeft n : ℝ) := by
  have hq : barrierBracketRight m ≤ barrierBracketLeft n := by
    unfold barrierBracketRight barrierBracketLeft
    apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℚ) ≤ 10000000000)
    exact_mod_cast h
  exact_mod_cast hq

private theorem barrierCase2Y_brackets_disjoint {m n : ℤ}
    (hm : m ∈ barrierCase2YBrackets) (hn : n ∈ barrierCase2YBrackets)
    (hmn : m ≠ n) {x : ℝ}
    (hx : x ∈ Set.Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ))
    (hy : x ∈ Set.Ioo (barrierBracketLeft n : ℝ) (barrierBracketRight n : ℝ)) :
    False := by
  rcases barrierCase2Y_bracket_separation m hm n hn hmn with hmn' | hnm'
  · have hs := barrierBracketRight_le_left_of_separated hmn'
    exact (not_lt_of_ge hs) (hy.1.trans hx.2)
  · have hs := barrierBracketRight_le_left_of_separated hnm'
    exact (not_lt_of_ge hs) (hx.1.trans hy.2)

private def barrierCase2YChosenRoot (m : ℤ) : ℝ :=
  if hm : m ∈ barrierCase2YBrackets then
    Classical.choose (barrierCase2AY_bracket_root m hm)
  else 0

private theorem barrierCase2YChosenRoot_spec (m : ℤ)
    (hm : m ∈ barrierCase2YBrackets) :
    barrierCase2YChosenRoot m ∈
        Set.Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ) ∧
      (barrierCase2AY.map (Rat.castHom ℝ)).eval (barrierCase2YChosenRoot m) = 0 := by
  simpa only [barrierCase2YChosenRoot, dite_eq_left hm] using
    Classical.choose_spec (barrierCase2AY_bracket_root m hm)

private def barrierCase2YChosenRoots : Finset ℝ := by
  classical
  exact barrierCase2YBrackets.toFinset.image barrierCase2YChosenRoot

private theorem barrierCase2YChosenRoots_card : barrierCase2YChosenRoots.card = 15 := by
  classical
  have hinj : Set.InjOn barrierCase2YChosenRoot
      (↑barrierCase2YBrackets.toFinset : Set ℤ) := by
    intro m hm n hn heq
    have hm' : m ∈ barrierCase2YBrackets := List.mem_toFinset.mp hm
    have hn' : n ∈ barrierCase2YBrackets := List.mem_toFinset.mp hn
    by_contra hmn
    exact barrierCase2Y_brackets_disjoint hm' hn' hmn
      (barrierCase2YChosenRoot_spec m hm').1
      (by simpa only [heq] using (barrierCase2YChosenRoot_spec n hn').1)
  unfold barrierCase2YChosenRoots
  rw [Finset.card_image_of_injOn hinj]
  norm_num [barrierCase2YBrackets]

private theorem barrierCase2YChosenRoots_spec {x : ℝ}
    (hx : x ∈ barrierCase2YChosenRoots) :
    x ∈ Set.Ioo (0 : ℝ) 1 ∧ (barrierCase2AY.map (Rat.castHom ℝ)).eval x = 0 := by
  classical
  change x ∈ barrierCase2YBrackets.toFinset.image barrierCase2YChosenRoot at hx
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hx
  have hm' : m ∈ barrierCase2YBrackets := List.mem_toFinset.mp hm
  have hr := barrierCase2YChosenRoot_spec m hm'
  exact ⟨barrierCase2Y_bracket_subset_interval hm' hr.1, hr.2⟩

private theorem barrierCase2AY_root_mem_chosen {x : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (hr : (barrierCase2AY.map (Rat.castHom ℝ)).eval x = 0) :
    x ∈ barrierCase2YChosenRoots := by
  classical
  by_contra hnot
  have hb : (insert x barrierCase2YChosenRoots).card ≤ 15 := by
    apply barrierCase2AY_interval_roots_card_le
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact ⟨hx, hr⟩
    · exact barrierCase2YChosenRoots_spec hy
  rw [Finset.card_insert_of_notMem hnot, barrierCase2YChosenRoots_card] at hb
  norm_num at hb

theorem barrierCase2AY_roots_exhausted {x : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (hr : (barrierCase2AY.map (Rat.castHom ℝ)).eval x = 0) :
    ∃ m ∈ barrierCase2YBrackets,
      x ∈ Set.Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ) := by
  classical
  have hmem := barrierCase2AY_root_mem_chosen hx hr
  change x ∈ barrierCase2YBrackets.toFinset.image barrierCase2YChosenRoot at hmem
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hmem
  have hm' : m ∈ barrierCase2YBrackets := List.mem_toFinset.mp hm
  exact ⟨m, hm', (barrierCase2YChosenRoot_spec m hm').1⟩

theorem barrierCase2AY_unique_root_in_bracket (m : ℤ)
    (hm : m ∈ barrierCase2YBrackets) :
    ∃! x : ℝ, x ∈ Set.Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ) ∧
      (barrierCase2AY.map (Rat.castHom ℝ)).eval x = 0 := by
  classical
  refine ⟨barrierCase2YChosenRoot m, barrierCase2YChosenRoot_spec m hm, ?_⟩
  intro y hy
  have hmem := barrierCase2AY_root_mem_chosen
    (barrierCase2Y_bracket_subset_interval hm hy.1) hy.2
  change y ∈ barrierCase2YBrackets.toFinset.image barrierCase2YChosenRoot at hmem
  obtain ⟨n, hn, heq⟩ := Finset.mem_image.mp hmem
  have hn' : n ∈ barrierCase2YBrackets := List.mem_toFinset.mp hn
  by_cases hnm : n = m
  · subst n
    exact heq.symm
  · exact False.elim (barrierCase2Y_brackets_disjoint hn' hm hnm
      (barrierCase2YChosenRoot_spec n hn').1 (by simpa only [heq] using hy.1))

open Polynomial

private theorem barrierCase2AY_simple_mapped_natDegree_le :
    (barrierCase2AY.map (Rat.castHom ℝ)).natDegree ≤ 24 := by
  calc
    _ ≤ barrierCase2AY.natDegree := Polynomial.natDegree_map_le
    _ = 24 := barrierCase2AY_natDegree

private theorem barrierCase2AY_simple_interval
    (a b : ℚ) (B : List ℤ) (n : ℕ) (hn : 0 < n)
    (hvar : (barrierDescartesTransform (barrierCase2AY.map (Rat.castHom ℝ))
      24 (a : ℝ) (b : ℝ)).signVariations = n)
    (hcard : B.toFinset.card = n)
    (hsep : ∀ m ∈ B, ∀ k ∈ B, m ≠ k → m + 2 ≤ k ∨ k + 2 ≤ m)
    (hinside : ∀ m ∈ B, a ≤ barrierBracketLeft m ∧ barrierBracketRight m ≤ b)
    (hsubset : ∀ m ∈ B, m ∈ barrierCase2YBrackets)
    {x : ℝ} (hx : x ∈ Set.Ioo (a : ℝ) (b : ℝ))
    (hp : (barrierCase2AY.map (Rat.castHom ℝ)).eval x = 0) :
    (barrierCase2AY.map (Rat.castHom ℝ)).rootMultiplicity x = 1 := by
  have hne : barrierDescartesTransform (barrierCase2AY.map (Rat.castHom ℝ))
      24 (a : ℝ) (b : ℝ) ≠ 0 := by
    intro hz
    have h := hvar
    rw [hz, Polynomial.signVariations_zero] at h
    exact (Nat.ne_of_gt hn) h.symm
  exact barrierDescartes_root_simple_of_brackets
    (barrierCase2AY.map (Rat.castHom ℝ)) 24 a b B
    barrierCase2AY_simple_mapped_natDegree_le hne hsep hinside
    (fun m hm => barrierCase2AY_bracket_root m (hsubset m hm))
    (le_of_eq (hvar.trans hcard.symm)) hx hp

private theorem barrierCase2AY_simple_interval0 {x : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) (1 / 4))
    (hp : (barrierCase2AY.map (Rat.castHom ℝ)).eval x = 0) :
    (barrierCase2AY.map (Rat.castHom ℝ)).rootMultiplicity x = 1 := by
  exact barrierCase2AY_simple_interval 0 (1 / 4)
    [176402802, 330649406, 764952882, 1227250753, 2149465998] 5
    (by decide)
    (by simpa using barrierCase2AY_transform0_signVariations)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by simpa using hx) hp

private theorem barrierCase2AY_simple_interval1 {x : ℝ}
    (hx : x ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2))
    (hp : (barrierCase2AY.map (Rat.castHom ℝ)).eval x = 0) :
    (barrierCase2AY.map (Rat.castHom ℝ)).rootMultiplicity x = 1 := by
  exact barrierCase2AY_simple_interval (1 / 4) (1 / 2)
    [3048189112, 4322699096] 2
    (by decide)
    (by simpa using barrierCase2AY_transform1_signVariations)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by simpa using hx) hp

private theorem barrierCase2AY_simple_interval2 {x : ℝ}
    (hx : x ∈ Set.Ioo (1 / 2 : ℝ) (3 / 4))
    (hp : (barrierCase2AY.map (Rat.castHom ℝ)).eval x = 0) :
    (barrierCase2AY.map (Rat.castHom ℝ)).rootMultiplicity x = 1 := by
  exact barrierCase2AY_simple_interval (1 / 2) (3 / 4)
    [5564757994, 6801929373] 2
    (by decide)
    (by simpa using barrierCase2AY_transform2_signVariations)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by simpa using hx) hp

private theorem barrierCase2AY_simple_interval3 {x : ℝ}
    (hx : x ∈ Set.Ioo (3 / 4 : ℝ) 1)
    (hp : (barrierCase2AY.map (Rat.castHom ℝ)).eval x = 0) :
    (barrierCase2AY.map (Rat.castHom ℝ)).rootMultiplicity x = 1 := by
  exact barrierCase2AY_simple_interval (3 / 4) 1
    [8031988371, 8877037851, 9577761832, 9838463999, 9972727815, 9992037196] 6
    (by decide)
    (by simpa using barrierCase2AY_transform3_signVariations)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by simpa using hx) hp

private theorem barrierCase2AY_simple_map_eval_rat_ne_zero (q : ℚ)
    (hq : barrierCase2AY.eval q ≠ 0) :
    (barrierCase2AY.map (Rat.castHom ℝ)).eval (q : ℝ) ≠ 0 := by
  have heval : (barrierCase2AY.map (Rat.castHom ℝ)).eval (q : ℝ) =
      ((barrierCase2AY.eval q : ℚ) : ℝ) := by
    change (barrierCase2AY.map (Rat.castHom ℝ)).eval ((Rat.castHom ℝ) q) =
      (Rat.castHom ℝ) (barrierCase2AY.eval q)
    exact Polynomial.eval_map_apply (Rat.castHom ℝ) q
  rw [heval]
  exact_mod_cast hq

private theorem barrierCase2AY_simple_root_subdivision {x : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (hr : (barrierCase2AY.map (Rat.castHom ℝ)).eval x = 0) :
    x ∈ Set.Ioo (0 : ℝ) (1 / 4) ∨ x ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2) ∨
      x ∈ Set.Ioo (1 / 2 : ℝ) (3 / 4) ∨ x ∈ Set.Ioo (3 / 4 : ℝ) 1 := by
  have hq1 : (barrierCase2AY.map (Rat.castHom ℝ)).eval (1 / 4 : ℝ) ≠ 0 := by
    simpa using barrierCase2AY_simple_map_eval_rat_ne_zero (1 / 4)
      barrierCase2AY_quarter_nonzero.1
  have hq2 : (barrierCase2AY.map (Rat.castHom ℝ)).eval (1 / 2 : ℝ) ≠ 0 := by
    simpa using barrierCase2AY_simple_map_eval_rat_ne_zero (1 / 2)
      barrierCase2AY_quarter_nonzero.2.1
  have hq3 : (barrierCase2AY.map (Rat.castHom ℝ)).eval (3 / 4 : ℝ) ≠ 0 := by
    simpa using barrierCase2AY_simple_map_eval_rat_ne_zero (3 / 4)
      barrierCase2AY_quarter_nonzero.2.2
  have hn1 : x ≠ (1 / 4 : ℝ) := by
    intro heq
    exact hq1 (by simpa only [heq] using hr)
  have hn2 : x ≠ (1 / 2 : ℝ) := by
    intro heq
    exact hq2 (by simpa only [heq] using hr)
  have hn3 : x ≠ (3 / 4 : ℝ) := by
    intro heq
    exact hq3 (by simpa only [heq] using hr)
  rcases lt_or_gt_of_ne hn1 with hlt1 | hgt1
  · exact Or.inl ⟨hx.1, hlt1⟩
  · rcases lt_or_gt_of_ne hn2 with hlt2 | hgt2
    · exact Or.inr (Or.inl ⟨hgt1, hlt2⟩)
    · rcases lt_or_gt_of_ne hn3 with hlt3 | hgt3
      · exact Or.inr (Or.inr (Or.inl ⟨hgt2, hlt3⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨hgt3, hx.2⟩))

theorem barrierCase2AY_rootMultiplicity_eq_one {x : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (hp : (barrierCase2AY.map (Rat.castHom ℝ)).eval x = 0) :
    (barrierCase2AY.map (Rat.castHom ℝ)).rootMultiplicity x = 1 := by
  rcases barrierCase2AY_simple_root_subdivision hx hp with h0 | h1 | h2 | h3
  · exact barrierCase2AY_simple_interval0 h0 hp
  · exact barrierCase2AY_simple_interval1 h1 hp
  · exact barrierCase2AY_simple_interval2 h2 hp
  · exact barrierCase2AY_simple_interval3 h3 hp

theorem barrierCase2AY_derivative_ne_zero_at_root {x : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (hp : (barrierCase2AY.map (Rat.castHom ℝ)).eval x = 0) :
    (barrierCase2AY.map (Rat.castHom ℝ)).derivative.eval x ≠ 0 := by
  have hm := barrierCase2AY_rootMultiplicity_eq_one hx hp
  have hne : barrierCase2AY.map (Rat.castHom ℝ) ≠ 0 := by
    intro hz
    simp only [hz, Polynomial.rootMultiplicity_zero, Nat.zero_ne_one] at hm
  intro hd
  have hgt := (Polynomial.one_lt_rootMultiplicity_iff_isRoot hne).mpr ⟨hp, hd⟩
  simp only [hm, lt_self_iff_false] at hgt

private theorem barrierCase2Y_simple_bracket_subset_interval {m : ℤ}
    (hm : m ∈ barrierCase2YBrackets) {x : ℝ}
    (hx : x ∈ Set.Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ)) :
    x ∈ Set.Ioo (0 : ℝ) 1 := by
  obtain ⟨ha, _, hb⟩ := barrierCase2Y_bracket_domain m hm
  have ha' : (0 : ℝ) < (barrierBracketLeft m : ℝ) := by exact_mod_cast ha
  have hb' : (barrierBracketRight m : ℝ) < (1 : ℝ) := by exact_mod_cast hb
  exact ⟨ha'.trans hx.1, hx.2.trans hb'⟩

theorem barrierCase2AY_simple_root_in_bracket (m : ℤ)
    (hm : m ∈ barrierCase2YBrackets) :
    ∃ x : ℝ, x ∈ Set.Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ) ∧
      (barrierCase2AY.map (Rat.castHom ℝ)).eval x = 0 ∧
      (barrierCase2AY.map (Rat.castHom ℝ)).rootMultiplicity x = 1 := by
  obtain ⟨x, hx, hp⟩ := barrierCase2AY_bracket_root m hm
  exact ⟨x, hx, hp,
    barrierCase2AY_rootMultiplicity_eq_one
      (barrierCase2Y_simple_bracket_subset_interval hm hx) hp⟩

theorem barrierCase2AY_unique_simple_root_in_bracket (m : ℤ)
    (hm : m ∈ barrierCase2YBrackets) :
    ∃! x : ℝ, x ∈ Set.Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ) ∧
      (barrierCase2AY.map (Rat.castHom ℝ)).eval x = 0 ∧
      (barrierCase2AY.map (Rat.castHom ℝ)).rootMultiplicity x = 1 := by
  obtain ⟨x, hx, huniq⟩ := barrierCase2AY_unique_root_in_bracket m hm
  refine ⟨x, ⟨hx.1, hx.2, barrierCase2AY_rootMultiplicity_eq_one
    (barrierCase2Y_simple_bracket_subset_interval hm hx.1) hx.2⟩, ?_⟩
  intro y hy
  exact huniq y ⟨hy.1, hy.2.1⟩

end InternalCatalan

end

end OAI
