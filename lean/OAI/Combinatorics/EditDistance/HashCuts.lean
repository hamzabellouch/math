import Mathlib

namespace OAI

/-!
# Finite cut hashes and averaged separation
-/

namespace EditCutHash
attribute [local instance] Classical.propDecidable
open scoped BigOperators
open Finset

noncomputable def sep {X : Type*} (x y : X) : ℝ := if x = y then 0 else 1
lemma sep_nonneg {X : Type*} (x y : X) : 0 ≤ sep x y := by unfold sep; split <;> norm_num
lemma sep_le_one {X : Type*} (x y : X) : sep x y ≤ 1 := by unfold sep; split <;> norm_num
@[simp] lemma sep_self {X : Type*} (x : X) : sep x x = 0 := by simp [sep]
lemma sep_eq_one {X : Type*} {x y : X} (h : x ≠ y) : sep x y = 1 := by simp [sep,h]

section Hash
variable {I X : Type*} [Fintype I]

noncomputable def distance (w : I → ℝ) (c : I → X → Bool) (x y : X) : ℝ :=
  ∑ i, w i * sep (c i x) (c i y)

lemma distance_nonneg {w : I → ℝ} (hw : ∀ i, 0 ≤ w i) (c : I → X → Bool) (x y : X) :
    0 ≤ distance w c x y := sum_nonneg (fun i _ => mul_nonneg (hw i) (sep_nonneg _ _))

noncomputable def coin (w : I → ℝ) (a : ℝ) (i : I) (b : Bool) : ℝ :=
  if b then 1-Real.exp (-a*w i) else Real.exp (-a*w i)

noncomputable def probability (w : I → ℝ) (a : ℝ) (h : I → Bool) : ℝ :=
  ∏ i, coin w a i (h i)

def key (c : I → X → Bool) (h : I → Bool) (x : X) : I → Bool :=
  fun i => h i && c i x

omit [Fintype I] in
lemma coin_sum (w : I → ℝ) (a : ℝ) (i : I) : ∑ b : Bool, coin w a i b = 1 := by
  simp [coin]

lemma probability_nonneg {w : I → ℝ} (hw : ∀ i, 0 ≤ w i) {a : ℝ} (ha : 0 ≤ a)
    (h : I → Bool) : 0 ≤ probability w a h := by
  apply prod_nonneg
  intro i _
  unfold coin
  split
  · have hb : Real.exp (-a*w i) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hw i])
    linarith
  · exact (Real.exp_pos _).le

lemma probability_sum (w : I → ℝ) (a : ℝ) : ∑ h : I → Bool, probability w a h = 1 := by
  classical
  unfold probability
  rw [←Fintype.prod_sum]
  simp only [coin_sum,prod_const_one]

lemma collision_indicator (c : I → X → Bool) (h : I → Bool) (x y : X) :
    (if key c h x = key c h y then (1 : ℝ) else 0) =
      ∏ i, if (h i && c i x) = (h i && c i y) then (1 : ℝ) else 0 := by
  classical
  by_cases he : key c h x = key c h y
  · rw [ite_eq_left he]
    have hh (i : I) : (h i && c i x) = (h i && c i y) := congrFun he i
    simp only [hh,ite_true,prod_const_one]
  · rw [ite_eq_right he]
    have hex : ∃ i, (h i && c i x) ≠ (h i && c i y) := by
      by_contra hn
      push Not at hn
      exact he (funext hn)
    obtain ⟨i,hi⟩ := hex
    symm
    exact prod_eq_zero (mem_univ i) (ite_eq_right hi)

theorem collision_probability (w : I → ℝ) (a : ℝ) (c : I → X → Bool) (x y : X) :
    (∑ h : I → Bool, probability w a h *
      if key c h x = key c h y then (1 : ℝ) else 0) = Real.exp (-a*distance w c x y) := by
  classical
  simp_rw [collision_indicator,probability,←prod_mul_distrib]
  rw [←Fintype.prod_sum (fun (i : I) (b : Bool) => coin w a i b *
    (if (b && c i x) = (b && c i y) then (1 : ℝ) else 0))]
  have hf (i : I) : (∑ b : Bool, coin w a i b *
      if (b && c i x) = (b && c i y) then (1 : ℝ) else 0) =
      Real.exp (-a*(w i*sep (c i x) (c i y))) := by
    cases hx : c i x <;> cases hy : c i y <;> simp [coin,sep]
  simp_rw [hf]
  rw [←Real.exp_sum]
  congr 1
  simp only [distance,mul_sum]

lemma separation_probability (w : I → ℝ) (a : ℝ) (c : I → X → Bool) (x y : X) :
    (∑ h : I → Bool, probability w a h * sep (key c h x) (key c h y)) =
      1-Real.exp (-a*distance w c x y) := by
  classical
  have hs (h : I → Bool) : sep (key c h x) (key c h y) =
      1-(if key c h x = key c h y then (1 : ℝ) else 0) := by
    unfold sep
    split <;> norm_num
  simp_rw [hs,mul_sub,mul_one]
  rw [sum_sub_distrib,probability_sum,collision_probability]

lemma separation_bound (w : I → ℝ) (a : ℝ) (c : I → X → Bool) (x y : X) :
    (∑ h : I → Bool, probability w a h * sep (key c h x) (key c h y)) ≤
      a*distance w c x y := by
  rw [separation_probability]
  have hh := Real.add_one_le_exp (-a*distance w c x y)
  linarith

end Hash
end EditCutHash

end OAI
