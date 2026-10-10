import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction
open MeasureTheory Finset

namespace OrdinarySharpWindow

def box (H x : ℝ) : ℝ := (Set.Ioc 0 H).indicator (fun _=>1) x

lemma box_nonneg (H x : ℝ) : 0≤box H x := by
  unfold box Set.indicator
  split_ifs <;> norm_num

lemma box_le_one (H x : ℝ) : box H x≤1 := by
  unfold box Set.indicator
  split_ifs <;> norm_num

lemma box_integrable (H : ℝ) : Integrable (box H) := by
  exact (integrable_indicator_iff measurableSet_Ioc).mpr
    (integrableOn_const («μ»:=volume) (s:=Set.Ioc 0 H) (C:=(1:ℝ)) (by simp))

lemma box_integral {H : ℝ} (hH : 0≤H) : (∫x : ℝ,box H x)=H := by
  unfold box
  rw [integral_indicator_const _ measurableSet_Ioc]
  simp [Real.volume_real_Ioc,hH]

lemma box_translation_pointwise {H z : ℝ} (hz : 0≤z) (x : ℝ) :
    |box H x-box H (x-z)|≤box z x+box z (x-H) := by
  by_cases hx : x∈Set.Ioc 0 H
  · by_cases hxz : x-z∈Set.Ioc 0 H
    · simp only [box,Set.indicator_of_mem hx,Set.indicator_of_mem hxz,sub_self,abs_zero]
      exact add_nonneg (box_nonneg _ _) (box_nonneg _ _)
    · have hx0 : 0<x := hx.1
      have hxzH : x-z≤H := by linarith [hx.2]
      have hxzz : x≤z := by
        by_contra hh
        apply hxz
        exact ⟨by linarith, hxzH⟩
      have hxx : x∈Set.Ioc 0 z := ⟨hx0,hxzz⟩
      simp only [box,Set.indicator_of_mem hx,Set.indicator_of_notMem hxz,
        Set.indicator_of_mem hxx,sub_zero,abs_one]
      change 1≤1+box z (x-H)
      linarith [box_nonneg z (x-H)]
  · by_cases hxz : x-z∈Set.Ioc 0 H
    · have hx0 : 0<x := by linarith [hxz.1]
      have hHx : H<x := by
        by_contra hh
        exact hx ⟨hx0,by linarith⟩
      have hxx : x-H∈Set.Ioc 0 z := ⟨by linarith,by linarith [hxz.2]⟩
      simp only [box,Set.indicator_of_notMem hx,Set.indicator_of_mem hxz,
        Set.indicator_of_mem hxx,zero_sub,abs_neg,abs_one]
      change 1≤box z x+1
      linarith [box_nonneg z x]
    · simp only [box,Set.indicator_of_notMem hx,Set.indicator_of_notMem hxz,
        sub_self,abs_zero]
      exact add_nonneg (box_nonneg _ _) (box_nonneg _ _)

lemma box_translation_l1_nonneg (H : ℝ) {z : ℝ} (hz : 0≤z) :
    (∫x : ℝ,|box H x-box H (x-z)|)≤2*z := by
  have h1 := box_integrable H
  have h2 := h1.comp_sub_right z
  have h3 := box_integrable z
  have h4 := h3.comp_sub_right H
  calc
    _ ≤ ∫x : ℝ,box z x+box z (x-H) :=
      integral_mono (h1.sub h2).norm (h3.add h4) (box_translation_pointwise hz)
    _ = 2*z := by
      rw [integral_add h3 h4,integral_sub_right_eq_self,box_integral hz]
      ring

lemma box_translation_l1 (H z : ℝ) :
    (∫x : ℝ,|box H x-box H (x-z)|)≤2*|z| := by
  rcases le_or_gt 0 z with hz|hz
  · simpa only [abs_of_nonneg hz] using box_translation_l1_nonneg H hz
  · have he : (∫x : ℝ,|box H x-box H (x-z)|)=
        ∫x : ℝ,|box H x-box H (x-(-z))| := by
      have hh := integral_sub_right_eq_self («μ»:=volume) (fun x : ℝ=>|box H x-box H (x-(-z))|) z
      convert hh using 1
      congr 1
      funext x
      have harg : x-z-(-z)=x := by ring
      rw [harg,abs_sub_comm]
    rw [he,abs_of_neg hz]
    exact box_translation_l1_nonneg H (by linarith)

def sharpWindow {ι : Type*} (s : Finset ι) (a : ι→ℂ) (u : ι→ℝ) (H x : ℝ) : ℂ :=
  ∑n∈s,a n*(box H (x-u n):ℂ)

lemma sharpWindow_integrable {ι : Type*} (s : Finset ι) (a : ι→ℂ) (u : ι→ℝ) (H : ℝ) :
    Integrable (sharpWindow s a u H) := by
  unfold sharpWindow
  apply integrable_finsetSum
  intro n hn
  exact ((box_integrable H).comp_sub_right (u n)).ofReal.const_mul (a n)

lemma sharpWindow_translation_l1 {ι : Type*} (s : Finset ι) (a : ι→ℂ) (u : ι→ℝ)
    (H z : ℝ) :
    (∫x : ℝ,‖sharpWindow s a u H x-sharpWindow s a u H (x-z)‖)
      ≤2*|z| *(∑n∈s,‖a n‖) := by
  classical
  have hint (n : ι) : Integrable (fun x : ℝ=>‖a n‖*|box H (x-u n)-box H (x-u n-z)|) :=
    ((((box_integrable H).sub ((box_integrable H).comp_sub_right z)).norm).comp_sub_right (u n)).const_mul _
  calc
    _ ≤ ∫x : ℝ,∑n∈s,‖a n‖*|box H (x-u n)-box H (x-u n-z)| := by
      apply integral_mono ((sharpWindow_integrable s a u H).sub
        ((sharpWindow_integrable s a u H).comp_sub_right z)).norm
        (integrable_finsetSum s (fun n hn=>hint n))
      intro x
      unfold sharpWindow
      dsimp only [Pi.sub_apply]
      rw [←sum_sub_distrib]
      apply (norm_sum_le _ _).trans
      apply sum_le_sum
      intro n hn
      rw [←mul_sub,norm_mul,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
      have he : x-z-u n=x-u n-z := by ring
      rw [he]
    _ = ∑n∈s,‖a n‖*(∫x : ℝ,|box H x-box H (x-z)|) := by
      rw [integral_finsetSum s (fun n hn=>hint n)]
      apply sum_congr rfl
      intro n hn
      rw [integral_const_mul]
      congr 1
      exact integral_sub_right_eq_self (fun x : ℝ=>|box H x-box H (x-z)|) (u n)
    _ ≤ ∑n∈s,‖a n‖*(2*|z|) := by
      apply sum_le_sum
      intro n hn
      exact mul_le_mul_of_nonneg_left (box_translation_l1 H z) (norm_nonneg _)
    _ = _ := by rw [←sum_mul]; ring

end OrdinarySharpWindow

end

end OAI
