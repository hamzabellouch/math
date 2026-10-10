import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
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
open Classical
open Classical Finset
open Classical Finset Real MeasureTheory

namespace OrdinaryRoughGate
open Real Filter
lemma eventual_gate (v : ℕ) : ∀ᶠ B : ℝ in atTop, ∃m:ℕ,
    ((2:ℕ)^(2^(1800*m+v)):ℝ) ≤ (1/2:ℝ)*Real.exp (B^(9999/10000:ℝ)) ∧
    (1/2:ℝ)^(2*m) ≤ 4*B^(-1/950:ℝ) := by
  let C : ℝ := Real.log 2*(2:ℝ)^v+1
  have hl2 : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  have hl21 : Real.log 2≤1 := by
    have ht := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at ht;exact ht
  have hlim := (_root_.tendsto_rpow_atTop (by norm_num : (0:ℝ)<9999/10000-18/19)).eventually_ge_atTop C
  filter_upwards [hlim,eventually_ge_atTop (1:ℝ)] with B hBC hB
  have hBp : 0<B := by linarith
  obtain ⟨m,hm,hm'⟩ := exists_nat_pow_near
    (Real.one_le_rpow hB (by norm_num) : (1:ℝ)≤B^(1/950:ℝ)) (by norm_num : (1:ℝ)<4)
  refine ⟨m,?_,?_⟩
  · have hp : (2:ℝ)^(1800*m+v) ≤ (2:ℝ)^v*B^(18/19:ℝ) := by
      have he : (2:ℝ)^(1800*m) = ((4:ℝ)^m)^900 := by
        calc
          _ = (((2:ℝ)^2)^m)^900 := by rw [←pow_mul,←pow_mul];congr 1;omega
          _ = _ := by norm_num
      have hr : (B^(1/950:ℝ))^900=B^(18/19:ℝ) := by
        rw [←Real.rpow_natCast,←Real.rpow_mul hBp.le];norm_num
      rw [pow_add,he,mul_comm]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [←hr]
      exact pow_le_pow_left₀ (by positivity) hm 900
    have hmargin : Real.log 2*(2:ℝ)^(1800*m+v)+Real.log 2≤B^(9999/10000:ℝ) := by
      have hprod := mul_le_mul_of_nonneg_left hBC (show 0≤B^(18/19:ℝ) by positivity)
      rw [←Real.rpow_add hBp] at hprod
      norm_num at hprod
      have hpow1 : 1≤B^(18/19:ℝ) := Real.one_le_rpow hB (by norm_num)
      have hh := mul_le_mul_of_nonneg_left hp hl2
      dsimp [C] at hprod
      nlinarith
    have he : ((2:ℕ)^(2^(1800*m+v)):ℝ) =
        Real.exp (Real.log 2*(2:ℝ)^(1800*m+v)) := by
      push_cast
      rw [←Real.rpow_natCast,Real.rpow_def_of_pos (by norm_num)]
      push_cast
      rfl
    rw [he]
    calc
      _ ≤ Real.exp (B^(9999/10000:ℝ)-Real.log 2) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := by rw [Real.exp_sub,Real.exp_log (by norm_num : (0:ℝ)<2)];ring
  · have he : (1/2:ℝ)^(2*m)=((4:ℝ)^m)⁻¹ := by
      rw [pow_mul,←inv_pow]
      congr 1
      norm_num
    rw [he,show (-1/950:ℝ)=-(1/950:ℝ) by ring,Real.rpow_neg hBp.le]
    have hp : 0<(4:ℝ)^m := by positivity
    have hBr : 0<B^(1/950:ℝ) := by positivity
    rw [pow_succ] at hm'
    calc
      _ = 1/((4:ℝ)^m) := by simp only [one_div]
      _ ≤ 4/(B^(1/950:ℝ)) := (div_le_div_iff₀ hp hBr).mpr (by nlinarith)
      _ = _ := by ring
end OrdinaryRoughGate

end

end OAI
