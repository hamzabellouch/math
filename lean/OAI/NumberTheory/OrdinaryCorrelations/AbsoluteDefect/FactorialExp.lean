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

namespace OrdinaryExponentialBudgets

lemma factorial_exp (k : ℕ) : (k.factorial:ℝ)≤Real.exp ((k:ℝ)^2) := by
  have hh : (k.factorial:ℝ)≤(k:ℝ)^k := by exact_mod_cast Nat.factorial_le_pow k
  apply hh.trans
  have he : (k:ℝ)≤Real.exp (k:ℝ) := le_trans (by linarith : (k:ℝ)≤(k:ℝ)+1) (Real.add_one_le_exp _)
  calc
    (k:ℝ)^k ≤ (Real.exp (k:ℝ))^k := pow_le_pow_left₀ (Nat.cast_nonneg _) he _
    _ = Real.exp ((k:ℝ)^2) := by rw [←Real.exp_nat_mul]; congr 1; ring

lemma two_pow_exp (k : ℕ) : (2:ℝ)^k≤Real.exp (k:ℝ) := by
  have he : (2:ℝ)≤Real.exp 1 := by have := Real.add_one_le_exp (1:ℝ); linarith
  calc
    (2:ℝ)^k ≤ (Real.exp 1)^k := pow_le_pow_left₀ (by norm_num) he _
    _ = Real.exp (k:ℝ) := by rw [←Real.exp_nat_mul]; simp

lemma polynomial_exp (k : ℕ) : 2+((k:ℝ)+Real.log 2)^2≤Real.exp (3*((k:ℝ)+1)^2) := by
  have hl : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  have hu : Real.log 2≤1 := by have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2); norm_num at this ⊢; exact this
  have hh : ((k:ℝ)+Real.log 2)^2≤((k:ℝ)+1)^2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
  have hs : 1≤((k:ℝ)+1)^2 := by nlinarith [Nat.cast_nonneg (α:=ℝ) k]
  have he := Real.add_one_le_exp (3*((k:ℝ)+1)^2)
  linarith

lemma amplification_weight_bound {A : ℝ} (hA : 0≤A) (k : ℕ) :
    A*(2+((k:ℝ)+Real.log 2)^2)*(2:ℝ)^k*(k.factorial:ℝ)*Real.exp ((k:ℝ)+Real.exp 1-1)
      ≤ Real.exp ((A+Real.exp 1+10)*((k:ℝ)+1)^2) := by
  have ha : A≤Real.exp A := by have := Real.add_one_le_exp A; linarith
  have hfac := factorial_exp k
  have hpow := two_pow_exp k
  have hpoly := polynomial_exp k
  have hkn : 0≤(k:ℝ) := Nat.cast_nonneg k
  calc
    _ ≤ Real.exp A*Real.exp (3*((k:ℝ)+1)^2)*Real.exp (k:ℝ)*Real.exp ((k:ℝ)^2)*Real.exp ((k:ℝ)+Real.exp 1-1) := by gcongr
    _ = Real.exp (A+3*((k:ℝ)+1)^2+(k:ℝ)+(k:ℝ)^2+((k:ℝ)+Real.exp 1-1)) := by simp only [Real.exp_add]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hs : 1≤((k:ℝ)+1)^2 := by nlinarith
      have ha' := mul_le_mul_of_nonneg_left hs hA
      have he' := mul_le_mul_of_nonneg_left hs (Real.exp_pos 1).le
      nlinarith

lemma moment_weight_bound {A : ℝ} (hA : 0≤A) (k : ℕ) :
    1+A*(2+(k:ℝ)^2)*(k.factorial:ℝ)≤Real.exp ((A+10)*((k:ℝ)+1)^2) := by
  have ha : A≤Real.exp A := by have := Real.add_one_le_exp A; linarith
  have hpoly : 2+(k:ℝ)^2≤Real.exp (3*((k:ℝ)+1)^2) := by
    have hh := Real.add_one_le_exp (3*((k:ℝ)+1)^2)
    nlinarith [Nat.cast_nonneg (α:=ℝ) k]
  have hh : A*(2+(k:ℝ)^2)*(k.factorial:ℝ)≤Real.exp (A+4*((k:ℝ)+1)^2) := by
    calc
      _ ≤ Real.exp A*Real.exp (3*((k:ℝ)+1)^2)*Real.exp ((k:ℝ)^2) := by gcongr; exact factorial_exp k
      _ = Real.exp (A+3*((k:ℝ)+1)^2+(k:ℝ)^2) := by simp only [Real.exp_add]
      _ ≤ _ := by apply Real.exp_le_exp.mpr; nlinarith [Nat.cast_nonneg (α:=ℝ) k]
  have hone : 1≤Real.exp (A+4*((k:ℝ)+1)^2) := Real.one_le_exp_iff.mpr (by positivity)
  calc
    _ ≤ 2*Real.exp (A+4*((k:ℝ)+1)^2) := by linarith
    _ ≤ Real.exp 1*Real.exp (A+4*((k:ℝ)+1)^2) := by gcongr; have := Real.add_one_le_exp (1:ℝ); linarith
    _ = Real.exp (1+(A+4*((k:ℝ)+1)^2)) := by simp only [Real.exp_add]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hs : 1≤((k:ℝ)+1)^2 := by nlinarith [Nat.cast_nonneg (α:=ℝ) k]
      have ha' := mul_le_mul_of_nonneg_left hs hA
      nlinarith

end OrdinaryExponentialBudgets

end

end OAI
