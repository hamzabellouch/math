import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.AnalyticTransition

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

namespace OrdinaryChainScales
open Finset OrdinaryNarrowGrid
attribute [local irreducible] E F mesh binQ binStart binWidth binLog amplifier

lemma first_threshold_gain {B H s L : ℕ} (hB : H+10≤B) (hL : E B s 0≤L) :
    threshold H 0 L^2≤Real.exp (-1024*(mesh B H s 0:ℝ)) := by
  have he := mesh_E B H s 0 hB
  have her : (E B s 0:ℝ)=(mesh B H s 0:ℝ)*(2:ℝ)^(H+10) := by exact_mod_cast he
  have hα : alpha H 0=((2:ℝ)^H)⁻¹/2 := by unfold alpha; norm_num; ring
  have hprod : 2*alpha H 0*(E B s 0:ℝ)=1024*(mesh B H s 0:ℝ) := by
    rw [hα,her,pow_add]
    norm_num
    have hne : (2:ℝ)^H≠0 := pow_ne_zero _ (by norm_num)
    field_simp
  have hLr : (E B s 0:ℝ)≤(L:ℝ) := by exact_mod_cast hL
  have hh := mul_le_mul_of_nonneg_left hLr (show 0≤2*alpha H 0 by have := alpha_nonneg H 0; positivity)
  unfold threshold
  rw [←Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  norm_num
  rw [hprod] at hh
  linarith only [hh]

lemma first_threshold_sum {B H s : ℕ} (hB : 2*H+s+30≤B) :
    ((grid (binQ B H s 0) (binStart B H s 0) (binWidth B s 0)).card:ℝ)*
      (∑i∈grid (binQ B H s 0) (binStart B H s 0) (binWidth B s 0),
        threshold H 0 (binLog B H s 0 i)^2)≤Real.exp (-1020*(mesh B H s 0:ℝ)) := by
  have hB0 : H+10≤B := by omega
  have hh : (∑i∈grid (binQ B H s 0) (binStart B H s 0) (binWidth B s 0),
      threshold H 0 (binLog B H s 0 i)^2)≤
      ((grid (binQ B H s 0) (binStart B H s 0) (binWidth B s 0)).card:ℝ)*
      Real.exp (-1024*(mesh B H s 0:ℝ)) := by
    calc
      _ ≤ ∑i∈grid (binQ B H s 0) (binStart B H s 0) (binWidth B s 0),Real.exp (-1024*(mesh B H s 0:ℝ)) := by
        apply sum_le_sum
        intro i hi
        exact first_threshold_gain (B:=B) (H:=H) (s:=s) hB0
          (bin_log_range (B:=B) (H:=H) (s:=s) (j:=0) hB0 hi).1
      _ = _ := by simp
  calc
    _ ≤ ((grid (binQ B H s 0) (binStart B H s 0) (binWidth B s 0)).card:ℝ)^2*
        Real.exp (-1024*(mesh B H s 0:ℝ)) := by
      have hm := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg (α:=ℝ) (grid (binQ B H s 0) (binStart B H s 0) (binWidth B s 0)).card)
      nlinarith only [hm]
    _ ≤ (Real.exp (2*(mesh B H s 0:ℝ)))^2*Real.exp (-1024*(mesh B H s 0:ℝ)) := by
      gcongr
      exact card_exp (j:=0) hB
    _ = _ := by rw [←Real.exp_nat_mul,←Real.exp_add]; congr 1; norm_num; ring

end OrdinaryChainScales

end

end OAI
