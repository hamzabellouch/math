import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.AdjacentCutoff
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.Threshold

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
attribute [local irreducible] E F mesh binQ binStart binWidth binLog amplifier
lemma half_le_log_two : (1:ℝ)/2≤Real.log 2 := by
  have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
  norm_num at hh ⊢
  exact hh

lemma threshold_moment {H j L R N : ℕ} (hH : 16*R≤2^H) (hN : 2^L≤N) :
    1≤(N:ℝ)*(threshold H j L)^(8*R) := by
  have hR : (16:ℝ)*(R:ℝ)≤(2:ℝ)^H := by exact_mod_cast hH
  have ha := alpha_le H j
  have hb : (8*(R:ℝ))*alpha H j≤(1:ℝ)/2 := by
    have hc := mul_le_mul_of_nonneg_left ha (show 0≤8*(R:ℝ) by positivity)
    have hh : (8*(R:ℝ))*((2:ℝ)^H)⁻¹≤(1:ℝ)/2 := by
      rw [←div_eq_mul_inv,div_le_iff₀ (by positivity)]
      linarith
    exact hc.trans hh
  have hexp : Real.exp (Real.log 2*(L:ℝ))≤(N:ℝ) := by
    rw [mul_comm,Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]
    exact_mod_cast hN
  have hv : (threshold H j L)^(8*R)=Real.exp (-(8*(R:ℝ))*alpha H j*(L:ℝ)) := by
    unfold threshold
    rw [←Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hv]
  calc
    1 ≤ Real.exp ((Real.log 2-8*(R:ℝ)*alpha H j)*(L:ℝ)) :=
      Real.one_le_exp_iff.mpr (mul_nonneg (sub_nonneg.mpr (hb.trans half_le_log_two)) (Nat.cast_nonneg _))
    _ = Real.exp (Real.log 2*(L:ℝ))*Real.exp (-(8*(R:ℝ))*alpha H j*(L:ℝ)) := by
      rw [←Real.exp_add]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hexp (Real.exp_pos _).le

lemma exponential_moment_size {k R e N : ℕ} {C m : ℝ}
    (hm0 : 0≤ m) (hm : m≤Real.exp (C*((k:ℝ)+1)^2))
    (hb : 16*(R:ℝ)*(1+C)*((k:ℝ)+1)^2≤(e:ℝ)) (hN : 2^e≤N) :
    (2*m)^(8*R)≤(N:ℝ) := by
  have he : (2:ℝ)≤Real.exp 1 := by have hh := Real.add_one_le_exp (1:ℝ); linarith only [hh]
  have hs : 1≤((k:ℝ)+1)^2 := by nlinarith only [Nat.cast_nonneg (α:=ℝ) k]
  have hlog := mul_le_mul_of_nonneg_right half_le_log_two (Nat.cast_nonneg (α:=ℝ) e)
  have hh := mul_le_mul_of_nonneg_left hs (show 0≤8*(R:ℝ) from mul_nonneg (by norm_num) (Nat.cast_nonneg _))
  have hbudget : (8*(R:ℝ))*(1+C*((k:ℝ)+1)^2)≤Real.log 2*(e:ℝ) := by
    nlinarith only [hb,hlog,hh]
  calc
    _ ≤ (Real.exp 1*Real.exp (C*((k:ℝ)+1)^2))^(8*R) := by gcongr
    _ = Real.exp ((8*(R:ℝ))*(1+C*((k:ℝ)+1)^2)) := by
      rw [←Real.exp_add,←Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    _ ≤ Real.exp (Real.log 2*(e:ℝ)) := Real.exp_le_exp.mpr hbudget
    _ = (2:ℝ)^e := by
      rw [mul_comm,Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]
    _ ≤ (N:ℝ) := by exact_mod_cast hN

lemma terminal_moment_size {B H s j K Kr k R N : ℕ} {C m : ℝ}
    (hm0 : 0≤ m) (hm : m≤Real.exp (C*((k:ℝ)+1)^2))
    (hC : 16*(R:ℝ)*(1+C)≤(2:ℝ)^K)
    (hB : H+4*s+2*Kr+K+70≤B) (hR : 64*R≤2^Kr)
    (hk : k<64*R*2^(3*j+2*s+22)) (hN : 2^(E B s j)≤N) :
    (2*m)^(8*R)≤(N:ℝ) := by
  apply exponential_moment_size hm0 hm _ hN
  have habs := terminal_square_absorption hB hR hk
  have habsr : (2:ℝ)^K*((k:ℝ)+1)^2≤(mesh B H s j:ℝ) := by exact_mod_cast habs
  have hme : (mesh B H s j:ℝ)≤(E B s j:ℝ) := by
    exact_mod_cast mesh_le_E B H s j (by omega)
  exact (mul_le_mul_of_nonneg_right hC (sq_nonneg _)).trans (habsr.trans hme)

end OrdinaryChainScales

end

end OAI
