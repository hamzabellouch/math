import OAI.NumberTheory.TwoPoint.Halasz.HalaszBandPowerCost
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OAI

/-! The fixed logarithmic saving retained after the actual band count. -/
namespace TwoPointCorrelations

open Filter

theorem halasz_exceptional_decay (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ B u : ℝ, 0 ≤ B → B ≤ L^(1/1000:ℝ) →
      L^(1/16:ℝ)/2 ≤ |u| →
      C*B*((min ((3/100:ℝ)*Real.log L) (Real.log (1+|u|))+1)*
        Real.exp (-min ((3/100:ℝ)*Real.log L) (Real.log (1+|u|)))+Real.log L/L) ≤
      L^(-1/40:ℝ) := by
  have hK : 0 < C+1 := by linarith
  have hb := (isLittleO_log_rpow_atTop (show (0:ℝ)<1/250 by norm_num)).bound
    (show (0:ℝ)<1/(4*(C+1)) by positivity)
  have hp := (tendsto_rpow_atTop (show (0:ℝ)<1/250 by norm_num)).eventually
    (eventually_ge_atTop (4*(C+1)))
  filter_upwards [hb,hp,eventually_ge_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (100:ℝ))]
    with L hb hp hL hlog
  have hL0 : 0 < L := by linarith
  have hlog0 : 0 ≤ Real.log L := by linarith
  rw [Real.norm_eq_abs,abs_of_nonneg hlog0,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hL0.le _)] at hb
  have hlogbound : (C+1)*Real.log L ≤ (1/4:ℝ)*L^(1/250:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hb hK.le
    field_simp at hh
    nlinarith
  have hconst : C+1 ≤ (1/4:ℝ)*L^(1/250:ℝ) := by linarith
  have hcommon : C*((3/100:ℝ)*Real.log L+1) ≤ (1/2:ℝ)*L^(1/250:ℝ) := by
    have hh : C*((3/100:ℝ)*Real.log L+1) ≤ (C+1)*(Real.log L+1) := by nlinarith
    nlinarith
  have hlogC : C*Real.log L ≤ (1/2:ℝ)*L^(1/250:ℝ) := by nlinarith
  intro B u hB hBL hu
  have hbase : 0 < L^(1/16:ℝ)/2 := by positivity
  have hlogu := Real.log_le_log hbase (hu.trans (by linarith : |u| ≤ 1+|u|))
  rw [Real.log_div (by positivity : L^(1/16:ℝ) ≠ 0) (by norm_num : (2:ℝ) ≠ 0),
    Real.log_rpow hL0] at hlogu
  have hlog2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hmin : min ((3/100:ℝ)*Real.log L) (Real.log (1+|u|)) =
      (3/100:ℝ)*Real.log L := min_eq_left (by linarith)
  rw [hmin]
  have he : Real.exp (-((3/100:ℝ)*Real.log L)) = L^(-3/100:ℝ) := by
    rw [Real.rpow_def_of_pos hL0]
    congr 1
    ring
  rw [he]
  have hprod : L^(1/1000:ℝ)*L^(-3/100:ℝ) = L^(-29/1000:ℝ) := by
    rw [← Real.rpow_add hL0]
    norm_num
  have hquot : L^(1/1000:ℝ)/L = L^(-999/1000:ℝ) := by
    rw [div_eq_mul_inv,← Real.rpow_neg_one,← Real.rpow_add hL0]
    norm_num
  calc
    _ ≤ C*L^(1/1000:ℝ)*(((3/100:ℝ)*Real.log L+1)*L^(-3/100:ℝ)+Real.log L/L) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hBL hC) (by positivity)
    _ = C*((3/100:ℝ)*Real.log L+1)*(L^(1/1000:ℝ)*L^(-3/100:ℝ))+
        (C*Real.log L)*(L^(1/1000:ℝ)/L) := by ring
    _ = C*((3/100:ℝ)*Real.log L+1)*L^(-29/1000:ℝ)+
        (C*Real.log L)*L^(-999/1000:ℝ) := by rw [hprod,hquot]
    _ ≤ ((1/2:ℝ)*L^(1/250:ℝ))*L^(-29/1000:ℝ)+
        ((1/2:ℝ)*L^(1/250:ℝ))*L^(-999/1000:ℝ) := by gcongr
    _ = (1/2:ℝ)*L^(-1/40:ℝ)+(1/2:ℝ)*L^(-199/200:ℝ) := by
      simp only [mul_assoc,← Real.rpow_add hL0]
      norm_num
    _ ≤ L^(-1/40:ℝ) := by
      have hh := Real.rpow_le_rpow_of_exponent_le hL (show (-199/200:ℝ) ≤ -1/40 by norm_num)
      linarith

end TwoPointCorrelations

end OAI
