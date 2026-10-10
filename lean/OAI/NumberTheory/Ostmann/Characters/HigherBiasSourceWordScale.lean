import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceScale
import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceWordBins
import OAI.NumberTheory.Ostmann.Characters.InitialCharacterStatisticScaleBasic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.HigherBiasSourceWord
open Filter InitialCharacterScale
open scoped Topology

def selectionCost (β δ : ℝ) : ℝ := 20+10*|β|+2*|Real.log δ|

theorem selectionCost_pos (β δ : ℝ) : 0<selectionCost β δ := by
  unfold selectionCost
  positivity

theorem bulk_gap_eventually (k : ℕ) {γ : ℝ} (hγ : 0<γ) :
    ∀ᶠ L : ℝ in atTop,∀u : ℝ,
      (wordSize k L:ℝ)*Real.exp (u-γ*L)≤Real.exp u := by
  have ht : Tendsto (fun L : ℝ=>depthScale k*L*Real.exp (-γ*L)) atTop (𝓝 0) := by
    simpa only [Real.rpow_one,←mul_assoc,mul_zero] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 γ hγ).const_mul (depthScale k)
  filter_upwards [eventually_ge_atTop (0:ℝ),
    ht.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))] with L hL hh
  intro u
  have hsmall : (wordSize k L:ℝ)*Real.exp (-γ*L)≤1 :=
    (mul_le_mul_of_nonneg_right (wordSize_bounds k hL).2 (Real.exp_pos _).le).trans hh.le
  have := mul_le_mul_of_nonneg_right hsmall (Real.exp_pos u).le
  convert this using 1
  · rw [show u-γ*L=(-γ*L)+u by ring,Real.exp_add,mul_assoc]
  · rw [one_mul]

theorem bin_scale_eventually (k : ℕ) {α γ : ℝ} (β : ℝ) (hα : 0<α) (hγ : 0<γ) :
    ∀ᶠ L : ℝ in atTop,∀u : ℝ,α*L-1≤u → u≤β*L →
      1≤wordSize k L ∧ 10≤Real.exp u ∧
      (wordSize k L:ℝ)*Real.exp (u-γ*L)≤Real.exp u ∧
      ((bins (Real.exp u)).card:ℝ)≤Real.exp ((2*|β|+1)*(wordSize k L:ℝ)) := by
  have ha : Tendsto (fun L : ℝ=>α*L-1) atTop atTop := by
    simpa only [id_eq,sub_eq_add_neg] using
      (tendsto_id.const_mul_atTop hα).atTop_add (tendsto_const_nhds (x:=(-1:ℝ)))
  filter_upwards [eventually_ge_atTop (2:ℝ),
    (Real.tendsto_exp_atTop.comp ha).eventually_ge_atTop 10,
    (Real.tendsto_exp_atTop.comp (wordSize_tendsto k)).eventually_ge_atTop 5,
    bulk_gap_eventually k hγ] with L hL hτ h5 hgap
  intro u hu hU
  have hm := wordSize_bounds k (by linarith : 0≤L)
  have hzL : L≤depthScale k*L := by nlinarith [one_le_depthScale k]
  have hm1 : 1≤wordSize k L := by exact_mod_cast (show (1:ℝ)≤wordSize k L by linarith)
  have hLm : L≤2*(wordSize k L:ℝ) := by linarith
  have hτu : 10≤Real.exp u := hτ.trans (Real.exp_le_exp.mpr hu)
  refine ⟨hm1,hτu,hgap u,?_⟩
  have hU' : u≤2*|β| *(wordSize k L:ℝ) := by
    calc
      u≤β*L := hU
      _≤|β| *L := mul_le_mul_of_nonneg_right (le_abs_self β) (by linarith)
      _≤|β| *(2*(wordSize k L:ℝ)) := mul_le_mul_of_nonneg_left hLm (abs_nonneg β)
      _=_ := by ring
  calc
    ((bins (Real.exp u)).card:ℝ)≤5*Real.exp u := bins_card_le (by linarith)
    _≤Real.exp (wordSize k L:ℝ)*Real.exp (2*|β| *(wordSize k L:ℝ)) :=
      mul_le_mul h5 (Real.exp_le_exp.mpr hU') (Real.exp_pos _).le (Real.exp_pos _).le
    _=Real.exp ((2*|β|+1)*(wordSize k L:ℝ)) := by rw [←Real.exp_add]; congr 1; ring

theorem typical_cost_eventually (k : ℕ) (β : ℝ) {cA : ℝ} (hcA : 0<cA) :
    ∀ᶠ L : ℝ in atTop,∀u : ℝ,0≤u → u≤β*L →
      Real.sqrt (higherSourceX k u:ℝ)*Real.exp (-(6*|β|+1)*(wordSize k L:ℝ))≤
        cA*Real.sqrt (higherSourceX k u:ℝ)/(Real.log (higherSourceX k u:ℝ))^3 := by
  filter_upwards [eventually_ge_atTop (2:ℝ),
    (Real.tendsto_exp_atTop.comp (wordSize_tendsto k)).eventually_ge_atTop
      ((1000*(4:ℝ)^k)^3/cA)] with L hL hC
  intro u hu hU
  have hm := wordSize_bounds k (by linarith : 0≤L)
  have hzL : L≤depthScale k*L := by nlinarith [one_le_depthScale k]
  have hLm : L≤2*(wordSize k L:ℝ) := by linarith
  have hU' : u≤2*|β| *(wordSize k L:ℝ) := by
    calc
      u≤β*L := hU
      _≤|β| *L := mul_le_mul_of_nonneg_right (le_abs_self β) (by linarith)
      _≤|β| *(2*(wordSize k L:ℝ)) := mul_le_mul_of_nonneg_left hLm (abs_nonneg β)
      _=_ := by ring
  have hb := higherSourceX_log_bounds k u hu
  have hx : 0<Real.log (higherSourceX k u:ℝ) :=
    lt_of_lt_of_le (by positivity) hb.2.1
  have hC' : (1000*(4:ℝ)^k)^3≤cA*Real.exp (wordSize k L:ℝ) := by
    have := (div_le_iff₀ hcA).mp hC
    simpa only [Function.comp_def,mul_comm] using this
  have hlog : (Real.log (higherSourceX k u:ℝ))^3≤
      cA*Real.exp ((6*|β|+1)*(wordSize k L:ℝ)) := by
    calc
      _≤(1000*(4:ℝ)^k*Real.exp u)^3 := pow_le_pow_left₀ hx.le hb.2.2 3
      _=(1000*(4:ℝ)^k)^3*Real.exp (3*u) := by rw [mul_pow,←Real.exp_nat_mul]; norm_num
      _≤(cA*Real.exp (wordSize k L:ℝ))*Real.exp (6*|β| *(wordSize k L:ℝ)) :=
        mul_le_mul hC' (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le (by positivity)
      _=cA*Real.exp ((6*|β|+1)*(wordSize k L:ℝ)) := by
        rw [mul_assoc,←Real.exp_add]; congr 2; ring
  apply (le_div_iff₀ (pow_pos hx 3)).mpr
  calc
    _=Real.sqrt (higherSourceX k u:ℝ)*
      (Real.exp (-(6*|β|+1)*(wordSize k L:ℝ))*(Real.log (higherSourceX k u:ℝ))^3) := by ring
    _≤Real.sqrt (higherSourceX k u:ℝ)*
      (Real.exp (-(6*|β|+1)*(wordSize k L:ℝ))*(cA*Real.exp ((6*|β|+1)*(wordSize k L:ℝ)))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog (Real.exp_pos _).le) (Real.sqrt_nonneg _)
    _=cA*Real.sqrt (higherSourceX k u:ℝ) := by
      rw [mul_left_comm (Real.exp _) cA,←Real.exp_add]
      have he : -(6*|β|+1)*(wordSize k L:ℝ)+(6*|β|+1)*(wordSize k L:ℝ)=0 := by ring
      rw [he,Real.exp_zero]; ring

end Ostmann.Characters.HigherBiasSourceWord

end

end OAI
