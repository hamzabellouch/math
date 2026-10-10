import OAI.NumberTheory.Ostmann.QuadraticCenter.ParameterSelectionBasic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters
open Filter

def higherSourceX (k : ℕ) (u : ℝ) : ℕ :=
  ⌊Real.exp (1000*(4:ℝ)^k*Real.exp u)⌋₊

theorem higherSourceX_log_bounds (k : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    1 ≤ higherSourceX k u ∧
    999*(4:ℝ)^k*Real.exp u ≤ Real.log (higherSourceX k u : ℝ) ∧
    Real.log (higherSourceX k u : ℝ) ≤ 1000*(4:ℝ)^k*Real.exp u := by
  have hp : (1:ℝ) ≤ (4:ℝ)^k := one_le_pow₀ (by norm_num)
  have he : 1 ≤ Real.exp u := Real.one_le_exp_iff.mpr hu
  have hm : 1 ≤ (4:ℝ)^k*Real.exp u := by nlinarith
  have hlog2 : Real.log 2 ≤ (1:ℝ) := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at hh
    exact hh
  have hh := QuadraticCenter.log_floor_exp_bounds
    (show Real.log 2 ≤ 1000*(4:ℝ)^k*Real.exp u by nlinarith)
  change 1 ≤ higherSourceX k u ∧
    1000*(4:ℝ)^k*Real.exp u-Real.log 2 ≤ Real.log (higherSourceX k u : ℝ) ∧
    Real.log (higherSourceX k u : ℝ) ≤ 1000*(4:ℝ)^k*Real.exp u at hh
  exact ⟨hh.1,by nlinarith [hh.2.1],hh.2.2⟩

theorem higherSourceX_loglog_bounds (k : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    u+Real.log (999*(4:ℝ)^k) ≤ Real.log (Real.log (higherSourceX k u : ℝ)) ∧
    Real.log (Real.log (higherSourceX k u : ℝ)) ≤ u+Real.log (1000*(4:ℝ)^k) := by
  have hb := higherSourceX_log_bounds k u hu
  have hlo : 0 < 999*(4:ℝ)^k*Real.exp u := by positivity
  have hx : 0 < Real.log (higherSourceX k u : ℝ) := hlo.trans_le hb.2.1
  have h1 := Real.log_le_log hlo hb.2.1
  have h2 := Real.log_le_log hx hb.2.2
  rw [Real.log_mul (by positivity) (Real.exp_ne_zero _),Real.log_exp] at h1 h2
  exact ⟨by linarith,by linarith⟩

theorem higherSourceX_mono (k : ℕ) : Monotone (higherSourceX k) := by
  intro u v huv
  apply Nat.floor_mono
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr huv) (by positivity)

theorem higherSourceX_tendsto (k : ℕ) : Tendsto (higherSourceX k) atTop atTop := by
  exact tendsto_nat_floor_atTop.comp (Real.tendsto_exp_atTop.comp
    (Real.tendsto_exp_atTop.const_mul_atTop (show 0 < 1000*(4:ℝ)^k by positivity)))

theorem eventually_higherSourceX_ge (k : ℕ) (α : ℝ) (hα : 0 < α) (N : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ u : ℝ, α*L-1 ≤ u → N ≤ higherSourceX k u := by
  have ht : Tendsto (fun L : ℝ => α*L-1) atTop atTop :=
    by simpa only [sub_eq_add_neg,id_eq] using
      tendsto_atTop_add_const_right _ (-1) (tendsto_id.const_mul_atTop hα)
  filter_upwards [((higherSourceX_tendsto k).comp ht).eventually_ge_atTop N] with L hL
  intro u hu
  exact hL.trans (higherSourceX_mono k hu)

theorem eventually_higherSourceX_property (k : ℕ) (α : ℝ) (hα : 0 < α)
    {P : ℕ → Prop} (hP : ∀ᶠ X : ℕ in atTop,P X) :
    ∀ᶠ L : ℝ in atTop, ∀ u : ℝ, α*L-1 ≤ u → P (higherSourceX k u) := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp hP
  filter_upwards [eventually_higherSourceX_ge k α hα N] with L hL
  intro u hu
  exact hN _ (hL u hu)

end Ostmann.Characters

end

end OAI
