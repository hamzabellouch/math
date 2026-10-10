import Mathlib

namespace OAI

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedCancellation
open Filter
open scoped Topology

theorem eventually_terminal_error_combine {c₁ c₂ α₁ α₂ : ℝ}
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) :
    ∃rate exponent : ℝ,0 < rate ∧ 0 < exponent ∧
    ∀ᶠ L : ℝ in atTop,∀z core : ℂ,
      ‖z-core‖ ≤ Real.exp (-c₁*Real.exp (α₁*L)) →
      ‖core‖ ≤ Real.exp (-c₂*Real.exp (α₂*L)) →
      ‖z‖ ≤ Real.exp (-rate*Real.exp (exponent*L)) := by
  let rate := min c₁ c₂
  let exponent := min α₁ α₂
  have hr : 0 < rate := lt_min hc₁ hc₂
  have ha : 0 < exponent := lt_min hα₁ hα₂
  have ht : Tendsto (fun L : ℝ=>Real.exp (exponent*L)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop ha)
  refine ⟨rate/2,exponent,half_pos hr,ha,?_⟩
  filter_upwards [ht.eventually (eventually_ge_atTop (2*Real.log 2/rate)),
    eventually_ge_atTop (0:ℝ)] with L hlarge hL
  intro z core herr hcore
  have hlarge' := (div_le_iff₀ hr).mp hlarge
  have h₁ : rate*Real.exp (exponent*L) ≤ c₁*Real.exp (α₁*L) :=
    mul_le_mul (min_le_left _ _) (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (min_le_left _ _) hL)) (Real.exp_pos _).le hc₁.le
  have h₂ : rate*Real.exp (exponent*L) ≤ c₂*Real.exp (α₂*L) :=
    mul_le_mul (min_le_right _ _) (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (min_le_right _ _) hL)) (Real.exp_pos _).le hc₂.le
  have he₁ : ‖z-core‖ ≤ Real.exp (-rate*Real.exp (exponent*L)) :=
    herr.trans (Real.exp_le_exp.mpr (by nlinarith))
  have he₂ : ‖core‖ ≤ Real.exp (-rate*Real.exp (exponent*L)) :=
    hcore.trans (Real.exp_le_exp.mpr (by nlinarith))
  calc
    ‖z‖ ≤ ‖z-core‖+‖core‖ := by simpa only [sub_add_cancel] using norm_add_le (z-core) core
    _ ≤ 2*Real.exp (-rate*Real.exp (exponent*L)) := by linarith
    _ = Real.exp (Real.log 2-rate*Real.exp (exponent*L)) := by
      rw [Real.exp_sub,Real.exp_log (by norm_num : (0:ℝ)<2)]
      simp only [neg_mul,Real.exp_neg,div_eq_mul_inv]
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI
