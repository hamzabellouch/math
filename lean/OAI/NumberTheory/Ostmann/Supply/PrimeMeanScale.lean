import OAI.NumberTheory.Ostmann.Supply.TruncationMargins

namespace OAI

noncomputable section
namespace Ostmann.Supply
open Filter

theorem eventually_exp_tail_le_unit_multiple {c : ℝ} (hc : 0<c) :
    ∀ᶠL:ℝ in atTop,∀H U:ℝ,H≤L → Real.exp (-8*supplyEpsilon*H)≤U →
      Real.exp (-10*L)≤c*U := by
  have hd : Tendsto (fun L:ℝ => Real.exp (-9*L)) atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by norm_num))
  filter_upwards [hd.eventually_le_const hc,eventually_ge_atTop (0:ℝ)] with L hd hL
  intro H U hH hU
  have hh := mul_le_mul_of_nonneg_left hH
    (by norm_num [supplyEpsilon] : 0≤8*supplyEpsilon)
  have he : -10*L≤-9*L+(-8*supplyEpsilon*H) := by
    norm_num only [supplyEpsilon] at hh ⊢
    linarith
  calc
    _ ≤ Real.exp (-9*L+(-8*supplyEpsilon*H)) := Real.exp_le_exp.mpr he
    _ = Real.exp (-9*L)*Real.exp (-8*supplyEpsilon*H) := Real.exp_add _ _
    _ ≤ _ := mul_le_mul hd hU (Real.exp_pos _).le hc.le

end Ostmann.Supply

end

end OAI
