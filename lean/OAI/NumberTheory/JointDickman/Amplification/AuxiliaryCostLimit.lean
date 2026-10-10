import OAI.NumberTheory.JointDickman.Amplification.AuxiliaryCostBound

namespace OAI

/-! # The auxiliary sampling error vanishes after the bin-count loss -/
namespace JointDickman
open Filter
open scoped Topology

noncomputable def auxiliaryVanishingCost (H L c β X : ℝ) : ℝ :=
  48000*(8*L^2/c^4/Real.log X+
    2*L^2*(H+1)*(Real.log X)^4*X^(β-1/12))

lemma auxiliaryVanishingCost_nonneg {H L c β X : ℝ} (hH : 0 ≤ H)
    (hX : 1 ≤ X) : 0 ≤ auxiliaryVanishingCost H L c β X := by
  unfold auxiliaryVanishingCost
  have hl := Real.log_nonneg hX
  positivity

theorem auxiliaryVanishingCost_tendsto (H L c : ℝ) {β : ℝ} (hβ : β < 1/12) :
    Tendsto (auxiliaryVanishingCost H L c β) atTop (𝓝 0) := by
  have hlog := tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have hp := log_power_div_power_tendsto_zero 4 (show 0 < 1/12-β by linarith)
  have hp' : Tendsto (fun X : ℝ => (Real.log X)^4*X^(β-1/12)) atTop (𝓝 0) := by
    apply hp.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with X hX
    rw [show β-1/12=-(1/12-β) by ring,Real.rpow_neg hX.le]
    norm_num [div_eq_mul_inv]
  have h1 := hlog.const_mul (8*L^2/c^4)
  have h2 := hp'.const_mul (2*L^2*(H+1))
  have hh := (h1.add h2).const_mul 48000
  unfold auxiliaryVanishingCost
  simpa only [Function.comp_apply,div_eq_mul_inv,mul_assoc,mul_zero,add_zero] using hh

theorem auxiliary_cost_eventually_bound (C H L : ℝ) (hC : 0 ≤ C) (hH : 0 ≤ H)
    {α β : ℝ} (hα : 0 < α) :
    ∀ᶠ N : ℕ in atTop, ∀ T a b k : ℝ,
      0 ≤ T → T ≤ N → Real.exp (-1)*(N:ℝ)^α ≤ a → a ≤ (N:ℝ)^β →
      0 ≤ k → k ≤ L*Real.log (N:ℝ) →
      k^2*auxiliarySampleCost C H N N T a b ≤
        auxiliaryVanishingCost H L (α/2) β N+L^2*b^2*C/(α/2)^2 := by
  have hlow := (eventually_auxiliary_log_lower hα).filter_mono tendsto_natCast_atTop_atTop
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop 1)
  filter_upwards [hlow,hlog,eventually_gt_atTop (0:ℕ)] with N hlow hlog hN
  intro T a b k hT hTN ha haβ hk0 hk
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hh := hlow a ha
  have ha0 : 0 ≤ a := le_trans (by positivity : 0 ≤ Real.exp (-1)*(N:ℝ)^α) ha
  exact auxiliary_cost_bound hn hlog hT hTN ha0 haβ hC hH
    (by positivity : 0<α/2) hh.1 hh.2 hk0 hk

end JointDickman

end OAI
