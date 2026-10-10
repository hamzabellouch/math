import OAI.NumberTheory.CubicMoment.Estimates.UniformCoreBlockMoment

namespace OAI

/-! A fixed logarithmic square-divisor cutoff satisfies the explicit
small-divisor power condition at every polynomial stopped length. -/
noncomputable section
open Filter
namespace CubicFirstMoment

lemma stopped_logarithmic_divisor_small {κ : ℝ} (hκ : 0 < κ) (q : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ (b D : ℝ), X^κ ≤ b → D ≤ (Real.log X)^q →
      D ≤ b^(1/1000:ℝ) := by
  filter_upwards [negative_power_log_saving (show 0 < κ/1000 by positivity) q,
    eventually_ge_atTop (Real.exp 1)] with X hdecay hX
  intro b D hb hD
  have hXp : 0 < X := (Real.exp_pos 1).trans_le hX
  have hz : 0 < Real.log X := by
    have hh := Real.log_le_log (Real.exp_pos 1) hX
    rw [Real.log_exp] at hh
    linarith
  have hpow : (1+Real.log X)^q ≤ X^(κ/1000) := by
    have hp : 0 < X^(κ/1000) := Real.rpow_pos_of_pos hXp _
    have hh : 1/X^(κ/1000) ≤ 1/(1+Real.log X)^q := by
      simpa only [Real.rpow_neg hXp.le,one_div] using hdecay
    simpa only [one_mul] using (div_le_div_iff₀ hp (by positivity)).mp hh
  apply (hD.trans ((pow_le_pow_left₀ hz.le (by linarith) q).trans hpow)).trans
  rw [show κ/1000 = κ*(1/1000) by ring,Real.rpow_mul hXp.le]
  exact Real.rpow_le_rpow (Real.rpow_nonneg hXp.le _) hb (by norm_num)

end CubicFirstMoment

end

end OAI
