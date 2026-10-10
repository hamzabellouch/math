import OAI.NumberTheory.Ostmann.Conclusion.Scales

namespace OAI

noncomputable section
namespace Ostmann.Construction.RepeatedErrorScale
open Filter
open scoped Topology

theorem fixed_power_eventually {k : ℕ} (hk : 0<k) (r : ℕ) :
    ∀ᶠ L : ℝ in atTop, (3*(Conclusion.bulkSize k L:ℝ))^r≤
      Real.exp (Conclusion.bulkSize k L:ℝ) := by
  have ht : Tendsto (fun L : ℝ => (3*(Conclusion.bulkSize k L:ℝ))^r *
      Real.exp (-(Conclusion.bulkSize k L:ℝ))) atTop (𝓝 0) := by
    have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero r).comp
      (Conclusion.bulkSize_tendsto_atTop hk)).const_mul ((3:ℝ)^r)
    simpa only [Function.comp_def,mul_pow,mul_assoc,mul_zero] using h
  filter_upwards [ht.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))] with L h
  have hh := (le_div_iff₀ (Real.exp_pos (-(Conclusion.bulkSize k L:ℝ)))).mpr h.le
  simpa only [one_div,← Real.exp_neg,neg_neg] using hh

theorem fifteen_thousand_le_exp : (15000:ℝ)≤Real.exp 14 := by
  have h2 : (2:ℝ)≤Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
  calc
    (15000:ℝ)≤(2:ℝ)^14 := by norm_num
    _≤(Real.exp 1)^14 := pow_le_pow_left₀ (by norm_num) h2 14
    _=Real.exp 14 := by simp [← Real.exp_nat_mul]

end Ostmann.Construction.RepeatedErrorScale

end

end OAI
