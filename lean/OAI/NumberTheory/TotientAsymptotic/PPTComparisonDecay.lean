import OAI.NumberTheory.TotientAsymptotic.Basic

namespace OAI

/-!
The fixed-seed comparison budget in the proof of Ford (5.23).  The
positive error has size at most a constant times `t^(2/3) (log t)^2`,
where `t = log log z`; the negative simplex gap has size `t/(log t)^3`.
The latter absorbs every fixed inverse power of `t`.
-/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

theorem ppt_comparison_exp_decay (A K : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ t : ℝ in atTop,
      Real.exp (A*t^(2/3 : ℝ)*(Real.log t)^2 - δ*t/(Real.log t)^3) ≤ t^(-K) := by
  have h₅ : Tendsto (fun t : ℝ => (Real.log t)^5/t^(1/3 : ℝ)) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast] using
      (isLittleO_log_rpow_rpow_atTop (5 : ℕ)
        (show (0 : ℝ) < 1/3 by norm_num)).tendsto_div_nhds_zero
  have h₄ : Tendsto (fun t : ℝ => (Real.log t)^4/t) atTop (𝓝 0) :=
    Real.isLittleO_pow_log_id_atTop.tendsto_div_nhds_zero
  have hsum : Tendsto (fun t : ℝ =>
      A*((Real.log t)^5/t^(1/3 : ℝ)) + K*((Real.log t)^4/t)) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using (h₅.const_mul A).add (h₄.const_mul K)
  filter_upwards [hsum.eventually (eventually_lt_nhds hδ),
    eventually_gt_atTop (1 : ℝ)] with t hbudget ht
  have ht0 : 0 < t := zero_lt_one.trans ht
  have hlog : 0 < Real.log t := Real.log_pos ht
  have hthird : 0 < t^(1/3 : ℝ) := Real.rpow_pos_of_pos ht0 _
  have hprod : t^(2/3 : ℝ)*t^(1/3 : ℝ) = t := by
    rw [← Real.rpow_add ht0]
    norm_num
  have h₁ : A*t^(2/3 : ℝ)*(Real.log t)^2 =
      (A*(Real.log t)^5/t^(1/3 : ℝ))*(t/(Real.log t)^3) := by
    rw [div_mul_div_comm]
    apply (eq_div_iff (mul_ne_zero hthird.ne' (pow_pos hlog 3).ne')).mpr
    calc
      _ = A*(Real.log t)^5*(t^(2/3 : ℝ)*t^(1/3 : ℝ)) := by ring
      _ = _ := by rw [hprod]
  have h₂ : K*Real.log t = (K*(Real.log t)^4/t)*(t/(Real.log t)^3) := by
    rw [div_mul_div_comm]
    apply (eq_div_iff (mul_ne_zero ht0.ne' (pow_pos hlog 3).ne')).mpr
    ring
  simp only [mul_div_assoc] at h₁ h₂
  have hbudget' : A*t^(2/3 : ℝ)*(Real.log t)^2 + K*Real.log t ≤
      δ*t/(Real.log t)^3 := by
    calc
      _ = (A*((Real.log t)^5/t^(1/3 : ℝ)) +
          K*((Real.log t)^4/t))*(t/(Real.log t)^3) := by
        rw [add_mul, ← h₁, ← h₂]
      _ ≤ δ*(t/(Real.log t)^3) :=
        mul_le_mul_of_nonneg_right hbudget.le (div_pos ht0 (pow_pos hlog 3)).le
      _ = _ := by ring
  conv_rhs => rw [Real.rpow_def_of_pos ht0]
  apply Real.exp_le_exp.mpr
  nlinarith

/-- Direct substitution of the totient scale, with the conventional
`(log log z)^(-K)` remainder in the exceptional-candidate count. -/
theorem ppt_comparison_exp_decay_at_scale (A K : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ z : ℝ in atTop,
      Real.exp (A*(B z)^(2/3 : ℝ)*(Real.log (B z))^2 -
        δ*B z/(Real.log (B z))^3) ≤ (B z)^(-K) := by
  exact (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually
    (ppt_comparison_exp_decay A K hδ)

end TotientAsymptotic

end

end OAI
