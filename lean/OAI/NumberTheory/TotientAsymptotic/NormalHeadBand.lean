import OAI.NumberTheory.TotientAsymptotic.SurvivingComparison

namespace OAI

/-! The first shifted prime has its largest factor above height 0.9. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

lemma head_logarithmic_loss : ∀ᶠ b : ℝ in atTop,
    2+Real.log (4*b) ≤ (1/10 : ℝ)*b := by
  have ht : Tendsto (fun b : ℝ => (2+Real.log 4)/b+Real.log b/b) atTop (nhds 0) := by
    have h1 : Tendsto (fun b : ℝ => (2+Real.log 4)/b) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    simpa only [add_zero,id_eq] using h1.add Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  filter_upwards [ht.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1/10)),
    eventually_gt_atTop (0 : ℝ)] with b hb hb0
  rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hb0.ne']
  have hh := (div_le_iff₀ hb0).mp (show (2+Real.log 4+Real.log b)/b ≤ (1/10 : ℝ) by
    simpa only [add_div] using hb.le)
  linarith

/-- This handles the largest-prime coordinate, whose band convention is
`u₀ = B x` rather than `B p`. -/
theorem normal_head_largest_factor : ∀ᶠ x : ℝ in atTop, ∀ S : ℝ, ∀ p : ℕ,
    IsNormalPrime S p → 1 < S → 0 ≤ B S → S ≤ x →
    x^(9/10 : ℝ) ≤ p → (p-1 : ℕ) ≤ x →
    (9/10 : ℝ)*B x ≤ B (largestPrimeFactor (p-1)) := by
  filter_upwards [B_tendsto.eventually head_logarithmic_loss,
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ)),eventually_gt_atTop (1 : ℝ),
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 9/10)).eventually (eventually_gt_atTop (2 : ℝ))]
    with x hloss hB hx hxpow
  intro S p hp hS hBS hSx hpmin hpx
  have hp3 : 3 ≤ p := by
    have hh : (2 : ℝ) < p := hxpow.trans_le hpmin
    exact_mod_cast hh
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.1.one_lt
  have hlog := Real.log_le_log (Real.rpow_pos_of_pos (zero_lt_one.trans hx) _) hpmin
  rw [Real.log_rpow (zero_lt_one.trans hx)] at hlog
  have hdouble := Real.log_le_log (mul_pos (by norm_num : (0 : ℝ) < 9/10) (Real.log_pos hx)) hlog
  rw [Real.log_mul (by norm_num : (9/10 : ℝ) ≠ 0) (Real.log_pos hx).ne'] at hdouble
  change Real.log (9/10 : ℝ)+B x ≤ Real.log (Real.log (p : ℝ)) at hdouble
  have hl9 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 9/10)
  norm_num only [inv_div,div_self] at hl9
  have hlower := largest_factor_doubleLog_lower (show 2 ≤ p-1 by omega)
    (show 0 < 4*B x by positivity) (normal_prime_omega_below hp hS hBS hSx hpx)
  have hshift := shifted_doubleLog_lower hp3
  change Real.log (Real.log (p : ℝ))-1 ≤ B (p-1 : ℕ) at hshift
  change 2+Real.log (4*B x) ≤ (1/10 : ℝ)*B x at hloss
  linarith

end TotientAsymptotic

end

end OAI
