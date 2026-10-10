import OAI.NumberTheory.EgyptianFractions.ChebyshevLowerSharp

namespace OAI
noncomputable section
open Filter Asymptotics

namespace Problem337.ChebyshevRealBounds

open ChebyshevLowerSharp

/-- Floor transfer of the stronger elementary lower bound to all real endpoints.
The threshold is uniform in the endpoint; no prime number theorem is used. -/
theorem eventually_psi_lower_real {c : ℝ} (hc : c < lowerConstant) :
    ∀ᶠ x : ℝ in atTop, c * x ≤ Chebyshev.psi x := by
  have hC : 0 < lowerConstant := by linarith [lowerConstant_gt_921_div_1000]
  let d := (max c 0 + lowerConstant) / 2
  have hmax : max c 0 < lowerConstant := max_lt hc hC
  have hdC : d < lowerConstant := by dsimp [d]; linarith
  have hd0 : 0 < d := by dsimp [d]; have := le_max_right c 0; linarith
  have hcd : c < d := by dsimp [d]; have := le_max_left c 0; linarith
  filter_upwards [tendsto_nat_floor_atTop.eventually (eventually_psi_lower hdC),
    eventually_ge_atTop (d / (d - c))] with x hx hlarge
  rw [Chebyshev.psi_eq_psi_coe_floor]
  have hmargin : d ≤ (d - c) * x := by
    have h := (div_le_iff₀ (sub_pos.2 hcd)).1 hlarge
    nlinarith
  have hfloor := mul_lt_mul_of_pos_left (Nat.lt_floor_add_one x) hd0
  nlinarith

/-- The same lower coefficient holds for the log-weighted sum over primes alone. -/
theorem eventually_theta_lower_real {c : ℝ} (hc : c < lowerConstant) :
    ∀ᶠ x : ℝ in atTop, c * x ≤ Chebyshev.theta x := by
  let δ := (lowerConstant - c) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hco : c + δ < lowerConstant := by dsimp [δ]; linarith
  have hsmall := (isLittleO_log_rpow_atTop (r := (1 / 2 : ℝ))
    (by norm_num)).bound (c := δ / 2) (by positivity)
  filter_upwards [eventually_psi_lower_real hco, hsmall,
    eventually_ge_atTop (2 : ℝ)] with x hx hs hx2
  have hx0 : 0 ≤ x := by linarith
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hs' : Real.log x ≤ δ / 2 * Real.sqrt x := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hlog0,
      abs_of_nonneg (Real.rpow_nonneg hx0 _), ← Real.sqrt_eq_rpow,
      abs_of_nonneg (Real.sqrt_nonneg x)] using hs
  have he := Chebyshev.psi_sub_theta_le (show 1 ≤ x by linarith)
  have hmul := mul_le_mul_of_nonneg_left hs' (show 0 ≤ 2 * Real.sqrt x by positivity)
  have hsquare := Real.mul_self_sqrt hx0
  nlinarith

/-- Natural endpoints for direct use in finite exceptional-prime deletion. -/
theorem eventually_theta_lower {c : ℝ} (hc : c < lowerConstant) :
    ∀ᶠ N : ℕ in atTop, c * N ≤ Chebyshev.theta N :=
  (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop).eventually
    (eventually_theta_lower_real hc)

/-- The sharp elementary prime-count lower bound at a real endpoint. -/
theorem eventually_primeCounting_lower_real {c : ℝ} (hc : c < lowerConstant) :
    ∀ᶠ x : ℝ in atTop, c * x / Real.log x ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
  filter_upwards [eventually_psi_lower_real hc, eventually_gt_atTop (1 : ℝ)] with x hx hx1
  exact (div_le_iff₀ (Real.log_pos hx1)).2
    (hx.trans (Chebyshev.psi_le_primeCounting_mul_log' x))

end Problem337.ChebyshevRealBounds

end

end OAI
