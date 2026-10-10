import OAI.NumberTheory.EgyptianFractions.ThreePrimeMangoldtAsymptotics

namespace OAI
noncomputable section
open Filter Asymptotics

namespace Problem337

/-- The elementary prime-power error is smaller than every power above `3/2`. -/
theorem mangoldt_triple_error_isLittleO_rpow
    (α : ℝ) (hα : 3 / 2 < α) :
    (fun x : ℝ => 3 * x * Real.log x ^ 2 *
      (Chebyshev.psi x - Chebyshev.theta x)) =o[atTop]
      (fun x : ℝ => x ^ α) := by
  have hlog : (fun x : ℝ => Real.log x ^ 2) =o[atTop]
      (fun x : ℝ => x ^ (α - 3 / 2)) := by
    simpa only [Real.rpow_two] using
      isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by linarith : 0 < α - 3 / 2)
  have hsmall := hlog.mul_isBigO Chebyshev.isBigO_psi_sub_theta_sqrt
  have hscaled := hsmall.mul_isBigO (isBigO_refl (fun x : ℝ => x) atTop)
  have hfinal :
      (fun x : ℝ => x * Real.log x ^ 2 * (Chebyshev.psi x - Chebyshev.theta x))
        =o[atTop] (fun x : ℝ => x ^ α) := by
    apply hscaled.congr'
    · exact Eventually.of_forall (fun x => by simp only [Pi.sub_apply]; ring)
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [Real.sqrt_eq_rpow]
      calc
        x ^ (α - 3 / 2) * x ^ (1 / 2 : ℝ) * x =
            x ^ (α - 3 / 2) * x ^ (1 / 2 : ℝ) * x ^ (1 : ℝ) := by
          rw [Real.rpow_one]
        _ = x ^ α := by
          rw [← Real.rpow_add hx, ← Real.rpow_add hx]
          congr 1
          ring
  simpa only [mul_assoc] using hfinal.const_mul_left 3

/-- Actual Mangoldt and prime-only convolutions differ by `o(u^α)` for `α>3/2`. -/
theorem mangoldtTripleSum_sub_primeTripleLogSum_isLittleO_rpow
    (α : ℝ) (hα : 3 / 2 < α) :
    (fun u : ℕ => mangoldtTripleSum u - primeTripleLogSum u) =o[atTop]
      (fun u : ℕ => (u : ℝ) ^ α) := by
  have hbound := (mangoldt_triple_error_isLittleO_rpow α hα).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))
  apply IsLittleO.of_bound
  intro c hc
  filter_upwards [hbound.bound hc] with u hu
  simp only [Function.comp_apply, Real.norm_eq_abs] at hu ⊢
  exact (abs_mangoldtTripleSum_sub_primeTripleLogSum_le u).trans
    ((le_abs_self _).trans hu)

/-- A positive power lower bound for the Mangoldt convolution survives removing
higher prime powers at any exponent above `3/2`. The lower bound itself remains
an explicit analytic premise. -/
theorem weighted_prime_power_lower_bound_of_mangoldt
    (α : ℝ) (hα : 3 / 2 < α) (c : ℝ) (hc : 0 < c)
    (hmain : ∀ᶠ u : ℕ in atTop, Odd u → c * (u : ℝ) ^ α ≤ mangoldtTripleSum u) :
    ∀ᶠ u : ℕ in atTop, Odd u →
      (c / 2) * (u : ℝ) ^ α ≤ primeTripleLogSum u := by
  have herr := (mangoldtTripleSum_sub_primeTripleLogSum_isLittleO_rpow α hα).bound
    (show 0 < c / 2 by positivity)
  filter_upwards [hmain, herr] with u hu herr
  intro hodd
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg u) α),
    Real.norm_eq_abs] at herr
  have habs := le_abs_self (mangoldtTripleSum u - primeTripleLogSum u)
  have hlower := hu hodd
  linarith

/-- Transfer of an arbitrary power-scale asymptotic to genuine prime triples,
including along the odd integers or any other subfilter tending to infinity. -/
theorem mangoldt_prime_rpow_asymptotic_iff_filter
    (α : ℝ) (hα : 3 / 2 < α) (l : Filter ℕ) (hl : l ≤ atTop) (σ : ℕ → ℝ) :
    ((fun u : ℕ => mangoldtTripleSum u - σ u * (u : ℝ) ^ α) =o[l]
      (fun u : ℕ => (u : ℝ) ^ α)) ↔
    ((fun u : ℕ => primeTripleLogSum u - σ u * (u : ℝ) ^ α) =o[l]
      (fun u : ℕ => (u : ℝ) ^ α)) := by
  have herr := (mangoldtTripleSum_sub_primeTripleLogSum_isLittleO_rpow α hα).mono hl
  constructor
  · intro h
    exact (h.sub herr).congr_left (fun u => by ring)
  · intro h
    exact (h.add herr).congr_left (fun u => by ring)

end Problem337

end

end OAI
