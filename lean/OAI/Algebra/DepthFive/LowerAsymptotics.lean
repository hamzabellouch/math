import Mathlib

namespace OAI

noncomputable section

namespace Problem335

open Filter

/-- The numerical comparison in the lower-bound argument, with an explicit
sufficient logarithmic threshold. No algebraic complexity hypotheses enter here. -/
theorem size_lower_bound_of_rank_bounds
    (x S D R C₁ C₂ : ℝ)
    (hx : 1 ≤ x) (hS : 0 ≤ S) (hD : 0 < D)
    (hlog : 400 * (|C₁| + |C₂| + 1) ≤ Real.log x)
    (hlower : D * Real.exp (-C₁ * Real.sqrt x) ≤ R)
    (hupper : R ≤ 2 * S ^ 2 * D * Real.exp (C₂ * Real.sqrt x) *
      x ^ (-Real.sqrt x / 100)) :
    x ^ (Real.sqrt x / 400) ≤ S := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hbounds := hlower.trans hupper
  have hleftpos : 0 < D * Real.exp (-C₁ * Real.sqrt x) :=
    mul_pos hD (Real.exp_pos _)
  have hSpos : 0 < S := by
    by_contra h
    have hzero : S = 0 := le_antisymm (le_of_not_gt h) hS
    simp only [hzero, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul] at hbounds
    exact (not_le_of_gt hleftpos) hbounds
  have hlogs := Real.log_le_log hleftpos hbounds
  have hDne : D ≠ 0 := ne_of_gt hD
  have hSne : S ≠ 0 := ne_of_gt hSpos
  simp [Real.log_mul, Real.log_pow, Real.log_rpow hxpos,
    hDne, hSne, ne_of_gt (Real.rpow_pos_of_pos hxpos (-Real.sqrt x / 100))] at hlogs
  have hsqrt : 1 ≤ Real.sqrt x := Real.one_le_sqrt.mpr hx
  have hlogtwo : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this ⊢
    exact this
  have habs₁ := le_abs_self C₁
  have habs₂ := le_abs_self C₂
  have hnonneg₁ := abs_nonneg C₁
  have hnonneg₂ := abs_nonneg C₂
  have hslack : C₁ + C₂ + 1 ≤ Real.log x / 400 := by linarith
  have hslackmul := mul_le_mul_of_nonneg_right hslack (Real.sqrt_nonneg x)
  have hlognonneg : 0 ≤ Real.log x := Real.log_nonneg hx
  have htarget : Real.sqrt x / 400 * Real.log x ≤ Real.log S := by
    nlinarith
  apply (Real.log_le_log_iff (Real.rpow_pos_of_pos hxpos _) hSpos).mp
  rw [Real.log_rpow hxpos]
  exact htarget

/-- Fixed exponential losses can be absorbed uniformly into the power saving.
The threshold is independent of `S`, `D`, and the rank value `R`. -/
theorem eventual_size_lower_bound_of_rank_bounds (C₁ C₂ : ℝ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ S D R : ℝ,
      0 ≤ S → 0 < D →
      D * Real.exp (-C₁ * Real.sqrt (n : ℝ)) ≤ R →
      R ≤ 2 * S ^ 2 * D * Real.exp (C₂ * Real.sqrt (n : ℝ)) *
        (n : ℝ) ^ (-Real.sqrt (n : ℝ) / 100) →
      (n : ℝ) ^ (Real.sqrt (n : ℝ) / 400) ≤ S := by
  have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hlog := Real.tendsto_log_atTop.comp hcast
  have hone : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ n :=
    hcast.eventually (eventually_ge_atTop 1)
  have hlarge : ∀ᶠ n : ℕ in atTop,
      400 * (|C₁| + |C₂| + 1) ≤ Real.log (n : ℝ) :=
    hlog.eventually (eventually_ge_atTop _)
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp (hone.and hlarge)
  refine ⟨n₀, ?_⟩
  intro n hn S D R hS hD hlower hupper
  exact size_lower_bound_of_rank_bounds (n : ℝ) S D R C₁ C₂
    (hn₀ n hn).1 hS hD (hn₀ n hn).2 hlower hupper

end Problem335

end

end OAI
