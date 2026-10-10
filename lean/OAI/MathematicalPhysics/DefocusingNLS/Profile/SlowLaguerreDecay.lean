import OAI.MathematicalPhysics.DefocusingNLS.Certificates.LaguerreHilbert
import OAI.MathematicalPhysics.DefocusingNLS.Profile.SlowLaguerreCone

namespace OAI

/-! # Decay and the convergent cone sum for the actual slow solution -/

open Filter Topology Asymptotics MeasureTheory Set

namespace DefocusingNLS

theorem memLp_halfWeighted_shiftedSlowDerivative (k : ℕ) (q : ℂ) (m : ℕ) (s : ℂ)
    (hq : -1 < q.re) (hsre : s.re = 0) (hsim : s.im ≠ 0) :
    MemLp (halfWeighted (shiftedSlowDerivative k q m s)) 2 (volume.restrict (Ioi 0)) := by
  apply memLp_halfWeighted_of_exp_bound
    _ (continuous_shiftedSlowDerivative k q m s hq hsim)
  exact (shiftedSlowDerivative_isBigO_rpow k q m s hq hsre).trans
    (isLittleO_rpow_exp_pos_mul_atTop _ (by norm_num : 0 < (1 / 4 : ℝ))).isBigO

theorem shiftedSlowDerivative_laguerre_tendsto_zero (k : ℕ) (q : ℂ) (m : ℕ) (s : ℂ)
    (hq : -1 < q.re) (hsre : s.re = 0) (hsim : s.im ≠ 0) :
    Tendsto (laguerreCoefficientIntegral (shiftedSlowDerivative k q m s)) atTop (𝓝 0) :=
  laguerreCoefficientIntegral_tendsto_zero _
    (memLp_halfWeighted_shiftedSlowDerivative k q m s hq hsre hsim)

theorem slowLaguerreB_tendsto_zero (q : ℂ) (m : ℕ) (s : ℂ)
    (hq : -1 < q.re) (hsre : s.re = 0) (hsim : s.im ≠ 0) :
    Tendsto (slowLaguerreB q m s) atTop (𝓝 0) := by
  apply (tendsto_add_atTop_iff_nat 1).mp
  simpa only [slowLaguerreB_eq_derivative_coefficient q m s _ hq hsre hsim, neg_zero] using
    (shiftedSlowDerivative_laguerre_tendsto_zero 1 q m s hq hsre hsim).neg

theorem slowLaguerreC_tendsto_zero (q : ℂ) (m : ℕ) (s : ℂ)
    (hq : -1 < q.re) (hsre : s.re = 0) (hsim : s.im ≠ 0) :
    Tendsto (slowLaguerreC q m s) atTop (𝓝 0) := by
  change Tendsto (fun n => slowLaguerreC q m s n) atTop (𝓝 0)
  simp_rw [slowLaguerreC_eq_derivative_coefficients q m s _ hq hsre hsim]
  simpa only [sub_self] using
    (shiftedSlowDerivative_laguerre_tendsto_zero 2 q m s hq hsre hsim).sub
      (shiftedSlowDerivative_laguerre_tendsto_zero 1 q m s hq hsre hsim)

/-- The exact infinite cone sum for the actual coefficients. Strict negativity
additionally requires a nonzero coefficient beyond the chosen cutoff. -/
theorem hasSum_slowLaguerre_cone_increments (σ : ℝ) (ℓ K : ℕ) (q s : ℂ)
    (hσ : -(1 / 32 : ℝ) ≤ σ) (hK : 3 ≤ K)
    (hq : q.re = σ + (ℓ : ℝ) / 2) (hsre : s.re = 0) (hsim : s.im ≠ 0) :
    HasSum (fun n : ℕ => (σ + ((n + K : ℕ) : ℝ) - 5 / 2) *
      Complex.normSq (slowLaguerreCoefficient q (ℓ + 6) s (n + K)))
      (-coneForm ((ℓ : ℝ) + 5) s (slowLaguerreB q (ℓ + 6) s K)
        (slowLaguerreC q (ℓ + 6) s K)) := by
  have hq' : -1 < q.re := by rw [hq]; linarith [Nat.cast_nonneg (α := ℝ) ℓ]
  apply hasSum_cone_increments
    (fun n => coneForm ((ℓ : ℝ) + 5) s (slowLaguerreB q (ℓ + 6) s n)
      (slowLaguerreC q (ℓ + 6) s n))
    (fun n => (σ + n - 5 / 2) * Complex.normSq (slowLaguerreCoefficient q (ℓ + 6) s n)) K
  · exact coneForm_tendsto_zero _ _ _ _
      (slowLaguerreB_tendsto_zero q (ℓ + 6) s hq' hsre hsim)
      (slowLaguerreC_tendsto_zero q (ℓ + 6) s hq' hsre hsim)
  · intro n
    exact slowLaguerre_mode_cone_increment σ ℓ n q s hσ hq hsre hsim
  · intro n hn
    exact mode_increment_nonneg σ n _ hσ (hK.trans hn)

end DefocusingNLS

end OAI
