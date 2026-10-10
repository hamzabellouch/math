import OAI.NumberTheory.EgyptianFractions.ThreePrimeContinuousEnergy
import OAI.NumberTheory.EgyptianFractions.ThreePrimeMinorArc

namespace OAI
noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Problem337.ThreePrimeContinuousMinorArc

/-- The actual prime logarithmic exponential sum, with positive phase. -/
def primeExponentialSum (u : ℕ) (x : ℝ) : ℂ :=
  ThreePrimeContinuousEnergy.natPolynomial (Nat.primesLE u)
    (fun p => (Real.log (p : ℝ) : ℂ)) x

lemma primeExponentialSum_eq (u : ℕ) (x : ℝ) :
    primeExponentialSum u x =
      ∑ p ∈ (Finset.Icc 1 u).filter Nat.Prime,
        (Real.log (p : ℝ) : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * (p : ℂ) * (x : ℂ)) := by
  rw [primeExponentialSum, ThreePrimeContinuousEnergy.natPolynomial,
    Nat.primesLE_eq_filter_Icc_one]

/-- Every real frequency gives a unit-modulus phase. -/
lemma phase_norm (t x : ℝ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * (t : ℂ) * (x : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im]

/-- The unconditional amplitude estimate needed in major-arc error budgets. -/
theorem primeExponentialSum_norm_le (u : ℕ) (x : ℝ) :
    ‖primeExponentialSum u x‖ ≤ Real.log 4 * (u : ℝ) := by
  apply ThreePrimeMinorArc.prime_sum_norm_le
  intro p hp
  exact (phase_norm p x).le

/-- Exact energy of the prime exponential sum on one unit interval. -/
theorem primeExponentialSum_parseval (u : ℕ) :
    (∫ x : ℝ in 0..1, ‖primeExponentialSum u x‖ ^ 2) =
      ∑ p ∈ Nat.primesLE u, Real.log (p : ℝ) ^ 2 := by
  simpa only [primeExponentialSum, Complex.norm_real, Real.norm_eq_abs, sq_abs] using
    ThreePrimeContinuousEnergy.nat_polynomial_parseval_interval
      (Nat.primesLE u) (fun p => (Real.log (p : ℝ) : ℂ))

/-- Continuous prime minor arcs with an arbitrary norm-bounded twist.
The prime supremum estimate remains an explicit analytic hypothesis. -/
theorem prime_minor_cubic_bound (u : ℕ) (hu : 2 ≤ u)
    (phase : ℝ → ℂ) (minor : Set ℝ) (hmeas : MeasurableSet minor)
    (hsubset : minor ⊆ Set.Icc 0 1) (ε : ℝ) (hε : 0 ≤ ε)
    (hminor : ∀ x ∈ minor, ‖primeExponentialSum u x‖ ≤
      ε * (u : ℝ) / Real.log (u : ℝ))
    (hphase : ∀ x ∈ minor, ‖phase x‖ ≤ 1) :
    ‖∫ x in minor, primeExponentialSum u x ^ 3 * phase x‖ ≤
      ε * Real.log 4 * (u : ℝ) ^ 2 := by
  have hu1 : 1 < (u : ℝ) := by exact_mod_cast (show 1 < u by omega)
  have hlog : 0 < Real.log (u : ℝ) := Real.log_pos hu1
  have hB : 0 ≤ ε * (u : ℝ) / Real.log (u : ℝ) := by positivity
  have h := ThreePrimeContinuousEnergy.nat_polynomial_interval_minor_cubic_bound
    (Nat.primesLE u) (fun p => (Real.log (p : ℝ) : ℂ)) phase minor hmeas hsubset
    (ε * (u : ℝ) / Real.log (u : ℝ)) hB hminor hphase
  change ‖∫ x in minor, primeExponentialSum u x ^ 3 * phase x‖ ≤ _ at h
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs] at h
  apply h.trans
  calc
    ε * (u : ℝ) / Real.log (u : ℝ) *
        (∑ p ∈ Nat.primesLE u, Real.log (p : ℝ) ^ 2) ≤
      ε * (u : ℝ) / Real.log (u : ℝ) *
        (Real.log 4 * (u : ℝ) * Real.log (u : ℝ)) :=
      mul_le_mul_of_nonneg_left (ThreePrimeMinorArc.prime_log_squares_le u (by omega)) hB
    _ = ε * Real.log 4 * (u : ℝ) ^ 2 := by field_simp

/-- Conventional negative extraction frequency for the cubic prime count. -/
theorem prime_minor_extraction_bound (u : ℕ) (hu : 2 ≤ u)
    (minor : Set ℝ) (hmeas : MeasurableSet minor)
    (hsubset : minor ⊆ Set.Icc 0 1) (ε : ℝ) (hε : 0 ≤ ε)
    (hminor : ∀ x ∈ minor, ‖primeExponentialSum u x‖ ≤
      ε * (u : ℝ) / Real.log (u : ℝ)) :
    ‖∫ x in minor, primeExponentialSum u x ^ 3 *
      Complex.exp (2 * Real.pi * Complex.I * (-(u : ℂ)) * (x : ℂ))‖ ≤
      ε * Real.log 4 * (u : ℝ) ^ 2 := by
  apply prime_minor_cubic_bound u hu _ minor hmeas hsubset ε hε hminor
  intro x hx
  simpa only [Complex.ofReal_neg, Complex.ofReal_natCast] using (phase_norm (-(u : ℝ)) x).le

end Problem337.ThreePrimeContinuousMinorArc

end

end OAI
