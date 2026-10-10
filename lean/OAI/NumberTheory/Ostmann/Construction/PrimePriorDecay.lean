import OAI.NumberTheory.Ostmann.Construction.HarmonicWordPriors
import OAI.NumberTheory.Ostmann.Construction.OneSidedDecayBudget

namespace OAI

/-! # Actual harmonic-prime point masses on the separated scales -/

namespace Ostmann

open scoped BigOperators
open Filter

theorem primeSubsetPrior_le_exp (P Q : Finset ℕ) (p : P) (H T : ℝ)
    (hmass : (∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹ ≤ Real.exp H)
    (hp : Real.exp T ≤ (p : ℝ)) :
    primeSubsetPrior P Q p ≤ Real.exp (H - T) := by
  have hp0 : 0 < (p : ℝ) := (Real.exp_pos T).trans_le hp
  have hi : (p : ℝ)⁻¹ ≤ Real.exp (-T) := by
    rw [Real.exp_neg]
    exact inv_anti₀ (Real.exp_pos _) hp
  calc
    _ ≤ (∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹ * (p : ℝ)⁻¹ := primeSubsetPrior_atom P Q p
    _ ≤ Real.exp H * Real.exp (-T) :=
      mul_le_mul hmass hi (inv_nonneg.mpr hp0.le) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1

/-- Polynomial exponential cell normalizers are absorbed by the lower prime
scale. The bound is uniform over every actual role and every sampled prime. -/
theorem eventual_primeSubsetPrior_decay (K z α c : ℝ) (d : ℕ)
    (hK : 0 ≤ K) (hz : 0 ≤ z) (hα : 0 < α) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ (m : ℝ) (P Q : Finset ℕ), 0 ≤ m → m ≤ z * L →
      (∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹ ≤ Real.exp (K * (1 + m) ^ d) →
      (∀ p ∈ P, Real.exp (c * Real.exp (α * L)) ≤ (p : ℝ)) →
      ∀ p : P, primeSubsetPrior P Q p ≤ Real.exp (-(c / 2) * Real.exp (α * L)) := by
  filter_upwards [eventual_polynomial_log_budget K z α (c / 2) d hK hz hα (by positivity)]
    with L hL m P Q hm hmL hmass hp p
  apply (primeSubsetPrior_le_exp P Q p _ _ hmass (hp p p.property)).trans
  apply Real.exp_le_exp.mpr
  linarith [hL m hm hmL]

end Ostmann

end OAI
