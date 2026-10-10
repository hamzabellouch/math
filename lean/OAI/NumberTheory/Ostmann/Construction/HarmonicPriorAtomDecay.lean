import OAI.NumberTheory.Ostmann.Construction.HarmonicTuplePointBound
import OAI.NumberTheory.Ostmann.Construction.OneSidedDecayBudget

namespace OAI

/-! # Actual harmonic prime priors have negligible point masses -/
namespace Ostmann
open Filter

/-- A lower prime cutoff dominates the harmonic normalization uniformly in
all selected cells, even after their permitted finite deletions. -/
theorem eventual_primeSubsetPrior_atom_decay (H z α c : ℝ)
    (hH : 0 ≤ H) (hz : 0 ≤ z) (hα : 0 < α) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ (m : ℝ) (P Q : Finset ℕ),
      0 ≤ m → m ≤ z * L →
      (∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹ ≤ Real.exp (H * (1 + m)) →
      (∀ q ∈ Q, Real.exp (c * Real.exp (α * L)) ≤ (q : ℝ)) →
      ∀ p : P, primeSubsetPrior P Q p ≤ Real.exp (-(c / 2) * Real.exp (α * L)) := by
  filter_upwards [eventual_polynomial_log_budget H z α (c / 2) 1 hH hz hα (by positivity)]
    with L hL m P Q hm hmL hmass hmin p
  have hh := primeSubsetPrior_le_lower_endpoint P Q (Real.exp (c * Real.exp (α * L)))
    (Real.exp_pos _) hmin p
  apply hh.trans
  calc
    _ ≤ Real.exp (H * (1 + m)) * (Real.exp (c * Real.exp (α * L)))⁻¹ :=
      mul_le_mul_of_nonneg_right hmass (by positivity)
    _ = Real.exp (H * (1 + m) - c * Real.exp (α * L)) := by
      rw [Real.exp_sub, div_eq_mul_inv]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have he := hL m hm hmL
      simp only [pow_one] at he
      linarith

/-- The extra unit and divisibility guards add a polynomially bounded
multiple of the same actual point mass. -/
theorem eventual_prime_prior_guard_decay (H z α c : ℝ)
    (hH : 0 ≤ H) (hz : 0 ≤ z) (hα : 0 < α) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ m atom ratio : ℝ,
      0 ≤ m → m ≤ z * L → 0 ≤ atom →
      atom ≤ Real.exp (-c * Real.exp (α * L)) →
      ratio ≤ Real.exp (H * (1 + m)) →
      atom + ratio * atom ≤ Real.exp (-(c / 2) * Real.exp (α * L)) := by
  filter_upwards [eventual_diagonal_atom_error H z α c 1 hH hz hα hc]
    with L hL m atom ratio hm hmL hatom hatomhi hratio
  have he : 1 ≤ Real.exp (H * (1 + m)) := Real.one_le_exp (by positivity)
  calc
    atom + ratio * atom ≤
        Real.exp (H * (1 + m)) * atom + Real.exp (H * (1 + m)) * atom :=
      add_le_add (le_mul_of_one_le_left hatom he) (mul_le_mul_of_nonneg_right hratio hatom)
    _ ≤ 2 * (Real.exp (H * (1 + m)) * Real.exp (-c * Real.exp (α * L))) := by
      have hh := mul_le_mul_of_nonneg_left hatomhi (Real.exp_nonneg (H * (1 + m)))
      linarith
    _ = 2 * Real.exp (H * (1 + m) - c * Real.exp (α * L)) := by
      rw [← Real.exp_add]
      congr 2
      ring
    _ ≤ _ := by simpa only [pow_one] using hL m hm hmL

end Ostmann

end OAI
