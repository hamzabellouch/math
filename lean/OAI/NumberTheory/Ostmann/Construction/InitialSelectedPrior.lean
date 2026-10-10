import OAI.NumberTheory.Ostmann.Construction.SelectedCompensationCells
import OAI.NumberTheory.Ostmann.Construction.TailFourierMass
import OAI.NumberTheory.Ostmann.Construction.SupportedPrimePrior
import OAI.NumberTheory.Ostmann.Construction.SmoothGiantSupport
import OAI.NumberTheory.Ostmann.Construction.InitialHalfListWeights

namespace OAI

/-! # Support and normalization of the actual initial cell priors -/
namespace Ostmann
open scoped Classical BigOperators

theorem smoothGiantPrior_log_distance (P : Finset ℕ) (G : ℝ) (q : P)
    (hq : smoothGiantPrior P logCellProfile G q ≠ 0) :
    |Real.log (q : ℝ) - G| ≤ 1 := by
  by_contra hn
  have hz := logCellProfile_zero_outside (Real.log (q : ℝ) - G) (le_of_not_ge hn)
  apply hq
  simp only [smoothGiantPrior, hz, mul_zero, zero_div]

theorem smoothGiantPrior_prime_bound (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime)
    (G : ℝ) (q : P) : (q : ℝ) * smoothGiantPrior P logCellProfile G q ≤
      Real.exp (smoothGiantLogNormalizer P logCellProfile G) := by
  rw [smoothGiantPrior_cancel_prime P hP]
  exact mul_le_of_le_one_right (Real.exp_nonneg _) (logCellProfile_le_one _)

theorem SelectedSmallTailCell.prior_properties
    {A B : Set ℕ} {N hi j : ℕ} {a C L X target : ℝ} {D : Finset ℕ}
    (h : SelectedSmallTailCell A B N a C L X hi D target j)
    (P : Finset ℕ)
    (hsub : selectedTailCellPrimes A B N X hi D j ⊆ P) :
    let μ := primeSubsetPrior P (selectedTailCellPrimes A B N X hi D j)
    (∑ q : P, μ q) = 1 ∧
      (∀ q, 0 ≤ μ q) ∧
      (∀ q : P, (q : ℝ) * μ q ≤ Real.exp (2 * L)) ∧
      (∀ q : P, μ q ≠ 0 → |Real.log (q : ℝ) - j| ≤ 1) ∧
      (∀ q : P, μ q ≠ 0 → (1 / 3 : ℝ) ≤ residueDensity (tailDensityMask A N q) ∧
        residueDensity (tailDensityMask A N q) ≤ 2 / 3) := by
  intro μ
  obtain ⟨_, _, _, _hmass, hpos, hnorm, hprop⟩ := h
  refine ⟨primeSubsetPrior_mass P _ hsub hpos.ne', primeSubsetPrior_nonneg P _, ?_, ?_, ?_⟩
  · intro q
    exact (prime_mul_primeSubsetPrior_le P _ q).trans hnorm
  · intro q hq
    have hmem := primeSubsetPrior_support P _ q hq
    obtain ⟨hp, hlo, hhi, _, _⟩ := hprop q hmem
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hp.pos
    have hl : (j : ℝ) < Real.log (q : ℝ) := (Real.lt_log_iff_exp_lt hq0).mpr hlo
    have hu : Real.log (q : ℝ) ≤ (j : ℝ) + 1 := (Real.log_le_iff_le_exp hq0).mpr hhi
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · intro q hq
    have hmem := primeSubsetPrior_support P _ q hq
    obtain ⟨hp, _, _, hlo, hhi⟩ := hprop q hmem
    exact (tailDensityMask_balanced_iff A N q hp.pos).mpr ⟨hlo, hhi⟩

end Ostmann

end OAI
