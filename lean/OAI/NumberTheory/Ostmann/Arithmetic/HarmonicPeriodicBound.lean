import OAI.NumberTheory.Ostmann.Construction.OriginalPriorPeriodicBound
import OAI.NumberTheory.Ostmann.Construction.HarmonicWordPriors

namespace OAI

/-! # Original harmonic prime priors with all frequency residue tests -/

namespace Ostmann

open scoped BigOperators Classical

theorem harmonic_periodic_polynomial_one_sided_bound (P Q : Finset ℕ)
    (hprime : ∀ q ∈ Q, q.Prime)
    (χ : ∀ q : Q, DirichletCharacter ℂ (q : ℕ)) (hnonprincipal : ∀ q, χ q ≠ 1)
    (a M K : ℕ) (ha : 0 < a) (hM : ∀ q : Q, M.Coprime (q : ℕ))
    (gate : Q → ZMod M → ℂ) (hgate : ∀ q z, ‖gate q z‖ ≤ 1)
    (hlow : ∀ p ∈ P, a ≤ p) (hhigh : ∀ p ∈ P, p < a + K * M)
    (b : ℝ) (hb : 0 < b) (hbQ : ∀ q ∈ Q, b ≤ (q : ℝ))
    (hPmass : 0 < ∑ p ∈ P, (p : ℝ)⁻¹) (hQmass : 0 < ∑ q ∈ Q, (q : ℝ)⁻¹)
    {n t : ℕ} (F : Q → Fin n → ClippedPolynomialFactor)
    (H : Q → Fin t → Polynomial ℝ) (keep : Q → (Fin t → Bool) → Bool)
    (B : ℝ) (R Bq : ℕ) (hB : 0 ≤ B)
    (hbudget : ∀ q, smoothPolynomialBudget (F q) ≤ B)
    (hcomplexity : ∀ q, polynomialWeightComplexity (F q) (H q) ≤ R)
    (hBq : ∀ q : Q, (q : ℕ) ≤ Bq)
    (U : P → ℂ) (V : Q → ℂ) (hU : ∀ p, ‖U p‖ ≤ 1) (hV : ∀ q, ‖V q‖ ≤ 1) :
    ‖∑ p : P, (primeSubsetPrior P P p : ℂ) *
      (U p * ∑ q : Q, (primeSubsetPrior Q Q q : ℂ) * V q *
        (χ q ((p : ℕ) : ZMod (q : ℕ)) *
          (gate q ((p : ℕ) : ZMod M) * polynomialAmplitude (F q) (H q) (keep q) (p : ℝ))))‖ ^ 2 ≤
      (∑ p ∈ P, (p : ℝ)⁻¹)⁻¹ *
        (((∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹ * b⁻¹) * (((K * M : ℕ) : ℝ) / a * B ^ 2) +
          (M : ℝ) * ((3 ^ (2 * R) : ℕ) * (2 * (a : ℝ)⁻¹ * B ^ 2)) * (Bq : ℝ) ^ 2) := by
  apply original_prior_periodic_polynomial_one_sided_bound (fun p : P => (p : ℕ)) Subtype.val_injective
    Q hprime χ hnonprincipal a M K ha hM gate hgate
    (fun p => hlow p p.property) (fun p => hhigh p p.property) F H keep B R Bq hB
    hbudget hcomplexity hBq (primeSubsetPrior P P) (primeSubsetPrior Q Q) U V
    ((∑ p ∈ P, (p : ℝ)⁻¹)⁻¹) ((∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹ * b⁻¹)
    (by positivity) (by positivity) (primeSubsetPrior_nonneg P P)
  · exact (primeSubsetPrior_mass P P (Finset.Subset.refl _) hPmass.ne').le
  · exact primeSubsetPrior_atom P P
  · exact primeSubsetPrior_nonneg Q Q
  · exact (primeSubsetPrior_mass Q Q (Finset.Subset.refl _) hQmass.ne').le
  · intro q
    apply (primeSubsetPrior_atom Q Q q).trans
    exact mul_le_mul_of_nonneg_left (inv_anti₀ hb (hbQ q q.property)) (by positivity)
  · exact hU
  · exact hV

end Ostmann

end OAI
