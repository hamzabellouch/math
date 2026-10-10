import OAI.NumberTheory.Ostmann.Arithmetic.MovingPrimeRowTransfer

namespace OAI

/-! # The exact smooth harmonic giant prior from (7.3) -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def smoothGiantMass (P : Finset ℕ) (φ : ℝ → ℝ) (G : ℝ) : ℝ :=
  ∑ p ∈ P, φ (Real.log p - G) / p

noncomputable def smoothGiantLogNormalizer (P : Finset ℕ) (φ : ℝ → ℝ) (G : ℝ) : ℝ :=
  -Real.log (smoothGiantMass P φ G)

noncomputable def smoothGiantPrior (P : Finset ℕ) (φ : ℝ → ℝ) (G : ℝ) (p : P) : ℝ :=
  Real.exp (smoothGiantLogNormalizer P φ G) * φ (Real.log p - G) / p

theorem smoothGiantPrior_nonneg (P : Finset ℕ) (φ : ℝ → ℝ) (G : ℝ)
    (hφ : ∀ x, 0 ≤ φ x) (p : P) : 0 ≤ smoothGiantPrior P φ G p :=
  div_nonneg (mul_nonneg (Real.exp_nonneg _) (hφ _)) (Nat.cast_nonneg _)

theorem smoothGiantPrior_mass (P : Finset ℕ) (φ : ℝ → ℝ) (G : ℝ)
    (hpos : 0 < smoothGiantMass P φ G) : ∑ p : P, smoothGiantPrior P φ G p = 1 := by
  have hs : (∑ p : P, φ (Real.log p - G) / (p : ℝ)) = smoothGiantMass P φ G := by
    simpa only [finite_univ_canonical, smoothGiantMass] using
      (Finset.sum_coe_sort P (fun p => φ (Real.log p - G) / (p : ℝ)))
  simp only [smoothGiantPrior, mul_div_assoc, ← Finset.mul_sum]
  rw [hs, smoothGiantLogNormalizer, Real.exp_neg, Real.exp_log hpos]
  exact inv_mul_cancel₀ hpos.ne'

/-- This is exactly `p μ_G(p) = exp(c_g) φ(log p - G)`, with the
normalizing constant computed from the finite original prime support. -/
theorem smoothGiantPrior_cancel_prime (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (φ : ℝ → ℝ) (G : ℝ) (p : P) :
    (p : ℝ) * smoothGiantPrior P φ G p =
      Real.exp (smoothGiantLogNormalizer P φ G) * φ (Real.log p - G) := by
  have hp : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hP p p.property).ne_zero
  unfold smoothGiantPrior
  field_simp

/-- Equation (7.12) with the actual normalized smooth prior. -/
theorem smoothGiantPrior_row_transfer {A : Type*} [Fintype A]
    (P I : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hPI : P ⊆ I)
    (φ : ℝ → ℝ) (G : ℝ) (hφ : ∀ x, 0 ≤ φ x)
    (hpos : 0 < smoothGiantMass P φ G)
    (μ : A → ℝ) (hμ : ∀ a, 0 ≤ μ a) (hμmass : ∑ a, μ a = 1)
    (U : A → ℕ)
    (row : ∀ a, (p : P) → Fin ((p : ℕ) * U a) → ℂ)
    (B : ∀ a p, Fin (p * U a) → ℂ)
    (hrow : ∀ a p, (∑ t, ‖row a p t‖ ^ 2) ≤ (p : ℕ) * (U a : ℝ)) :
    ‖∑ a, (μ a : ℂ) * ∑ p : P, (smoothGiantPrior P φ G p : ℂ) *
        ∑ t, row a p t * B a p t‖ ^ 2 ≤
      Real.exp (smoothGiantLogNormalizer P φ G) *
        ∑ a, μ a * (U a : ℝ) *
          ∑ p ∈ I, φ (Real.log p - G) * ∑ t, ‖B a p t‖ ^ 2 :=
  moving_prime_row_transfer P I hP hPI μ hμ hμmass
    (fun p => φ (Real.log p - G)) (fun _ _ => hφ _)
    (Real.exp (smoothGiantLogNormalizer P φ G)) (Real.exp_nonneg _)
    (smoothGiantPrior_mass P φ G hpos) U row B hrow

end Ostmann

end OAI
