import OAI.NumberTheory.CubicMoment.Estimates.DispersionAlgebra

namespace OAI

/-!
# Exact expansion of the dispersion variance

The two independent coefficient variables produce the mixed cubic character
in the lattice variable. This is the algebraic starting point for applying
Poisson summation, before separating cube and noncube frequencies.
-/

noncomputable section
open scoped BigOperators

namespace CubicFirstMoment

def dispersionAmplitude (β : Eisenstein → ℂ) (u : ℝ) (b : Eisenstein) : ℂ :=
  β b * normTwist u b * gauss b

/-- Pointwise second moment, with the character orientation fixed by the
conjugation in the definition of the row polynomial. -/
theorem dispersion_norm_sq_expansion (B : Finset Eisenstein) (β : Eisenstein → ℂ)
    (u : ℝ) (a : Eisenstein) :
    ((‖dispersionPolynomial B β u a‖ ^ 2 : ℝ) : ℂ) =
      ∑ b₁ ∈ B, ∑ b₂ ∈ B,
        dispersionAmplitude β u b₁ * star (dispersionAmplitude β u b₂) *
          mixedCubic b₂ b₁ a := by
  have h := Complex.mul_conj' (dispersionPolynomial B β u a)
  simp only [starRingEnd_apply] at h
  rw [Complex.ofReal_pow, ← h]
  simp only [dispersionPolynomial, star_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b₁ hb₁
  apply Finset.sum_congr rfl
  intro b₂ hb₂
  simp only [dispersionAmplitude, mixedCubic, star_mul, star_star]
  ring

/-- Weighted lattice second moment as a sum over pairs of coefficients.
The finite lattice support and weight are arbitrary, so smooth lattice
weights and localized cell weights both fit this identity. -/
theorem dispersion_variance_expansion (A B : Finset Eisenstein)
    (W β : Eisenstein → ℂ) (u : ℝ) :
    (∑ a ∈ A, W a * ((‖dispersionPolynomial B β u a‖ ^ 2 : ℝ) : ℂ)) =
      ∑ b₁ ∈ B, ∑ b₂ ∈ B,
        dispersionAmplitude β u b₁ * star (dispersionAmplitude β u b₂) *
          ∑ a ∈ A, W a * mixedCubic b₂ b₁ a := by
  simp_rw [dispersion_norm_sq_expansion, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b₁ hb₁
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b₂ hb₂
  apply Finset.sum_congr rfl
  intro a ha
  ring

end CubicFirstMoment

end

end OAI
