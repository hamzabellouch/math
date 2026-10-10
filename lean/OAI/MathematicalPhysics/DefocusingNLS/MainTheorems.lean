import OAI.MathematicalPhysics.DefocusingNLS.Certificates.RectangleRouche
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.GaussianCounterexample

namespace OAI

/-! # Stable defocusing Schrödinger blowup

Theorem 1.1 and Corollary 1.2 of OpenAI, *Stable self-similar blowup for a
supercritical defocusing Schrödinger equation on the torus* (September 2026).
-/

open Set Filter Topology MeasureTheory
namespace DefocusingNLS

attribute [local irreducible] HasFiniteTimeSelfSimilarBlowup IsClassicalDefocusingFlow
  maximalSobolevInteractionDomain

/-- Theorem 1.1: arbitrarily large odd powers admit a nonempty open family of
classical solutions with finite-time self-similar blowup on the twelve-torus. -/
theorem stable_blowup (p₀ : ℕ) :
    ∃ p k : ℕ, p₀ ≤ p ∧ Odd p ∧ 3 ≤ p ∧ ∃ hk : 8 < (k : ℝ),
      ∃ U : Set FourierL2, U.Nonempty ∧ IsOpen U ∧ ∀ f ∈ U,
        IsClassicalDefocusingFlow k (by linarith) ((p - 1) / 2) f ∧
        HasFiniteTimeSelfSimilarBlowup k (by linarith) ((p - 1) / 2)
          (1 / ((p : ℝ) - 1)) f :=
  stable_blowup_conditional rectangle_rouche p₀

/-- Corollary 1.2: for every permitted Gaussian Fourier decay exponent,
the same open blowup family has positive Gaussian probability. -/
theorem gaussian_blowup (p₀ : ℕ) :
    ∃ p k : ℕ, p₀ ≤ p ∧ Odd p ∧ 3 ≤ p ∧ ∃ hk : 8 < (k : ℝ),
      ∃ U : Set FourierL2, U.Nonempty ∧ IsOpen U ∧
      (∀ f ∈ U, IsClassicalDefocusingFlow k (by linarith) ((p - 1) / 2) f ∧
        HasFiniteTimeSelfSimilarBlowup k (by linarith) ((p - 1) / 2)
          (1 / ((p : ℝ) - 1)) f) ∧
      ∀ α : ℝ, (k : ℝ) + 6 < α →
        (∀ᵐ g ∂fourierGaussianLaw, Memℓp (weightedGaussianCoefficient k α g) 2) ∧
        (∀ᵐ g ∂fourierGaussianLaw, ∀ n,
          sobolevFourierCoefficient k (weightedGaussianVector k α g) n =
            (1 + ‖n‖ ^ 2) ^ (-α / 2) • g n) ∧
        0 < weightedGaussianLaw k α U :=
  gaussian_blowup_conditional rectangle_rouche p₀

/-- In particular, Gaussian data are not almost surely globally continuable. -/
theorem gaussian_not_almost_sure_global (p₀ : ℕ) :
    ∃ p k : ℕ, p₀ ≤ p ∧ Odd p ∧ 3 ≤ p ∧ ∃ hk : 8 < (k : ℝ),
      ∀ α : ℝ, (k : ℝ) + 6 < α →
        ¬ ∀ᵐ f ∂weightedGaussianLaw k α,
          maximalSobolevInteractionDomain k (by linarith) ((p - 1) / 2) f = univ :=
  gaussian_not_almost_sure_global_conditional rectangle_rouche p₀

end DefocusingNLS

end OAI
