import OAI.MeasureTheory.Falconer.Angular.SphereModel
import OAI.MeasureTheory.Falconer.Fourier.StationaryInverse
import Mathlib.Analysis.InnerProductSpace.Laplacian

namespace OAI

/-!
# The fixed negative-quadratic stationary-phase input

Maciej Zworski, *Semiclassical Analysis*, AMS Graduate Studies in Mathematics
138 (2012), Theorem 3.13, equation (3.5.3), and the remainder estimate in its
proof (printed pp. 54–55):
https://math.jhu.edu/~lindblad/633/Zworski_final.pdf

This is only the specialization `Q = -I`, `h = 1 / Λ`, in dimension
`n = d - 1 ≥ 2`, for amplitudes supported in the fixed closed unit ball.
The Fourier convention in the cited formula is `exp (-i ⟨x, ξ⟩)`, with
`D = (1/i) ∂`. Consequently `⟨Q⁻¹ D, D⟩` is the ordinary Laplacian
`∑ ∂ᵢ²`, and the coefficient is `Δʲ / ((2i)ʲ j!)`. The Gaussian factor is
`(2π)^(n/2) exp (-iπn/4)`, already defined as `sphereStationaryConstant`.

The source controls the remainder by derivatives through order `2J+n+1`.
An operator-norm bound for the iterated Fréchet derivatives bounds each
coordinate derivative; its dimensional constants are absorbed into `C`.
No spherical stationary-phase statement is assumed here.
-/

namespace Falconer
open Set MeasureTheory
open scoped BigOperators ContDiff

/-- Actual Euclidean iterated Laplacian, with the ordinary positive-second-
derivative sign convention. -/
noncomputable def quadraticJetCoefficient {n : ℕ} (j : ℕ) (a : Space n → ℂ) : ℂ :=
  sphereStationaryConstant n / ((2 * Complex.I)^j * (j.factorial : ℂ)) *
    ((Laplacian.laplacian : (Space n → ℂ) → (Space n → ℂ))^[j] a) 0

@[simp] theorem quadraticJetCoefficient_zero {n : ℕ} (a : Space n → ℂ) :
    quadraticJetCoefficient 0 a = sphereStationaryConstant n * a 0 := by
  simp [quadraticJetCoefficient]

/-- The fixed-quadratic stationary-phase hypothesis, uniform over
amplitudes and frequencies. -/
def PublishedQuadraticStationary : Prop :=
  ∀ (n J : ℕ), 2 ≤ n → 1 ≤ J → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (a : Space n → ℂ), ContDiff ℝ ∞ a →
      tsupport a ⊆ Metric.closedBall (0 : Space n) 1 →
      ∀ B : ℝ, 0 ≤ B →
        (∀ k ≤ 2*J+n+1, ∀ x, ‖iteratedFDeriv ℝ k a x‖ ≤ B) →
        ∀ Λ : ℝ, 1 ≤ Λ →
          ‖((Λ ^ ((n : ℝ)/2) : ℝ) : ℂ) *
              (∫ x : Space n, Complex.exp (-(Complex.I*(Λ : ℂ)/2)*
                (‖x‖^2 : ℝ)) * a x) -
            ∑ j ∈ Finset.range J,
              ((Λ ^ (-(j : ℝ)) : ℝ) : ℂ) * quadraticJetCoefficient j a‖ ≤
            C * Λ ^ (-(J : ℝ)) * B

theorem quadratic_stationary_remainder
    (hpublished : PublishedQuadraticStationary) (n J : ℕ)
    (hn : 2 ≤ n) (hJ : 1 ≤ J) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : Space n → ℂ), ContDiff ℝ ∞ a →
      tsupport a ⊆ Metric.closedBall (0 : Space n) 1 →
      ∀ B : ℝ, 0 ≤ B →
        (∀ k ≤ 2*J+n+1, ∀ x, ‖iteratedFDeriv ℝ k a x‖ ≤ B) →
        ∀ Λ : ℝ, 1 ≤ Λ → ∃ E : ℂ,
          ((Λ ^ ((n : ℝ)/2) : ℝ) : ℂ) *
              (∫ x : Space n, Complex.exp (-(Complex.I*(Λ : ℂ)/2)*
                (‖x‖^2 : ℝ)) * a x) =
            (∑ j ∈ Finset.range J,
              ((Λ ^ (-(j : ℝ)) : ℝ) : ℂ) * quadraticJetCoefficient j a) + E ∧
          ‖E‖ ≤ C * Λ ^ (-(J : ℝ)) * B := by
  obtain ⟨C, hC, hrem⟩ := hpublished n J hn hJ
  refine ⟨C, hC, ?_⟩
  intro a ha hs B hB hder Λ hΛ
  refine ⟨_, ?_, hrem a ha hs B hB hder Λ hΛ⟩
  ring

end Falconer

end OAI
