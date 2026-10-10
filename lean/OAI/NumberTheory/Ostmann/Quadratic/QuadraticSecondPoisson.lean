import OAI.NumberTheory.Ostmann.Quadratic.QuadraticPositiveCoprime
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticFresnelMain

namespace OAI

/-! # The second Poisson formula for the actual quadratic Fourier test -/

namespace Ostmann

open MeasureTheory Set
open scoped Classical BigOperators SchwartzMap FourierTransform

theorem quadraticFourierSquare_fourier_zero (ρ : 𝓢(ℝ, ℂ)) (a : ℝ)
    (ha : 1 ≤ |a|) (hρ : ∀ t < 1 / 2, ρ t = 0) :
    𝓕 (quadraticFourierSquare ρ a ha) 0 =
      (quadraticFresnelPhase a / (Real.sqrt |a| : ℂ)) *
        ∫ x in Ioi (0 : ℝ), ρ (x ^ 2) := by
  rw [quadratic_fourier_phase_integral]
  simpa only [mul_zero, neg_zero, realAdditivePhase_zero, one_mul,
    quadraticFourierSquare_apply] using quadratic_fresnel_main ρ a ha hρ

noncomputable def quadraticSecondPoissonCore (q : ℕ) (ρ : 𝓢(ℝ, ℂ))
    (a : ℝ) (ha : 1 ≤ |a|) (X U V : ℝ) (L : ℕ) : ℂ :=
  ((((X : ℂ) * q.totient / q) *
      ((quadraticFresnelPhase a / (Real.sqrt |a| : ℂ)) *
        ∫ x in Ioi (0 : ℝ), ρ (x ^ 2))) -
    𝓕 ρ 0 * (∑ d ∈ q.divisors.filter (fun d : ℕ => (d : ℝ) ≤ V),
      (ArithmeticFunction.moebius d : ℂ)) -
    ((quadraticFresnelPhase a / (Real.sqrt |a| : ℂ)) *
      ∫ x in Ioi (0 : ℝ), ρ (x ^ 2)) *
        (∑ d ∈ q.divisors.filter (fun d : ℕ => V < (d : ℝ)),
          (ArithmeticFunction.moebius d : ℂ) * ((X / d : ℝ) : ℂ)) +
    ∑ d ∈ q.divisors.filter (fun d : ℕ => U < (d : ℝ) ∧ (d : ℝ) ≤ V),
      (ArithmeticFunction.moebius d : ℂ) * ((X / d : ℝ) : ℂ) *
        quadraticLatticeWindow (𝓕 (quadraticFourierSquare ρ a ha)) (X / d) L) / 2

theorem quadraticSecondPoissonCore_eq (q : ℕ) (ρ : 𝓢(ℝ, ℂ))
    (a : ℝ) (ha : 1 ≤ |a|) (hρ : ∀ t < 1 / 2, ρ t = 0)
    (X U V : ℝ) (L : ℕ) :
    quadraticSecondPoissonCore q ρ a ha X U V L =
      quadraticPoissonCore q (quadraticFourierSquare ρ a ha) X U V L / 2 := by
  unfold quadraticSecondPoissonCore quadraticPoissonCore
  rw [quadraticFourierSquare_fourier_zero ρ a ha hρ, quadraticFourierSquare_apply]
  simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero]

theorem quadratic_second_poisson (ρ : 𝓢(ℝ, ℂ)) (a : ℝ)
    (ha : 1 ≤ |a|) (hρ : ∀ t < 1 / 2, ρ t = 0) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, [NeZero q] → q ≠ 1 →
      ∀ X U V J : ℝ, 0 < X → 0 < U → 0 < V → 1 ≤ J →
      U * J ≤ X → X * J ≤ V → ∀ L : ℕ, (V / X) ^ 2 ≤ (L : ℝ) + 1 →
      ‖(∑' n : ℕ+, (1 : DirichletCharacter ℂ q) (n : ZMod q) *
        𝓕 ρ (a * ((n : ℝ) / X) ^ 2)) -
          quadraticSecondPoissonCore q ρ a ha X U V L‖ ≤ C * X / J ^ A := by
  obtain ⟨C, hC, hc⟩ := quadratic_uniform_positive_poisson
    (quadraticFourierSquare ρ a ha) (quadraticFourierSquare_even ρ a ha) A
  refine ⟨C, hC, ?_⟩
  intro q _ hq X U V J hX hU hV hJ hUJ hJV L hL
  simpa only [quadraticSecondPoissonCore_eq q ρ a ha hρ X U V L,
    quadraticFourierSquare_apply] using hc q hq X U V J hX hU hV hJ hUJ hJV L hL

end Ostmann

end OAI
