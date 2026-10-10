import OAI.NumberTheory.Ostmann.QuadraticCenter.DivisorFrequencyExpansion
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticArrayApproximation

namespace OAI

/-! # The positive Fourier expression is the actual arithmetic statistic -/

namespace Ostmann

open scoped BigOperators SchwartzMap

noncomputable def originalPositiveFourier (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (M N h₀ : ℕ) (θ R : ℝ) (Φ : 𝓢(ℝ, ℂ)) : ℂ :=
  ∑ U ∈ Q.powerset, quadraticSymbolCoefficient M U *
    primeDivisorFrequency Q hQ D U M N h₀ θ R Φ

theorem quadraticArrayStatistic_finset (S : Finset ℕ) (M : ℕ) (F : ℕ → ℂ) :
    quadraticArrayStatistic S M F =
      ∑ s ∈ S, (Real.sqrt (s : ℝ) : ℂ)⁻¹ * F s * (realJacobi s M : ℂ) := by
  unfold quadraticArrayStatistic
  rw [show (∑ s : S, rootNormalizedCoefficient F s * (realJacobi s.val M : ℂ)) =
    ∑ s ∈ S, rootNormalizedCoefficient F s * (realJacobi s M : ℂ) from
      Finset.sum_coe_sort S (fun s : ℕ => rootNormalizedCoefficient F s * (realJacobi s M : ℂ))]
  simp only [rootNormalizedCoefficient]

/-- This is the exact finite form of equation (src8). Its coefficients are
the same ones whose uniform moments satisfy the stated bounds. -/
theorem originalPositiveFourier_expansion (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (M N h₀ : ℕ) [NeZero M]
    (θ R H : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (hR : 0 < R) (hH : 0 ≤ H) (hN : 1 ≤ N)
    (hcut : H * R * Q.toList.prod ≤ N) (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    originalPositiveFourier Q hQ D M N h₀ θ R Φ =
      ∑ P ∈ M.divisors, (ArithmeticFunction.moebius P : ℂ) *
        quadraticArrayStatistic (squarefreeKernelSupport Q.toList.prod N) M
          (arithmeticQuadraticCoefficient Q hQ D Φ R P M h₀ θ) := by
  classical
  unfold originalPositiveFourier
  have he (U : Finset ℕ) (hU : U ∈ Q.powerset) :=
    primeDivisorFrequency_expansion Q hQ D U (Finset.mem_powerset.mp hU)
      M N h₀ θ R H Φ hR hH hN hcut hΦ
  -- First replace each original density transform by its proved expansion.
  have hexpand :
      (∑ U ∈ Q.powerset, quadraticSymbolCoefficient M U * primeDivisorFrequency Q hQ D U M N h₀ θ R Φ) =
      ∑ U ∈ Q.powerset, quadraticSymbolCoefficient M U *
        (∑ P ∈ M.divisors, (ArithmeticFunction.moebius P : ℂ) *
          ∑ s ∈ squarefreeKernelSupport Q.toList.prod N,
            ((realJacobi s M : ℂ) * (Real.sqrt (s : ℝ) : ℂ)⁻¹) *
            ∑ V ∈ Q.powerset,
              ((realJacobi V.toList.prod M : ℂ) * (Real.sqrt (V.toList.prod : ℝ) : ℂ)⁻¹) *
              primeDivisorMultiples Q hQ D (divisorQuadraticScalar (quadraticInverseResidue M) V)
                (fun _ => (h₀ : ℝ) + θ) Φ R V.toList.prod P U s) := by
    apply Finset.sum_congr rfl
    intro U hU
    rw [he U hU]
  rw [hexpand]
  simp only [quadraticArrayStatistic_finset, arithmeticQuadraticCoefficient,
    fullQuadraticCoefficient, divisorWeightedCoefficient, quadraticDivisorSymbol,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro P hP
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro V hV
  apply Finset.sum_congr rfl
  intro U hU
  ring

end Ostmann

end OAI
