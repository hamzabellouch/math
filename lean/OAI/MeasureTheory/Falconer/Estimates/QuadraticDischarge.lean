import OAI.MeasureTheory.Falconer.Estimates.QuadraticCoefficients
import OAI.MeasureTheory.Falconer.Fourier.CompactFourierBound

namespace OAI

/-! Discharge of the fixed negative-quadratic stationary-phase input. -/

namespace Falconer
open Set MeasureTheory
open scoped FourierTransform SchwartzMap

theorem quadratic_stationary_schwartz (n K : ℕ) (hn : 0 < n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (φ : 𝓢(Space n, ℂ)),
      tsupport φ ⊆ Metric.closedBall (0 : Space n) 1 →
      ∀ B : ℝ, 0 ≤ B →
      (∀ j ≤ 2*(K+1)+n+1, ∀ x, ‖iteratedFDeriv ℝ j φ x‖ ≤ B) →
      ∀ Λ : ℝ, 1 ≤ Λ →
        ‖((Λ^((n : ℝ)/2) : ℝ) : ℂ) *
          (∫ x : Space n, Complex.exp (-(Complex.I*(Λ : ℂ)/2)*(‖x‖^2 : ℝ)) * φ x) -
          ∑ j ∈ Finset.range (K+1), ((Λ^(-(j : ℝ)) : ℝ) : ℂ) * quadraticJetCoefficient j φ‖ ≤
            C * Λ^(-((K+1 : ℕ) : ℝ)) * B := by
  obtain ⟨M, hM, hm⟩ := compact_inverse_fourier_moment_bound n (2*(K+1))
  let A := (2*Real.pi)^((n : ℝ)/2)
  let D := (2*Real.pi^2)^(K+1)/(K.factorial : ℝ)
  refine ⟨A*D*M, by dsimp [A, D]; positivity, ?_⟩
  intro φ hs B hB hd Λ hΛ
  have hΛ0 : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  have hβ : 0 ≤ 2*Real.pi^2/Λ := by positivity
  have hmoment := hm φ hs B hB hd
  have ht := radial_taylor_integral_bound (𝓕⁻ φ) K hβ
  have he : ‖((Λ^((n : ℝ)/2) : ℝ) : ℂ) *
        (∫ x : Space n, Complex.exp (-(Complex.I*(Λ : ℂ)/2)*(‖x‖^2 : ℝ)) * φ x) -
        ∑ j ∈ Finset.range (K+1), ((Λ^(-(j : ℝ)) : ℝ) : ℂ) * quadraticJetCoefficient j φ‖ =
      A * ‖(∫ x : Space n, PlanarFalconer.imaginaryExponential
          ((2*Real.pi^2/Λ)*‖x‖^2)*𝓕⁻ φ x) -
        (∫ x : Space n, PlanarFalconer.imaginaryTaylor K
          ((2*Real.pi^2/Λ)*‖x‖^2)*𝓕⁻ φ x)‖ := by
    rw [normalized_gaussian_identity hn hΛ0 φ, ← normalized_quadratic_taylor φ K hΛ0,
      ← mul_sub, norm_mul, norm_sphereStationaryConstant]
  rw [he]
  calc
    _ ≤ A * (((2*Real.pi^2/Λ)^(K+1)/(K.factorial : ℝ)) *
        ∫ x : Space n, ‖x‖^(2*(K+1))*‖𝓕⁻ φ x‖) :=
      mul_le_mul_of_nonneg_left ht (by dsimp [A]; positivity)
    _ ≤ A * (((2*Real.pi^2/Λ)^(K+1)/(K.factorial : ℝ)) * (M*B)) := by
      gcongr
    _ = (A*D*M) * Λ^(-((K+1 : ℕ) : ℝ)) * B := by
      rw [Real.rpow_neg hΛ0.le, Real.rpow_natCast, div_pow]
      dsimp [D]
      ring

theorem published_quadratic_stationary : PublishedQuadraticStationary := by
  intro n J hn hJ
  cases J with
  | zero => omega
  | succ K =>
    obtain ⟨C, hC, hc⟩ := quadratic_stationary_schwartz n K (by omega)
    refine ⟨C, hC, ?_⟩
    intro a ha hs B hB hd Λ hΛ
    have hsupp : HasCompactSupport a :=
      (isCompact_closedBall (0 : Space n) 1).of_isClosed_subset isClosed_closure hs
    let φ : 𝓢(Space n, ℂ) := hsupp.toSchwartzMap ha
    exact hc φ hs B hB hd Λ hΛ

end Falconer

end OAI
