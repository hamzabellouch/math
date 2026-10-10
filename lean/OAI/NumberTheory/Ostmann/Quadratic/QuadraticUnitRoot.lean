import OAI.NumberTheory.Ostmann.Quadratic.QuadraticVaryingUnit
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticRootDivisor

namespace OAI

/-! # Uniform root-kernel estimates at divisor one -/

namespace Ostmann

open MeasureTheory
open scoped Classical BigOperators SchwartzMap FourierTransform

theorem quadratic_unit_positive_root_gauss_bound (ρ : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M N : ℕ) (X : ℕ → ℝ), 0 < N →
      (∀ m ∈ oddSquarefreeRange M, 0 < X m) →
      ∀ (v w : ℕ → ℂ) (K₁ K₂ : ℝ), 0 ≤ K₁ → 0 ≤ K₂ →
      (∀ n < N, v n = 0) → (∀ n < N, w n = 0) →
      QuadraticSieveBound M (2 * N) K₁ → QuadraticSieveBound M (2 * N) K₂ →
      (∑ m ∈ oddSquarefreeRange M, ‖quadraticRootGaussDivisor ρ (X m) N 1 v w m‖) ≤
        C * (Real.sqrt (2 * K₁ * quadraticDivisorMoment (2 * N) v) *
          Real.sqrt (2 * K₂ * quadraticDivisorMoment (2 * N) w)) := by
  obtain ⟨C, hC, hc⟩ := quadratic_log_root_kernel_envelope ρ 0
  let J := ∫ u : ℝ, quadraticFourierEnvelope u
  have hJ : 0 ≤ J := integral_nonneg quadraticFourierEnvelope_nonneg
  refine ⟨3 * C * J, by positivity, ?_⟩
  intro M N X hN hX v w K₁ K₂ hK₁ hK₂ hv hw h₁ h₂
  let f := fun m => quadraticLogRootKernel ρ (X m) N
  let ω := fun u : ℝ => C * quadraticFourierEnvelope u
  have hω : Integrable ω := quadraticFourierEnvelope_integrable.const_mul C
  have hω₀ : ∀ u, 0 ≤ ω u := fun u => mul_nonneg hC (quadraticFourierEnvelope_nonneg u)
  have hf : ∀ m ∈ oddSquarefreeRange M, ∀ u : ℝ, ‖𝓕 (f m) u‖ ≤ ω u := by
    intro m hm u
    simpa only [pow_zero, div_one, min_self, mul_one] using
      hc N hN (X m) (X m) (hX m hm) le_rfl u
  have hbound := quadratic_unit_varying_weighted_gauss_bound f ω hω hω₀
    M (2 * N) (2 * N) v w K₁ K₂ hK₁ hK₂ h₁ h₂ hf
  have he : (∑ m ∈ oddSquarefreeRange M,
      ‖quadraticRootGaussDivisor ρ (X m) N 1 v w m‖) =
      ∑ m ∈ oddSquarefreeRange M,
        ‖quadraticLogWeightedGaussDivisor (f m) (2 * N) (2 * N) 1 v w m‖ := by
    apply Finset.sum_congr rfl
    intro m _
    rw [quadratic_root_gauss_divisor_eq ρ (X m) hN 1 v w m hv hw]
  rw [he]
  convert hbound using 1
  dsimp only [ω, J]
  rw [integral_const_mul]
  ring

end Ostmann

end OAI
