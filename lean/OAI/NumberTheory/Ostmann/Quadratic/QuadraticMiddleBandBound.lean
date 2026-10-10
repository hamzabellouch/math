import OAI.NumberTheory.Ostmann.Quadratic.QuadraticCorrectionWeights

namespace OAI

/-! # The middle correction with its original reciprocal weights -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap

theorem quadratic_middle_weighted_band_bound (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : ℝ) (e B N D : ℕ), 0 < M → 0 < e → 0 < B → 0 < N → 0 < D →
      ∀ (L : ℕ) (U V : ℝ), ∀ (v w : ℕ → ℂ) (K₁ K₂ : ℕ → ℝ) (T : ℝ), 0 ≤ T →
      (∀ n < N, v n = 0) → (∀ n < N, w n = 0) →
      (∀ i ≤ Nat.log 2 (2 * N), 0 ≤ K₁ i) →
      (∀ j ≤ Nat.log 2 (2 * N), 0 ≤ K₂ j) →
      (∀ i ≤ Nat.log 2 (2 * N), QuadraticSieveBound (2 * B) (2 * N / 2 ^ i) (K₁ i)) →
      (∀ j ≤ Nat.log 2 (2 * N), QuadraticSieveBound (2 * B) (2 * N / 2 ^ j) (K₂ j)) →
      (∀ i ≤ Nat.log 2 (2 * N), ∀ j ≤ Nat.log 2 (2 * N),
        D < 4 * (2 ^ i * 2 ^ j) → 2 ^ i * 2 ^ j ≤ 2 * D →
        Real.sqrt (2 * K₁ i * (2 ^ i : ℕ) * quadraticDivisorMoment (2 * N) v) *
          Real.sqrt (2 * K₂ j * (2 ^ j : ℕ) * quadraticDivisorMoment (2 * N) w) ≤ T) →
      ‖∑ d ∈ (Finset.Ioc D (2 * D)).filter (fun d : ℕ => U < (d : ℝ) ∧ (d : ℝ) ≤ V),
        ∑ b ∈ (oddSquarefreeRange (2 * B)).filter (fun b => B ≤ b),
          (((ArithmeticFunction.moebius d : ℂ) / d) / (Real.sqrt b : ℂ)) *
            quadraticMiddleWindow ρ a ha M e N d v w b L‖ ≤
        ((2 * L + 1) * C * ((((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ)) ^ 2 * T)) /
          ((D : ℝ) * Real.sqrt B) := by
  obtain ⟨C, hC, hc⟩ := quadratic_middle_window_bound ρ a ha
  refine ⟨C, hC, ?_⟩
  intro M e B N D hM he hB hN hD L U V v w K₁ K₂ T hT hv hw hK₁ hK₂ h₁ h₂ hcost
  exact quadratic_middle_correction_band ρ a ha M e N L v w hD hB U V _
    (hc M e (2 * B) N D hM he hN L v w K₁ K₂ T hT hv hw hK₁ hK₂ h₁ h₂ hcost)

end Ostmann

end OAI
