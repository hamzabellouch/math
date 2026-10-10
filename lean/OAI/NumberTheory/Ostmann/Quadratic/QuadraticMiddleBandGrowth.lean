import OAI.NumberTheory.Ostmann.Quadratic.QuadraticHighBandGrowth

namespace OAI

/-! # The original middle-divisor correction at the current sieve exponent -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap

noncomputable def quadraticMiddleCorrectionBand (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|)
    (M : ℝ) (e B N D L : ℕ) (P : ℕ → ℕ → Prop) (v w : ℕ → ℂ) : ℂ :=
  ∑ d ∈ Finset.Ioc D (2 * D), ∑ b ∈ oddSquarefreeRange (2 * B),
    if B ≤ b ∧ P d b then
      (((ArithmeticFunction.moebius d : ℂ) / d) / (Real.sqrt b : ℂ)) *
        quadraticMiddleWindow ρ a ha M e N d v w b L else 0

theorem quadratic_middle_band_growth (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|) :
    ∃ Cρ : ℝ, 0 ≤ Cρ ∧ ∀ C ε ξ M J : ℝ, 0 ≤ C →
      ∀ e B N D L : ℕ, 0 < M → 0 < e → 0 < B → 0 < N → 0 < D → 1 ≤ J →
      quadraticCorrectionBase M N e B / (8 * J) ≤ (D : ℝ) →
      ∀ P : ℕ → ℕ → Prop, ∀ v w : ℕ → ℂ,
      (∀ n < N, v n = 0) → (∀ n < N, w n = 0) →
      (∀ i ≤ Nat.log 2 (2 * N), QuadraticSieveBound (2 * B) (2 * N / 2 ^ i)
        (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N) i)) →
      ‖((Real.sqrt M / Real.sqrt e : ℝ) : ℂ) *
          quadraticMiddleCorrectionBand ρ a ha M e B N D L P v w‖ ≤
        128 * J * (2 * L + 1) * Cρ * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 *
          quadraticCorrectionGrowthScale C ε ξ M e B N v w := by
  classical
  obtain ⟨Cρ, hCρ, hcρ⟩ := quadratic_variable_middle_band_bound ρ a ha
  refine ⟨Cρ, hCρ, ?_⟩
  intro C ε ξ M J hC e B N D L hM he hB hN hD hJ hcut P v w hv hw hmat
  let T := quadraticGrowthDivisorBudget C ε ξ (2 * B) (2 * N) D v w
  have hT : 0 ≤ T := quadratic_growth_divisor_budget_nonneg hC _ _ _ _ _
  have hl := hcρ M e B N D hM he hB hN hD L P v w
    (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N))
    (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N)) T hT hv hw
    (fun i _ => quadratic_growth_cutoff_nonneg hC _ _ i)
    (fun i _ => quadratic_growth_cutoff_nonneg hC _ _ i) hmat hmat
    (fun _ _ _ _ _ hp => quadratic_growth_cutoff_cost hC hD v w hp)
  change ‖quadraticMiddleCorrectionBand ρ a ha M e B N D L P v w‖ ≤ _ at hl
  have hb := quadratic_first_high_budget hM (show (0 : ℝ) < N by exact_mod_cast hN)
    he hB hD hJ
    (show 0 ≤ C * (((2 * B : ℕ) : ℝ) * (2 * N : ℕ)) ^ ε by positivity)
    (show 0 ≤ ((2 * B : ℕ) : ℝ) ^ ξ by positivity)
    (show 0 ≤ Real.sqrt (quadraticDivisorMoment (2 * N) v) *
      Real.sqrt (quadraticDivisorMoment (2 * N) w) by positivity) hcut
  have hb' : (Real.sqrt M / (Real.sqrt e * Real.sqrt B * D)) * T ≤
      128 * J * quadraticCorrectionGrowthScale C ε ξ M e B N v w := by
    simpa only [T, quadraticGrowthDivisorBudget, quadraticCorrectionGrowthScale,
      Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using hb
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  apply (mul_le_mul_of_nonneg_left hl (by positivity)).trans
  calc
    _ = ((2 * L + 1) * Cρ * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2) *
        (Real.sqrt M / (Real.sqrt e * Real.sqrt B * D) * T) := by ring
    _ ≤ ((2 * L + 1) * Cρ * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2) *
        (128 * J * quadraticCorrectionGrowthScale C ε ξ M e B N v w) :=
      mul_le_mul_of_nonneg_left hb' (by positivity)
    _ = _ := by ring

end Ostmann

end OAI
