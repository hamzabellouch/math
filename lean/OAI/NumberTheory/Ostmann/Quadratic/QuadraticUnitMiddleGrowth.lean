import OAI.NumberTheory.Ostmann.Quadratic.QuadraticUnitCorrectionGrowth

namespace OAI

/-! # The normalized middle correction at the divisor-one boundary -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap

noncomputable def quadraticMiddleCorrectionUnit (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|)
    (M : ℝ) (e B N L : ℕ) (P : ℕ → Prop) (v w : ℕ → ℂ) : ℂ :=
  ∑ b ∈ oddSquarefreeRange (2 * B), if B ≤ b ∧ P b then
    (1 / (Real.sqrt b : ℂ)) * quadraticMiddleWindow ρ a ha M e N 1 v w b L else 0

theorem quadratic_middle_unit_growth (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|) :
    ∃ Cρ : ℝ, 0 ≤ Cρ ∧ ∀ C ε ξ M J : ℝ, 0 ≤ C →
      ∀ e B N L : ℕ, 0 < M → 0 < e → 0 < B → 0 < N → 1 ≤ J →
      quadraticCorrectionBase M N e B / (8 * J) ≤ 1 →
      ∀ P : ℕ → Prop, ∀ v w : ℕ → ℂ,
      (∀ n < N, v n = 0) → (∀ n < N, w n = 0) →
      QuadraticSieveBound (2 * B) (2 * N) (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N) 0) →
      ‖((Real.sqrt M / Real.sqrt e : ℝ) : ℂ) *
          quadraticMiddleCorrectionUnit ρ a ha M e B N L P v w‖ ≤
        128 * J * (2 * L + 1) * Cρ * quadraticCorrectionGrowthScale C ε ξ M e B N v w := by
  classical
  obtain ⟨Cρ, hCρ, hcρ⟩ := quadratic_unit_middle_window_bound ρ a ha
  refine ⟨Cρ, hCρ, ?_⟩
  intro C ε ξ M J hC e B N L hM he hB hN hJ hcut P v w hv hw hmat
  let T := quadraticGrowthDivisorBudget C ε ξ (2 * B) (2 * N) 1 v w
  let K := quadraticGrowthCutoff C ε ξ (2 * B) (2 * N) 0
  have hK : 0 ≤ K := quadratic_growth_cutoff_nonneg hC _ _ _
  have hroot := quadratic_growth_unit_cost (ε := ε) (ξ := ξ) hC (2 * B) (2 * N) v w
  have hl : ‖quadraticMiddleCorrectionUnit ρ a ha M e B N L P v w‖ ≤
      ((2 * L + 1) * Cρ * T) / Real.sqrt B := by
    have hf := quadratic_filtered_unit_root_weight B 1 hB (by decide) P
      (fun b => quadraticMiddleWindow ρ a ha M e N 1 v w b L)
    have hu := (hcρ M e (2 * B) N hM he hN L v w K K hK hK hv hw hmat hmat).trans
      (mul_le_mul_of_nonneg_left hroot (show 0 ≤ (2 * L + 1 : ℝ) * Cρ by positivity))
    have hf' : ‖quadraticMiddleCorrectionUnit ρ a ha M e B N L P v w‖ ≤
        (1 / Real.sqrt B) * ∑ b ∈ oddSquarefreeRange (2 * B),
          ‖quadraticMiddleWindow ρ a ha M e N 1 v w b L‖ := by
      simpa [quadraticMiddleCorrectionUnit] using hf
    exact hf'.trans (by simpa [T, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_of_nonneg_left hu (show 0 ≤ 1 / Real.sqrt (B : ℝ) by positivity))
  have hb := quadratic_first_high_budget hM (show (0 : ℝ) < N by exact_mod_cast hN)
    he hB (show 0 < (1 : ℕ) by decide) hJ
    (show 0 ≤ C * (((2 * B : ℕ) : ℝ) * (2 * N : ℕ)) ^ ε by positivity)
    (show 0 ≤ ((2 * B : ℕ) : ℝ) ^ ξ by positivity)
    (show 0 ≤ Real.sqrt (quadraticDivisorMoment (2 * N) v) *
      Real.sqrt (quadraticDivisorMoment (2 * N) w) by positivity) (by simpa using hcut)
  have hb' : (Real.sqrt M / (Real.sqrt e * Real.sqrt B)) * T ≤
      128 * J * quadraticCorrectionGrowthScale C ε ξ M e B N v w := by
    simpa only [T, quadraticGrowthDivisorBudget, quadraticCorrectionGrowthScale,
      Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, mul_one, mul_assoc] using hb
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  apply (mul_le_mul_of_nonneg_left hl (by positivity)).trans
  calc
    _ = ((2 * L + 1) * Cρ) * (Real.sqrt M / (Real.sqrt e * Real.sqrt B) * T) := by ring
    _ ≤ ((2 * L + 1) * Cρ) * (128 * J * quadraticCorrectionGrowthScale C ε ξ M e B N v w) :=
      mul_le_mul_of_nonneg_left hb' (by positivity)
    _ = _ := by ring

end Ostmann

end OAI
