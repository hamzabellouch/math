import OAI.NumberTheory.Ostmann.Quadratic.QuadraticOriginalMiddleGrowth
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticFrequencyGrowth
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticFrequencyAggregation

namespace OAI

/-! # The entire original middle correction at the current sieve exponent -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap

noncomputable def quadraticFullMiddleCorrection (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|)
    (M H J : ℝ) (e N Q K L : ℕ)
    (R : ℕ → ℕ → Prop) (v w : ℕ → ℂ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 Q, ∑ b ∈ oddSquarefreeRange K,
    if R d b ∧ quadraticSecondLower (quadraticCorrectionBase M H e b) J < (d : ℝ) ∧
        (d : ℝ) ≤ quadraticSecondUpper (quadraticCorrectionBase M H e b) J then
      (((ArithmeticFunction.moebius d : ℂ) / d) / (Real.sqrt b : ℂ)) *
        quadraticMiddleWindow ρ a ha M e N d v w b L else 0

theorem quadratic_full_middle_growth (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|) :
    ∃ Cu Cb : ℝ, 0 ≤ Cu ∧ 0 ≤ Cb ∧ ∀ C ε ξ M H J : ℝ,
      0 ≤ C → 0 ≤ ε → 1 / 2 ≤ ξ → ξ ≤ 2 → ∀ e N Q K L : ℕ,
      0 < M → 0 < H → (N : ℝ) ≤ 2 * H → 0 < e →
      0 < N → 1 ≤ Q → 0 < K → 1 ≤ J →
      ∀ R : ℕ → ℕ → Prop, ∀ v w : ℕ → ℂ,
      (∀ n < N, v n = 0) → (∀ n < N, w n = 0) →
      (∀ B : ℕ, 0 < B → B ≤ K → ∀ i ≤ Nat.log 2 (2 * N),
        QuadraticSieveBound (2 * B) (2 * N / 2 ^ i)
          (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N) i)) →
      ‖((Real.sqrt M / Real.sqrt e : ℝ) : ℂ) *
          quadraticFullMiddleCorrection ρ a ha M H J e N Q K L R v w‖ ≤
        ((Nat.log 2 K + 1 : ℕ) : ℝ) *
          ((128 * (2 * J) * (2 * L + 1) * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 *
            (10 * C * (4 * (K : ℝ) * N) ^ ε *
              (M + Real.sqrt M * (K : ℝ) ^ (ξ - 1 / 2)) *
                (Real.sqrt (quadraticDivisorMoment (2 * N) v) *
                  Real.sqrt (quadraticDivisorMoment (2 * N) w)))) *
                    (Cu + ((Nat.log 2 Q + 1 : ℕ) : ℝ) * Cb)) := by
  classical
  obtain ⟨Cu, Cb, hCu, hCb, hc⟩ := quadratic_whole_original_middle_growth ρ a ha
  refine ⟨Cu, Cb, hCu, hCb, ?_⟩
  intro C ε ξ M H J hC hε hξ hξ' e N Q K L hM hH hNH he hN hQ hK hJ R v w hv hw hmat
  apply quadratic_correction_frequency_bound
  intro i hi
  let B := 2 ^ i
  have hB : 0 < B := by dsimp [B]; positivity
  have hBK : B ≤ K := quadratic_frequency_block_le hK hi
  let R' := fun d b => b ≤ K ∧ b < 2 * B ∧ R d b
  have heq : (∑ d ∈ Finset.Icc 1 Q, ∑ b ∈ oddSquarefreeRange (2 * B),
      if B ≤ b ∧ b ≤ K ∧ b < 2 * B then
        (if R d b ∧ quadraticSecondLower (quadraticCorrectionBase M H e b) J < (d : ℝ) ∧
        (d : ℝ) ≤ quadraticSecondUpper (quadraticCorrectionBase M H e b) J then
          (((ArithmeticFunction.moebius d : ℂ) / d) / (Real.sqrt b : ℂ)) *
            quadraticMiddleWindow ρ a ha M e N d v w b L else 0) else 0) =
      quadraticMiddleCorrectionTotal ρ a ha M e B N Q L
        (fun d b => R' d b ∧ quadraticSecondLower (quadraticCorrectionBase M H e b) J < (d : ℝ) ∧
          (d : ℝ) ≤ quadraticSecondUpper (quadraticCorrectionBase M H e b) J) v w := by
    unfold quadraticMiddleCorrectionTotal
    apply Finset.sum_congr rfl
    intro d _
    apply Finset.sum_congr rfl
    intro b _
    dsimp [R']
    by_cases h₁ : B ≤ b <;> by_cases h₂ : b ≤ K <;> by_cases h₃ : b < 2 * B <;>
      simp [h₁, h₂, h₃]
  change ‖((Real.sqrt M / Real.sqrt e : ℝ) : ℂ) * _‖ ≤ _
  rw [heq]
  apply (hc C ε ξ M H J hC e B N Q L hM hH hNH he hB hN hQ hJ R' v w hv hw
    (hmat B hB hBK)).trans
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (quadratic_correction_growth_uniform hC hε hξ hξ' hM he hB hBK le_rfl v w)
      (show 0 ≤ 128 * (2 * J) * (2 * L + 1) * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 by positivity))
        (by positivity)

end Ostmann

end OAI
