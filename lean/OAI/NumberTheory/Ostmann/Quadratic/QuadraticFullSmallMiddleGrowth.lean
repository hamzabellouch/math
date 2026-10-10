import OAI.NumberTheory.Ostmann.Quadratic.QuadraticOriginalMiddleGrowth
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticFrequencyGrowth
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticFrequencyAggregation

namespace OAI

/-! # The entire original small-kernel middle correction at the current sieve exponent -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap FourierTransform

noncomputable def quadraticFullSmallMiddleCorrection (ρ : 𝓢(ℝ, ℂ)) (M J : ℝ) (E N Q K L : ℕ)
    (R : ℕ → ℕ → Prop) (v w : ℕ → ℂ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 Q, ∑ b ∈ oddSquarefreeRange K,
    if R d b ∧ quadraticSecondLower (quadraticSmallScale M b) J < (E * d : ℕ) ∧
        (E * d : ℕ) ≤ quadraticSecondUpper (quadraticSmallScale M b) J then
      ((((ArithmeticFunction.moebius (E * d) : ℂ) / (E * d : ℕ)) / (Real.sqrt b : ℂ)) *
        quadraticLatticeWindow (𝓕 (quadraticSmallSquareTest ρ)) (quadraticSmallScale M b / (E * d : ℕ)) L) * quadraticDivisorBilinear (2 * N) (2 * N) d
        v w b else 0

theorem quadratic_full_small_middle_growth (ρ : 𝓢(ℝ, ℂ)) {C ε ξ M J : ℝ} (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hξ : 1 / 2 ≤ ξ) (hξ' : ξ ≤ 2) {E N Q K L : ℕ}
    (hM : 0 < M) (hE : 1 ≤ E)
    (hN : 0 < N) (hQ : 1 ≤ Q) (hK : 0 < K) (hJ : 1 ≤ J)
    (R : ℕ → ℕ → Prop) (v w : ℕ → ℂ)
    (hmat : ∀ B : ℕ, 0 < B → B ≤ K → ∀ i ≤ Nat.log 2 (2 * N),
      QuadraticSieveBound (2 * B) (2 * N / 2 ^ i)
        (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N) i)) :
    ‖(Real.sqrt M : ℂ) * quadraticFullSmallMiddleCorrection ρ M J E N Q K L R v w‖ ≤
      ((Nat.log 2 K + 1 : ℕ) : ℝ) * (((Nat.log 2 Q + 2 : ℕ) : ℝ) *
        (16 * (2 * L + 1) * quadraticSmallFourierBound ρ * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 *
          (4 * C * (4 * (K : ℝ) * N) ^ ε *
            (Real.sqrt M * (K : ℝ) ^ (ξ - 1 / 2) + (8 * E * J) * N) *
              (Real.sqrt (quadraticDivisorMoment (2 * N) v) *
                Real.sqrt (quadraticDivisorMoment (2 * N) w))))) := by
  classical
  have hρ := quadraticSmallFourierBound_nonneg ρ
  apply quadratic_correction_frequency_bound
  intro i hi
  let B := 2 ^ i
  have hB : 0 < B := by dsimp [B]; positivity
  have hBK : B ≤ K := quadratic_frequency_block_le hK hi
  let R' := fun d b => b ≤ K ∧ b < 2 * B ∧ R d b
  have heq : (∑ d ∈ Finset.Icc 1 Q, ∑ b ∈ oddSquarefreeRange (2 * B),
      if B ≤ b ∧ b ≤ K ∧ b < 2 * B then
        (if R d b ∧ quadraticSecondLower (quadraticSmallScale M b) J < (E * d : ℕ) ∧
        (E * d : ℕ) ≤ quadraticSecondUpper (quadraticSmallScale M b) J then
          ((((ArithmeticFunction.moebius (E * d) : ℂ) / (E * d : ℕ)) / (Real.sqrt b : ℂ)) *
        quadraticLatticeWindow (𝓕 (quadraticSmallSquareTest ρ)) (quadraticSmallScale M b / (E * d : ℕ)) L) * quadraticDivisorBilinear (2 * N) (2 * N) d
            v w b else 0) else 0) =
      quadraticSmallMiddleTotal ρ M E B N Q L
        (fun d b => R' d b ∧ quadraticSecondLower (quadraticSmallScale M b) J < (E * d : ℕ) ∧
          (E * d : ℕ) ≤ quadraticSecondUpper (quadraticSmallScale M b) J) v w := by
    unfold quadraticSmallMiddleTotal
    apply Finset.sum_congr rfl
    intro d _
    apply Finset.sum_congr rfl
    intro b _
    dsimp [R']
    by_cases h₁ : B ≤ b <;> by_cases h₂ : b ≤ K <;> by_cases h₃ : b < 2 * B <;>
      simp [h₁, h₂, h₃]
  change ‖(Real.sqrt M : ℂ) * _‖ ≤ _
  rw [heq]
  apply (quadratic_whole_original_small_middle_growth ρ hC hM hE hB hN hQ hJ R' v w
    (hmat B hB hBK)).trans
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
    (quadratic_small_growth_uniform hC hε hξ hξ' hM.le (by positivity) hB hBK le_rfl v w)
      (show 0 ≤ 16 * (2 * L + 1) * quadraticSmallFourierBound ρ * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 by positivity))
        (Nat.cast_nonneg _)

end Ostmann

end OAI
