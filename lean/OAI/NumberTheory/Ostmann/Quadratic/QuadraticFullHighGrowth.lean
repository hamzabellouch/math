import OAI.NumberTheory.Ostmann.Quadratic.QuadraticOriginalCutoffGrowth
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticFrequencyGrowth
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticFrequencyAggregation

namespace OAI

/-! # The entire original high correction at the current sieve exponent -/

namespace Ostmann

open scoped Classical BigOperators

noncomputable def quadraticFullHighCorrection (M H J : ℝ) (e N Q K : ℕ)
    (R : ℕ → ℕ → Prop) (v w : ℕ → ℂ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 Q, ∑ b ∈ oddSquarefreeRange K,
    if R d b ∧ quadraticSecondUpper (quadraticCorrectionBase M H e b) J < (d : ℝ) then
      (((ArithmeticFunction.moebius d : ℂ) / d) / (Real.sqrt b : ℂ)) * quadraticGaussDivisorBilinear (2 * N) (2 * N) d
        v w b else 0

theorem quadratic_full_high_growth {C ε ξ M H J : ℝ} (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hξ : 1 / 2 ≤ ξ) (hξ' : ξ ≤ 2) {e N Q K : ℕ}
    (hM : 0 < M) (hH : 0 < H) (hNH : (N : ℝ) ≤ 2 * H) (he : 0 < e)
    (hN : 0 < N) (hQ : 1 ≤ Q) (hK : 0 < K) (hJ : 1 ≤ J)
    (R : ℕ → ℕ → Prop) (v w : ℕ → ℂ)
    (hmat : ∀ B : ℕ, 0 < B → B ≤ K → ∀ i ≤ Nat.log 2 (2 * N),
      QuadraticSieveBound (2 * B) (2 * N / 2 ^ i)
        (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N) i)) :
    ‖((Real.sqrt M / Real.sqrt e : ℝ) : ℂ) * quadraticFullHighCorrection M H J e N Q K R v w‖ ≤
      ((Nat.log 2 K + 1 : ℕ) : ℝ) * (((Nat.log 2 Q + 2 : ℕ) : ℝ) *
        (384 * (2 * J) * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 *
          (10 * C * (4 * (K : ℝ) * N) ^ ε *
            (M + Real.sqrt M * (K : ℝ) ^ (ξ - 1 / 2)) *
              (Real.sqrt (quadraticDivisorMoment (2 * N) v) *
                Real.sqrt (quadraticDivisorMoment (2 * N) w))))) := by
  classical
  apply quadratic_correction_frequency_bound
  intro i hi
  let B := 2 ^ i
  have hB : 0 < B := by dsimp [B]; positivity
  have hBK : B ≤ K := quadratic_frequency_block_le hK hi
  let R' := fun d b => b ≤ K ∧ b < 2 * B ∧ R d b
  have heq : (∑ d ∈ Finset.Icc 1 Q, ∑ b ∈ oddSquarefreeRange (2 * B),
      if B ≤ b ∧ b ≤ K ∧ b < 2 * B then
        (if R d b ∧ quadraticSecondUpper (quadraticCorrectionBase M H e b) J < (d : ℝ) then
          (((ArithmeticFunction.moebius d : ℂ) / d) / (Real.sqrt b : ℂ)) * quadraticGaussDivisorBilinear (2 * N) (2 * N) d
            v w b else 0) else 0) =
      quadraticHighCorrectionTotal B N Q
        (fun d b => R' d b ∧ quadraticSecondUpper (quadraticCorrectionBase M H e b) J < (d : ℝ)) v w := by
    unfold quadraticHighCorrectionTotal
    apply Finset.sum_congr rfl
    intro d _
    apply Finset.sum_congr rfl
    intro b _
    dsimp [R']
    by_cases h₁ : B ≤ b <;> by_cases h₂ : b ≤ K <;> by_cases h₃ : b < 2 * B <;>
      simp [h₁, h₂, h₃]
  change ‖((Real.sqrt M / Real.sqrt e : ℝ) : ℂ) * _‖ ≤ _
  rw [heq]
  apply (quadratic_whole_original_high_growth hC hM hH hNH he hB hN hQ hJ R' v w
    (hmat B hB hBK)).trans
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
    (quadratic_correction_growth_uniform hC hε hξ hξ' hM he hB hBK le_rfl v w)
      (show 0 ≤ 384 * (2 * J) * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 by positivity))
        (Nat.cast_nonneg _)

theorem quadratic_full_high_of_growth {ξ : ℝ} (h : QuadraticSieveGrowth ξ)
    (hξ : 1 / 2 ≤ ξ) (hξ' : ξ ≤ 2) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M H J : ℝ, ∀ e N Q K : ℕ,
      0 < M → 0 < H → (N : ℝ) ≤ 2 * H → 0 < e → 0 < N → 1 ≤ Q → 0 < K → 1 ≤ J →
      ∀ R : ℕ → ℕ → Prop, ∀ v w : ℕ → ℂ,
      ‖((Real.sqrt M / Real.sqrt e : ℝ) : ℂ) * quadraticFullHighCorrection M H J e N Q K R v w‖ ≤
        ((Nat.log 2 K + 1 : ℕ) : ℝ) * (((Nat.log 2 Q + 2 : ℕ) : ℝ) *
          (384 * (2 * J) * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 *
            (10 * C * (4 * (K : ℝ) * N) ^ ε *
              (M + Real.sqrt M * (K : ℝ) ^ (ξ - 1 / 2)) *
                (Real.sqrt (quadraticDivisorMoment (2 * N) v) *
                  Real.sqrt (quadraticDivisorMoment (2 * N) w))))) := by
  obtain ⟨C, hC, hc⟩ := quadratic_growth_cutoff_bounds h hε
  refine ⟨C, hC, ?_⟩
  intro M H J e N Q K hM hH hNH he hN hQ hK hJ R v w
  apply quadratic_full_high_growth hC.le hε.le hξ hξ' hM hH hNH he hN hQ hK hJ R v w
  intro B hB _
  exact hc (2 * B) (2 * N) (by omega) (by omega)

end Ostmann

end OAI
