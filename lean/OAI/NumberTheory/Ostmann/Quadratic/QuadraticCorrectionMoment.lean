import OAI.NumberTheory.Ostmann.Quadratic.QuadraticCorrectionEnvelope
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticGcdTwistMoment

namespace OAI

/-! # The correction envelope uses only the original coefficient energy -/

namespace Ostmann

noncomputable def quadraticCorrectionScalar (C ε ξ M J : ℝ) (N Q K L : ℕ) : ℝ :=
  (2 * L + 1) * J * ((Nat.log 2 K + 1 : ℕ) : ℝ) *
    ((Nat.log 2 Q + 2 : ℕ) : ℝ) * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 *
      (C * (4 * (K : ℝ) * N) ^ ε * (M + Real.sqrt M * (K : ℝ) ^ (ξ - 1 / 2)))

theorem quadraticCorrectionScalar_nonneg {C ε ξ M J : ℝ}
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hJ : 0 ≤ J) (N Q K L : ℕ) :
    0 ≤ quadraticCorrectionScalar C ε ξ M J N Q K L := by
  unfold quadraticCorrectionScalar
  positivity

theorem quadraticCorrectionEnvelope_diagonal (C ε ξ M J : ℝ) (N Q K L : ℕ) (v : ℕ → ℂ) :
    quadraticCorrectionEnvelope C ε ξ M J N Q K L v v =
      quadraticCorrectionScalar C ε ξ M J N Q K L * quadraticDivisorMoment (2 * N) v := by
  have hv : 0 ≤ quadraticDivisorMoment (2 * N) v := by
    unfold quadraticDivisorMoment
    positivity
  unfold quadraticCorrectionEnvelope quadraticCorrectionScalar
  rw [Real.mul_self_sqrt hv]
  ring

theorem quadratic_gcd_correction_moment {δ : ℝ} (hδ : 0 < δ) :
    ∃ A : ℝ, 0 < A ∧ ∀ C ε ξ M J : ℝ, 0 ≤ C → 0 ≤ M → 0 ≤ J →
      ∀ R D Q K L : ℕ, Squarefree D → Odd D → ∀ u : ℤ, ∀ v : ℕ → ℂ,
        quadraticCorrectionEnvelope C ε ξ M J (quadraticGcdBlockSize R D) Q K L
          (quadraticFrequencyTwist u 1 (quadraticGcdBlockCoeff R D v))
          (quadraticFrequencyTwist u 1 (quadraticGcdBlockCoeff R D v)) ≤
        quadraticCorrectionScalar C ε ξ M J (quadraticGcdBlockSize R D) Q K L *
          (A * (2 * (R : ℝ)) ^ δ * quadraticSieveEnergy (2 * R) v) := by
  obtain ⟨A, hA, hm⟩ := quadratic_gcd_twist_moment δ hδ
  refine ⟨A, hA, ?_⟩
  intro C ε ξ M J hC hM hJ R D Q K L hD ho u v
  rw [quadraticCorrectionEnvelope_diagonal]
  exact mul_le_mul_of_nonneg_left (hm R D hD ho u v)
    (quadraticCorrectionScalar_nonneg hC hM hJ _ _ _ _)

end Ostmann

end OAI
