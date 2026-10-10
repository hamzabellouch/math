import OAI.NumberTheory.Ostmann.Quadratic.QuadraticCorrectionMoment
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticGcdSecondTotal

namespace OAI

/-! # The actual signed gcd term at the current quadratic-sieve exponent -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap

theorem quadraticCorrectionScalar_scale (C ε ξ M J : ℝ) (N Q K L : ℕ) :
    quadraticCorrectionScalar C ε ξ M J N Q K L =
      C * quadraticCorrectionScalar 1 ε ξ M J N Q K L := by
  unfold quadraticCorrectionScalar
  ring

theorem quadratic_gcd_second_growth {ξ ε δ : ℝ} (h : QuadraticSieveGrowth ξ)
    (hξ : 1 / 2 ≤ ξ) (hξ' : ξ ≤ 2) (hε : 0 < ε) (hδ : 0 < δ)
    (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|) :
    ∃ A : ℝ, 0 < A ∧ ∀ M J : ℝ, 0 < M → 1 ≤ J →
      ∀ R D e K : ℕ, 0 < R → Squarefree D → Odd D → D ≤ R → 0 < e → 0 < K →
      ∀ u : ℤ, ∀ v : ℕ → ℂ, (∀ n < R, v n = 0) →
        ‖quadraticGcdSecondTotal ρ a ha M ((R : ℝ) / D) J R D e K u v v‖ ≤
          A * quadraticCorrectionScalar 1 ε ξ M J (quadraticGcdBlockSize R D)
            ((2 * quadraticGcdBlockSize R D) ^ 2) K (quadraticSecondWindow J) *
              (2 * (R : ℝ)) ^ δ * quadraticSieveEnergy (2 * R) v := by
  obtain ⟨A₀, hA₀, hc⟩ := quadratic_second_combination_growth ρ a ha
  obtain ⟨C, hC, hmat⟩ := quadratic_growth_cutoff_bounds h hε
  obtain ⟨A₁, hA₁, hmom⟩ := quadratic_gcd_correction_moment hδ
  refine ⟨A₀ * C * A₁, by positivity, ?_⟩
  intro M J hM hJ R D e K hR hD ho hDR he hK u v hv
  have hD₀ : 0 < D := Nat.pos_of_ne_zero hD.ne_zero
  have hH : 0 < (R : ℝ) / D := div_pos (by exact_mod_cast hR) (by exact_mod_cast hD₀)
  have hN := quadraticGcdBlockSize_pos hR hD₀
  obtain ⟨hHN, hNH⟩ := quadraticGcdBlockSize_comparable hD₀ hDR
  have hs : ∀ n < quadraticGcdBlockSize R D,
      quadraticFrequencyTwist u 1 (quadraticGcdBlockCoeff R D v) n = 0 :=
    fun n hn => quadratic_gcd_twist_lower hD₀ u v hv hn
  have hQ : 1 ≤ (2 * quadraticGcdBlockSize R D) ^ 2 := by
    have : 1 ≤ quadraticGcdBlockSize R D := hN
    nlinarith
  have hb := hc C ε ξ M ((R : ℝ) / D) J hC.le hε.le hξ hξ' e
    (quadraticGcdBlockSize R D) ((2 * quadraticGcdBlockSize R D) ^ 2) K (quadraticSecondWindow J)
    hM hH hHN hNH he hN hQ hK hJ (fun _ _ => True)
    (quadraticFrequencyTwist u 1 (quadraticGcdBlockCoeff R D v))
    (quadraticFrequencyTwist u 1 (quadraticGcdBlockCoeff R D v)) hs hs
    (fun B hB _ => hmat (2 * B) (2 * quadraticGcdBlockSize R D) (by omega) (by omega))
  have hm := hmom C ε ξ M J hC.le hM.le (by linarith)
    R D ((2 * quadraticGcdBlockSize R D) ^ 2) K (quadraticSecondWindow J) hD ho u v
  calc
    _ ≤ A₀ * quadraticCorrectionEnvelope C ε ξ M J (quadraticGcdBlockSize R D)
        ((2 * quadraticGcdBlockSize R D) ^ 2) K (quadraticSecondWindow J)
        (quadraticFrequencyTwist u 1 (quadraticGcdBlockCoeff R D v))
        (quadraticFrequencyTwist u 1 (quadraticGcdBlockCoeff R D v)) := by
      rw [quadratic_gcd_second_total_split ρ a ha hM _ _ hD ho he]
      exact hb
    _ ≤ A₀ * (quadraticCorrectionScalar C ε ξ M J (quadraticGcdBlockSize R D)
        ((2 * quadraticGcdBlockSize R D) ^ 2) K (quadraticSecondWindow J) *
          (A₁ * (2 * (R : ℝ)) ^ δ * quadraticSieveEnergy (2 * R) v)) :=
      mul_le_mul_of_nonneg_left hm hA₀.le
    _ = _ := by rw [quadraticCorrectionScalar_scale]; ring

end Ostmann

end OAI
