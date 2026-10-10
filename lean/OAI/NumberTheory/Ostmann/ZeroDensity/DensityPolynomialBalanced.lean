import OAI.NumberTheory.Ostmann.ZeroDensity.DensityPolynomialAlternative
import OAI.NumberTheory.Ostmann.ZeroDensity.DensityPolynomialBalance

namespace OAI

/-! # The balanced density exponent for the actual polynomial alternative -/

namespace Ostmann

open scoped BigOperators Classical

 theorem density_polynomial_alternative_balanced :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ, 1 ≤ Q → ∀ T σ : ℝ,
      2 ≤ T → 1 / 2 ≤ σ → σ ≤ 1 → ∀ X : ℕ, 1 ≤ X → (Q : ℝ) ^ 2 * T ≤ X →
      ∀ {ι : Type} (R : Finset ι) (c : ι → PrimitiveComplexCharacter) (t β : ι → ℝ),
      (∀ i ∈ R, (c i).modulus ≤ Q) → (∀ i ∈ R, |t i| ≤ T) →
      (∀ i ∈ R, ∀ j ∈ R, c i = c j → i ≠ j → 1 ≤ |t i - t j|) →
      (∀ i ∈ R, σ ≤ β i ∧ β i ≤ 1) →
      (∀ i ∈ R, (1 / 8 : ℝ) ≤ ‖∑ n ∈
        (Finset.Icc 1 ⌊((Q : ℝ) ^ 2 * T) ^ densityBalanceExponent σ⌋₊).filter (fun n => X < n),
        LSeries.term (densityDetectorCharacterCoefficient (c i) X) (densityVerticalPoint (β i) (t i)) n *
          densityDetectorWeight (n / (((Q : ℝ) ^ 2 * T) ^ densityBalanceExponent σ))‖) →
      (R.card : ℝ) ≤ C * ((Q : ℝ) ^ 2 * T) ^ densityTargetExponent σ *
        (Real.log ((Q : ℝ) * T)) ^ 9 := by
  obtain ⟨C, hC, hb⟩ := density_polynomial_alternative_count
  refine ⟨2 * C * 8 ^ 9, by positivity, ?_⟩
  intro Q hQ T σ hT hσ hσ1 X hX hBX ι R c t β hc ht hs hβ hlarge
  let B := (Q : ℝ) ^ 2 * T
  let Y := B ^ densityBalanceExponent σ
  let L := Real.log ((Q : ℝ) * T)
  have hq : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hB : 2 ≤ B := by dsimp [B]; nlinarith
  have hY : 2 ≤ Y := by
    have h := Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ B)
      (density_balance_at_least_one σ hσ hσ1)
    rw [Real.rpow_one] at h
    exact hB.trans h
  have hL : 0 ≤ L := Real.log_nonneg (by nlinarith)
  have hlog := density_balanced_log_cost Q hQ T σ hT hσ hσ1
  have hpow := density_polynomial_balanced_powers B X σ (by linarith) hBX hσ hσ1
  have h := hb X Q hX hQ Y T σ hY (by linarith) hσ hσ1 R c t β hc ht hs hβ hlarge
  apply h.trans
  calc
    _ ≤ C * (8 * L) ^ 9 * (2 * B ^ densityTargetExponent σ) := by
      apply mul_le_mul _ hpow (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by
        have := Real.log_nonneg (by linarith : 1 ≤ 2 * Y + 1)
        linarith) hlog 9) hC.le
    _ = _ := by ring

end Ostmann

end OAI
