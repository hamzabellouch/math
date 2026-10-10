import OAI.NumberTheory.Ostmann.ZeroDensity.DensityIntegralAlternative
import OAI.NumberTheory.Ostmann.ZeroDensity.DensityBalanceParameters

namespace OAI

/-! # The balanced Montgomery exponent for the integral alternative -/

namespace Ostmann

open MeasureTheory
open scoped BigOperators Classical

 theorem density_integral_alternative_balanced :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ, 1 ≤ Q → ∀ T σ : ℝ,
      2 ≤ T → 1 / 2 < σ → σ ≤ 1 →
      1 / Real.log ((Q : ℝ) ^ 2 * T) ≤ σ - 1 / 2 →
      ∃ X : ℕ, 1 ≤ X ∧ (Q : ℝ) ^ 2 * T ≤ X ∧
      ∀ {ι : Type} (S : Finset ι) (c : ι → PrimitiveComplexCharacter) (β t : ι → ℝ),
      (∀ i ∈ S, (c i).modulus ≤ Q) → (∀ i ∈ S, |t i| ≤ T) →
      (∀ i ∈ S, ∀ j ∈ S, c i = c j → i ≠ j → 1 ≤ |t i - t j|) →
      (∀ i ∈ S, σ ≤ β i ∧ β i ≤ 1 ∧ (c i).L (densityVerticalPoint (β i) (t i)) = 0) →
      (∀ i ∈ S, (1 / 8 : ℝ) ≤ ‖densityDetectorMean (c i) X (densityVerticalPoint (β i) (t i))
        (((Q : ℝ) ^ 2 * T) ^ densityBalanceExponent σ)‖) →
      (S.card : ℝ) ^ 3 ≤ C * (((Q : ℝ) ^ 2 * T) ^ densityTargetExponent σ) ^ 3 *
        (Real.log ((Q : ℝ) * T)) ^ 12 := by
  obtain ⟨C, hC, hb⟩ := density_integral_alternative_count
  refine ⟨C * 256 ^ 4 * 17 ^ 2 * 20 ^ 2, by positivity, ?_⟩
  intro Q hQ T σ hT hσ hσ1 hgap
  obtain ⟨X, hX, hXB, hsize, hlogX⟩ := density_detector_cutoff Q hQ T hT
  refine ⟨X, hX, hXB, ?_⟩
  intro ι S c β t hc ht hs hz hlarge
  let B := (Q : ℝ) ^ 2 * T
  let Y := B ^ densityBalanceExponent σ
  let L := Real.log ((Q : ℝ) * T)
  have hq : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hB : 1 ≤ B := by dsimp [B]; nlinarith
  have hBp : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hY : 1 ≤ Y := Real.one_le_rpow hB (le_trans zero_le_one (density_balance_at_least_one σ hσ.le hσ1))
  have hYp : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hL : 0 ≤ L := Real.log_nonneg (by nlinarith)
  have hXlog : 0 ≤ 1 + Real.log X := by
    have hx : (1 : ℝ) ≤ X := by exact_mod_cast hX
    have h := Real.log_nonneg hx
    linarith
  have hK : 128 * Y ^ (1 / 2 - σ) / (σ - 1 / 2) ≤
      256 * Y ^ (1 / 2 - σ) * L := by
    have h := density_away_inverse_gap Q hQ T σ hT hσ hgap
    have hm := mul_le_mul_of_nonneg_left h
      (show 0 ≤ 128 * Y ^ (1 / 2 - σ) by positivity)
    convert hm using 1
    · ring
    · dsimp [L]
      ring
  have hpow : (Y ^ (1 / 2 - σ)) ^ (4 : ℕ) = Y ^ (2 - 4 * σ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hYp.le]
    congr 1
    ring
  have hK4 : (128 * Y ^ (1 / 2 - σ) / (σ - 1 / 2)) ^ 4 ≤
      256 ^ 4 * Y ^ (2 - 4 * σ) * L ^ 4 := by
    have h := pow_le_pow_left₀ (by positivity) hK 4
    simpa only [mul_pow, hpow] using h
  have hcount := hb X Q hX hQ T σ Y hT hσ hY S c β t hc ht hs hz hlarge
  apply hcount.trans
  calc
    _ ≤ C * (256 ^ 4 * Y ^ (2 - 4 * σ) * L ^ 4) * B * (17 * B) ^ 2 * L ^ 6 * (20 * L) ^ 2 := by
      gcongr
    _ = (C * 256 ^ 4 * 17 ^ 2 * 20 ^ 2) * (B ^ 3 * Y ^ (2 - 4 * σ)) * L ^ 12 := by ring
    _ = _ := by rw [density_balance_identity B σ hBp (by linarith)]

end Ostmann

end OAI
