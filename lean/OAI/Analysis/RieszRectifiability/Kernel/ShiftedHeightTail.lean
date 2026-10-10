import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.HeightTailSplit

namespace OAI

/-!
# Height tails after a dyadic shift

Rescaling the initial radius reindexes the dyadic annuli. Applying the weighted
height-tail estimate at this shifted radius yields a geometric decay term and a
Lipschitz-controlled far tail for the normalized height.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function
open scoped NNReal

theorem dyadicAnnulus_shift {d : ℕ} (a : Ambient d) (R : ℝ) (ℓ k : ℕ) :
    dyadicAnnulus a (R * 2 ^ ℓ) k = dyadicAnnulus a R (ℓ + k) := by
  ext y
  simp only [dyadicAnnulus, mem_ofPred_eq, pow_add, mul_assoc]

theorem normalized_weighted_height_tail_shifted {d : ℕ} (m : ℕ) (C B : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth m C μ) (hCB : C * 2 ^ m ≤ B)
    (w : Ambient d → ℝ) (K : ℝ≥0) (hw : LipschitzWith K w)
    (a : Ambient d) (R : ℝ) (hR : 0 < R) (N ℓ : ℕ) (hℓ : ℓ ≤ N)
    (δ b W : ℝ) (hδ : 0 < δ) (hb0 : 0 ≤ b) (hb2 : b < 2) (hW : |w a| ≤ W)
    (hsecond : ∀ k < N, (∫ y in dyadicAnnulus a R k, w y ^ 2 ∂μ) ≤
      (B * (R * 2 ^ k) ^ m) * (δ * (R * 2 ^ k) * b ^ k) ^ 2) :
    IntegrableOn (fun y => |w y / δ| * inverseDistancePow (m + 2) a y)
      (closedExterior a (R * 2 ^ ℓ)) μ ∧
      (∫ y in closedExterior a (R * 2 ^ ℓ), |w y / δ| * inverseDistancePow (m + 2) a y ∂μ) ≤
        (B / R) / (1 - b / 2) * (b / 2) ^ ℓ +
          (((K : ℝ) + W / R) * (2 * (C * 2 ^ m))) * ((R * 2 ^ N)⁻¹ / δ) := by
  have hshift : ∀ k < N - ℓ,
      (∫ y in dyadicAnnulus a (R * 2 ^ ℓ) k, w y ^ 2 ∂μ) ≤
        (B * ((R * 2 ^ ℓ) * 2 ^ k) ^ m) *
          ((δ * b ^ ℓ) * ((R * 2 ^ ℓ) * 2 ^ k) * b ^ k) ^ 2 := by
    intro k hk
    rw [dyadicAnnulus_shift]
    have h := hsecond (ℓ + k) (by omega)
    convert! h using 1
    simp only [pow_add, mul_pow]
    ring
  obtain ⟨hi, hb⟩ := improved_weighted_height_tail_bound m C B μ hg hCB w K hw a
    (R * 2 ^ ℓ) (by positivity) (N - ℓ) (δ * b ^ ℓ) b (by positivity) hb0 hb2 hshift
  have hrad : (R * 2 ^ ℓ) * 2 ^ (N - ℓ) = R * (2 : ℝ) ^ N := by
    rw [mul_assoc, ← pow_add, Nat.add_sub_of_le hℓ]
  rw [hrad] at hb
  have heq : (fun y => |w y / δ| * inverseDistancePow (m + 2) a y) =
      (fun y => (|w y| * inverseDistancePow (m + 2) a y) / δ) := by
    funext y
    rw [abs_div, abs_of_pos hδ]
    ring
  refine ⟨?_, ?_⟩
  · rw [heq]
    exact hi.div_const δ
  · rw [heq, integral_div]
    have hden : 0 < 1 - b / 2 := by linarith
    have hmain : ((B * (δ * b ^ ℓ) / (R * 2 ^ ℓ)) / (1 - b / 2)) / δ =
        (B / R) / (1 - b / 2) * (b / 2) ^ ℓ := by
      rw [div_pow]
      field_simp
    have hTpos : 0 < R * (2 : ℝ) ^ N := by positivity
    have hRT : R ≤ R * (2 : ℝ) ^ N := by
      simpa only [mul_one] using! mul_le_mul_of_nonneg_left
        (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) hR.le
    have hW0 : 0 ≤ W := (abs_nonneg _).trans hW
    have hcenter : |w a| / (R * 2 ^ N) ≤ W / R :=
      (div_le_div_of_nonneg_right hW hTpos.le).trans
        (div_le_div_of_nonneg_left hW0 hR hRT)
    have htail : (((K : ℝ) + |w a| / (R * 2 ^ N)) * (2 * (C * 2 ^ m / (R * 2 ^ N)))) / δ ≤
        (((K : ℝ) + W / R) * (2 * (C * 2 ^ m))) * ((R * 2 ^ N)⁻¹ / δ) := by
      calc
        _ ≤ (((K : ℝ) + W / R) * (2 * (C * 2 ^ m / (R * 2 ^ N)))) / δ :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right (add_le_add le_rfl hcenter) (by positivity [hg.1])) hδ.le
        _ = _ := by ring
    calc
      _ ≤ ((B * (δ * b ^ ℓ) / (R * 2 ^ ℓ)) / (1 - b / 2) +
        ((K : ℝ) + |w a| / (R * 2 ^ N)) * (2 * (C * 2 ^ m / (R * 2 ^ N)))) / δ :=
          div_le_div_of_nonneg_right hb hδ.le
      _ = (B / R) / (1 - b / 2) * (b / 2) ^ ℓ +
        (((K : ℝ) + |w a| / (R * 2 ^ N)) * (2 * (C * 2 ^ m / (R * 2 ^ N)))) / δ := by
          rw [add_div, hmain]
      _ ≤ _ := add_le_add le_rfl htail

end

end RieszRectifiability

end OAI
