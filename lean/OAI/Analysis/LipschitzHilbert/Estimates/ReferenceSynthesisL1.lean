import OAI.Analysis.LipschitzHilbert.Estimates.ReferenceSynthesis

namespace OAI

/-! The L1 synthesis estimate that supplies the dual local coefficient
budget. Reference length need not be a dyadic scale. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal FourierTransform NNReal

namespace LipschitzHilbert
namespace ReferencePacketFamily
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

theorem threshold_lintegral (hL : LepingleInput) {lo hi : ℝ}
    (hlo : 0 < lo) (hhi : 0 ≤ hi) :
    ∃ K : ℝ≥0, 0 < K ∧ ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)] (P : ReferencePacketFamily N κ ι)
      (c : ∀ j, ι j → EuclideanSpace ℂ κ) (d : Fin N → ℝ) (v : ℝ × ℝ → ℝ),
      Monotone d →
      (∀ j i k, Measurable (fun z : ℝ × ℝ => P.wave j i k z.1 z.2)) →
      (∀ j i k y ξ, |ξ| < lo * (2:ℝ)^j.val → 𝓕 (P.wave j i k y) ξ = 0) →
      (∀ j i k y ξ, hi * (2:ℝ)^j.val < |ξ| → 𝓕 (P.wave j i k y) ξ = 0) →
      (∫⁻ z : ℝ × ℝ, ENNReal.ofReal ‖P.thresholdSynthesis c d v z‖) ≤
        ENNReal.ofReal (Real.pi^2 * P.radius * P.width) ^ (1/2:ℝ) *
        ((K : ℝ≥0∞) * ENNReal.ofReal
          (((4 * Real.pi)^2 * P.constant^2 * 256 * Real.pi^2) *
            P.width * P.coefficientEnergy c)) ^ (1/2:ℝ) := by
  obtain ⟨K,hK,hbound⟩ := weighted_variation hL hlo hhi
  refine ⟨K,hK,?_⟩
  intro N κ ι instκ instι P c d v hd hw hlow hhigh
  have hcs := weighted_lintegral_cauchySchwarz volume
    (referenceWeight P.centerX P.centerZ P.radius P.width) (P.variation c)
    (referenceWeight_measurable _ _ _ _) (P.variation_measurable c hw)
    (referenceWeight_pos _ _ _ _)
  rw [P.weightedVariationEnergy_eq c hw] at hcs
  calc
    _ ≤ ∫⁻ z : ℝ × ℝ, ENNReal.ofReal (P.variation c z) :=
      lintegral_mono (fun z => ENNReal.ofReal_le_ofReal
        (P.thresholdSynthesis_le_variation c d hd v z))
    _ ≤ _ := hcs
    _ ≤ _ := mul_le_mul
      (ENNReal.rpow_le_rpow
        (referenceWeight_inverse_integral _ _ _ _ P.radius_pos P.width_pos) (by norm_num))
      (ENNReal.rpow_le_rpow (hbound N κ ι P c hlow hhigh) (by norm_num)) bot_le bot_le

end ReferencePacketFamily
end LipschitzHilbert

end

end OAI
