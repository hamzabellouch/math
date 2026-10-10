import OAI.Analysis.LipschitzHilbert.Estimates.ReferenceAnalysis
import OAI.Analysis.LipschitzHilbert.Estimates.SelfEnergy

namespace OAI

/-! The local Carleson budget for the actual main analyzing coefficients
in a reference box, conditional only on scalar Lépingle. -/

noncomputable section
open MeasureTheory
open scoped BigOperators FourierTransform ENNReal NNReal

namespace LipschitzHilbert
namespace ReferencePacketFamily
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

theorem mainCoefficient_carleson (hL : LepingleInput) {lo hi : ℝ}
    (hlo : 0 < lo) (hhi : 0 ≤ hi) :
    ∃ A : ℝ, 0 < A ∧ ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)] (P : ReferencePacketFamily N κ ι)
      (d : Fin N → ℝ) (v : ℝ × ℝ → ℝ) (g : ℝ × ℝ → EuclideanSpace ℂ κ),
      Monotone d → Measurable v → Measurable g → (∀ z, ‖g z‖ ≤ 1) →
      (∀ j i k, Measurable (fun z : ℝ × ℝ => P.wave j i k z.1 z.2)) →
      (∀ j i k y ξ, |ξ| < lo * (2:ℝ)^j.val → 𝓕 (P.wave j i k y) ξ = 0) →
      (∀ j i k y ξ, hi * (2:ℝ)^j.val < |ξ| → 𝓕 (P.wave j i k y) ξ = 0) →
      P.width * P.coefficientEnergy (P.mainCoefficient d v g) ≤
        A * P.constant^2 * (P.radius * P.width) := by
  obtain ⟨K,hK,hL1⟩ := threshold_lintegral hL hlo hhi
  refine ⟨(K:ℝ) * (4*Real.pi)^2 * 256 * Real.pi^4, by positivity, ?_⟩
  intro N κ ι instκ instι P d v g hd hv hg hg1 hw hlow hhigh
  let a := P.mainCoefficient d v g
  let B := P.width * P.coefficientEnergy a
  let D := (K:ℝ) * ((4*Real.pi)^2 * P.constant^2 * 256 * Real.pi^2)
  have hB : 0 ≤ B := mul_nonneg P.width_pos.le (P.coefficientEnergy_nonneg a)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hsum : (∑ s : Σ j, ι j, (P.length s.1 * P.width) *
      ‖analyzingCoefficient volume (fun s : Σ j, ι j => P.length s.1 * P.width)
        (P.selectedWave d v) g s‖^2) = B := by
    rw [Fintype.sum_sigma]
    dsimp [B, coefficientEnergy]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    change (P.length j * P.width) * ‖a j i‖^2 = _
    ring
  have hpair := analyzingCoefficient_energy_le volume
    (fun s : Σ j, ι j => P.length s.1 * P.width) (P.selectedWave d v) g
    (fun s => mul_pos (P.length_pos s.1) P.width_pos)
    (P.analyzing_integrable d v hv hw g hg hg1) hg1
  rw [hsum] at hpair
  have heq (z : ℝ × ℝ) : diagonalSynthesis (P.selectedWave d v)
      (analyzingCoefficient volume (fun s : Σ j, ι j => P.length s.1 * P.width)
        (P.selectedWave d v) g) z = P.thresholdSynthesis a d v z :=
    P.diagonalSynthesis_selectedWave d v a z
  simp_rw [heq] at hpair
  have h := hpair.trans (hL1 N κ ι P a d v hd hw hlow hhigh)
  have hprod : (K : ℝ≥0∞) * ENNReal.ofReal
      (((4 * Real.pi)^2 * P.constant^2 * 256 * Real.pi^2) * P.width * P.coefficientEnergy a) =
      ENNReal.ofReal (D * B) := by
    dsimp [D,B]
    rw [← ENNReal.ofReal_coe_nnreal]
    rw [← ENNReal.ofReal_mul K.coe_nonneg]
    congr 1
    ring
  rw [hprod] at h
  have hbudget := energy_le_of_sqrt_self hB (mul_nonneg (mul_nonneg (sq_nonneg _) P.radius_pos.le) P.width_pos.le) hD h
  change B ≤ _
  convert hbudget using 1
  dsimp [D]
  ring

end ReferencePacketFamily
end LipschitzHilbert

end

end OAI
