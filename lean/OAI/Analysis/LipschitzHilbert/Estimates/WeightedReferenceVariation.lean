import OAI.Analysis.LipschitzHilbert.Packets.ReferencePacketFamily
import OAI.Analysis.LipschitzHilbert.Fourier.LocalizedAnnularVariation

namespace OAI

/-! The polynomially weighted maximal-synthesis estimate about an arbitrary
reference box, conditional only on the published scalar Lépingle input. -/

noncomputable section
open MeasureTheory
open scoped BigOperators FourierTransform ENNReal NNReal

namespace LipschitzHilbert
namespace ReferencePacketFamily
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

def transverseEnergy (P : ReferencePacketFamily N κ ι)
    (c : ∀ j, ι j → EuclideanSpace ℂ κ) (y : ℝ) : ℝ :=
  ∑ j, P.length j * ∑ i, ‖c j i‖^2 *
    lineEnvelope (P.baseZ + P.width * (P.site j i).2) P.width 1 y

theorem transverseEnergy_nonneg (P : ReferencePacketFamily N κ ι)
    (c : ∀ j, ι j → EuclideanSpace ℂ κ) (y : ℝ) : 0 ≤ P.transverseEnergy c y := by
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (P.length_pos j).le (Finset.sum_nonneg
    (fun i _ => mul_nonneg (sq_nonneg _) (lineEnvelope_nonneg _ _ _ _)))

theorem transverseEnergy_integrable (P : ReferencePacketFamily N κ ι)
    (c : ∀ j, ι j → EuclideanSpace ℂ κ) : Integrable (P.transverseEnergy c) := by
  apply integrable_finsetSum
  intro j _
  apply Integrable.const_mul
  apply integrable_finsetSum
  intro i _
  exact (integrable_lineEnvelope_one _ _ P.width_pos).const_mul _

theorem integral_transverseEnergy (P : ReferencePacketFamily N κ ι)
    (c : ∀ j, ι j → EuclideanSpace ℂ κ) :
    (∫ y, P.transverseEnergy c y) = Real.pi * P.width * P.coefficientEnergy c := by
  unfold transverseEnergy
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul]
    simp_rw [integral_finsetSum Finset.univ (fun i _ =>
      (integrable_lineEnvelope_one _ _ P.width_pos).const_mul _)]
    simp_rw [integral_const_mul, integral_lineEnvelope_one _ _ P.width_pos]
    simp only [coefficientEnergy, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    ring
  · intro j _
    apply Integrable.const_mul
    apply integrable_finsetSum
    intro i _
    exact (integrable_lineEnvelope_one _ _ P.width_pos).const_mul _

def weightedVariationEnergy (P : ReferencePacketFamily N κ ι)
    (c : ∀ j, ι j → EuclideanSpace ℂ κ) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (polynomialWeight P.centerZ P.width 1 y ^ 2) *
    ∫⁻ x, ENNReal.ofReal (polynomialWeight P.centerX P.radius 1 x ^ 2) *
      ENNReal.ofReal (finiteCubicVariation
        (fun n => hilbertPartialBandSum (P.packets c y) n x) N) ^ (2 / 3 : ℝ)

theorem weighted_variation (hL : LepingleInput) {lo hi : ℝ}
    (hlo : 0 < lo) (hhi : 0 ≤ hi) :
    ∃ K : ℝ≥0, 0 < K ∧ ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)] (P : ReferencePacketFamily N κ ι)
      (c : ∀ j, ι j → EuclideanSpace ℂ κ),
      (∀ j i k y ξ, |ξ| < lo * (2 : ℝ)^j.val → 𝓕 (P.wave j i k y) ξ = 0) →
      (∀ j i k y ξ, hi * (2 : ℝ)^j.val < |ξ| → 𝓕 (P.wave j i k y) ξ = 0) →
      P.weightedVariationEnergy c ≤ (K : ℝ≥0∞) * ENNReal.ofReal
        (((4 * Real.pi)^2 * P.constant^2 * 256 * Real.pi^2) *
          P.width * P.coefficientEnergy c) := by
  obtain ⟨K,hK,hbound⟩ := dyadic_hilbert_annular_variation hL hlo hhi
  refine ⟨K,hK,?_⟩
  intro N κ ι instκ instι P c hlow hhigh
  let A := (4 * Real.pi)^2 * P.constant^2 * 256 * Real.pi
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hline (y : ℝ) :
      (∫⁻ x, ENNReal.ofReal (polynomialWeight P.centerX P.radius 1 x ^ 2) *
        ENNReal.ofReal (finiteCubicVariation
          (fun n => hilbertPartialBandSum (P.packets c y) n x) N) ^ (2 / 3 : ℝ)) ≤
      (K : ℝ≥0∞) * ENNReal.ofReal
        (∑ j, ∑ k, ∫ x, ‖polynomialLocalization P.centerX P.radius 1
          (P.packets c y j k) x‖ ^ 2) := by
    have hl (j : Fin N) (k : κ) (ξ : ℝ) (hξ : |ξ| < lo*(2:ℝ)^j.val) :
        𝓕 (P.packets c y j k) ξ = 0 :=
      packetSynthesis_fourier_zero _ _ ξ (fun i => hlow j i k y ξ hξ)
    have hh (j : Fin N) (k : κ) (ξ : ℝ) (hξ : hi*(2:ℝ)^j.val < |ξ|) :
        𝓕 (P.packets c y j k) ξ = 0 :=
      packetSynthesis_fourier_zero _ _ ξ (fun i => hhigh j i k y ξ hξ)
    have h := hbound N κ
      (fun j k => polynomialLocalization P.centerX P.radius 1 (P.packets c y j k))
      (fun j k => polynomialLocalization_low _ _ _ _ _ _ (hl j k) (hh j k))
      (fun j k => polynomialLocalization_high _ _ _ _ _ _ (hl j k) (hh j k))
    simpa only [hilbertPartialBandSum_polynomialLocalization,
      ennreal_finiteCubicVariation_smul_square] using h
  have hpoint (y : ℝ) :
      ENNReal.ofReal (polynomialWeight P.centerZ P.width 1 y ^ 2) *
      (∫⁻ x, ENNReal.ofReal (polynomialWeight P.centerX P.radius 1 x ^ 2) *
        ENNReal.ofReal (finiteCubicVariation
          (fun n => hilbertPartialBandSum (P.packets c y) n x) N) ^ (2 / 3 : ℝ)) ≤
      (K : ℝ≥0∞) * ENNReal.ofReal (A * P.transverseEnergy c y) := by
    calc
      _ ≤ ENNReal.ofReal (polynomialWeight P.centerZ P.width 1 y ^ 2) *
          ((K : ℝ≥0∞) * ENNReal.ofReal _) := mul_le_mul_right (hline y) _
      _ = (K : ℝ≥0∞) * ENNReal.ofReal
          (polynomialWeight P.centerZ P.width 1 y ^ 2 * _) := by
        rw [ENNReal.ofReal_mul (sq_nonneg _)]
        ac_rfl
      _ ≤ _ := mul_le_mul_right (ENNReal.ofReal_le_ofReal (P.weighted_energy c y)) _
  calc
    _ ≤ ∫⁻ y, (K : ℝ≥0∞) * ENNReal.ofReal (A * P.transverseEnergy c y) :=
      lintegral_mono hpoint
    _ = (K : ℝ≥0∞) * ENNReal.ofReal (∫ y, A * P.transverseEnergy c y) := by
      rw [lintegral_const_mul' _ _ (by simp),
        ofReal_integral_eq_lintegral_ofReal ((P.transverseEnergy_integrable c).const_mul A)
          (Filter.Eventually.of_forall (fun y => mul_nonneg hA (P.transverseEnergy_nonneg c y)))]
    _ = _ := by
      rw [integral_const_mul, P.integral_transverseEnergy]
      congr 2
      dsimp [A]
      ring

end ReferencePacketFamily
end LipschitzHilbert

end

end OAI
