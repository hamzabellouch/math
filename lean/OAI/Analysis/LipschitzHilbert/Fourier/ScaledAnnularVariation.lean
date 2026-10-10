import OAI.Analysis.LipschitzHilbert.Fourier.SchwartzDilation
import OAI.Analysis.LipschitzHilbert.Fourier.DyadicAnnularVariation

namespace OAI

/-! One annular-variation constant works for every common physical
frequency scale. This removes dependence on the top's horizontal length. -/

noncomputable section
open MeasureTheory
open scoped BigOperators FourierTransform NNReal ENNReal
namespace LipschitzHilbert

theorem partialBandSum_dilation {N : ℕ} (f : Fin N → SchwartzMap ℝ ℂ)
    (r : ℝ) (hr : r ≠ 0) (i : ℕ) (x : ℝ) :
    partialBandSum (fun j => schwartzDilation (f j) r hr) i x = partialBandSum f i (r*x) := by
  simp only [partialBandSum,schwartzDilation_apply]

theorem scaled_dyadic_scalar_annular_variation (hL : LepingleInput) {a b : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) :
    ∃ K : ℝ≥0, 0 < K ∧ ∀ (r : ℝ), 0 < r → ∀ (N : ℕ) (f : Fin N → SchwartzMap ℝ ℂ),
      (∀ j ξ, |ξ| < (a/r)*(2:ℝ)^j.val → 𝓕 (f j) ξ = 0) →
      (∀ j ξ, (b/r)*(2:ℝ)^j.val < |ξ| → 𝓕 (f j) ξ = 0) →
      (∫⁻ x, ENNReal.ofReal (finiteCubicVariation (fun i => partialBandSum f i x) N) ^ (2/3:ℝ)) ≤
        (K:ℝ≥0∞)*ENNReal.ofReal (∑ j, ∫ x, ‖f j x‖^2) := by
  obtain ⟨K,hK,hbound⟩ := dyadic_scalar_annular_variation hL ha hb
  refine ⟨K,hK,?_⟩
  intro r hr N f hlow hhigh
  let g := fun j => schwartzDilation (f j) r hr.ne'
  have hlo (j : Fin N) (ξ : ℝ) (hξ : |ξ| < a*(2:ℝ)^j.val) : 𝓕 (g j) ξ = 0 := by
    apply schwartzDilation_low (f j) r (a*(2:ℝ)^j.val) hr _ ξ hξ
    intro η hη
    apply hlow j η
    convert hη using 1
    ring
  have hhi (j : Fin N) (ξ : ℝ) (hξ : b*(2:ℝ)^j.val < |ξ|) : 𝓕 (g j) ξ = 0 := by
    apply schwartzDilation_high (f j) r (b*(2:ℝ)^j.val) hr _ ξ hξ
    intro η hη
    apply hhigh j η
    convert hη using 1
    ring
  have h := hbound N g hlo hhi
  have hv : (∫⁻ x, ENNReal.ofReal (finiteCubicVariation (fun i => partialBandSum g i x) N) ^ (2/3:ℝ)) =
      ENNReal.ofReal |r⁻¹| * (∫⁻ x, ENNReal.ofReal
        (finiteCubicVariation (fun i => partialBandSum f i x) N) ^ (2/3:ℝ)) := by
    simp only [g,partialBandSum_dilation]
    exact lintegral_dilation _
      ((measurable_finiteCubicVariation _ (partialBandSum_measurable f) N).ennreal_ofReal.pow_const _) r hr.ne'
  have he : (∑ j, ∫ x, ‖g j x‖^2) = |r⁻¹| * (∑ j, ∫ x, ‖f j x‖^2) := by
    simp only [g,schwartzDilation_energy,Finset.mul_sum]
  rw [hv,he,ENNReal.ofReal_mul (abs_nonneg _)] at h
  have hp : ENNReal.ofReal |r⁻¹| ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr
    (abs_pos.mpr (inv_ne_zero hr.ne')))
  rw [mul_left_comm (K:ℝ≥0∞)] at h
  exact (ENNReal.mul_le_mul_iff_right hp ENNReal.ofReal_ne_top).mp h

theorem scaled_dyadic_hilbert_annular_variation (hL : LepingleInput) {a b : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) :
    ∃ K : ℝ≥0, 0 < K ∧ ∀ (r : ℝ), 0 < r → ∀ (N : ℕ) (κ : Type) [Fintype κ]
      (f : Fin N → κ → SchwartzMap ℝ ℂ),
      (∀ j k ξ, |ξ| < (a/r) * (2 : ℝ) ^ j.val → 𝓕 (f j k) ξ = 0) →
      (∀ j k ξ, (b/r) * (2 : ℝ) ^ j.val < |ξ| → 𝓕 (f j k) ξ = 0) →
      (∫⁻ x, ENNReal.ofReal (finiteCubicVariation
        (fun i => hilbertPartialBandSum f i x) N) ^ (2 / 3 : ℝ)) ≤
      (K : ℝ≥0∞) * ENNReal.ofReal (∑ j, ∑ k, ∫ x, ‖f j k x‖ ^ 2) := by
  obtain ⟨K,hK,hbound⟩ := scaled_dyadic_scalar_annular_variation hL ha hb
  refine ⟨K,hK,?_⟩
  intro r hr N κ inst f hlow hhigh
  calc
    _ ≤ ∫⁻ x, ∑ k, ENNReal.ofReal (finiteCubicVariation
        (fun i => partialBandSum (fun j => f j k) i x) N) ^ (2 / 3 : ℝ) := by
      apply lintegral_mono
      intro x
      exact ennreal_complex_variation_coordinates (fun i => hilbertPartialBandSum f i x) N
    _ = ∑ k, ∫⁻ x, ENNReal.ofReal (finiteCubicVariation
        (fun i => partialBandSum (fun j => f j k) i x) N) ^ (2 / 3 : ℝ) := by
      apply lintegral_finsetSum
      intro k _
      exact (measurable_finiteCubicVariation _ (partialBandSum_measurable (fun j => f j k)) N).ennreal_ofReal.pow_const _
    _ ≤ ∑ k, (K : ℝ≥0∞) * ENNReal.ofReal (∑ j, ∫ x, ‖f j k x‖ ^ 2) :=
      Finset.sum_le_sum (fun k _ => hbound r hr N (fun j => f j k)
        (fun j => hlow j k) (fun j => hhigh j k))
    _ = _ := by
      rw [← Finset.mul_sum, ← ENNReal.ofReal_sum_of_nonneg]
      · congr 2
        exact Finset.sum_comm
      · intro k _
        exact Finset.sum_nonneg (fun j _ => integral_nonneg (fun x => sq_nonneg _))

end LipschitzHilbert

end

end OAI
