import OAI.Analysis.LipschitzHilbert.Fourier.GlobalAnnularVariation
import OAI.Analysis.LipschitzHilbert.Estimates.ComplexVariationCoordinates

namespace OAI

/-! The finite-dimensional complex annular variation estimate, with no
dependence of the constant on the number of coordinates. -/

noncomputable section

open MeasureTheory
open scoped BigOperators FourierTransform ENNReal NNReal

namespace LipschitzHilbert

def hilbertPartialBandSum {N : ℕ} {κ : Type*} [Fintype κ]
    (f : Fin N → κ → SchwartzMap ℝ ℂ) (i : ℕ) (x : ℝ) : EuclideanSpace ℂ κ :=
  WithLp.toLp 2 (fun k => partialBandSum (fun j => f j k) i x)

theorem ennreal_complex_variation_coordinates {κ : Type*} [Fintype κ]
    (F : ℕ → EuclideanSpace ℂ κ) (N : ℕ) :
    ENNReal.ofReal (finiteCubicVariation F N) ^ (2 / 3 : ℝ) ≤
      ∑ k, ENNReal.ofReal (finiteCubicVariation (fun i => F i k) N) ^ (2 / 3 : ℝ) := by
  have h := ENNReal.ofReal_le_ofReal (complex_finiteCubicVariation_le F N)
  rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => Real.rpow_nonneg
    (finiteCubicVariation_nonneg _ _) _)] at h
  simpa only [ENNReal.ofReal_rpow_of_nonneg (finiteCubicVariation_nonneg _ _)
    (by norm_num : (0 : ℝ) ≤ 2 / 3)] using h

theorem partialBandSum_measurable {N : ℕ} (f : Fin N → SchwartzMap ℝ ℂ) (i : ℕ) :
    Measurable (partialBandSum f i) := by
  apply Finset.measurable_sum
  intro j _
  by_cases hj : j.val < i
  · simpa only [ite_eq_left hj] using (f j).continuous.measurable
  · simpa only [ite_eq_right hj] using (measurable_const : Measurable (fun _ : ℝ => (0 : ℂ)))

theorem hilbert_annular_variation (hL : LepingleInput) :
    ∃ K : ℝ≥0, 0 < K ∧ ∀ (N : ℕ) (κ : Type) [Fintype κ]
      (f : Fin N → κ → SchwartzMap ℝ ℂ),
      (∀ j k ξ, |ξ| < bandInner j.val → 𝓕 (f j k) ξ = 0) →
      (∀ j k ξ, bandOuter j.val < |ξ| → 𝓕 (f j k) ξ = 0) →
      (∫⁻ x, ENNReal.ofReal (finiteCubicVariation
        (fun i => hilbertPartialBandSum f i x) N) ^ (2 / 3 : ℝ)) ≤
      (K : ℝ≥0∞) * ENNReal.ofReal (∑ j, ∑ k, ∫ x, ‖f j k x‖ ^ 2) := by
  obtain ⟨K,hK,hbound⟩ := scalar_annular_variation hL
  refine ⟨K,hK,?_⟩
  intro N κ inst f hlow hhigh
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
      Finset.sum_le_sum (fun k _ => hbound N (fun j => f j k)
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
