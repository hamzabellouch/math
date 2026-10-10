import OAI.Analysis.LipschitzHilbert.Estimates.PolynomialLocalization
import OAI.Analysis.LipschitzHilbert.Fourier.DyadicAnnularVariation
import OAI.Analysis.LipschitzHilbert.Estimates.VariationScalar

namespace OAI

/-! Localizing the dyadic annular variation estimate by the manuscript's
polynomial weights. The constant is uniform in the number of scales,
coordinates, and the location and length of the interval. -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators FourierTransform ENNReal NNReal

namespace LipschitzHilbert

theorem partialBandSum_polynomialLocalization {N : ℕ} (f : Fin N → SchwartzMap ℝ ℂ)
    (a r : ℝ) (q i : ℕ) (x : ℝ) :
    partialBandSum (fun j => polynomialLocalization a r q (f j)) i x =
      (polynomialWeight a r q x : ℂ) * partialBandSum f i x := by
  unfold partialBandSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp only [polynomialLocalization_apply, mul_zero]

theorem hilbertPartialBandSum_polynomialLocalization {N : ℕ} {κ : Type*} [Fintype κ]
    (f : Fin N → κ → SchwartzMap ℝ ℂ) (a r : ℝ) (q i : ℕ) (x : ℝ) :
    hilbertPartialBandSum (fun j k => polynomialLocalization a r q (f j k)) i x =
      polynomialWeight a r q x • hilbertPartialBandSum f i x := by
  ext k
  change partialBandSum (fun j => polynomialLocalization a r q (f j k)) i x =
    polynomialWeight a r q x • partialBandSum (fun j => f j k) i x
  rw [partialBandSum_polynomialLocalization, Complex.real_smul]

theorem localized_dyadic_hilbert_variation (hL : LepingleInput) {lo hi : ℝ}
    (hlo : 0 < lo) (hhi : 0 ≤ hi) :
    ∃ K : ℝ≥0, 0 < K ∧ ∀ (N : ℕ) (κ : Type) [Fintype κ]
      (f : Fin N → κ → SchwartzMap ℝ ℂ) (a r : ℝ) (q : ℕ)
      (J : Set ℝ) (c : ℝ),
      (∀ j k ξ, |ξ| < lo * (2 : ℝ) ^ j.val → 𝓕 (f j k) ξ = 0) →
      (∀ j k ξ, hi * (2 : ℝ) ^ j.val < |ξ| → 𝓕 (f j k) ξ = 0) →
      MeasurableSet J → 0 ≤ c → (∀ x ∈ J, c ≤ polynomialWeight a r q x) →
      ENNReal.ofReal (c ^ 2) *
          (∫⁻ x in J, ENNReal.ofReal (finiteCubicVariation
            (fun i => hilbertPartialBandSum f i x) N) ^ (2 / 3 : ℝ)) ≤
        (K : ℝ≥0∞) * ENNReal.ofReal
          (∑ j, ∑ k, ∫ x, ‖polynomialLocalization a r q (f j k) x‖ ^ 2) := by
  obtain ⟨K,hK,hbound⟩ := dyadic_hilbert_annular_variation hL hlo hhi
  refine ⟨K,hK,?_⟩
  intro N κ inst f a r q J c hlow hhigh hJ hc hweight
  let F := fun j k => polynomialLocalization a r q (f j k)
  have hF := hbound N κ F
    (fun j k => polynomialLocalization_low a r q (f j k) _ _ (hlow j k) (hhigh j k))
    (fun j k => polynomialLocalization_high a r q (f j k) _ _ (hlow j k) (hhigh j k))
  have hpoint (x : ℝ) (hx : x ∈ J) :
      ENNReal.ofReal (c ^ 2) * ENNReal.ofReal (finiteCubicVariation
          (fun i => hilbertPartialBandSum f i x) N) ^ (2 / 3 : ℝ) ≤
        ENNReal.ofReal (finiteCubicVariation
          (fun i => hilbertPartialBandSum F i x) N) ^ (2 / 3 : ℝ) := by
    have heq : (fun i => hilbertPartialBandSum F i x) =
        (fun i => polynomialWeight a r q x • hilbertPartialBandSum f i x) := by
      funext i
      exact hilbertPartialBandSum_polynomialLocalization f a r q i x
    rw [heq, ennreal_finiteCubicVariation_smul_square]
    gcongr
    exact hweight x hx
  calc
    _ = ∫⁻ x in J, ENNReal.ofReal (c ^ 2) * ENNReal.ofReal (finiteCubicVariation
          (fun i => hilbertPartialBandSum f i x) N) ^ (2 / 3 : ℝ) :=
      (lintegral_const_mul' _ _ (by simp)).symm
    _ ≤ ∫⁻ x in J, ENNReal.ofReal (finiteCubicVariation
          (fun i => hilbertPartialBandSum F i x) N) ^ (2 / 3 : ℝ) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hJ] with x hx
      exact hpoint x hx
    _ ≤ ∫⁻ x, ENNReal.ofReal (finiteCubicVariation
          (fun i => hilbertPartialBandSum F i x) N) ^ (2 / 3 : ℝ) :=
      lintegral_mono' Measure.restrict_le_self (fun _ => le_rfl)
    _ ≤ _ := hF

end LipschitzHilbert

end

end OAI
