import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.SupportedExteriorPairing
import OAI.Analysis.RieszRectifiability.Kernel.NormalizedExteriorPairing

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped NNReal

theorem normalized_region_tails_vanish {d : ℕ} (m : ℕ) (C B : ℝ)
    (μ : ℕ → Measure (Ambient d)) [∀ j, SFinite (μ j)]
    (A : Set (Ambient d)) (hA : MeasurableSet A) [∀ j, IsFiniteMeasure ((μ j).restrict A)]
    (s : ℕ → Set (Ambient d)) (a : Ambient d)
    (hcontain : ∀ r : ℝ, ∀ᶠ H in atTop, ball a r ⊆ s H)
    (hg : ∀ j, GlobalUpperGrowth m C (μ j)) (hCB : C * 2 ^ m ≤ B)
    (u φ : ℕ → Ambient d → ℝ) (K : ℝ≥0) (hu : ∀ j, LipschitzWith K (u j))
    (hφm : ∀ j, Measurable (φ j)) (hφ : ∀ j, Integrable (φ j) ((μ j).restrict A))
    (hφzero : ∀ j x, x ∉ A → φ j x = 0)
    (H₀ R : ℝ) (hH₀ : 0 ≤ H₀) (hR : 0 < R) (hHR : 2 * H₀ ≤ R) (hAR : A ⊆ ball a R)
    (hnear : ∀ j, ∀ᵐ x ∂(μ j).restrict A, φ j x ≠ 0 → dist x a ≤ H₀)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (δ : ℕ → ℝ) (hδ : ∀ j, 0 < δ j)
    (b W P : ℝ) (hb0 : 0 ≤ b) (hb2 : b < 2) (hW : ∀ j, |u j a| ≤ W)
    (hφu : ∀ j, Integrable (fun x => φ j x * (u j x / δ j)) ((μ j).restrict A))
    (hPφ : ∀ᶠ j in atTop, (∫ x in A, |φ j x| ∂μ j) ≤ P)
    (hPu : ∀ᶠ j in atTop, (∫ x in A, |φ j x * (u j x / δ j)| ∂μ j) ≤ P)
    (hlast : Tendsto (fun j => (R * (2 : ℝ) ^ N j)⁻¹ / δ j) atTop (𝓝 0))
    (hsecond : ∀ j k, k < N j → (∫ y in dyadicAnnulus a R k, u j y ^ 2 ∂μ j) ≤
      (B * (R * 2 ^ k) ^ m) * (δ j * (R * 2 ^ k) * b ^ k) ^ 2) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ H in atTop, ∀ᶠ j in atTop,
      Integrable (renormalizedNormalIntegrand m (fun x => u j x / δ j) (φ j) a)
        (((μ j).restrict (s H)).prod ((μ j).restrict (s H)ᶜ)) ∧
      (∫ q, |renormalizedNormalIntegrand m (fun x => u j x / δ j) (φ j) a q|
        ∂((μ j).restrict (s H)).prod ((μ j).restrict (s H)ᶜ)) < ε := by
  intro ε hε
  obtain ⟨ℓ, hℓ⟩ := normalized_far_pairings_vanish m C B μ (fun j => (μ j).restrict A)
    hg hCB u φ K hu hφm hφ a H₀ R hH₀ hR hHR hnear N hN δ hδ b W P hb0 hb2 hW
    hφu hPφ hPu hlast hsecond ε hε
  have hRle : R ≤ R * (2 : ℝ) ^ ℓ := by
    simpa only [mul_one] using! mul_le_mul_of_nonneg_left
      (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) hR.le
  filter_upwards [hcontain (R * 2 ^ ℓ)] with H hH
  filter_upwards [hℓ] with j hj
  obtain ⟨hi, hb⟩ := renormalized_pairing_complement_bound m (μ j) a (R * 2 ^ ℓ) A (s H) hA
    (hAR.trans ((ball_subset_ball hRle).trans hH)) hH
    (fun x => u j x / δ j) (φ j) (hφzero j) hj.1
  exact ⟨hi, hb.trans_lt hj.2⟩

end

end RieszRectifiability

end OAI
