import OAI.MeasureTheory.Falconer.Fourier.DescriptorPairDerivativeScale

namespace OAI

/-! # One ambient derivative scale for the two original profile products -/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff
open PlanarFalconer (PolicyDescriptor)

theorem uniform_two_profile_derivatives (d K P : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (Q₁ Q₂ : DyadicCube d) (ρ₁ ρ₂ : Measure (Space d)) (f₁ f₂ : ℝ → ℝ)
        (J i L : ℕ) (F G : Finset PolicyDescriptor)
        (S₁ S₂ : PolicyDescriptor → Finset (Sphere d)),
      F.card ≤ (N+1)^P → G.card ≤ (N+1)^P →
      (∀ b ∈ F, PlanarFalconer.descriptorLength b ≤ L) →
      (∀ b ∈ G, PlanarFalconer.descriptorLength b ≤ L) →
      (∀ b ∈ F, ∀ w ∈ S₁ b, ∀ z ∈ S₁ b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z) →
      (∀ b ∈ G, ∀ w ∈ S₂ b, ∀ z ∈ S₂ b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z) →
      ∀ x y k, k ≤ K → ∀ w : Space d,
        ‖iteratedFDeriv ℝ k (fun t =>
          (descriptorAmbientProduct Q₁ ρ₁ f₁ N σ J i F S₁ x t : ℂ)*
          (descriptorAmbientProduct Q₂ ρ₂ f₂ N σ J i G S₂ y t : ℂ)) w‖ ≤
          (2:ℝ)^K*(descriptorDerivativeScale N σ L)^k := by
  obtain ⟨N₀,hN₀⟩ := uniform_descriptor_global_scale d K P hσ
  refine ⟨N₀,?_⟩
  intro N hN Q₁ Q₂ ρ₁ ρ₂ f₁ f₂ J i L F G S₁ S₂ hF hG hFL hGL hsepF hsepG x y k hk w
  exact equal_scale_product_derivatives
    (zero_le_one.trans (descriptorDerivativeScale_ge_one N hσ.le L)) _ _
    (Complex.ofRealCLM.contDiff.comp (descriptorAmbientProduct_contDiff Q₁ ρ₁ f₁ N σ J i F S₁ x))
    (Complex.ofRealCLM.contDiff.comp (descriptorAmbientProduct_contDiff Q₂ ρ₂ f₂ N σ J i G S₂ y))
    (fun l hl z => hN₀ N hN Q₁ ρ₁ f₁ J i L F S₁ hF hFL hsepF x z l hl)
    (fun l hl z => hN₀ N hN Q₂ ρ₂ f₂ J i L G S₂ hG hGL hsepG y z l hl)
    k hk w

end Falconer

end OAI
