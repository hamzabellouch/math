import OAI.MeasureTheory.Falconer.Estimates.DescriptorPairBudget
import OAI.MeasureTheory.Falconer.Geometry.NormalizedDescriptorFamily

namespace OAI

/-! # Uniform derivatives of the actual two-endpoint amplitude

The finite-order product loss is fixed before scale, classes, lists and
points. This supplies the derivative premise of the masked inverse remainder.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

theorem uniform_descriptor_pair_derivatives (d K P : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (Q : DyadicCube d) (ρ : Measure (Space d)) (f : ℝ → ℝ) (J i L : ℕ)
        (B : Finset PlanarFalconer.PolicyDescriptor)
        (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d)),
      B.card ≤ (N+1)^P →
      (∀ b ∈ B, PlanarFalconer.descriptorLength b ≤ L) →
      (∀ b ∈ B, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z →
        descriptorMaskRadius N σ b/2 ≤ dist w z) →
      ∀ x y k, k ≤ K → ∀ w : Space d,
        ‖iteratedFDeriv ℝ k (descriptorPairAmplitude Q ρ f N σ J i B S x y) w‖ ≤
          (2:ℝ)^K*(descriptorDerivativeScale N σ L)^k := by
  obtain ⟨N₀,hN₀⟩ := uniform_descriptor_global_scale d K P hσ
  refine ⟨N₀,?_⟩
  intro N hN Q ρ f J i L B S hB hL hsep x y k hk w
  have hs (z : Space d) : ContDiff ℝ ∞ (fun v =>
      (descriptorAmbientProduct Q ρ f N σ J i B S z v : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (descriptorAmbientProduct_contDiff Q ρ f N σ J i B S z)
  have hb (z : Space d) : ∀ l ≤ K, ∀ v,
      ‖iteratedFDeriv ℝ l (fun u => (descriptorAmbientProduct Q ρ f N σ J i B S z u : ℂ)) v‖ ≤
        (descriptorDerivativeScale N σ L)^l := by
    intro l hl v
    exact hN₀ N hN Q ρ f J i L B S hB hL hsep z v l hl
  exact equal_scale_product_derivatives
    (zero_le_one.trans (descriptorDerivativeScale_ge_one N hσ.le L))
    _ _ (hs x) (hs y) (hb x) (hb y) k hk w

end Falconer

end OAI
