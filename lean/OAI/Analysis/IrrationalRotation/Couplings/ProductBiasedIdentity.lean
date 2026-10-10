import OAI.Analysis.IrrationalRotation.Couplings.ProductPairIdentity
import OAI.Analysis.IrrationalRotation.Couplings.ProductBiasedIdentityFromTriangular

namespace OAI

noncomputable section
open MeasureTheory

namespace Invariant233.OrderedProductCoupling

theorem exists_covariantProjectionField_all_biased_pairIdentity
    (θ c : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Summable θ)
    (hc : ∀ i, 0 ≤ c i) (hsampling : ProductModel.HasAllFiniteCoordinateSampling θ)
    (p : ProductModel.Hilbert →L[ℂ] ProductModel.Hilbert)
    (hpM : p ∈ ProductModel.factor θ) (hp : IsStarProjection p)
    (hinv : (1 - p) * ProductModel.weightedOperator θ c * p = 0) :
    ∃ F : ProductModel.Base → ProductModel.Fiber →L[ℂ] ProductModel.Fiber,
      ProductModel.IsCovariantFieldRepresentation θ p F 1 ∧
      (∀ x, IsStarProjection (F x)) ∧
      ∀ P : Parameters, Summable (energyBound P) →
        ∀ᵐ xy ∂circlePairLaw P, ProductModel.PairIdentity θ c F xy := by
  obtain ⟨F, hrep, hproj, htri⟩ :=
    ProductModel.exists_covariantProjectionField_pairIdentity θ c hθ0 hθ hc hsampling
      p hpM hp hinv
  refine ⟨F, hrep, hproj, ?_⟩
  intro P hsum
  exact circlePairLaw_pairIdentity_of_covariantField P hsum θ c hθ0 hθ hc p F hrep hproj htri

theorem exists_source_covariantProjectionField_biased_pairIdentity
    (θ c : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Summable θ)
    (hc : ∀ i, 0 ≤ c i) (hsampling : ProductModel.HasAllFiniteCoordinateSampling θ)
    (p : ProductModel.Hilbert →L[ℂ] ProductModel.Hilbert)
    (hpM : p ∈ ProductModel.factor θ) (hp : IsStarProjection p)
    (hinv : (1 - p) * ProductModel.weightedOperator θ c * p = 0)
    (m : ℕ → ℕ) (a b : ℕ → ℝ) (hm : ∀ s, 100 ≤ m s)
    (ha : ∀ s, 1 / (m s : ℝ) ≤ a s) (ha' : ∀ s, a s ≤ 1 / 4)
    (hb : ∀ s, 1 / (m s : ℝ) ≤ b s) (hb' : ∀ s, b s ≤ 1 / 4)
    (e : ℕ ≃ Σ s, Fin (m s)) :
    ∃ F : ProductModel.Base → ProductModel.Fiber →L[ℂ] ProductModel.Fiber,
      ProductModel.IsCovariantFieldRepresentation θ p F 1 ∧
      (∀ x, IsStarProjection (F x)) ∧
      ∀ tag : ℕ, ∀ᵐ xy ∂circlePairLaw
        (ofBlocks m sourceKappa a b sourceKappa_nonneg sourceKappa_le hm ha ha' hb hb' e tag),
        ProductModel.PairIdentity θ c F xy := by
  obtain ⟨F, hrep, hproj, htri⟩ :=
    ProductModel.exists_covariantProjectionField_pairIdentity θ c hθ0 hθ hc hsampling
      p hpM hp hinv
  exact ⟨F, hrep, hproj, source_circlePairLaw_pairIdentity_of_triangular m a b
    hm ha ha' hb hb' e θ c hθ0 hθ hc F hproj
      (fun i => (hrep.2.2.1 (lp.single 2 i 1)).measurable) htri⟩

end Invariant233.OrderedProductCoupling

end

end OAI
