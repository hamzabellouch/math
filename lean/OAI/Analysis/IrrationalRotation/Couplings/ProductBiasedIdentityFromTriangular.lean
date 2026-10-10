import OAI.Analysis.IrrationalRotation.Sampling.PrefixReferenceCompletion
import OAI.Analysis.IrrationalRotation.Couplings.ProductBiasedPrefixTransfer
import OAI.Analysis.IrrationalRotation.Couplings.BlockProductCoupling

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Invariant233.OrderedProductCoupling

theorem circlePairLaw_pairIdentity_of_triangular
    (P : Parameters) (hsum : Summable (energyBound P))
    (θ c : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Summable θ)
    (hc : ∀ i, 0 ≤ c i)
    (F : ProductModel.Base → ProductModel.Fiber →L[ℂ] ProductModel.Fiber)
    (hF : ∀ x, IsStarProjection (F x))
    (hFm : ∀ i : ℤ, Measurable (fun x => F x (lp.single 2 i 1)))
    (htri : ∀ I : Finset ℕ, ∀ᵐ xy ∂ProductModel.triangularLaw I,
      ProductModel.PairIdentity θ c F xy) :
    ∀ᵐ xy ∂circlePairLaw P, ProductModel.PairIdentity θ c F xy :=
  circlePairLaw_pairIdentity_of_triangular_domination P hsum θ c hθ0 hθ hc
    (circle_prefix_absolutelyContinuous_triangular_sum P hsum) F hF hFm htri

theorem circlePairLaw_pairIdentity_of_covariantField
    (P : Parameters) (hsum : Summable (energyBound P))
    (θ c : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Summable θ)
    (hc : ∀ i, 0 ≤ c i)
    (A : ProductModel.Hilbert →L[ℂ] ProductModel.Hilbert)
    (F : ProductModel.Base → ProductModel.Fiber →L[ℂ] ProductModel.Fiber)
    (hrep : ProductModel.IsCovariantFieldRepresentation θ A F 1)
    (hF : ∀ x, IsStarProjection (F x))
    (htri : ∀ I : Finset ℕ, ∀ᵐ xy ∂ProductModel.triangularLaw I,
      ProductModel.PairIdentity θ c F xy) :
    ∀ᵐ xy ∂circlePairLaw P, ProductModel.PairIdentity θ c F xy :=
  circlePairLaw_pairIdentity_of_triangular P hsum θ c hθ0 hθ hc F hF
    (fun i => (hrep.2.2.1 (lp.single 2 i 1)).measurable) htri

theorem source_circlePairLaw_pairIdentity_of_triangular
    (m : ℕ → ℕ) (a b : ℕ → ℝ) (hm : ∀ s, 100 ≤ m s)
    (ha : ∀ s, 1 / (m s : ℝ) ≤ a s) (ha' : ∀ s, a s ≤ 1 / 4)
    (hb : ∀ s, 1 / (m s : ℝ) ≤ b s) (hb' : ∀ s, b s ≤ 1 / 4)
    (e : ℕ ≃ Σ s, Fin (m s))
    (θ c : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Summable θ)
    (hc : ∀ i, 0 ≤ c i)
    (F : ProductModel.Base → ProductModel.Fiber →L[ℂ] ProductModel.Fiber)
    (hF : ∀ x, IsStarProjection (F x))
    (hFm : ∀ i : ℤ, Measurable (fun x => F x (lp.single 2 i 1)))
    (htri : ∀ I : Finset ℕ, ∀ᵐ xy ∂ProductModel.triangularLaw I,
      ProductModel.PairIdentity θ c F xy) :
    ∀ tag : ℕ, ∀ᵐ xy ∂circlePairLaw
      (ofBlocks m sourceKappa a b sourceKappa_nonneg sourceKappa_le hm ha ha' hb hb' e tag),
      ProductModel.PairIdentity θ c F xy := by
  intro tag
  exact circlePairLaw_pairIdentity_of_triangular _
    (ofBlocks_energy_sum m sourceKappa a b sourceKappa_nonneg sourceKappa_le hm
      ha ha' hb hb' e tag summable_sourceKappa_sq).1 θ c hθ0 hθ hc F hF hFm htri

end Invariant233.OrderedProductCoupling

end

end OAI
