import OAI.Analysis.IrrationalRotation.Couplings.ProductCouplingPrefix
import OAI.Analysis.IrrationalRotation.Couplings.PrefixPairIdentity

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Invariant233.OrderedProductCoupling

theorem circlePairLaw_pairIdentity_of_triangular_domination
    (P : Parameters) (hsum : Summable (energyBound P))
    (θ c : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Summable θ)
    (hc : ∀ i, 0 ≤ c i)
    (hdom : ∀ D, ProductModel.prefixPairLaw (circlePairLaw P) D ≪
      ∑ I ∈ (Finset.range D).powerset, ProductModel.triangularLaw I)
    (p : ProductModel.Base → ProductModel.Fiber →L[ℂ] ProductModel.Fiber)
    (hp : ∀ x, IsStarProjection (p x))
    (hpm : ∀ i : ℤ, Measurable (fun x => p x (lp.single 2 i 1)))
    (htri : ∀ I : Finset ℕ, ∀ᵐ xy ∂ProductModel.triangularLaw I,
      ProductModel.PairIdentity θ c p xy) :
    ∀ᵐ xy ∂circlePairLaw P, ProductModel.PairIdentity θ c p xy := by
  let ν : FiniteMeasure ProductModel.EndpointPair := ⟨circlePairLaw P, inferInstance⟩
  obtain ⟨hfst, hsnd⟩ := circlePairLaw_marginals_ac_of_energy P hsum
  exact ProductModel.prefix_pairIdentity_of_triangular_domination θ c hθ0 hθ hc ν
    hfst hsnd (circlePairLaw_ordered P)
    (circlePairLaw_prefix_hasUniformL2Marginals P hsum) hdom p hp hpm htri

end Invariant233.OrderedProductCoupling

end

end OAI
