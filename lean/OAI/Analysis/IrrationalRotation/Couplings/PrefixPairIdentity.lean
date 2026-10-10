import OAI.Analysis.IrrationalRotation.Model.ProductPairIdentity
import OAI.Analysis.IrrationalRotation.Sampling.PrefixCompactTransfer

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Invariant233.ProductModel

theorem prefix_pairIdentity_of_triangular_domination
    (θ c : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Summable θ)
    (hc : ∀ i, 0 ≤ c i) (ν : FiniteMeasure EndpointPair)
    (hfst : (ν : Measure EndpointPair).map Prod.fst ≪ baseMeasure)
    (hsnd : (ν : Measure EndpointPair).map Prod.snd ≪ baseMeasure)
    (horder : ∀ᵐ xy ∂(ν : Measure EndpointPair), Ordered xy.1 xy.2)
    (hL2 : HasUniformL2Marginals (prefixPairLaw (ν : Measure EndpointPair)))
    (hdom : ∀ D, prefixPairLaw (ν : Measure EndpointPair) D ≪
      ∑ I ∈ (Finset.range D).powerset, triangularLaw I)
    (p : Base → Fiber →L[ℂ] Fiber)
    (hp : ∀ x, IsStarProjection (p x))
    (hpm : ∀ i : ℤ, Measurable (fun x => p x (lp.single 2 i 1)))
    (htri : ∀ I : Finset ℕ, ∀ᵐ xy ∂triangularLaw I, PairIdentity θ c p xy) :
    ∀ᵐ xy ∂(ν : Measure EndpointPair), PairIdentity θ c p xy := by
  have hz := prefix_operator_relation_of_triangular_domination θ c hθ0 hθ hc ν
    hfst hsnd horder hL2 hdom p hp hpm (fun I => ?_)
  · filter_upwards [ae_ordered_cocycle_ratio_cap θ c hθ0 hθ hc
      (ν : Measure EndpointPair) hfst hsnd horder, hz] with xy hcap hzero
    refine ⟨hcap, ?_⟩
    simpa only [ratioDiagonal, cocycleRatio, Invariant233.ratioDiagonal,
      mul_assoc, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc] using hzero
  · filter_upwards [htri I] with xy hxy
    simpa only [ratioDiagonal, cocycleRatio, Invariant233.ratioDiagonal,
      mul_assoc, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc] using hxy.2

end Invariant233.ProductModel

end

end OAI
