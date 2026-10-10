import OAI.Analysis.IrrationalRotation.Sampling.ProductPrefixDomination
import OAI.Analysis.IrrationalRotation.Analysis.RealTriangularLaw
import OAI.Analysis.IrrationalRotation.Couplings.PrefixHybrid

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Invariant233.OrderedProductCoupling

lemma circleHybridEndpoint_selected (I : Finset ℕ) (ω : Sample) :
    circleHybridEndpoint (fun i => decide (i ∈ I)) ω =
      ProductModel.selectedEndpoint I (circleLeftEndpoint ω) (circleRightEndpoint ω) := by
  funext i
  by_cases hi : i ∈ I <;>
    simp [circleHybridEndpoint, circleLeftEndpoint, circleRightEndpoint,
      circleEndpoint, hybridEndpoint, ProductModel.selectedEndpoint, hi]

theorem map_prefixPairLaw_circle (P : Parameters) (D : ℕ) :
    (prefixPairLaw P D).map circlePairEndpoint =
      ProductModel.prefixPairLaw (circlePairLaw P) D := by
  rw [prefixPairLaw, Measure.map_map circlePairEndpoint_measurable
    (leftEndpoint_measurable.prodMk (hybridEndpoint_measurable _)),
    ProductModel.prefixPairLaw, circlePairLaw,
    Measure.map_map (ProductModel.measurable_prefixPair D)
      (circleLeftEndpoint_measurable.prodMk circleRightEndpoint_measurable)]
  congr 1
  funext ω
  exact Prod.ext rfl (circleHybridEndpoint_selected (Finset.range D) ω)

theorem circle_prefix_first_marginal (P : Parameters) (D : ℕ) :
    (ProductModel.prefixPairLaw (circlePairLaw P) D).map Prod.fst =
      (law P).map circleLeftEndpoint := by
  rw [ProductModel.prefixPairLaw_first_marginal, circlePairLaw_fst]

theorem circle_prefix_second_marginal (P : Parameters) (D : ℕ) :
    (ProductModel.prefixPairLaw (circlePairLaw P) D).map Prod.snd =
      (law P).map (circleHybridEndpoint (fun i => decide (i ∈ Finset.range D))) := by
  rw [ProductModel.prefixPairLaw_second_marginal, circlePairLaw,
    Measure.map_map (ProductModel.continuous_prefixEndpoint D).measurable
      (circleLeftEndpoint_measurable.prodMk circleRightEndpoint_measurable)]
  congr 1
  funext ω
  exact (circleHybridEndpoint_selected (Finset.range D) ω).symm

theorem circle_prefix_absolutelyContinuous_reference (P : Parameters)
    (hsum : Summable (energyBound P)) (D : ℕ) :
    ProductModel.prefixPairLaw (circlePairLaw P) D ≪
      (prefixReferencePairLaw D).map circlePairEndpoint := by
  simpa only [map_prefixPairLaw_circle] using
    (prefixPairLaw_absolutelyContinuous P hsum D).map circlePairEndpoint_measurable

theorem map_sum_realTriangularLaw (s : Finset (Finset ℕ)) :
    (∑ I ∈ s, realTriangularLaw I).map circlePairEndpoint =
      ∑ I ∈ s, ProductModel.triangularLaw I := by
  rw [CouplingMixture.map_finsetSum s _ circlePairEndpoint_measurable]
  simp_rw [map_realTriangularLaw]

theorem map_absolutelyContinuous_sum_triangularLaw (s : Finset (Finset ℕ))
    {ν : Measure (Endpoint × Endpoint)} (hν : ν ≪ ∑ I ∈ s, realTriangularLaw I) :
    ν.map circlePairEndpoint ≪ ∑ I ∈ s, ProductModel.triangularLaw I := by
  simpa only [map_sum_realTriangularLaw] using hν.map circlePairEndpoint_measurable

end Invariant233.OrderedProductCoupling

end

end OAI
