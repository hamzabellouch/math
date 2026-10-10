import OAI.Analysis.IrrationalRotation.Sampling.PrefixCocycleCap
import OAI.Analysis.IrrationalRotation.Operators.OperatorCompactTransfer
import OAI.Analysis.IrrationalRotation.Sampling.ProductSamplingAbsoluteContinuity

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators

namespace Invariant233.ProductModel

theorem prefixPairLaw_finiteMeasure_tendsto (ν : FiniteMeasure EndpointPair) :
    Tendsto (fun D : ℕ => ν.map (prefixPair D)) atTop (𝓝 ν) := by
  apply FiniteMeasure.tendsto_of_forall_integral_tendsto
  intro φ
  have h := prefixPairLaw_weaklyConverges (ν : Measure EndpointPair)
    (⟨φ, φ.continuous⟩ : C(EndpointPair, ℝ))
  simpa only [prefixPairLaw, FiniteMeasure.map, FiniteMeasure.toMeasure,
    ContinuousMap.coe_mk] using h

theorem prefix_operator_relation_transfer
    (θ c : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Summable θ)
    (hc : ∀ i, 0 ≤ c i) (ν : FiniteMeasure EndpointPair)
    (hfst : (ν : Measure EndpointPair).map Prod.fst ≪ baseMeasure)
    (hsnd : (ν : Measure EndpointPair).map Prod.snd ≪ baseMeasure)
    (horder : ∀ᵐ xy ∂(ν : Measure EndpointPair), Ordered xy.1 xy.2)
    (hL2 : HasUniformL2Marginals (prefixPairLaw (ν : Measure EndpointPair)))
    (p : Base → SequenceHilbert ℤ →L[ℂ] SequenceHilbert ℤ)
    (hp : ∀ x, IsStarProjection (p x))
    (hpm : ∀ i : ℤ, Measurable (fun x => p x (lp.single 2 i 1)))
    (hzero : ∀ D, ∀ᵐ xy ∂prefixPairLaw (ν : Measure EndpointPair) D,
      (1 - p xy.2).comp
        ((ratioDiagonal (ProductCocycle.cocycleVersion θ c) xy).comp
          (p xy.1)) = 0) :
    ∀ᵐ xy ∂(ν : Measure EndpointPair),
      (1 - p xy.2).comp
        ((ratioDiagonal (ProductCocycle.cocycleVersion θ c) xy).comp
          (p xy.1)) = 0 := by
  obtain ⟨hfirst, hsecond⟩ := hL2.uniformlyAbsolutelyContinuous
  have hcapn : ∀ D k, ∀ᵐ xy ∂prefixPairLaw (ν : Measure EndpointPair) D,
      ProductCocycle.cocycleVersion θ c k xy.2 /
        ProductCocycle.cocycleVersion θ c k xy.1 ≤ 1 := by
    intro D k
    filter_upwards [prefixPairLaw_cocycle_ratio_cap θ c hθ0 hθ hc
      (ν : Measure EndpointPair) hfst hsnd horder D] with xy hxy
    exact (hxy k).2
  have hcap : ∀ k, ∀ᵐ xy ∂(ν : Measure EndpointPair),
      ProductCocycle.cocycleVersion θ c k xy.2 /
        ProductCocycle.cocycleVersion θ c k xy.1 ≤ 1 := by
    intro k
    filter_upwards [ae_ordered_cocycle_ratio_cap θ c hθ0 hθ hc
      (ν : Measure EndpointPair) hfst hsnd horder] with xy hxy
    exact (hxy k).2
  exact CompactTransfer.compact_operator_transfer baseMeasure p hp
    (ProductCocycle.cocycleVersion θ c)
    (ProductCocycle.cocycleVersion_pos θ c)
    (ProductCocycle.measurable_cocycleVersion θ c) hpm
    (prefixPairLaw_finiteMeasure_tendsto ν) hfirst hsecond
    1 zero_lt_one hcapn hcap hzero

theorem ae_of_absolutelyContinuous_finite_sum
    {α ι : Type*} [MeasurableSpace α] (s : Finset ι)
    (μ : ι → Measure α) (ν : Measure α)
    (hν : ν ≪ ∑ i ∈ s, μ i) {P : α → Prop}
    (hP : ∀ i ∈ s, ∀ᵐ x ∂μ i, P x) : ∀ᵐ x ∂ν, P x := by
  apply hν.ae_le
  rw [← Measure.sum_coe_finset]
  exact Measure.ae_sum_iff.mpr (fun i => hP i i.property)

theorem prefix_operator_relation_of_triangular_domination
    (θ c : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Summable θ)
    (hc : ∀ i, 0 ≤ c i) (ν : FiniteMeasure EndpointPair)
    (hfst : (ν : Measure EndpointPair).map Prod.fst ≪ baseMeasure)
    (hsnd : (ν : Measure EndpointPair).map Prod.snd ≪ baseMeasure)
    (horder : ∀ᵐ xy ∂(ν : Measure EndpointPair), Ordered xy.1 xy.2)
    (hL2 : HasUniformL2Marginals (prefixPairLaw (ν : Measure EndpointPair)))
    (hdom : ∀ D, prefixPairLaw (ν : Measure EndpointPair) D ≪
      ∑ I ∈ (Finset.range D).powerset, triangularLaw I)
    (p : Base → SequenceHilbert ℤ →L[ℂ] SequenceHilbert ℤ)
    (hp : ∀ x, IsStarProjection (p x))
    (hpm : ∀ i : ℤ, Measurable (fun x => p x (lp.single 2 i 1)))
    (htri : ∀ I : Finset ℕ, ∀ᵐ xy ∂triangularLaw I,
      (1 - p xy.2).comp
        ((ratioDiagonal (ProductCocycle.cocycleVersion θ c) xy).comp
          (p xy.1)) = 0) :
    ∀ᵐ xy ∂(ν : Measure EndpointPair),
      (1 - p xy.2).comp
        ((ratioDiagonal (ProductCocycle.cocycleVersion θ c) xy).comp
          (p xy.1)) = 0 := by
  apply prefix_operator_relation_transfer θ c hθ0 hθ hc ν hfst hsnd horder hL2 p hp hpm
  intro D
  exact ae_of_absolutelyContinuous_finite_sum (Finset.range D).powerset triangularLaw
    (prefixPairLaw (ν : Measure EndpointPair) D) (hdom D) (fun I _ => htri I)

end Invariant233.ProductModel

end

end OAI
