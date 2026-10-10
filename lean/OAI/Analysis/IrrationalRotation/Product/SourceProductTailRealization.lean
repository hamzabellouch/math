import OAI.Analysis.IrrationalRotation.Model.SourceProductTail
import OAI.Analysis.IrrationalRotation.Product.SourceProductTailAttenuation
import OAI.Analysis.IrrationalRotation.Product.ProductScaleRealization

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology

namespace Invariant233.ProductScaleLaws
open OrderedProductCoupling
variable {p : ProductScaleData} (hp : ProductScaleLaws p)

theorem eventually_source_product_tail_estimate
    (e : ℕ ≃ Σ s, Fin (p.m s))
    (he : ∀ a : Σ s, Fin (p.m s),
      e.symm a = (∑ r ∈ Finset.range a.1, p.m r) + a.2.val)
    (θ : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθsum : Summable θ)
    (hb : ∀ j, ∀ i ∈ ProductPhases.consecutiveBlock p.m j,
      θ i ∈ Icc (1 / p.N j) (2 / p.N j))
    (hsmall : ∀ s, ProductPhases.smallPhaseCondition
      (ProductPhases.consecutiveBlock p.m s) (p.K s) (p.G s) θ)
    (hlarge : ∀ᶠ s in atTop, ProductPhases.largePhaseCondition
      (ProductPhases.consecutiveBlock p.m s) (p.N s) θ) :
    ∀ᶠ j in atTop, SourceTailEstimate p e θ j
      (sourceBlocks p.m p.a p.b hp.m_ge_100
        (fun s => (hp.a_bounds s).1) (fun s => (hp.a_bounds s).2)
        (fun s => (hp.b_bounds s).1) (fun s => (hp.b_bounds s).2) e j) := by
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.1 hlarge
  filter_upwards [eventually_ge_atTop j₀] with j hj
  exact hp.source_product_tail_conditional_attenuation e he θ hθ0 hθsum j
    (hb j) (fun s _ => hsmall s) (fun s hjs => hj₀ s (hj.trans hjs))

end Invariant233.ProductScaleLaws

namespace Invariant233.ProductModel
open OrderedProductCoupling

theorem exists_product_operator_and_source_tail_estimates :
    ∃ p : ProductScaleData, ∃ hp : ProductScaleLaws p,
      ∃ (e : ℕ ≃ Σ s, Fin (p.m s)) (θ : ℕ → ℝ),
      (∀ a : Σ s, Fin (p.m s),
        e.symm a = (∑ r ∈ Finset.range a.1, p.m r) + a.2.val) ∧
      AdmissibleAnglesAndCosts θ (fun i => p.C (e i).1) ∧
      HasNegInfiniteLogIntegral baseMeasure (weight θ (fun i => p.C (e i).1)) ∧
      weightedOperator θ (fun i => p.C (e i).1) ∈ factor θ ∧
      weightedOperator θ (fun i => p.C (e i).1) ≠ 0 ∧
      NormQuasinilpotent (weightedOperator θ (fun i => p.C (e i).1)) ∧
      (∀ᶠ j in atTop, SourceTailEstimate p e θ j
        (sourceBlocks p.m p.a p.b hp.m_ge_100
          (fun s => (hp.a_bounds s).1) (fun s => (hp.a_bounds s).2)
          (fun s => (hp.b_bounds s).1) (fun s => (hp.b_bounds s).2) e j)) := by
  obtain ⟨p, hp, e, θ, he, hθ, _hsum, _hsum', hadm, hlog, _hpos,
      hsmall, hlarge, hmem, hne, hqn, _hspec⟩ :=
    exists_product_scales_phase_quasinilpotent
  exact ⟨p, hp, e, θ, he, hadm, hlog, hmem, hne, hqn,
    hp.eventually_source_product_tail_estimate e he θ
      (fun i => (hadm.1 i).1.le) hadm.2.1 hθ hsmall hlarge⟩

end Invariant233.ProductModel

end

end OAI
