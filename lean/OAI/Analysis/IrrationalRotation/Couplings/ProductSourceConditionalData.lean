import OAI.Analysis.IrrationalRotation.Couplings.ProductConditionalData
import OAI.Analysis.IrrationalRotation.Analysis.BlockedSourceTransport

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace Invariant233.ProductModel
open OrderedProductCoupling
open InvariantProjection.ConditionalConvolution

abbrev actualSourceParameters {p : ProductScaleData} (hp : ProductScaleLaws p)
    (e : ℕ ≃ Σ s, Fin (p.m s)) (j : ℕ) : Parameters :=
  sourceBlocks p.m p.a p.b hp.m_ge_100
    (fun s => (hp.a_bounds s).1) (fun s => (hp.a_bounds s).2)
    (fun s => (hp.b_bounds s).1) (fun s => (hp.b_bounds s).2) e j

theorem actualSourcePair_marginals_ac {p : ProductScaleData} (hp : ProductScaleLaws p)
    (e : ℕ ≃ Σ s, Fin (p.m s)) (j : ℕ) :
    (circlePairLaw (actualSourceParameters hp e j)).map Prod.fst ≪ baseMeasure ∧
    (circlePairLaw (actualSourceParameters hp e j)).map Prod.snd ≪ baseMeasure := by
  let P := actualSourceParameters hp e j
  have hac (side : Bool) : (law P).map (circleHybridEndpoint (fun _ => side)) ≪ baseMeasure := by
    obtain ⟨g, _, _, _, _, hg⟩ := exists_source_circle_hybrid_density p.m p.a p.b
      hp.m_ge_100 (fun s => (hp.a_bounds s).1) (fun s => (hp.a_bounds s).2)
      (fun s => (hp.b_bounds s).1) (fun s => (hp.b_bounds s).2) e j (fun _ => side)
    change (law P).map (circleHybridEndpoint (fun _ => side)) = _ at hg
    rw [hg]
    exact withDensity_absolutelyContinuous _ _
  have hm : Measurable (fun ω : Sample => (circleLeftEndpoint ω, circleRightEndpoint ω)) :=
    circleLeftEndpoint_measurable.prodMk circleRightEndpoint_measurable
  constructor
  · change ((law P).map _).map Prod.fst ≪ baseMeasure
    rw [Measure.map_map measurable_fst hm]
    exact hac false
  · change ((law P).map _).map Prod.snd ≪ baseMeasure
    rw [Measure.map_map measurable_snd hm]
    exact hac true

theorem eventually_actualSource_conditionalData
    {p : ProductScaleData} (hp : ProductScaleLaws p)
    (e : ℕ ≃ Σ s, Fin (p.m s))
    (he : ∀ a : Σ s, Fin (p.m s),
      e.symm a = (∑ r ∈ Finset.range a.1, p.m r) + a.2.val)
    (θ : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθsum : Summable θ)
    (hphase : ∀ i, θ i ∈ Set.Icc (1 / p.N (e i).1) (2 / p.N (e i).1))
    (A : Hilbert →L[ℂ] Hilbert) (F : Base → Fiber →L[ℂ] Fiber)
    (hF : IsCovariantFieldRepresentation θ A F 1)
    (hproj : ∀ x, IsStarProjection (F x))
    (hinv : (1 - A) * weightedOperator θ (fun i => p.C (e i).1) * A = 0)
    (hdiag : ∀ᵐ x ∂baseMeasure,
      0 < BlockedProductCoupling.projectionDiagonal F x ∧
      BlockedProductCoupling.projectionDiagonal F x < 1)
    (hpair : ∀ j, ∀ᵐ xy ∂circlePairLaw (actualSourceParameters hp e j),
      PairIdentity θ (fun i => p.C (e i).1) F xy)
    (htail : ∀ᶠ j in atTop,
      SourceTailEstimate p e θ j (actualSourceParameters hp e j)) :
    ∀ᶠ j in atTop,
      Nonempty (Data Sample (law (actualSourceParameters hp e j))
        (p.K j) (p.coefficientBound j) (1 / ((j + 1 : ℕ) : ℝ))
        (Real.exp (-82) / 2) (Real.exp (-p.L j)) (Real.exp (-p.L j / 400))) := by
  have hr : Measurable (BlockedProductCoupling.projectionDiagonal F) := by
    exact Complex.measurable_re.comp
      ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 0).continuous.measurable.comp (hF.2.2.1 _).measurable)
  have hmass := BlockedProductCoupling.eventually_flatSourceEvent_mass hp e hr hdiag
  filter_upwards [hmass, htail] with j hj ht
  let E := BlockedProductCoupling.flatSourceEvent p e (BlockedProductCoupling.projectionDiagonal F) j
  have hE : MeasurableSet E := BlockedProductCoupling.measurable_flatSourceEvent p e hr j
  have hb := BlockedProductCoupling.ae_flatSourceEvent_coefficient_properties hp e θ hphase F
    (Filter.Eventually.of_forall hproj) j
  have htag := BlockedProductCoupling.ae_flatSourceEvent_tag_endpoints hp e he
    (BlockedProductCoupling.projectionDiagonal F) j
  have hmem : ∀ᵐ ω ∂(law (actualSourceParameters hp e j)).restrict E, ω ∈ E :=
    ae_restrict_mem hE
  apply conditionalData_of_sourceTail hp e θ hθ0 hθsum (actualSourceParameters hp e j) j A F hF hproj hinv
    (actualSourcePair_marginals_ac hp e j).1 (actualSourcePair_marginals_ac hp e j).2
    (hpair j) ht E hE (Real.exp (-82) / 2) hj
  · filter_upwards [ae_restrict_of_ae hb, hmem] with ω hω hωE
    simpa only [BlockedProductCoupling.sourceCoefficientA, BlockedProductCoupling.sourceCoefficientB,
      BlockedProductCoupling.circleLeftEndpoint_unflatten,
      BlockedProductCoupling.circleRightEndpoint_unflatten,
      coeffA, coeffB, sourceLeftVector, sourceRightVector, sourceLeftCocycle,
      sourceRightCocycle, sourceUnitVector, BlockedProductCoupling.sourceBasisZero] using hω hωE
  · filter_upwards [ae_restrict_of_ae htag, hmem] with ω hω hωE
    exact hω hωE

theorem actualSource_projection_contradiction
    {p : ProductScaleData} (hp : ProductScaleLaws p)
    (e : ℕ ≃ Σ s, Fin (p.m s))
    (he : ∀ a : Σ s, Fin (p.m s),
      e.symm a = (∑ r ∈ Finset.range a.1, p.m r) + a.2.val)
    (θ : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθsum : Summable θ)
    (hphase : ∀ i, θ i ∈ Set.Icc (1 / p.N (e i).1) (2 / p.N (e i).1))
    (A : Hilbert →L[ℂ] Hilbert) (F : Base → Fiber →L[ℂ] Fiber)
    (hF : IsCovariantFieldRepresentation θ A F 1)
    (hproj : ∀ x, IsStarProjection (F x))
    (hinv : (1 - A) * weightedOperator θ (fun i => p.C (e i).1) * A = 0)
    (hdiag : ∀ᵐ x ∂baseMeasure,
      0 < BlockedProductCoupling.projectionDiagonal F x ∧
      BlockedProductCoupling.projectionDiagonal F x < 1)
    (hpair : ∀ j, ∀ᵐ xy ∂circlePairLaw (actualSourceParameters hp e j),
      PairIdentity θ (fun i => p.C (e i).1) F xy)
    (htail : ∀ᶠ j in atTop,
      SourceTailEstimate p e θ j (actualSourceParameters hp e j)) : False := by
  apply hp.not_eventually_conditional_data
    (fun j => law (actualSourceParameters hp e j)) (Real.exp (-82) / 2) (by positivity)
  exact eventually_actualSource_conditionalData hp e he θ hθ0 hθsum hphase A F
    hF hproj hinv hdiag hpair htail

end Invariant233.ProductModel

end

end OAI
