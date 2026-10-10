import OAI.Analysis.IrrationalRotation.Product.SourceProductTailRealization
import OAI.Analysis.IrrationalRotation.Couplings.ProductSourceConditionalData
import OAI.Analysis.IrrationalRotation.Product.ProductPositiveDiagonal
import OAI.Analysis.IrrationalRotation.Couplings.ProductPairIdentity
import OAI.Analysis.IrrationalRotation.Couplings.ProductBiasedIdentityFromTriangular

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology InnerProductSpace

namespace Invariant233.ProductModel

theorem hasOnlyTrivialInvariantProjections_of_sampling_and_phases
    {p : ProductScaleData} (hp : ProductScaleLaws p)
    (e : ℕ ≃ Σ s, Fin (p.m s))
    (he : ∀ a : Σ s, Fin (p.m s),
      e.symm a = (∑ r ∈ Finset.range a.1, p.m r) + a.2.val)
    (θ : ℕ → ℝ)
    (hadm : AdmissibleAnglesAndCosts θ (fun i => p.C (e i).1))
    (hb : ∀ j, ∀ i ∈ ProductPhases.consecutiveBlock p.m j,
      θ i ∈ Set.Icc (1 / p.N j) (2 / p.N j))
    (hsmall : ∀ s, ProductPhases.smallPhaseCondition
      (ProductPhases.consecutiveBlock p.m s) (p.K s) (p.G s) θ)
    (hlarge : ∀ᶠ s in atTop, ProductPhases.largePhaseCondition
      (ProductPhases.consecutiveBlock p.m s) (p.N s) θ)
    (hsampling : HasAllFiniteCoordinateSampling θ) :
    HasOnlyTrivialInvariantProjections (factor θ)
      (weightedOperator θ (fun i => p.C (e i).1)) := by
  intro A hAm hA hinv
  by_cases hA0 : A = 0
  · exact Or.inl hA0
  by_cases hA1 : A = 1
  · exact Or.inr hA1
  exfalso
  have hθ0 : ∀ i, 0 ≤ θ i := fun i => (hadm.1 i).1.le
  have hc : ∀ i, 0 ≤ p.C (e i).1 := fun i => (hp.C_pos (e i).1).le
  obtain ⟨F, hF, hproj, htri⟩ := exists_covariantProjectionField_pairIdentity
    θ (fun i => p.C (e i).1) hθ0 hadm.2.1 hc hsampling A hAm hA hinv
  have hnorm : ‖A‖ = 1 := by
    have heq : ‖A‖ * ‖A‖ = ‖A‖ := by
      rw [← CStarRing.norm_star_mul_self, hA.isSelfAdjoint.star_eq,
        hA.isIdempotentElem.eq]
    have hpos : 0 < ‖A‖ := norm_pos_iff.mpr hA0
    nlinarith
  have hdiag := ae_strict_diagonal_of_invariant_projection hadm A hAm hA hA0 hA1
    hinv F (fun x => by simpa only [hnorm] using hF.2.1 x) hF.2.2.1 hF.2.2.2.1
  have hdiag' : ∀ᵐ x ∂baseMeasure,
      0 < BlockedProductCoupling.projectionDiagonal F x ∧
      BlockedProductCoupling.projectionDiagonal F x < 1 := by
    simpa only [BlockedProductCoupling.projectionDiagonal,
      BlockedProductCoupling.sourceBasisZero, PositiveDiagonalModel.e0,
      lp.inner_single_left, RCLike.inner_apply, map_one, mul_one] using hdiag
  have hpair := OrderedProductCoupling.source_circlePairLaw_pairIdentity_of_triangular
    p.m p.a p.b hp.m_ge_100
    (fun s => (hp.a_bounds s).1) (fun s => (hp.a_bounds s).2)
    (fun s => (hp.b_bounds s).1) (fun s => (hp.b_bounds s).2)
    e θ (fun i => p.C (e i).1) hθ0 hadm.2.1 hc F hproj
    (fun i => (hF.2.2.1 (lp.single 2 i 1)).measurable) htri
  have htail := hp.eventually_source_product_tail_estimate e he θ hθ0 hadm.2.1
    hb hsmall hlarge
  exact actualSource_projection_contradiction hp e he θ hθ0 hadm.2.1
    (fun i => hb (e i).1 i (ProductPhases.mem_consecutiveBlock_enumeration p.m e he i))
    A F hF hproj hinv hdiag' hpair htail

end Invariant233.ProductModel

end

end OAI
