import OAI.Analysis.KadisonKastler.PublishedTwoRatioProduct
import OAI.Analysis.KadisonKastler.PublishedPointedOperations

namespace OAI

/-! # Absorbing an extra family of lambda sites

The explicit even/odd bijection is applied to finite-site coordinates
of the actual product representation. The published input contains
only construction, sum and reindexing facts for pointed products.
-/

namespace KadisonKastler

open UnitalTomsWinter

noncomputable section

universe u

/-- The fixed two-ratio product absorbs the lambda-only Powers product,
by an actual vector-preserving unitary between the Hilbert spaces. -/
theorem TwoRatioProductModel.absorbs_powers (P : TwoRatioProductModel.{u})
    (hProduct : PublishedPointedMatrixOperations.{u}) :
    ∃ R : PointedMatrixProduct.{u} (fun _ : ℕ => fixedProductLambda),
    ∃ U : SpatialHilbert P.K R.K ≃ₗᵢ[ℂ] P.K,
      U (tensorVector R.vector P.stages.vector) = P.stages.vector ∧
      ∀ x : SpatialHilbert P.K R.K →L[ℂ] SpatialHilbert P.K R.K,
        x ∈ spatialProductAlgebra P.stages.algebra R.algebra ↔
          U.conjStarAlgEquiv x ∈ P.stages.algebra := by
  obtain ⟨R⟩ := hProduct.powers
  obtain ⟨s⟩ := hProduct.sum TwoRatioSite ℕ P.K R.K
    P.stages.algebra R.algebra P.stages.vector R.vector
    twoRatioSiteParameter (fun _ => fixedProductLambda) P.coordinates R.coordinates
  obtain ⟨U, hU, hmem⟩ := hProduct.reindex (TwoRatioSite ⊕ ℕ) TwoRatioSite
    (SpatialHilbert P.K R.K) P.K
    (spatialProductAlgebra P.stages.algebra R.algebra) P.stages.algebra
    (tensorVector R.vector P.stages.vector) P.stages.vector
    (Sum.elim twoRatioSiteParameter (fun _ => fixedProductLambda))
    twoRatioSiteParameter s P.coordinates lambdaAbsorptionSiteEquiv
    lambdaAbsorptionSiteEquiv_preserves_parameter
  exact ⟨R, U, hU, hmem⟩

end

end KadisonKastler

end OAI
