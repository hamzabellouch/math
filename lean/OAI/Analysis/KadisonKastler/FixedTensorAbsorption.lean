import OAI.Analysis.KadisonKastler.FixedProductAbsorption
import OAI.Analysis.KadisonKastler.SpatialAssociatorTransport
import OAI.Analysis.KadisonKastler.SpatialAssociatorAlgebra

namespace OAI

/-! # Absorption after adjoining an arbitrary first algebra -/

namespace KadisonKastler

open UnitalTomsWinter

noncomputable section

universe u

private def algebraEquivOfAlgebraEq
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {M N : VonNeumannAlgebra H} (h : M = N) : Algebra M ≃⋆ₐ[ℂ] Algebra N := by
  cases h
  exact StarAlgEquiv.refl _ _

private def rightTensorEquivOfTransport
    {H K L : Type u}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
    (U : K ≃ₗᵢ[ℂ] L) (M : VonNeumannAlgebra H)
    (D : VonNeumannAlgebra K) (E : VonNeumannAlgebra L)
    (hD : spatialTransportAlgebra U D = E) :
    Algebra (spatialProductAlgebra M D) ≃⋆ₐ[ℂ] Algebra (spatialProductAlgebra M E) :=
  (spatialTransportEquiv (spatialTensorEquiv (LinearIsometryEquiv.refl ℂ H) U)
    (spatialProductAlgebra M D)).trans
      (algebraEquivOfAlgebraEq
        ((spatialTensorEquiv_right_spatialProduct U M D).trans
          (congrArg (spatialProductAlgebra M) hD)))

/-- The fixed factor absorbs the Powers product even after tensoring
with an arbitrary represented algebra. Both reassociation and changing
the second tensor leg are implemented on the actual Hilbert spaces. -/
theorem TwoRatioProductModel.tensor_absorbs_powers (P : TwoRatioProductModel.{u})
    (hProduct : PublishedPointedMatrixOperations.{u}) (hK : PublishedKaplanskyDensity.{u})
    (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H) :
    ∃ R : PointedMatrixProduct.{u} (fun _ : ℕ => fixedProductLambda),
      Nonempty (Algebra (spatialProductAlgebra (spatialProductAlgebra M P.stages.algebra)
        R.algebra) ≃⋆ₐ[ℂ] Algebra (spatialProductAlgebra M P.stages.algebra)) := by
  obtain ⟨R, U, _, hU⟩ := P.absorbs_powers hProduct
  have hD : spatialTransportAlgebra U (spatialProductAlgebra P.stages.algebra R.algebra) =
      P.stages.algebra := by
    apply SetLike.coe_injective
    ext T
    change T ∈ spatialTransportAlgebra U
      (spatialProductAlgebra P.stages.algebra R.algebra) ↔ T ∈ P.stages.algebra
    rw [mem_spatialTransportAlgebra, hU]
    rw [U.conjStarAlgEquiv.apply_symm_apply]
  have e₁ := spatialTransportEquiv (spatialAssociator (H := H) (K := P.K) (L := R.K))
    (spatialProductAlgebra (spatialProductAlgebra M P.stages.algebra) R.algebra)
  rw [spatialTransport_spatialProduct_assoc hK] at e₁
  have e₂ := rightTensorEquivOfTransport U M
    (spatialProductAlgebra P.stages.algebra R.algebra) P.stages.algebra hD
  exact ⟨R, ⟨e₁.trans e₂⟩⟩

end

end KadisonKastler

end OAI
