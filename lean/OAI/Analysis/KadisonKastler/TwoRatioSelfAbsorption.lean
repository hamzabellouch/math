import OAI.Analysis.KadisonKastler.FixedTensorAbsorption

namespace OAI

/-! # Self-absorption of the fixed two-ratio product

Interleaving both families of sites gives an actual pointed spatial
isomorphism. This also applies after adjoining any first tensor leg.
-/

namespace KadisonKastler

open UnitalTomsWinter

noncomputable section

universe u

def twoRatioDoublingEquiv : (TwoRatioSite ⊕ TwoRatioSite) ≃ TwoRatioSite :=
  (Equiv.sumSumSumComm ℕ ℕ ℕ ℕ).trans
    (Equiv.sumCongr Equiv.natSumNatEquivNat Equiv.natSumNatEquivNat)

theorem twoRatioDoublingEquiv_parameter (i : TwoRatioSite ⊕ TwoRatioSite) :
    twoRatioSiteParameter (twoRatioDoublingEquiv i)=
      Sum.elim twoRatioSiteParameter twoRatioSiteParameter i := by
  rcases i with ((i | i) | (i | i)) <;> rfl

theorem TwoRatioProductModel.absorbs_self (P : TwoRatioProductModel.{u})
    (hProduct : PublishedPointedMatrixOperations.{u}) :
    ∃ U : SpatialHilbert P.K P.K ≃ₗᵢ[ℂ] P.K,
      U (tensorVector P.stages.vector P.stages.vector)=P.stages.vector ∧
      spatialTransportAlgebra U (spatialProductAlgebra P.stages.algebra P.stages.algebra)=
        P.stages.algebra := by
  obtain ⟨s⟩ := hProduct.sum TwoRatioSite TwoRatioSite P.K P.K
    P.stages.algebra P.stages.algebra P.stages.vector P.stages.vector
    twoRatioSiteParameter twoRatioSiteParameter P.coordinates P.coordinates
  obtain ⟨U,hU,hmem⟩ := hProduct.reindex (TwoRatioSite ⊕ TwoRatioSite) TwoRatioSite
    (SpatialHilbert P.K P.K) P.K
    (spatialProductAlgebra P.stages.algebra P.stages.algebra) P.stages.algebra
    (tensorVector P.stages.vector P.stages.vector) P.stages.vector
    (Sum.elim twoRatioSiteParameter twoRatioSiteParameter) twoRatioSiteParameter
    s P.coordinates twoRatioDoublingEquiv twoRatioDoublingEquiv_parameter
  refine ⟨U,hU,?_⟩
  apply SetLike.coe_injective
  ext T
  change T ∈ spatialTransportAlgebra U
    (spatialProductAlgebra P.stages.algebra P.stages.algebra) ↔ T ∈ P.stages.algebra
  rw [mem_spatialTransportAlgebra,hmem,U.conjStarAlgEquiv.apply_symm_apply]

theorem TwoRatioProductModel.tensor_absorbs_self (P : TwoRatioProductModel.{u})
    (hProduct : PublishedPointedMatrixOperations.{u}) (hK : PublishedKaplanskyDensity.{u})
    (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H) :
    Nonempty (Algebra (spatialProductAlgebra (spatialProductAlgebra M P.stages.algebra)
      P.stages.algebra) ≃⋆ₐ[ℂ] Algebra (spatialProductAlgebra M P.stages.algebra)) := by
  obtain ⟨U,_,hU⟩ := P.absorbs_self hProduct
  let V := spatialAssociator (H := H) (K := P.K) (L := P.K)
  let W := spatialTensorEquiv (LinearIsometryEquiv.refl ℂ H) U
  have hV := spatialTransport_spatialProduct_assoc hK M P.stages.algebra P.stages.algebra
  have hW := spatialTensorEquiv_right_spatialProduct U M
    (spatialProductAlgebra P.stages.algebra P.stages.algebra)
  have htarget : spatialTransportAlgebra W
      (spatialProductAlgebra M (spatialProductAlgebra P.stages.algebra P.stages.algebra))=
        spatialProductAlgebra M P.stages.algebra := by
    exact hW.trans (congrArg (spatialProductAlgebra M) hU)
  have eV := spatialTransportEquiv V
    (spatialProductAlgebra (spatialProductAlgebra M P.stages.algebra) P.stages.algebra)
  rw [hV] at eV
  have eW := spatialTransportEquiv W
    (spatialProductAlgebra M (spatialProductAlgebra P.stages.algebra P.stages.algebra))
  rw [htarget] at eW
  exact ⟨eV.trans eW⟩

end

end KadisonKastler

end OAI
