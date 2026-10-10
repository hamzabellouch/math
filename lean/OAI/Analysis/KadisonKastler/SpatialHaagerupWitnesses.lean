import OAI.Analysis.KadisonKastler.ModularHaagerupWitnesses
import OAI.Analysis.KadisonKastler.SpatialModularCoisometries

namespace OAI

/-! # Haagerup witnesses in the constructed spatial two-ratio product -/

namespace KadisonKastler

open Generator UnitalTomsWinter

noncomputable section

universe u

variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [TopologicalSpace.SeparableSpace (SpatialHilbert H K)]
  {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K} {Ω : H} {ξ : K}

namespace PointedMatrixSites

variable (P : PointedMatrixSites N ξ twoRatioSiteParameter)

theorem spatial_haagerup_witnesses
    (hunit : ‖Ω‖=1)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω))
    (hIII : TypeIIIFactor (spatialProductAlgebra M N))
    (J : SpatialHilbert H K ≃ₗᵢ⋆[ℂ] SpatialHilbert H K) :
    let hs := separating_spatialProduct_vector_of_separating M N Ω ξ hsep P.separating
    let hc := denseRange_spatialProduct_vector M N Ω ξ hcyc P.cyclic
    HaagerupCommutatorWitnesses (constructedModularConjugationData J (tensorVector ξ Ω) hs hc
      (tomitaPolarConjugation_commutant_eq J (tensorVector ξ Ω) hs hc)) := by
  let hs := separating_spatialProduct_vector_of_separating M N Ω ξ hsep P.separating
  let hc := denseRange_spatialProduct_vector M N Ω ξ hcyc P.cyclic
  let d := constructedModularConjugationData J (tensorVector ξ Ω) hs hc
    (tomitaPolarConjugation_commutant_eq J (tensorVector ξ Ω) hs hc)
  let S := constructedModularSpectralResolution J (tensorVector ξ Ω) hs hc
    (modularStrongGroup_normalizes J (tensorVector ξ Ω) hs hc)
  have hun : ‖tensorVector ξ Ω‖=1 := by rw [norm_tensorVector_apply,hunit,P.unit_vector,mul_one]
  obtain ⟨ψ,hψ,hinv,hprod⟩ := exists_modular_product_state_of_simple
    (spatialProductAlgebra M N) (tensorVector ξ Ω) hun
    (typeIII_algebra_simple publishedVonNeumannSpectralCut publishedTypeIIIProjectionComparison _ hIII) d S
  change HaagerupCommutatorWitnesses d
  apply haagerupCommutatorWitnesses_of_modular_product J hs hc d rfl S
    (fun _ => rfl) hun ψ hψ hinv hprod
  intro t ht ht1
  obtain ⟨v,hv,hscale,hconv⟩ := P.exists_spatial_modular_coisometries hsep hcyc J d rfl ht ht1
  exact ⟨v,hv,hscale (tensorVector ξ Ω),hconv⟩

end PointedMatrixSites

end

end KadisonKastler

end OAI
