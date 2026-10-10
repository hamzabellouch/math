import OAI.Analysis.KadisonKastler.PositiveReferenceModular
import OAI.Analysis.KadisonKastler.SpatialHaagerupWitnesses
import OAI.Analysis.KadisonKastler.SymmetricVectorAngle

namespace OAI

/-! # Haagerup witnesses at positive references

The spatial coisometries scale on every vector. Positivity identifies the
new reference's polar conjugation with the old one, so the constructed
modular-product-state argument applies again at the new reference.
-/

namespace KadisonKastler

open Generator Generator.Tracial UnitalTomsWinter Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

/-- A concrete all-vector coisometry property; the spatial product below
supplies it by the already constructed remote matrix sequences. -/
def UniversalModularCoisometries (M : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H) : Prop :=
  ∀ t : ℝ, 0 < t → t < 1 → ∃ w : ℕ → Algebra M,
    (∀ n, w n*star (w n)=1) ∧
    (∀ η : H, Tendsto (fun n => (w n).val η-
      (t : ℂ) • conjugationOperator J (star (w n).val) η) atTop (𝓝 0)) ∧
    ∀ (a : Algebra M) (η : H),
      Tendsto (fun n => (w n*a*star (w n)).val η) atTop (𝓝 (a.val η))

theorem haagerup_witnesses_of_polar_coisometries
    (J : H ≃ₗᵢ⋆[ℂ] H) (η : H) (hunit : ‖η‖=1)
    (hsep : Function.Injective (algebraVectorMap M η))
    (hcyc : DenseRange (algebraVectorMap M η))
    (hpolar : tomitaPolarConjugation J η hsep hcyc=J)
    (hIII : TypeIIIFactor M) (hremote : UniversalModularCoisometries M J) :
    HaagerupCommutatorWitnesses (constructedModularConjugationData J η hsep hcyc
      (tomitaPolarConjugation_commutant_eq J η hsep hcyc)) := by
  let d := constructedModularConjugationData J η hsep hcyc
    (tomitaPolarConjugation_commutant_eq J η hsep hcyc)
  let S := constructedModularSpectralResolution J η hsep hcyc
    (modularStrongGroup_normalizes J η hsep hcyc)
  obtain ⟨ψ,hψ,hinv,hprod⟩ := exists_modular_product_state_of_simple M η hunit
    (typeIII_algebra_simple publishedVonNeumannSpectralCut publishedTypeIIIProjectionComparison M hIII) d S
  change HaagerupCommutatorWitnesses d
  apply haagerupCommutatorWitnesses_of_modular_product J hsep hcyc d rfl S
    (fun _ => rfl) hunit ψ hψ hinv hprod
  intro t ht ht1
  obtain ⟨w,hw,hs,hc⟩ := hremote t ht ht1
  refine ⟨w,hw,?_,hc⟩
  simpa only [ModularConjugationData.rightAction,d,
    constructedModularConjugationData,hpolar] using hs η

local instance positiveHaagerupRealInner : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

theorem positive_reference_haagerup_witnesses
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ=ξ)
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    {η : H} (hη : η ∈ modularPositiveCone (M := M) J ξ) (hunit : ‖η‖=1)
    (hsep : Function.Injective (algebraVectorMap M η))
    (hcyc : DenseRange (algebraVectorMap M η))
    (hIII : TypeIIIFactor M) (hremote : UniversalModularCoisometries M J) :
    HaagerupCommutatorWitnesses (constructedModularConjugationData J η hsep hcyc
      (tomitaPolarConjugation_commutant_eq J η hsep hcyc)) :=
  haagerup_witnesses_of_polar_coisometries J η hunit hsep hcyc
    (positiveCone_polar_conjugation J hJ hright hleft ξ hξ hpos hη hsep hcyc) hIII hremote

theorem positive_reference_noncollinear_projection_witness
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ=ξ)
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    {η : H} (hη : η ∈ modularPositiveCone (M := M) J ξ) (hunit : ‖η‖=1)
    (hsep : Function.Injective (algebraVectorMap M η))
    (hcyc : DenseRange (algebraVectorMap M η))
    (hIII : TypeIIIFactor M) (hremote : UniversalModularCoisometries M J)
    (ζ : H) (hζ : J ζ=ζ) (huζ : ‖ζ‖=1) (hne : ζ≠η) (hne' : ζ≠-η)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ p : AlgebraProjection M, p.val≠0 ∧
      (1-(inner ℂ η ζ).re^2)*(‖p.val.val η‖^2+‖p.val.val ζ‖^2) <
        16384*‖centralVectorDefect J ζ p.val.val‖^2 ∧
      ‖centralVectorDefect J η p.val.val‖^2 < δ*‖centralVectorDefect J ζ p.val.val‖^2 := by
  let d := constructedModularConjugationData J η hsep hcyc
    (tomitaPolarConjugation_commutant_eq J η hsep hcyc)
  have hd : d.conjugation=J := positiveCone_polar_conjugation
    J hJ hright hleft ξ hξ hpos hη hsep hcyc
  have hw := positive_reference_haagerup_witnesses J hJ hright hleft ξ hξ hpos
    hη hunit hsep hcyc hIII hremote
  simpa only [hd] using d.noncollinear_projection_witness hIII hw hcyc hunit ζ
    (by rwa [hd]) huζ hne hne' hδ

universe u

variable {A B : Type u} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]
  [TopologicalSpace.SeparableSpace (SpatialHilbert A B)]
  {R : VonNeumannAlgebra A} {N : VonNeumannAlgebra B} {Ω : A} {ξ : B}

theorem PointedMatrixSites.spatial_universal_modular_coisometries
    (P : PointedMatrixSites N ξ twoRatioSiteParameter)
    (hsep : Function.Injective (algebraVectorMap R Ω))
    (hcyc : DenseRange (algebraVectorMap R Ω))
    (J : SpatialHilbert A B ≃ₗᵢ⋆[ℂ] SpatialHilbert A B) :
    UniversalModularCoisometries (spatialProductAlgebra R N)
      (tomitaPolarConjugation J (tensorVector ξ Ω)
        (separating_spatialProduct_vector_of_separating R N Ω ξ hsep P.separating)
        (denseRange_spatialProduct_vector R N Ω ξ hcyc P.cyclic)) := by
  let hs := separating_spatialProduct_vector_of_separating R N Ω ξ hsep P.separating
  let hc := denseRange_spatialProduct_vector R N Ω ξ hcyc P.cyclic
  let d := constructedModularConjugationData J (tensorVector ξ Ω) hs hc
    (tomitaPolarConjugation_commutant_eq J (tensorVector ξ Ω) hs hc)
  intro t ht ht1
  exact P.exists_spatial_modular_coisometries hsep hcyc J d rfl ht ht1

end

end KadisonKastler

end OAI
