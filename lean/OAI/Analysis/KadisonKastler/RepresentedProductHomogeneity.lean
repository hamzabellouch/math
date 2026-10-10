import OAI.Analysis.KadisonKastler.RepresentedProductBicentralizer
import OAI.Analysis.KadisonKastler.CoisometryStateHomogeneity
import OAI.Analysis.KadisonKastler.SpatialStateHomogeneity

namespace OAI

/-! # Constructed faithful-state homogeneity in every required representation

The modular coisometries give homogeneity on the faithful cyclic tensor
representation. A state-preserving spatial equivalence returns it to the
original tensor representation, including arbitrary multiplicity.
-/

namespace KadisonKastler
open Generator.Tracial UnitalTomsWinter
noncomputable section
universe u

section Isometric
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H] [TopologicalSpace.SeparableSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}

theorem TypeIIIFactor.exists_spatial_equiv_of_isometric (hM : TypeIIIFactor M)
    (e : Algebra M ≃⋆ₐ[ℂ] Algebra N) (V : K →ₗᵢ[ℂ] H)
    (hV : ∀ (a : Algebra M) (x : K), V ((e a).val x)=a.val (V x))
    (ψ : K) (hu : ‖ψ‖=1) (hs : Function.Injective (algebraVectorMap N ψ))
    (hc : DenseRange (algebraVectorMap N ψ)) :
    ∃ W : H ≃ₗᵢ[ℂ] K, ∀ (a : Algebra M) (x : H), W (a.val x)=(e a).val (W x) := by
  obtain ⟨Ω,_,hΩc,_,hstate⟩ := hM.exists_cyclic_vector_same_state (V ψ)
    ((V.norm_map ψ).trans hu) (isometric_vector_separating e V hV ψ hs)
  have he (a : Algebra M) : inner ℂ Ω (a.val Ω)=inner ℂ ψ ((e a).val ψ) :=
    (congrArg (fun φ : Algebra M →L[ℂ] ℂ => φ a) hstate).trans
      (isometric_vectorFunctional e V hV ψ a)
  exact ⟨statePreservingUnitary e Ω ψ hΩc hc he,
    statePreservingUnitary_intertwines e Ω ψ hΩc hc he⟩

theorem TypeIIIFactor.exists_spatial_equiv_of_amplified_isometric (hM : TypeIIIFactor M)
    (e : Algebra M ≃⋆ₐ[ℂ] Algebra N) (V : K →ₗᵢ[ℂ] CountableHilbertSum H)
    (hV : ∀ (a : Algebra M) (x : K), V ((e a).val x)=l2Diagonal a.val (V x))
    (ψ : K) (hu : ‖ψ‖=1) (hs : Function.Injective (algebraVectorMap N ψ))
    (hc : DenseRange (algebraVectorMap N ψ)) :
    ∃ W : H ≃ₗᵢ[ℂ] K, ∀ (a : Algebra M) (x : H), W (a.val x)=(e a).val (W x) := by
  obtain ⟨U,hU⟩ := hM.exists_countable_amplification_unitary
  let W : K →ₗᵢ[ℂ] H := U.toLinearIsometry.comp V
  have hW (a : Algebra M) (x : K) : W ((e a).val x)=a.val (W x) :=
    (congrArg U (hV a x)).trans (hU a (V x))
  exact hM.exists_spatial_equiv_of_isometric e W hW ψ hu hs hc

omit [Nontrivial H] [TopologicalSpace.SeparableSpace H] in
theorem faithfulStateHomogeneity_of_spatial_equiv
    (e : Algebra M ≃⋆ₐ[ℂ] Algebra N)
    (hW : ∃ W : H ≃ₗᵢ[ℂ] K,
      ∀ (a : Algebra M) (x : H), W (a.val x)=(e a).val (W x))
    (hN : FaithfulVectorStateHomogeneity N) : FaithfulVectorStateHomogeneity M := by
  obtain ⟨W,hW⟩ := hW
  apply FaithfulVectorStateHomogeneity.spatial_transport e.symm W.symm _ hN
  intro a x
  apply W.injective
  rw [W.apply_symm_apply,hW,e.apply_symm_apply,W.apply_symm_apply]
end Isometric

section Cyclic
variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [Nontrivial (SpatialHilbert H K)] [TopologicalSpace.SeparableSpace (SpatialHilbert H K)]
  {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K} {Ω : H} {ξ : K}

theorem PointedMatrixSites.spatial_state_homogeneity
    (P : PointedMatrixSites N ξ twoRatioSiteParameter)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω))
    (hIII : TypeIIIFactor (spatialProductAlgebra M N)) :
    FaithfulVectorStateHomogeneity (spatialProductAlgebra M N) := by
  let S := spatialProductAlgebra M N
  let ψ := tensorVector ξ Ω
  have hs : Function.Injective (algebraVectorMap S ψ) :=
    separating_spatialProduct_vector_of_separating M N Ω ξ hsep P.separating
  have hc : DenseRange (algebraVectorMap S ψ) :=
    denseRange_spatialProduct_vector M N Ω ξ hcyc P.cyclic
  obtain ⟨J,_⟩ := exists_hilbert_conjugation (H := SpatialHilbert H K)
  exact stateHomogeneity_of_modular_coisometries ψ hs hc J hIII
    (P.spatial_universal_modular_coisometries hsep hcyc J)
end Cyclic

section Represented
variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H] [TopologicalSpace.SeparableSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [Nontrivial K] [TopologicalSpace.SeparableSpace K]
  {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K} {ξ : K}

theorem PointedMatrixSites.exists_faithful_product_spatial_equiv
    (P : PointedMatrixSites N ξ twoRatioSiteParameter)
    (hIII : TypeIIIFactor (spatialProductAlgebra M N)) :
    ∃ W : SpatialHilbert H K ≃ₗᵢ[ℂ] SpatialHilbert (faithfulCyclicSpace M) K,
      ∀ (a : Algebra (spatialProductAlgebra M N)) (x : SpatialHilbert H K),
        W (a.val x)=(faithfulTensorEquiv M N a).val (W x) := by
  let S := spatialProductAlgebra M N
  let C := faithfulCyclicAlgebra M
  let T := spatialProductAlgebra C N
  let ψ := tensorVector ξ (faithfulCyclicVector M)
  let e : Algebra S ≃⋆ₐ[ℂ] Algebra T := faithfulTensorEquiv M N
  have hu : ‖ψ‖=1 := by
    change ‖tensorVector ξ (faithfulCyclicVector M)‖=1
    rw [norm_tensorVector_apply,norm_faithfulCyclicVector,P.unit_vector,mul_one]
  have hs : Function.Injective (algebraVectorMap T ψ) :=
    separating_spatialProduct_vector_of_separating C N (faithfulCyclicVector M) ξ
      (faithfulCyclicAlgebra_separating M) P.separating
  have hc : DenseRange (algebraVectorMap T ψ) :=
    denseRange_spatialProduct_vector C N (faithfulCyclicVector M) ξ
      (tensorCompatibleCyclicRepresentation M).cyclic P.cyclic
  exact hIII.exists_spatial_equiv_of_amplified_isometric e (faithfulTensorEmbedding M)
    (faithfulTensorEquiv_intertwines M N) ψ hu hs hc

theorem PointedMatrixSites.represented_state_homogeneity
    (P : PointedMatrixSites N ξ twoRatioSiteParameter)
    (hIII : TypeIIIFactor (spatialProductAlgebra M N)) :
    FaithfulVectorStateHomogeneity (spatialProductAlgebra M N) := by
  let C := faithfulCyclicAlgebra M
  let e : Algebra (spatialProductAlgebra M N) ≃⋆ₐ[ℂ] Algebra (spatialProductAlgebra C N) :=
    faithfulTensorEquiv M N
  have ht : FaithfulVectorStateHomogeneity (spatialProductAlgebra C N) :=
    P.spatial_state_homogeneity (M := C) (Ω := faithfulCyclicVector M)
      (faithfulCyclicAlgebra_separating M) (tensorCompatibleCyclicRepresentation M).cyclic
      (hIII.of_starAlgEquiv e)
  exact faithfulStateHomogeneity_of_spatial_equiv e
    (P.exists_faithful_product_spatial_equiv (M := M) hIII) ht

theorem PointedMatrixSites.constructed_represented_expected_matrix_subfactor
    (P : PointedMatrixSites N ξ twoRatioSiteParameter)
    (hIII : TypeIIIFactor (spatialProductAlgebra M N)) :
    Nonempty (ExpectedMatrixSubfactorModel (spatialProductAlgebra M N)) :=
  P.represented_expected_matrix_subfactor hIII (P.represented_state_homogeneity hIII)
end Represented

end
end KadisonKastler

end OAI
