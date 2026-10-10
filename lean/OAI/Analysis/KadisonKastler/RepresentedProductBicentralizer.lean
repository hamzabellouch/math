import OAI.Analysis.KadisonKastler.SpatialExpectedSubfactor
import OAI.Analysis.KadisonKastler.TypeIIICyclicState
import OAI.Analysis.KadisonKastler.TypeIIICountableAmplification
import OAI.Analysis.KadisonKastler.FaithfulTensorRange
import OAI.Analysis.KadisonKastler.FactorIsomorphism

namespace OAI

/-! # The constructed product state in the original representation

The faithful cyclic tensor representation embeds in countable amplification.
A commutant unitary returns it to the original space, and a support isometry
makes its vector cyclic without changing the state.
-/

namespace KadisonKastler
open Generator.Tracial UnitalTomsWinter
noncomputable section
universe u

variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H] [TopologicalSpace.SeparableSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [Nontrivial K] [TopologicalSpace.SeparableSpace K]
  {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K} {ξ : K}

local instance representedProductRealInner : InnerProductSpace ℝ (SpatialHilbert H K) :=
  InnerProductSpace.complexToReal

private theorem equivOfEq_operator {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] {A B : VonNeumannAlgebra E}
    (h : A=B) (a : Algebra A) : (vonNeumannAlgebraEquivOfEq h a).val=a.val := by
  subst B
  rfl

omit [Nontrivial K] [TopologicalSpace.SeparableSpace K] in
theorem faithfulTensorEquiv_intertwines
    (M : VonNeumannAlgebra H) (N : VonNeumannAlgebra K)
    (a : Algebra (spatialProductAlgebra M N))
    (x : SpatialHilbert (faithfulCyclicSpace M) K) :
    faithfulTensorEmbedding M ((faithfulTensorEquiv M N a).val x)=
      l2Diagonal a.val (faithfulTensorEmbedding M x) := by
  have he : (faithfulTensorEquiv M N a).val=faithfulTensorHom M N a := by
    change (vonNeumannAlgebraEquivOfEq (faithfulTensorHom_generated_range M N)
      ((boundedWeakNormalEquiv (spatialProductAlgebra M N) (faithfulTensorHom M N)
        (faithfulTensorHom_injective M N) (faithfulTensorHom_boundedWeakNormal M N)) a)).val=_
    rw [equivOfEq_operator]
    rfl
  rw [he]
  exact faithfulTensorHom_intertwines M N a x

theorem PointedMatrixSites.exists_represented_scalar_bicentralizer
    (P : PointedMatrixSites N ξ twoRatioSiteParameter)
    (hIII : TypeIIIFactor (spatialProductAlgebra M N)) :
    ∃ Ω : SpatialHilbert H K, ‖Ω‖=1 ∧
      Function.Injective (algebraVectorMap (spatialProductAlgebra M N) Ω) ∧
      DenseRange (algebraVectorMap (spatialProductAlgebra M N) Ω) ∧
      ∀ a : Algebra (spatialProductAlgebra M N),
        stateBicentralizerMember Ω a → ∃ z : ℂ, a=z • 1 := by
  let S := spatialProductAlgebra M N
  let F := tensorCompatibleCyclicRepresentation M
  let T := spatialProductAlgebra F.algebra N
  let ψ := tensorVector ξ F.vector
  let e : Algebra S ≃⋆ₐ[ℂ] Algebra T := faithfulTensorEquiv M N
  obtain ⟨U,hU⟩ := hIII.exists_countable_amplification_unitary
  let V : SpatialHilbert F.K K →ₗᵢ[ℂ] SpatialHilbert H K :=
    U.toLinearIsometry.comp (faithfulTensorEmbedding M)
  have hV (a : Algebra S) (x : SpatialHilbert F.K K) : V ((e a).val x)=a.val (V x) := by
    exact (congrArg U (faithfulTensorEquiv_intertwines M N a x)).trans
      (hU a (faithfulTensorEmbedding M x))
  have hu : ‖ψ‖=1 := by
    change ‖tensorVector ξ F.vector‖=1
    rw [norm_tensorVector_apply,F.unit_vector,P.unit_vector,mul_one]
  have hs : Function.Injective (algebraVectorMap T ψ) :=
    separating_spatialProduct_vector_of_separating F.algebra N F.vector ξ F.separating P.separating
  have hscalar : ∀ a : Algebra T, stateBicentralizerMember ψ a → ∃ z : ℂ, a=z • 1 :=
    P.spatial_state_bicentralizer_scalar F.unit_vector F.separating F.cyclic
      (hIII.of_starAlgEquiv e)
  have hs' := isometric_vector_separating e V hV ψ hs
  obtain ⟨Ω,hΩ,hΩc,hΩs,hstate⟩ := hIII.exists_cyclic_vector_same_state (V ψ)
    ((V.norm_map ψ).trans hu) hs'
  refine ⟨Ω,hΩ,hΩs,hΩc,?_⟩
  intro a ha
  exact scalar_stateBicentralizer_of_isometric e V hV ψ hscalar a
    ((stateBicentralizerMember_congr_vectorFunctional hstate a).mp ha)

theorem PointedMatrixSites.represented_expected_matrix_subfactor
    (P : PointedMatrixSites N ξ twoRatioSiteParameter)
    (hIII : TypeIIIFactor (spatialProductAlgebra M N))
    (hhom : FaithfulVectorStateHomogeneity (spatialProductAlgebra M N)) :
    Nonempty (ExpectedMatrixSubfactorModel (spatialProductAlgebra M N)) := by
  obtain ⟨Ω,hu,hs,hc,hscalar⟩ := P.exists_represented_scalar_bicentralizer hIII
  obtain ⟨J,_⟩ := exists_hilbert_conjugation (H := SpatialHilbert H K)
  let d := constructedModularConjugationData J Ω hs hc
    (tomitaPolarConjugation_commutant_eq J Ω hs hc)
  have hpos : ∀ a : Algebra (spatialProductAlgebra M N),
      0 ≤ inner ℝ Ω (modularQuadratic d.conjugation a Ω) := by
    intro a
    exact (tomitaPolarConjugation_quadratic_nonneg J Ω hs hc a).1
  exact expectedMatrixSubfactorModel_of_one_bicentralizer hIII Ω hu hs hc d hpos hhom hscalar

end
end KadisonKastler

end OAI
