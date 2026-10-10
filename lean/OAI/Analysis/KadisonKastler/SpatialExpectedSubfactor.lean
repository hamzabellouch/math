import OAI.Analysis.KadisonKastler.SpatialScalarBicentralizer
import OAI.Analysis.KadisonKastler.ExpectedFromOneBicentralizer

namespace OAI

/-! # The two-ratio product has the required expected subfactor

Faithful-state homogeneity of the product factor transports its
reference-state bicentralizer to the required faithful state.
-/

namespace KadisonKastler

open Generator.Tracial UnitalTomsWinter

noncomputable section

universe u

variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [Nontrivial (SpatialHilbert H K)] [TopologicalSpace.SeparableSpace (SpatialHilbert H K)]
  {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K} {Ω : H} {ξ : K}

local instance spatialExpectedRealInner : InnerProductSpace ℝ (SpatialHilbert H K) :=
  InnerProductSpace.complexToReal

theorem PointedMatrixSites.spatial_expected_matrix_subfactor
    (P : PointedMatrixSites N ξ twoRatioSiteParameter)
    (hunit : ‖Ω‖=1) (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω))
    (hIII : TypeIIIFactor (spatialProductAlgebra M N))
    (hhom : FaithfulVectorStateHomogeneity (spatialProductAlgebra M N)) :
    Nonempty (ExpectedMatrixSubfactorModel (spatialProductAlgebra M N)) := by
  let S := spatialProductAlgebra M N
  let ψ := tensorVector ξ Ω
  have hs : Function.Injective (algebraVectorMap S ψ) :=
    separating_spatialProduct_vector_of_separating M N Ω ξ hsep P.separating
  have hc : DenseRange (algebraVectorMap S ψ) :=
    denseRange_spatialProduct_vector M N Ω ξ hcyc P.cyclic
  have hu : ‖ψ‖=1 := by
    change ‖tensorVector ξ Ω‖=1
    rw [norm_tensorVector_apply,hunit,P.unit_vector,mul_one]
  obtain ⟨J,_⟩ := exists_hilbert_conjugation (H := SpatialHilbert H K)
  let d := constructedModularConjugationData J ψ hs hc
    (tomitaPolarConjugation_commutant_eq J ψ hs hc)
  have hpos : ∀ a : Algebra S, 0 ≤ inner ℝ ψ (modularQuadratic d.conjugation a ψ) := by
    intro a
    exact (tomitaPolarConjugation_quadratic_nonneg J ψ hs hc a).1
  exact expectedMatrixSubfactorModel_of_one_bicentralizer hIII ψ hu hs hc d hpos hhom
    (fun a ha => P.spatial_state_bicentralizer_scalar hunit hsep hcyc hIII a ha)

end

end KadisonKastler

end OAI
