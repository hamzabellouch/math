import OAI.Analysis.KadisonKastler.FaithfulCoisometryBicentralizers
import OAI.Analysis.KadisonKastler.SpatialScalarBicentralizer

namespace OAI

/-! # Faithful bicentralizers in the concrete two-ratio tensor product -/

namespace KadisonKastler
open Generator.Tracial UnitalTomsWinter
noncomputable section
universe u

variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [Nontrivial (SpatialHilbert H K)] [TopologicalSpace.SeparableSpace (SpatialHilbert H K)]
  {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K} {Ω : H} {ξ : K}

local instance spatialFaithfulReal : InnerProductSpace ℝ (SpatialHilbert H K) :=
  InnerProductSpace.complexToReal

theorem PointedMatrixSites.spatial_faithful_bicentralizers_scalar
    (P : PointedMatrixSites N ξ twoRatioSiteParameter)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω))
    (hIII : TypeIIIFactor (spatialProductAlgebra M N)) :
    FaithfulVectorBicentralizersScalar (spatialProductAlgebra M N) := by
  let S := spatialProductAlgebra M N
  let ψ := tensorVector ξ Ω
  have hs : Function.Injective (algebraVectorMap S ψ) :=
    separating_spatialProduct_vector_of_separating M N Ω ξ hsep P.separating
  have hc : DenseRange (algebraVectorMap S ψ) :=
    denseRange_spatialProduct_vector M N Ω ξ hcyc P.cyclic
  obtain ⟨J,_⟩ := exists_hilbert_conjugation (H := SpatialHilbert H K)
  let d := constructedModularConjugationData J ψ hs hc
    (tomitaPolarConjugation_commutant_eq J ψ hs hc)
  apply faithful_bicentralizers_scalar_of_modular_coisometries d.conjugation d.involutive
    (d.right_mem le_rfl) d.left_mem ψ d.fixes_vector hs hc
  · intro a
    exact (tomitaPolarConjugation_quadratic_nonneg J ψ hs hc a).1
  · exact hIII
  · exact P.spatial_universal_modular_coisometries hsep hcyc J

end
end KadisonKastler

end OAI
