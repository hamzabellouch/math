import OAI.Analysis.KadisonKastler.PositiveStateRepresentative
import OAI.Analysis.KadisonKastler.ModularCoisometryBicentralizer
import OAI.Analysis.KadisonKastler.SpatialBicentralizer
import OAI.Analysis.KadisonKastler.PositiveReferenceModular

namespace OAI

/-! # All faithful vector states under the constructed modular coisometries

Positive state representation keeps the same modular conjugation. Thus the
fixed-conjugation coisometry argument applies at every faithful vector state,
without assuming state homogeneity.
-/

namespace KadisonKastler
open Generator.Tracial
noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H] [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

local instance faithfulCoisometryReal : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

theorem faithful_bicentralizers_scalar_of_modular_coisometries
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (Ω : H) (hΩ : J Ω=Ω)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω))
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ Ω (modularQuadratic J a Ω))
    (hIII : TypeIIIFactor M) (hremote : UniversalModularCoisometries M J) :
    FaithfulVectorBicentralizersScalar M := by
  have hp : tomitaPolarConjugation J Ω hsep hcyc=J :=
    tomitaPolarConjugation_eq_of_quadratic_positive J hJ hright hleft Ω hΩ hsep hcyc
      (positiveCone_quadratic_complex_nonneg J hJ hright Ω hΩ hpos
        (reference_mem_modularPositiveCone J hJ Ω))
  intro ξ hξ hξsep a ha
  obtain ⟨η,hη,hηunit,hηsep,_,hstate⟩ :=
    hIII.exists_positive_unit_state_representative Ω hcyc hsep J ξ hξ hξsep
  change η ∈ modularPositiveCone (M := M) (tomitaPolarConjugation J Ω hsep hcyc) Ω at hη
  rw [hp] at hη
  exact state_bicentralizer_scalar_of_modular_coisometries J hJ hright hleft η
    (modularPositiveCone_fixed J hright Ω hΩ hη) hηunit hηsep
    (fun b => positiveCone_quadratic_nonneg J hJ hright Ω hpos hη b) hIII hremote a
    ((stateBicentralizerMember_congr_vectorFunctional hstate a).mpr ha)

end
end KadisonKastler

end OAI
