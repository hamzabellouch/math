import OAI.Analysis.KadisonKastler.RelativePositiveDecomposition

namespace OAI

/-! # The state-to-vector estimate in a finite-matrix relative commutant

The positive parts remain in the central-vector space. Their support
reflection belongs to the relative algebra, so its restricted state norm
already controls the ambient vector distance.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}
  {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

local instance relativePowersStormerRealInner : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

theorem relative_positiveCone_norm_sq_le_state_norm
    (E : MatrixUnitSystem ι (Algebra M))
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ=ξ) (hcyc : DenseRange (algebraVectorMap M ξ))
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    {η ζ : H} (hη : η ∈ modularPositiveCone (M := M) J ξ)
    (hζ : ζ ∈ modularPositiveCone (M := M) J ξ)
    (hηE : η ∈ centralVectorSpace (matrixUnitConcreteAlgebra E) J)
    (hζE : ζ ∈ centralVectorSpace (matrixUnitConcreteAlgebra E) J) :
    ‖η-ζ‖^2 ≤ ‖vectorFunctional (M := E.relativeVonNeumann) η-vectorFunctional ζ‖ := by
  have hfixed : J (η-ζ)=η-ζ := by
    rw [map_sub,modularPositiveCone_fixed J hright ξ hξ hη,
      modularPositiveCone_fixed J hright ξ hξ hζ]
  obtain ⟨α,β,hα,hβ,hαE,_,horth,heq⟩ := exists_relative_positive_decomposition
    E J hJ hright hleft ξ hξ hcyc hpos (η-ζ) hfixed
      ((centralVectorSpace (matrixUnitConcreteAlgebra E) J).sub_mem hηE hζE)
  let p := vectorSupportProjection M α
  let q : AlgebraProjection E.relativeVonNeumann :=
    ⟨⟨p.val.val,vectorSupportProjection_mem_relative E J hright α hαE⟩,by
      constructor
      · apply Subtype.ext
        exact congrArg (fun a : Algebra M => a.val) p.property.isIdempotentElem.eq
      · apply Subtype.ext
        exact congrArg (fun a : Algebra M => a.val) p.property.isSelfAdjoint.star_eq⟩
  apply norm_sq_le_vectorState_norm_of_projection η ζ α β heq q
  · exact vectorSupportProjection_apply M α
  · exact positiveCone_support_kills_of_orthogonal J hJ hright hleft ξ hξ hpos hα hβ horth
  · exact modularPositiveCone_acute J hJ hright ξ hpos hα hζ
  · exact modularPositiveCone_acute J hJ hright ξ hpos hβ hη

end

end KadisonKastler

end OAI
