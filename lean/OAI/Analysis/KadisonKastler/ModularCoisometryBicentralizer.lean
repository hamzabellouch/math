import OAI.Analysis.KadisonKastler.ProjectionCentralScalar
import OAI.Analysis.KadisonKastler.StateBicentralizerTests

namespace OAI

/-! # Scalar bicentralizers from the constructed modular coisometries

Only the fixed reference state is used. No state homogeneity, absorption
classification, or scalar-bicentralizer premise enters this implication.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H] [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

local instance coisometryBicentralizerRealInner : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

theorem vector_bicentralizer_scalar_of_modular_coisometries
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ=ξ) (huξ : ‖ξ‖=1)
    (hsep : Function.Injective (algebraVectorMap M ξ))
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    (hIII : TypeIIIFactor M) (hremote : UniversalModularCoisometries M J)
    (a : Algebra M) (ha : vectorBicentralizerMember J ξ a) :
    ∃ z : ℂ, a=z • 1 := by
  obtain ⟨z,hz⟩ := projectionCentralSpace_scalar J hJ hright hleft ξ hξ huξ hsep hpos
    hIII hremote (a.val ξ) (bicentralizer_vector_mem_projectionCentralSpace J hJ hright ξ hξ a ha)
  refine ⟨z,hsep ?_⟩
  change a.val ξ=(z • (1 : Algebra M)).val ξ
  simpa only [SetLike.val_smul,OneMemClass.coe_one,smul_apply,one_apply_eq_self] using hz

theorem state_bicentralizer_scalar_of_modular_coisometries
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ=ξ) (huξ : ‖ξ‖=1)
    (hsep : Function.Injective (algebraVectorMap M ξ))
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    (hIII : TypeIIIFactor M) (hremote : UniversalModularCoisometries M J)
    (a : Algebra M) (ha : stateBicentralizerMember ξ a) :
    ∃ z : ℂ, a=z • 1 := by
  apply vector_bicentralizer_scalar_of_modular_coisometries J hJ hright hleft ξ hξ huξ hsep
    hpos hIII hremote a
  intro x hx
  exact ha x (hx.state_commutator hJ hright hξ)

end

end KadisonKastler

end OAI
