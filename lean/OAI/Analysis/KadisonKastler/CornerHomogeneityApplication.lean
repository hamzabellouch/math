import OAI.Analysis.KadisonKastler.CornerHomogeneityTransfer

namespace OAI

/-! # The exact corner specialization of state homogeneity

Connes--Størmer, J. Funct. Anal. 28 (1978), 187--196, states norm
transitivity of inner automorphisms on faithful normal states of a type
III₁ factor. Its vector-state special case gives the corner application formalized here.
-/

namespace KadisonKastler

open Generator.Tracial NormedSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

def FaithfulVectorStateHomogeneity (M : VonNeumannAlgebra H) : Prop :=
  ∀ ξ ζ : H, ‖ξ‖=1 → ‖ζ‖=1 →
    Function.Injective (algebraVectorMap M ξ) →
    Function.Injective (algebraVectorMap M ζ) →
    ∀ ε : ℝ, 0 < ε → ∃ u : unitary (Algebra M),
      ‖sandwichFunctional (vectorFunctional ξ) u.val-vectorFunctional ζ‖ < ε

theorem vectorCornerState_supported (p : AlgebraProjection M) (ξ : H) :
    cornerFunctional (vectorCornerState p ξ) p.val=vectorCornerState p ξ := by
  ext a
  change (projectionVectorWeight p ξ)⁻¹ •
      (vectorFunctional (p.val.val ξ)) (p.val*a*p.val) =
    (projectionVectorWeight p ξ)⁻¹ • (vectorFunctional (p.val.val ξ)) a
  congr 1
  have h := congrArg (fun f : Algebra M →L[ℂ] ℂ => f a)
    (cornerFunctional_idempotent (vectorFunctional ξ) p.val p.property)
  rw [cornerFunctional_vectorFunctional p] at h
  exact h

theorem TypeIIIFactor.corner_comparison_of_vector_state_homogeneity
    [TopologicalSpace.SeparableSpace H] (hM : TypeIIIFactor M)
    (hhom : FaithfulVectorStateHomogeneity M) (p : AlgebraProjection M)
    (hp : p.val≠0) (ξ ζ : H)
    (hξ : Function.Injective (algebraVectorMap M ξ))
    (hζ : Function.Injective (algebraVectorMap M ζ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ w : Algebra M, star w*w=p.val ∧ w*star w=p.val ∧
      ‖sandwichFunctional (vectorCornerState p ξ) w-vectorCornerState p ζ‖ < ε := by
  obtain ⟨v,hv,hvp⟩ := hM.exists_isometry_onto_projection p.val p.property hp
  have hnξ : (star v).val ξ≠0 := by
    intro hz
    have he := isometry_pullback_norm_sq p v hvp ξ
    rw [hz,norm_zero,zero_pow (by decide)] at he
    exact (ne_of_gt (projectionVectorWeight_pos p ξ hξ hp)) he.symm
  have hnζ : (star v).val ζ≠0 := by
    intro hz
    have he := isometry_pullback_norm_sq p v hvp ζ
    rw [hz,norm_zero,zero_pow (by decide)] at he
    exact (ne_of_gt (projectionVectorWeight_pos p ζ hζ hp)) he.symm
  obtain ⟨u,hu⟩ := hhom (normalize ((star v).val ξ)) (normalize ((star v).val ζ))
    (norm_normalize hnξ) (norm_normalize hnζ)
    (normalized_isometry_pullback_separating v hv ξ hξ hnξ)
    (normalized_isometry_pullback_separating v hv ζ hζ hnζ) ε hε
  have hw := isometry_corner_unitary p v hv hvp u
  refine ⟨v*u.val*star v,hw.1,hw.2,?_⟩
  rw [corner_unitary_comparison_norm _ _ p.val v p.property hv hvp
    (isometry_norm_le_one v hv) (vectorCornerState_supported p ζ) u,
    vectorCornerState_pullback p v hv hvp ξ,vectorCornerState_pullback p v hv hvp ζ]
  exact hu

end

end KadisonKastler

end OAI
