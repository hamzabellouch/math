import OAI.Analysis.KadisonKastler.MatrixStateHomogeneity

namespace OAI

/-! # State approximation by a finite matrix centralizer

Two-sided vector pinching centralizes an almost-central projection.
The constructed matrix state then differs from the original vector
state by at most the requested error plus four times the projection gap.
Connes--Størmer homogeneity is retained as its exact explicit input.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

local instance matrixStatePreparationRealInner : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

theorem TypeIIIFactor.exists_matrix_state_of_projection_gap
    (hM : TypeIIIFactor M) (hhom : FaithfulVectorStateHomogeneity M)
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ=ξ) (hunit : ‖ξ‖=1)
    (hsep : Function.Injective (algebraVectorMap M ξ))
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    (p : AlgebraProjection M) (hp0 : p.val≠0) (hp1 : p.val≠1)
    (hgap : ‖p.val.val ξ-conjugationOperator J p.val.val ξ‖ < 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (r s : ℕ) (E : MatrixUnitSystem (Fin (r+1) ⊕ Fin (s+1)) (Algebra M)) (ζ : H),
      p.val ∈ E.algebra ∧ ‖ζ‖=1 ∧ ζ ∈ modularPositiveCone (M := M) J ξ ∧
      Function.Injective (algebraVectorMap M ζ) ∧
      ζ ∈ centralVectorSpace (matrixUnitConcreteAlgebra E) J ∧
      ‖vectorFunctional (M := M) ζ-vectorFunctional ξ‖ <
        ε+4*‖p.val.val ξ-conjugationOperator J p.val.val ξ‖ := by
  obtain ⟨η,hηn,hηc,hηs,hηp,hηclose⟩ :=
    exists_positive_projection_central_unit_vector J hJ hright ξ hξ hunit hsep hpos p hgap
  obtain ⟨r,s,E,ζ,hpE,hζn,hζc,hζs,hζE,hstate⟩ :=
    hM.exists_nearby_positive_matrix_central_state hhom J hJ hright hleft ξ hξ hpos
      η hηc hηn hηs p hp0 hp1 hηp ε hε
  refine ⟨r,s,E,ζ,hpE,hζn,hζc,hζs,hζE,?_⟩
  have hnorm := vectorFunctional_norm_sub_le (M := M) η ξ
  rw [hηn,hunit] at hnorm
  have hsmall : ‖vectorFunctional (M := M) η-vectorFunctional ξ‖ ≤
      4*‖p.val.val ξ-conjugationOperator J p.val.val ξ‖ := by nlinarith
  calc
    _ = ‖(vectorFunctional (M := M) ζ-vectorFunctional η)+
        (vectorFunctional η-vectorFunctional ξ)‖ := by congr 1; abel
    _ ≤ ‖vectorFunctional (M := M) ζ-vectorFunctional η‖+
        ‖vectorFunctional η-vectorFunctional ξ‖ := norm_add_le _ _
    _ < _ := by linarith

end

end KadisonKastler

end OAI
