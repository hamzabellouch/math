import OAI.Analysis.KadisonKastler.MatrixStatePreparation
import OAI.Analysis.KadisonKastler.PositiveConePowersStormer

namespace OAI

/-! # Nearby positive matrix-central vectors

The proved Powers–Størmer inequality turns the two-corner state comparison
into the vector comparison required by finite-matrix refinement.
Connes–Størmer homogeneity remains the explicit published premise.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

local instance matrixVectorPreparationRealInner : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

theorem TypeIIIFactor.exists_matrix_vector_of_projection_gap
    (hM : TypeIIIFactor M) (hhom : FaithfulVectorStateHomogeneity M)
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ=ξ) (hunit : ‖ξ‖=1)
    (hsep : Function.Injective (algebraVectorMap M ξ))
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    (p : AlgebraProjection M) (hp0 : p.val≠0) (hp1 : p.val≠1)
    (hgap : ‖p.val.val ξ-conjugationOperator J p.val.val ξ‖ < 1)
    (ε : ℝ) (hε : 0 < ε)
    (hsmall : ‖p.val.val ξ-conjugationOperator J p.val.val ξ‖ < ε^2/8) :
    ∃ (r s : ℕ) (E : MatrixUnitSystem (Fin (r+1) ⊕ Fin (s+1)) (Algebra M)) (ζ : H),
      p.val ∈ E.algebra ∧ ‖ζ‖=1 ∧ ζ ∈ modularPositiveCone (M := M) J ξ ∧
      Function.Injective (algebraVectorMap M ζ) ∧
      ζ ∈ centralVectorSpace (matrixUnitConcreteAlgebra E) J ∧ ‖ζ-ξ‖ < ε := by
  obtain ⟨r,s,E,ζ,hpE,hζn,hζc,hζs,hζE,hstate⟩ :=
    hM.exists_matrix_state_of_projection_gap hhom J hJ hright hleft ξ hξ hunit hsep hpos
      p hp0 hp1 hgap (ε^2/2) (by positivity)
  have hcyc := cyclic_of_separating_of_conjugation_fixed J hJ hleft hξ hsep
  have hdist := positiveCone_norm_sq_le_state_norm J hJ hright hleft ξ hξ hcyc hpos
    hζc (reference_mem_modularPositiveCone J hJ ξ)
  refine ⟨r,s,E,ζ,hpE,hζn,hζc,hζs,hζE,?_⟩
  nlinarith [norm_nonneg (ζ-ξ)]

/-- The comparison matrix is packaged as a concrete finite stage. -/
theorem TypeIIIFactor.exists_matrix_stage_near_projection
    (hM : TypeIIIFactor M) (hhom : FaithfulVectorStateHomogeneity M)
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ=ξ) (hunit : ‖ξ‖=1)
    (hsep : Function.Injective (algebraVectorMap M ξ))
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    (p : AlgebraProjection M) (hp0 : p.val≠0) (hp1 : p.val≠1)
    (hgap : ‖p.val.val ξ-conjugationOperator J p.val.val ξ‖ < 1)
    (ε : ℝ) (hε : 0 < ε)
    (hsmall : ‖p.val.val ξ-conjugationOperator J p.val.val ξ‖ < ε^2/8) :
    ∃ (F : FiniteMatrixStage M) (ζ : H), p.val.val ∈ F.units.concreteAlgebra ∧
      ‖ζ‖=1 ∧ ζ ∈ modularPositiveCone (M := M) J ξ ∧
      Function.Injective (algebraVectorMap M ζ) ∧
      ζ ∈ centralVectorSpace (matrixUnitConcreteAlgebra F.units) J ∧ ‖ζ-ξ‖ < ε := by
  classical
  obtain ⟨r,s,E,ζ,hpE,hζn,hζc,hζs,hζE,hdist⟩ :=
    hM.exists_matrix_vector_of_projection_gap hhom J hJ hright hleft ξ hξ hunit hsep hpos
      p hp0 hp1 hgap ε hε hsmall
  let e : Fin (Fintype.card (Fin (r+1) ⊕ Fin (s+1))) ≃ (Fin (r+1) ⊕ Fin (s+1)) :=
    (Fintype.equivFin _).symm
  let F : FiniteMatrixStage M := ⟨_,Fintype.card_pos,E.reindex e⟩
  refine ⟨F,ζ,?_,hζn,hζc,hζs,?_,hdist⟩
  · apply ((E.reindex e).mem_concreteAlgebra p.val).mpr
    rwa [E.reindex_algebra e]
  · apply (mem_centralVectorSpace_matrix_iff F.units J ζ).mpr
    intro i j
    exact (mem_centralVectorSpace_matrix_iff E J ζ).mp hζE (e i) (e j)

end

end KadisonKastler

end OAI
