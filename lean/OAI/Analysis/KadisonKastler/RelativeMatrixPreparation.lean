import OAI.Analysis.KadisonKastler.RelativeMatrixStateHomogeneity
import OAI.Analysis.KadisonKastler.RelativePositivePinching

namespace OAI

/-! # A nearby relative matrix stage containing an almost-central projection

Relative Powers–Størmer converts state approximation into approximation
on the original Hilbert space. The resulting stage extends the initial one.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

local instance relativePreparationRealInner : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

theorem TypeIIIFactor.exists_relative_matrix_state_of_projection_gap
    (hM : TypeIIIFactor M) (E : FiniteMatrixStage M)
    (hhom : FaithfulVectorStateHomogeneity E.units.relativeVonNeumann)
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ=ξ)
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    (η : H) (hη : η ∈ modularPositiveCone (M := M) J ξ) (hηnorm : ‖η‖=1)
    (hηsep : Function.Injective (algebraVectorMap M η))
    (hηE : η ∈ centralVectorSpace (matrixUnitConcreteAlgebra E.units) J)
    (p : AlgebraProjection E.units.relativeVonNeumann) (hp0 : p.val≠0) (hp1 : p.val≠1)
    (hgap : ‖p.val.val η-conjugationOperator J p.val.val η‖ < 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (r s : ℕ)
      (F : MatrixUnitSystem (Fin (r+1) ⊕ Fin (s+1)) (Algebra E.units.relativeVonNeumann))
      (ζ : H), p.val ∈ F.algebra ∧ ‖ζ‖=1 ∧ ζ ∈ modularPositiveCone (M := M) J ξ ∧
      Function.Injective (algebraVectorMap M ζ) ∧
      ζ ∈ centralVectorSpace (matrixUnitConcreteAlgebra E.units) J ∧
      ζ ∈ centralVectorSpace (matrixUnitConcreteAlgebra F) J ∧
      ‖vectorFunctional (M := E.units.relativeVonNeumann) ζ-vectorFunctional η‖ <
        ε+4*‖p.val.val η-conjugationOperator J p.val.val η‖ := by
  obtain ⟨ω,hωn,hωc,hωs,_,hωp,hωclose⟩ :=
    exists_relative_positive_projection_central_unit_vector E J hJ hright ξ hξ hpos
      η hη hηnorm hηsep hηE p hgap
  obtain ⟨r,s,F,ζ,hpF,hζn,hζc,hζs,hζE,hζF,hstate⟩ :=
    hM.exists_relative_nearby_positive_matrix_central_state E hhom J hJ hright hleft ξ hξ
      hpos ω hωc hωn hωs p hp0 hp1 hωp ε hε
  refine ⟨r,s,F,ζ,hpF,hζn,hζc,hζs,hζE,hζF,?_⟩
  have hn := vectorFunctional_norm_sub_le (M := E.units.relativeVonNeumann) ω η
  rw [hωn,hηnorm] at hn
  have hs : ‖vectorFunctional (M := E.units.relativeVonNeumann) ω-vectorFunctional η‖ ≤
      4*‖p.val.val η-conjugationOperator J p.val.val η‖ := by nlinarith
  calc
    _ = ‖(vectorFunctional (M := E.units.relativeVonNeumann) ζ-vectorFunctional ω)+
        (vectorFunctional ω-vectorFunctional η)‖ := by congr 1; abel
    _ ≤ ‖vectorFunctional (M := E.units.relativeVonNeumann) ζ-vectorFunctional ω‖+
        ‖vectorFunctional ω-vectorFunctional η‖ := norm_add_le _ _
    _ < _ := by linarith

theorem TypeIIIFactor.exists_relative_matrix_stage_near_projection
    (hM : TypeIIIFactor M) (E : FiniteMatrixStage M)
    (hhom : FaithfulVectorStateHomogeneity E.units.relativeVonNeumann)
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ=ξ) (hcyc : DenseRange (algebraVectorMap M ξ))
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    (η : H) (hη : η ∈ modularPositiveCone (M := M) J ξ) (hηnorm : ‖η‖=1)
    (hηsep : Function.Injective (algebraVectorMap M η))
    (hηE : η ∈ centralVectorSpace (matrixUnitConcreteAlgebra E.units) J)
    (p : AlgebraProjection E.units.relativeVonNeumann) (hp0 : p.val≠0) (hp1 : p.val≠1)
    (hgap : ‖p.val.val η-conjugationOperator J p.val.val η‖ < 1)
    (ε : ℝ) (hε : 0 < ε)
    (hsmall : ‖p.val.val η-conjugationOperator J p.val.val η‖ < ε^2/8) :
    ∃ (F : FiniteMatrixStage M) (ζ : H),
      E.units.concreteAlgebra ≤ F.units.concreteAlgebra ∧
      p.val.val ∈ F.units.concreteAlgebra ∧ ‖ζ‖=1 ∧
      ζ ∈ modularPositiveCone (M := M) J ξ ∧
      Function.Injective (algebraVectorMap M ζ) ∧
      ζ ∈ centralVectorSpace (matrixUnitConcreteAlgebra F.units) J ∧ ‖ζ-η‖ < ε := by
  classical
  let : Nonempty (Fin E.size) := ⟨⟨0,E.positive⟩⟩
  obtain ⟨r,s,G,ζ,hpG,hζn,hζc,hζs,hζE,hζG,hstate⟩ :=
    hM.exists_relative_matrix_state_of_projection_gap E hhom J hJ hright hleft ξ hξ hpos
      η hη hηnorm hηsep hηE p hp0 hp1 hgap (ε^2/2) (by positivity)
  have hdist := relative_positiveCone_norm_sq_le_state_norm E.units J hJ hright hleft
    ξ hξ hcyc hpos hζc hη hζE hηE
  have hclose : ‖ζ-η‖ < ε := by nlinarith [norm_nonneg (ζ-η)]
  let e : Fin (Fintype.card (Fin (r+1) ⊕ Fin (s+1))) ≃ (Fin (r+1) ⊕ Fin (s+1)) :=
    (Fintype.equivFin _).symm
  let G' : FiniteMatrixStage E.units.relativeVonNeumann :=
    ⟨_,Fintype.card_pos,G.reindex e⟩
  have hζG' : ζ ∈ centralVectorSpace (matrixUnitConcreteAlgebra G'.units) J := by
    apply (mem_centralVectorSpace_matrix_iff G'.units J ζ).mpr
    intro i j
    exact (mem_centralVectorSpace_matrix_iff G J ζ).mp hζG (e i) (e j)
  have hpG' : p.val.val ∈ G'.units.concreteAlgebra := by
    apply ((G.reindex e).mem_concreteAlgebra p.val).mpr
    rwa [G.reindex_algebra e]
  exact ⟨relativeMatrixExtension E G',ζ,relativeMatrixExtension_contains_left E G',
    relativeMatrixExtension_contains_right E G' hpG',hζn,hζc,hζs,
    relativeMatrixExtension_central E G' J hJ hright ζ hζE hζG',hclose⟩

end

end KadisonKastler

end OAI
