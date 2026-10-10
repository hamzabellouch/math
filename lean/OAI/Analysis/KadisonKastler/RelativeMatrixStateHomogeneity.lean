import OAI.Analysis.KadisonKastler.RelativeRankMatrixState
import OAI.Analysis.KadisonKastler.MatrixStateHomogeneity

namespace OAI

/-! # Faithful matrix-state approximation in a relative algebra

The matrix comparison is performed in the relative algebra, while positivity,
faithfulness and the central-vector conditions stay on the original space.
Connes–Størmer homogeneity remains an explicit input.
-/

namespace KadisonKastler

open Generator Generator.Tracial
open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

local instance relativeMatrixHomogeneityRealInner : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

theorem TypeIIIFactor.exists_relative_nearby_positive_matrix_central_state
    (hM : TypeIIIFactor M) (E : FiniteMatrixStage M)
    (hhom : FaithfulVectorStateHomogeneity E.units.relativeVonNeumann)
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ=ξ)
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    (η : H) (hη : η ∈ modularPositiveCone (M := M) J ξ) (hηnorm : ‖η‖=1)
    (hηsep : Function.Injective (algebraVectorMap M η))
    (p : AlgebraProjection E.units.relativeVonNeumann) (hp0 : p.val≠0) (hp1 : p.val≠1)
    (hpη : p.val.val η=conjugationOperator J p.val.val η)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (r s : ℕ)
      (F : MatrixUnitSystem (Fin (r+1) ⊕ Fin (s+1)) (Algebra E.units.relativeVonNeumann))
      (ζ : H), p.val ∈ F.algebra ∧ ‖ζ‖=1 ∧ ζ ∈ modularPositiveCone (M := M) J ξ ∧
      Function.Injective (algebraVectorMap M ζ) ∧
      ζ ∈ centralVectorSpace (matrixUnitConcreteAlgebra E.units) J ∧
      ζ ∈ centralVectorSpace (matrixUnitConcreteAlgebra F) J ∧
      ‖vectorFunctional (M := E.units.relativeVonNeumann) ζ-vectorFunctional η‖ < ε := by
  let : Nonempty (Fin E.size) := ⟨⟨0,E.positive⟩⟩
  have hsepη := relative_vector_separating E.units η hηsep
  have ht := projectionVectorWeight_mem_Ioo p η hsepη hηnorm hp0 hp1
  obtain ⟨r,s,F,ζ,hF,hζnorm,hζcone,hζsep,hζE,hζF,hweight⟩ :=
    hM.exists_relative_positive_matrix_state_near_weight E J hJ hright hleft ξ hξ hpos
      hη hηnorm hηsep p hp0 hp1 (projectionVectorWeight p η) (ε/3) ht.1 ht.2
      (by positivity)
  have hpF : p.val ∈ F.algebra := by
    rw [← hF]
    exact F.algebra.sum_mem (fun i _ => F.entry_mem _ _)
  have hrightN := relative_conjugation_mem_commutant E.units J hright
  have hζp := matrixCentralVector_projection_state F J hJ hrightN ζ hζF p hpF
  have hηp := vectorFunctional_centralizes_projection J hJ hrightN p η hpη
  obtain ⟨u,hup,huclose⟩ := (hM.relative_matrix E).central_projection_state_comparison
    hhom p hp0 hp1 ζ η (relative_vector_separating E.units ζ hζsep) hζnorm
    hsepη hηnorm hζp hηp (ε/3) (by positivity)
  let G := unitaryConjugateMatrixUnits F u
  let ω := (modularUnitary J hJ u : H →L[ℂ] H) ζ
  let uM : unitary (Algebra M) :=
    Unitary.map (StarMonoidHom.ofClass
      (StarSubalgebra.inclusion E.units.relativeVonNeumann_le)) u
  have hw : |projectionVectorWeight p ζ-projectionVectorWeight p η| < ε/3 := by
    have he := congrArg Complex.re (vectorFunctional_projection p ζ)
    change (inner ℂ ζ (p.val.val ζ)).re=(projectionVectorWeight p ζ : ℂ).re at he
    rw [Complex.ofReal_re] at he
    rwa [he] at hweight
  refine ⟨r,s,G,ω,unitaryConjugateMatrixUnits_contains_projection F u p hpF hup,
    (Unitary.norm_map _ ζ).trans hζnorm,?_,?_,?_,?_,?_⟩
  · exact modularQuadratic_preserves_positiveCone J hJ hright ξ uM.val hζcone
  · exact modularUnitary_vector_separating J hJ hright uM ζ hζsep
  · exact relative_modularQuadratic_mem_central E.units J hJ hright u.val hζE
  · exact modularUnitary_matrix_central J hJ hrightN F u hζF
  · change ‖vectorFunctional (M := E.units.relativeVonNeumann)
        ((modularUnitary J hJ u : H →L[ℂ] H) ζ)-vectorFunctional η‖ < ε
    rw [modularUnitary_vectorFunctional J hJ hrightN]
    linarith

end

end KadisonKastler

end OAI
