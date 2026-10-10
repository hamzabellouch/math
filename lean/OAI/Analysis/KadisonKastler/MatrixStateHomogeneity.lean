import OAI.Analysis.KadisonKastler.PositiveProjectionState
import OAI.Analysis.KadisonKastler.TwoCornerHomogeneity
import OAI.Analysis.KadisonKastler.ConjugatedMatrixInsertion

namespace OAI

/-! # Nearby matrix-central states from the exact homogeneity input

This constructs the state approximation in Haagerup's Lemma3.6 from
Connes--Størmer homogeneity. The finite matrix algebra and its positive
vector are constructed. The homogeneity input remains explicit and is
not discharged by this adapter.
-/

namespace KadisonKastler

open Generator Generator.Tracial
open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

local instance matrixStateHomogeneityRealInner : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

theorem TypeIIIFactor.exists_nearby_positive_matrix_central_state
    (hM : TypeIIIFactor M) (hhom : FaithfulVectorStateHomogeneity M)
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ=ξ)
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    (η : H) (hη : η ∈ modularPositiveCone (M := M) J ξ) (hηnorm : ‖η‖=1)
    (hηsep : Function.Injective (algebraVectorMap M η))
    (p : AlgebraProjection M) (hp0 : p.val≠0) (hp1 : p.val≠1)
    (hpη : p.val.val η=conjugationOperator J p.val.val η)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (r s : ℕ) (F : MatrixUnitSystem (Fin (r+1) ⊕ Fin (s+1)) (Algebra M)) (ζ : H),
      p.val ∈ F.algebra ∧ ‖ζ‖=1 ∧ ζ ∈ modularPositiveCone (M := M) J ξ ∧
      Function.Injective (algebraVectorMap M ζ) ∧
      ζ ∈ centralVectorSpace (matrixUnitConcreteAlgebra F) J ∧
      ‖vectorFunctional (M := M) ζ-vectorFunctional η‖ < ε := by
  have ht := projectionVectorWeight_mem_Ioo p η hηsep hηnorm hp0 hp1
  obtain ⟨r,s,E,ζ,hE,hζnorm,hζcone,hζsep,_,hζcentral,hweight⟩ :=
    hM.exists_positive_matrix_state_near_projection_weight J hJ hright hleft ξ hξ hpos
      hη hηnorm hηsep p hp0 hp1 (projectionVectorWeight p η) (ε/3) ht.1 ht.2
      (by positivity)
  have hpE : p.val ∈ E.algebra := by
    rw [← hE]
    exact E.algebra.sum_mem (fun i _ => E.entry_mem _ _)
  have hζp := matrixCentralVector_projection_state E J hJ hright ζ hζcentral p hpE
  have hηp := vectorFunctional_centralizes_projection J hJ hright p η hpη
  obtain ⟨u,hup,huclose⟩ := hM.central_projection_state_comparison hhom p hp0 hp1 ζ η
    hζsep hζnorm hηsep hηnorm hζp hηp (ε/3) (by positivity)
  let F := unitaryConjugateMatrixUnits E u
  let ω := (modularUnitary J hJ u : H →L[ℂ] H) ζ
  have hw : |projectionVectorWeight p ζ-projectionVectorWeight p η| < ε/3 := by
    have he := congrArg Complex.re (vectorFunctional_projection p ζ)
    change (inner ℂ ζ (p.val.val ζ)).re=(projectionVectorWeight p ζ : ℂ).re at he
    rw [Complex.ofReal_re] at he
    rwa [he] at hweight
  refine ⟨r,s,F,ω,unitaryConjugateMatrixUnits_contains_projection E u p hpE hup,
    (Unitary.norm_map _ ζ).trans hζnorm,?_,?_,?_,?_⟩
  · exact modularQuadratic_preserves_positiveCone J hJ hright ξ u.val hζcone
  · exact modularUnitary_vector_separating J hJ hright u ζ hζsep
  · exact modularUnitary_matrix_central J hJ hright E u hζcentral
  · change ‖vectorFunctional (M := M) ((modularUnitary J hJ u : H →L[ℂ] H) ζ)-
      vectorFunctional η‖ < ε
    rw [modularUnitary_vectorFunctional J hJ hright]
    linarith

end

end KadisonKastler

end OAI
