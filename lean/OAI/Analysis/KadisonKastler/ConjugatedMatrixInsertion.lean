import OAI.Analysis.KadisonKastler.PositiveUnitaryTransport
import OAI.Analysis.KadisonKastler.RelativeMatrixExtension

namespace OAI

/-! # Finite matrix insertion from a positive-vector comparison

A unitary commuting with the prescribed projection carries a matrix
algebra containing that projection to another such matrix algebra.
The quadratic vector transport supplies its actual central unit vector.
-/

namespace KadisonKastler

open Generator Generator.Tracial
open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}
  {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem unitaryConjugateMatrixUnits_hom (E : MatrixUnitSystem ι (Algebra M))
    (u : unitary (Algebra M)) (a : Matrix ι ι ℂ) :
    (unitaryConjugateMatrixUnits E u).hom a =
      Unitary.conjStarAlgAut ℂ (Algebra M) u (E.hom a) := by
  rw [E.hom_apply,map_sum]
  simp_rw [map_sum,map_smul]
  rfl

theorem mem_unitaryConjugateMatrixUnits (E : MatrixUnitSystem ι (Algebra M))
    (u : unitary (Algebra M)) (a : Algebra M) (ha : a ∈ E.algebra) :
    Unitary.conjStarAlgAut ℂ (Algebra M) u a ∈ (unitaryConjugateMatrixUnits E u).algebra := by
  obtain ⟨b,rfl⟩ := ha
  exact ⟨b,unitaryConjugateMatrixUnits_hom E u b⟩

theorem unitaryConjugateMatrixUnits_contains_projection
    (E : MatrixUnitSystem ι (Algebra M)) (u : unitary (Algebra M))
    (p : AlgebraProjection M) (hp : p.val ∈ E.algebra)
    (hcomm : u.val*p.val=p.val*u.val) :
    p.val ∈ (unitaryConjugateMatrixUnits E u).algebra := by
  have h := mem_unitaryConjugateMatrixUnits E u p.val hp
  have he : Unitary.conjStarAlgAut ℂ (Algebra M) u p.val = p.val := by
    change u.val*p.val*star u.val = p.val
    rw [hcomm,mul_assoc,u.property.2,mul_one]
  rwa [he] at h

variable [Nonempty ι]

theorem exists_matrix_stage_of_conjugated_vector
    (E : MatrixUnitSystem ι (Algebra M))
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (ξ η : H) (hηnorm : ‖η‖=1)
    (hηcone : η ∈ modularPositiveCone (M := M) J ξ)
    (hηcentral : η ∈ centralVectorSpace (matrixUnitConcreteAlgebra E) J)
    (p : AlgebraProjection M) (hp : p.val ∈ E.algebra)
    (u : unitary (Algebra M)) (hcomm : u.val*p.val=p.val*u.val)
    (δ : ℝ) (hclose : ‖(modularUnitary J hJ u : H →L[ℂ] H) η-ξ‖ ≤ δ) :
    ∃ (F : FiniteMatrixStage M) (ζ : H), p.val.val ∈ F.units.concreteAlgebra ∧
      ‖ζ‖=1 ∧ ζ ∈ modularPositiveCone (M := M) J ξ ∧
      ζ ∈ centralVectorSpace (matrixUnitConcreteAlgebra F.units) J ∧ ‖ζ-ξ‖ ≤ δ := by
  classical
  let G := unitaryConjugateMatrixUnits E u
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let F : FiniteMatrixStage M := ⟨Fintype.card ι,Fintype.card_pos,G.reindex e⟩
  let ζ := (modularUnitary J hJ u : H →L[ℂ] H) η
  have hg : p.val ∈ G.algebra := unitaryConjugateMatrixUnits_contains_projection E u p hp hcomm
  have hc : ζ ∈ centralVectorSpace (matrixUnitConcreteAlgebra G) J :=
    modularUnitary_matrix_central J hJ hright E u hηcentral
  refine ⟨F,ζ,?_,?_,?_,?_,hclose⟩
  · apply ((G.reindex e).mem_concreteAlgebra p.val).mpr
    rwa [G.reindex_algebra e]
  · exact (Unitary.norm_map _ η).trans hηnorm
  · exact modularQuadratic_preserves_positiveCone J hJ hright ξ u.val hηcone
  · apply (mem_centralVectorSpace_matrix_iff F.units J ζ).mpr
    intro i j
    exact (mem_centralVectorSpace_matrix_iff G J ζ).mp hc (e i) (e j)

end

end KadisonKastler

end OAI
