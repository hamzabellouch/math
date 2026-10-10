import OAI.Analysis.KadisonKastler.PositiveConePowersStormer
import OAI.Analysis.KadisonKastler.RelativeMatrixCone

namespace OAI

/-! # Positive decomposition inside a finite-matrix central space

Orthogonal positive parts of a central vector remain central: the positive
central projection cannot discard a common nonzero component of those parts.
Their support projections therefore belong to the relative commutant.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}
  {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

local instance relativePositiveDecompositionRealInner : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

theorem positiveCone_parts_mem_centralVectorSpace
    (E : MatrixUnitSystem ι (Algebra M))
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (ξ : H) (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    {α β : H} (hα : α ∈ modularPositiveCone (M := M) J ξ)
    (hβ : β ∈ modularPositiveCone (M := M) J ξ)
    (horth : inner ℝ α β=0)
    (hdiff : α-β ∈ centralVectorSpace (matrixUnitConcreteAlgebra E) J) :
    α ∈ centralVectorSpace (matrixUnitConcreteAlgebra E) J ∧
      β ∈ centralVectorSpace (matrixUnitConcreteAlgebra E) J := by
  classical
  let K := centralVectorSpace (matrixUnitConcreteAlgebra E) J
  let P := K.starProjection
  let d := α-P α
  have hPd : P (α-β)=α-β := Submodule.starProjection_eq_self_iff.mpr hdiff
  have he : β-P β=d := by
    rw [map_sub] at hPd
    dsimp [d]
    calc
      β-P β=α-(P α-P β)-P β := by rw [hPd]; abel
      _=α-P α := by abel
  have hd : d ∈ Kᗮ := K.sub_starProjection_mem_orthogonal α
  have hcrossa : inner ℝ (P α) d=0 := by
    exact congrArg Complex.re (K.inner_right_of_mem_orthogonal (K.starProjection_apply_mem α) hd)
  have hcrossb : inner ℝ d (P β)=0 := by
    exact congrArg Complex.re (K.inner_left_of_mem_orthogonal (K.starProjection_apply_mem β) hd)
  have hpair : inner ℝ α β=inner ℝ (P α) (P β)+‖d‖^2 := by
    have ha : α=P α+d := by dsimp [d]; abel
    have hb : β=P β+d := by rw [← he]; abel
    conv_lhs => rw [ha,hb]
    rw [inner_add_left,inner_add_right,inner_add_right,hcrossa,hcrossb,
      real_inner_self_eq_norm_sq]
    ring
  have hPα := matrixCentralProjection_preserves_positiveCone E J hJ hright ξ
    (Classical.choice inferInstance) hα
  have hPβ := matrixCentralProjection_preserves_positiveCone E J hJ hright ξ
    (Classical.choice inferInstance) hβ
  have hnonneg := modularPositiveCone_acute J hJ hright ξ hpos hPα hPβ
  have hd0 : d=0 := by
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg d]
  constructor
  · have ha : α=P α := sub_eq_zero.mp hd0
    rw [ha]
    exact K.starProjection_apply_mem α
  · have hb : β=P β := sub_eq_zero.mp (he.trans hd0)
    rw [hb]
    exact K.starProjection_apply_mem β

theorem exists_relative_positive_decomposition
    (E : MatrixUnitSystem ι (Algebra M))
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ=ξ) (hcyc : DenseRange (algebraVectorMap M ξ))
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    (x : H) (hxJ : J x=x)
    (hx : x ∈ centralVectorSpace (matrixUnitConcreteAlgebra E) J) :
    ∃ α β : H, α ∈ modularPositiveCone (M := M) J ξ ∧
      β ∈ modularPositiveCone (M := M) J ξ ∧
      α ∈ centralVectorSpace (matrixUnitConcreteAlgebra E) J ∧
      β ∈ centralVectorSpace (matrixUnitConcreteAlgebra E) J ∧
      inner ℝ α β=0 ∧ x=α-β := by
  obtain ⟨α,β,hα,hβ,horth,heq⟩ :=
    exists_positiveCone_orthogonal_decomposition J hJ hright hleft ξ hξ hcyc x hxJ
  have hp := positiveCone_parts_mem_centralVectorSpace E J hJ hright ξ hpos hα hβ horth
    (heq ▸ hx)
  exact ⟨α,β,hα,hβ,hp.1,hp.2,horth,heq⟩

omit [Nonempty ι] in
/-- The support of a matrix-central vector lies in the relative commutant. -/
theorem vectorSupportProjection_mem_relative
    (E : MatrixUnitSystem ι (Algebra M))
    (J : H ≃ₗᵢ⋆[ℂ] H)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (α : H) (hα : α ∈ centralVectorSpace (matrixUnitConcreteAlgebra E) J) :
    (vectorSupportProjection M α).val.val ∈ E.relativeVonNeumann := by
  apply (E.relativeStar_mem _).mpr
  refine ⟨(vectorSupportProjection M α).val.property,?_⟩
  have hcomm := vectorSupport_commutes_of_right_vectors M (matrixUnitConcreteAlgebra E)
    (matrixUnitConcreteAlgebra_le E) α (fun a =>
      ⟨⟨conjugationOperator J (star a).val,
        hright ⟨(star a).val,(matrixUnitConcreteAlgebra_le E) (star a).property⟩⟩,hα a⟩)
  intro i j
  exact (hcomm (concreteMatrixUnits E |>.entry i j)).symm

end

end KadisonKastler

end OAI
