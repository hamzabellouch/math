import OAI.Analysis.KadisonKastler.MatrixProductCentral

namespace OAI

/-! # Central vectors for a finite-matrix relative extension -/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem relativeMatrixExtension_central
    (E : FiniteMatrixStage M) (F : FiniteMatrixStage E.units.relativeVonNeumann)
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (ξ : H)
    (hE : ξ ∈ centralVectorSpace (matrixUnitConcreteAlgebra E.units) J)
    (hF : ξ ∈ centralVectorSpace (matrixUnitConcreteAlgebra F.units) J) :
    ξ ∈ centralVectorSpace (matrixUnitConcreteAlgebra (relativeMatrixExtension E F).units) J := by
  classical
  let f := StarSubalgebra.inclusion E.units.relativeVonNeumann_le
  let G := F.units.map f
  have hc : ∀ i j k l, Commute (E.units.entry i j) (G.entry k l) := by
    intro i j k l
    apply Subtype.ext
    exact ((E.units.relativeStar_mem _).mp (F.units.entry k l).property).2 i j
  have hG : ξ ∈ centralVectorSpace (matrixUnitConcreteAlgebra G) J := by
    apply (mem_centralVectorSpace_matrix_iff G J ξ).mpr
    intro i j
    exact (mem_centralVectorSpace_matrix_iff F.units J ξ).mp hF i j
  have hprod : ξ ∈ centralVectorSpace
      (matrixUnitConcreteAlgebra (E.units.product G hc)) J := by
    rw [matrix_product_centralVectorSpace E.units G hc J hJ hright]
    exact ⟨hE,hG⟩
  let e : Fin (Fintype.card (Fin E.size × Fin F.size)) ≃ Fin E.size × Fin F.size :=
    (Fintype.equivFin _).symm
  apply (mem_centralVectorSpace_matrix_iff (relativeMatrixExtension E F).units J ξ).mpr
  intro i j
  exact (mem_centralVectorSpace_matrix_iff (E.units.product G hc) J ξ).mp hprod (e i) (e j)

end

end KadisonKastler

end OAI
