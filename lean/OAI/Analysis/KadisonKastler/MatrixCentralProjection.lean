import OAI.Analysis.KadisonKastler.MatrixCentralVectorTests
import OAI.Analysis.KadisonKastler.PairedMatrixProjection

namespace OAI

/-! # The explicit finite-matrix central-vector projection

Haagerup, Acta Math. 158 (1987), Lemma 3.5: the central-vector projection is
the normalized sum of matching left and conjugate-right matrix units.
The formula is proved from the matrix-unit relations and commutation.
-/

namespace KadisonKastler

open Generator

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}
  {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def matrixCentralProjection (E : MatrixUnitSystem ι (Algebra M))
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J) : H →L[ℂ] H :=
  pairedMatrixProjection (E.map M.toStarSubalgebra.subtype)
    (conjugateMatrixUnits J hJ (E.map M.toStarSubalgebra.subtype))

theorem matrixCentralProjection_eq (E : MatrixUnitSystem ι (Algebra M))
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant) :
    (centralVectorSpace (matrixUnitConcreteAlgebra E) J).starProjection =
      matrixCentralProjection E J hJ := by
  let F := E.map M.toStarSubalgebra.subtype
  let G := conjugateMatrixUnits J hJ F
  have hc (i j k l : ι) : Commute (F.entry i j) (G.entry k l) :=
    VonNeumannAlgebra.mem_commutant_iff.mp (hright (E.entry k l))
      (E.entry i j).val (E.entry i j).property
  have hQ : IsSelfAdjoint (matrixCentralProjection E J hJ) :=
    pairedMatrixProjection_selfAdjoint F G hc
  have hmem (ξ : H) : matrixCentralProjection E J hJ ξ ∈
      centralVectorSpace (matrixUnitConcreteAlgebra E) J := by
    apply (mem_centralVectorSpace_matrix_iff E J _).mpr
    intro i j
    have he := congrArg (fun T : H →L[ℂ] H => T ξ)
      (pairedMatrixProjection_intertwines F G hc i j)
    change (E.entry i j).val (matrixCentralProjection E J hJ ξ) =
      conjugationOperator J (E.entry j i).val (matrixCentralProjection E J hJ ξ) at he
    have hs : star (E.entry i j).val = (E.entry j i).val :=
      congrArg (fun a : Algebra M => a.val) (E.star_entry i j)
    rw [hs]
    exact he
  have hfix (ξ : H) (hξ : ξ ∈ centralVectorSpace (matrixUnitConcreteAlgebra E) J) :
      matrixCentralProjection E J hJ ξ = ξ := by
    apply pairedMatrixProjection_fixed F G ξ
    intro i j
    change (E.entry i j).val ξ = conjugationOperator J (E.entry j i).val ξ
    have h := (mem_centralVectorSpace_matrix_iff E J ξ).mp hξ i j
    have hs : star (E.entry i j).val = (E.entry j i).val :=
      congrArg (fun a : Algebra M => a.val) (E.star_entry i j)
    rwa [hs] at h
  ext ξ
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (hmem ξ)
  intro w hw
  have hs : (matrixCentralProjection E J hJ).adjoint = matrixCentralProjection E J hJ :=
    hQ.star_eq
  rw [inner_sub_left, ← ContinuousLinearMap.adjoint_inner_right, hs, hfix w hw, sub_self]

end

end KadisonKastler

end OAI
