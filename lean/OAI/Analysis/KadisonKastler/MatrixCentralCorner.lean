import OAI.Analysis.KadisonKastler.PairedMatrixColumn
import OAI.Analysis.KadisonKastler.MatrixCentralProjection
import OAI.Analysis.KadisonKastler.PartialIsometryCorner

namespace OAI

/-! # The Hilbert-space identification of a matrix corner and central vectors

The map from Haagerup's Lemma3.5 is a genuine unitary between these
closed subspaces. State and natural-cone properties are separate claims.
-/

namespace KadisonKastler

open Generator

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem starProjection_range_of_projection {P : H →L[ℂ] H} (hP : IsStarProjection P)
    [CompleteSpace P.range] : P.range.starProjection = P := by
  ext ξ
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (show P ξ ∈ P.range from ⟨ξ,rfl⟩)
  rintro _ ⟨η,rfl⟩
  have he : P (P η) = P η := congrArg (fun T : H →L[ℂ] H => T η) hP.isIdempotentElem.eq
  have hs : P.adjoint = P := hP.isSelfAdjoint.star_eq
  rw [inner_sub_left,← P.adjoint_inner_right,hs]
  change inner ℂ ξ (P η) - inner ℂ ξ (P (P η)) = 0
  rw [he,sub_self]

variable {M : VonNeumannAlgebra H}
  {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  (E : MatrixUnitSystem ι (Algebra M))
  (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
  (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)

def matrixCentralCornerProjection (o : ι) : H →L[ℂ] H :=
  (E.entry o o).val * conjugationOperator J (E.entry o o).val

include hJ hright in
omit [Nonempty ι] in
theorem matrixCentralCornerProjection_isProjection (o : ι) :
    IsStarProjection (matrixCentralCornerProjection E J o) := by
  have he : IsStarProjection (E.entry o o).val :=
    (E.diagonal_projection o).map M.toStarSubalgebra.subtype
  have hf : IsStarProjection (conjugationOperator J (E.entry o o).val) := by
    constructor
    · change conjugationOperator J (E.entry o o).val *
        conjugationOperator J (E.entry o o).val = conjugationOperator J (E.entry o o).val
      rw [← conjugationOperator_mul J hJ,he.isIdempotentElem.eq]
    · change star (conjugationOperator J (E.entry o o).val) =
        conjugationOperator J (E.entry o o).val
      rw [← conjugationOperator_star J hJ,he.isSelfAdjoint.star_eq]
  exact he.mul hf
    (VonNeumannAlgebra.mem_commutant_iff.mp (hright (E.entry o o))
      (E.entry o o).val (E.entry o o).property)

def matrixCentralCorner (o : ι) : Submodule ℂ H :=
  (matrixCentralCornerProjection E J o).range

include hJ hright in
omit [Nonempty ι] in
theorem matrixCentralCorner_complete (o : ι) :
    CompleteSpace (matrixCentralCorner E J o) :=
  (ContinuousLinearMap.IsIdempotentElem.isClosed_range
    (matrixCentralCornerProjection_isProjection E J hJ hright o).isIdempotentElem).completeSpace_coe

def matrixCentralColumn (o : ι) : H →L[ℂ] H :=
  pairedMatrixColumn (E.map M.toStarSubalgebra.subtype)
    (conjugateMatrixUnits J hJ (E.map M.toStarSubalgebra.subtype)) o

include hright in
theorem matrixCentralColumn_initial (o : ι) :
    star (matrixCentralColumn E J hJ o) * matrixCentralColumn E J hJ o =
      matrixCentralCornerProjection E J o := by
  apply pairedMatrixColumn_initial
  intro i j k l
  exact VonNeumannAlgebra.mem_commutant_iff.mp (hright (E.entry k l))
    (E.entry i j).val (E.entry i j).property

include hright in
theorem matrixCentralColumn_final (o : ι) :
    matrixCentralColumn E J hJ o * star (matrixCentralColumn E J hJ o) =
      (centralVectorSpace (matrixUnitConcreteAlgebra E) J).starProjection := by
  rw [matrixCentralProjection_eq E J hJ hright]
  apply pairedMatrixColumn_final
  intro i j k l
  exact VonNeumannAlgebra.mem_commutant_iff.mp (hright (E.entry k l))
    (E.entry i j).val (E.entry i j).property

include hright in
def matrixCentralCornerEquiv (o : ι) :
    matrixCentralCorner E J o ≃ₗᵢ[ℂ] centralVectorSpace (matrixUnitConcreteAlgebra E) J := by
  letI := matrixCentralCorner_complete E J hJ hright o
  letI : CompleteSpace (matrixCentralCornerProjection E J o).range :=
    matrixCentralCorner_complete E J hJ hright o
  apply partialIsometryCornerEquiv (matrixCentralCorner E J o).subtypeₗᵢ
    (centralVectorSpace (matrixUnitConcreteAlgebra E) J).subtypeₗᵢ
    (matrixCentralColumn E J hJ o)
  · change star (matrixCentralColumn E J hJ o) * matrixCentralColumn E J hJ o =
      (matrixCentralCorner E J o).subtypeL.comp (matrixCentralCorner E J o).subtypeL.adjoint
    rw [Submodule.adjoint_subtypeL]
    change _ = (matrixCentralCornerProjection E J o).range.starProjection
    rw [starProjection_range_of_projection (matrixCentralCornerProjection_isProjection E J hJ hright o)]
    exact matrixCentralColumn_initial E J hJ hright o
  · change matrixCentralColumn E J hJ o * star (matrixCentralColumn E J hJ o) =
      (centralVectorSpace (matrixUnitConcreteAlgebra E) J).subtypeL.comp
        (centralVectorSpace (matrixUnitConcreteAlgebra E) J).subtypeL.adjoint
    rw [Submodule.adjoint_subtypeL]
    exact matrixCentralColumn_final E J hJ hright o

end

end KadisonKastler

end OAI
