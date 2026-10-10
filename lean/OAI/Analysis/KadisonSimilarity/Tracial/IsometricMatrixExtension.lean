import OAI.Analysis.KadisonSimilarity.Representation.IntertwinerExtension
import OAI.Analysis.KadisonSimilarity.Representation.SquareArrayPadding

namespace OAI

/-! Isometric extension by zero preserves every finite operator-matrix norm. -/

noncomputable section
namespace KadisonSimilarity

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (J : H →ₗᵢ[ℂ] K)

theorem norm_matrix_isometricExtension {n : ℕ}
    (X : Matrix (Fin n) (Fin n) (H →L[ℂ] H)) :
    ‖matrixOperator (fun i j => isometricExtension J (X i j))‖ = ‖matrixOperator X‖ := by
  let L := mapCopies J.toContinuousLinearMap n
  let R := mapCopies J.toContinuousLinearMap.adjoint n
  have hL : ‖L‖ ≤ 1 := (norm_mapCopies_le _ _).trans J.norm_toContinuousLinearMap_le
  have hR : ‖R‖ ≤ 1 := (norm_mapCopies_le _ _).trans (by
    simpa only [ContinuousLinearMap.adjoint.norm_map] using J.norm_toContinuousLinearMap_le)
  have hRL : R.comp L = ContinuousLinearMap.id ℂ (HilbertCopies H n) := by
    dsimp [R, L]
    rw [← mapCopies_comp_eq, J.adjoint_comp_self]
    exact mapCopies_id_eq n
  have hext : L.comp ((matrixOperator X).comp R) =
      matrixOperator (fun i j => isometricExtension J (X i j)) := by
    apply ContinuousLinearMap.ext
    intro x
    ext i
    change J (matrixOperator X (mapCopies J.toContinuousLinearMap.adjoint n x) i) = _
    rw [matrixOperator_apply (H := H) X
      (mapCopies J.toContinuousLinearMap.adjoint n x) i, map_sum]
    simpa only [isometricExtension, ContinuousLinearMap.comp_apply,
      LinearIsometry.coe_toContinuousLinearMap, mapCopies_apply] using
      (matrixOperator_apply (H := K) (fun i j => isometricExtension J (X i j)) x i).symm
  rw [← hext]
  exact norm_split_extension L R hL hR hRL _

end KadisonSimilarity

end

end OAI
