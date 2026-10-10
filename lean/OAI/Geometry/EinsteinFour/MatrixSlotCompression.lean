import OAI.Geometry.EinsteinFour.MatrixSlotOperator
import OAI.Geometry.EinsteinFour.BianchiCurvatureProjection

namespace OAI

/-! The bounded matrix-slot operator and the concrete Bianchi compression
use the same Euclidean pairing and normalization. -/

namespace PositiveEinsteinFour.Geometry

open scoped BigOperators
open TraceHessian Bianchi

noncomputable section

def rawGradientVector (Z : RawGradient) : GradientVector :=
  WithLp.toLp 2 (rawCoordinates Z)

def tensorGradientVector (Z : Tensor) : GradientVector := rawGradientVector Z.matrix

theorem inner_rawGradientVector (Z W : RawGradient) :
    inner ℝ (rawGradientVector Z) (rawGradientVector W) = rawPairing Z W := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    rawGradientVector, rawPairing]
  apply Finset.sum_congr rfl
  intro p _
  ring

theorem inner_tensorGradientVector (Z W : Tensor) :
    inner ℝ (tensorGradientVector Z) (tensorGradientVector W) = 6 * Z.pairing W := by
  simp only [tensorGradientVector]
  rw [inner_rawGradientVector, tensor_pairing_eq_raw]

theorem tensorGradientVector_norm_sq (Z : Tensor) :
    ‖tensorGradientVector Z‖ ^ 2 = Z.squaredNorm := by
  rw [← real_inner_self_eq_norm_sq, tensorGradientVector,
    inner_rawGradientVector, rawPairing_vectors]
  simp only [real_inner_self_eq_norm_sq, Tensor.squaredNorm]

private theorem tensorGradientVector_trace (Z : Tensor) (hz : Z.traceFree) (i : Fin 4) :
    (∑ a, tensorGradientVector Z (i, a, a)) = 0 := by
  have h := congrArg (fun v : Vec => v i) hz
  simpa [tensorGradientVector, rawGradientVector, rawCoordinates,
    Tensor.traceFree, Tensor.matrix, Fin.sum_univ_three] using h

/-- The CLM has exactly the actual trace-free anticommutator entries. -/
theorem matrixSlotOperator_tensor (S : Shape) (v : ℝ) (Z : Tensor) (hz : Z.traceFree) :
    matrixSlotOperator (Matrix.diagonal (fun s => v * S.s s)) (tensorGradientVector Z) =
      tensorGradientVector (matrixCurvatureTensor S v Z) := by
  ext p
  rcases p with ⟨i, a, b⟩
  rw [matrixSlotOperator_on_traceFree _ _ (tensorGradientVector_trace Z hz)]
  change matrixSlotAction (Matrix.diagonal (fun s => v * S.s s))
    (fun c d => Z.matrix c d i) a b = (matrixCurvatureTensor S v Z).matrix a b i
  exact (congrArg (fun M : Mat => M a b)
    (matrixSlotAction_diagonal (fun s => v * S.s s)
      (show Mat from fun c d => Z.matrix c d i))).trans
        (matrixCurvatureTensor_matrix S v Z a b i).symm

/-- Its uncompressed pairing against any trace-free tensor has the same
normalization as the algebraic curvature form. -/
theorem matrixSlotOperator_pairing (S : Shape) (v : ℝ) (Z W : Tensor)
    (hz : Z.traceFree) (hw : W.traceFree) :
    inner ℝ (matrixSlotOperator (Matrix.diagonal (fun s => v * S.s s))
      (tensorGradientVector Z)) (tensorGradientVector W) =
        6 * curvatureBilinear S v Z W := by
  rw [matrixSlotOperator_tensor S v Z hz, inner_tensorGradientVector,
    matrixCurvatureTensor_pairing S v Z W hw]

/-- The `E_B` term in the operator Green identity is the square of the
actual orthogonal Bianchi compression. -/
theorem matrixSlotOperator_compressed_energy (S : Shape) (v : ℝ) (p k l : Vec) :
    inner ℝ (matrixSlotOperator (Matrix.diagonal (fun s => v * S.s s))
      (tensorGradientVector (parameters S p k l)))
      (tensorGradientVector (curvatureAction S v p k l)) =
        (curvatureAction S v p k l).squaredNorm := by
  rw [matrixSlotOperator_tensor S v _ (parameters_traceFree S p k l),
    inner_tensorGradientVector, curvatureAction_compressed_energy]
  ring

end

end PositiveEinsteinFour.Geometry

end OAI
