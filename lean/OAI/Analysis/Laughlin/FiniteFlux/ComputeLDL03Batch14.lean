import OAI.Analysis.Laughlin.FiniteFlux.Data14

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_14_3_0 : MatrixCompute.compressed 14 candidateY_14 candidateZ_14 3 0 =
    (lower_14 * Matrix.diagonal pivots_14 * lower_14.transpose) 3 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_14_3_1 : MatrixCompute.compressed 14 candidateY_14 candidateZ_14 3 1 =
    (lower_14 * Matrix.diagonal pivots_14 * lower_14.transpose) 3 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_14_3_2 : MatrixCompute.compressed 14 candidateY_14 candidateZ_14 3 2 =
    (lower_14 * Matrix.diagonal pivots_14 * lower_14.transpose) 3 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_14_3_3 : MatrixCompute.compressed 14 candidateY_14 candidateZ_14 3 3 =
    (lower_14 * Matrix.diagonal pivots_14 * lower_14.transpose) 3 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_14_3_4 : MatrixCompute.compressed 14 candidateY_14 candidateZ_14 3 4 =
    (lower_14 * Matrix.diagonal pivots_14 * lower_14.transpose) 3 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_14_3_5 : MatrixCompute.compressed 14 candidateY_14 candidateZ_14 3 5 =
    (lower_14 * Matrix.diagonal pivots_14 * lower_14.transpose) 3 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_14_3_6 : MatrixCompute.compressed 14 candidateY_14 candidateZ_14 3 6 =
    (lower_14 * Matrix.diagonal pivots_14 * lower_14.transpose) 3 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
