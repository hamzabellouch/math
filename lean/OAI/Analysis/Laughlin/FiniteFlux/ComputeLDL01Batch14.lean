import OAI.Analysis.Laughlin.FiniteFlux.Data14

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_14_1_0 : MatrixCompute.compressed 14 candidateY_14 candidateZ_14 1 0 =
    (lower_14 * Matrix.diagonal pivots_14 * lower_14.transpose) 1 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_14_1_1 : MatrixCompute.compressed 14 candidateY_14 candidateZ_14 1 1 =
    (lower_14 * Matrix.diagonal pivots_14 * lower_14.transpose) 1 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_14_1_2 : MatrixCompute.compressed 14 candidateY_14 candidateZ_14 1 2 =
    (lower_14 * Matrix.diagonal pivots_14 * lower_14.transpose) 1 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_14_1_3 : MatrixCompute.compressed 14 candidateY_14 candidateZ_14 1 3 =
    (lower_14 * Matrix.diagonal pivots_14 * lower_14.transpose) 1 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_14_1_4 : MatrixCompute.compressed 14 candidateY_14 candidateZ_14 1 4 =
    (lower_14 * Matrix.diagonal pivots_14 * lower_14.transpose) 1 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_14_1_5 : MatrixCompute.compressed 14 candidateY_14 candidateZ_14 1 5 =
    (lower_14 * Matrix.diagonal pivots_14 * lower_14.transpose) 1 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_14_1_6 : MatrixCompute.compressed 14 candidateY_14 candidateZ_14 1 6 =
    (lower_14 * Matrix.diagonal pivots_14 * lower_14.transpose) 1 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
