import OAI.Analysis.Laughlin.FiniteFlux.Data14

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_14_5_0 : MatrixCompute.compressed 14 candidateY_14 candidateZ_14 5 0 =
    (lower_14 * Matrix.diagonal pivots_14 * lower_14.transpose) 5 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_14_5_1 : MatrixCompute.compressed 14 candidateY_14 candidateZ_14 5 1 =
    (lower_14 * Matrix.diagonal pivots_14 * lower_14.transpose) 5 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_14_5_2 : MatrixCompute.compressed 14 candidateY_14 candidateZ_14 5 2 =
    (lower_14 * Matrix.diagonal pivots_14 * lower_14.transpose) 5 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_14_5_3 : MatrixCompute.compressed 14 candidateY_14 candidateZ_14 5 3 =
    (lower_14 * Matrix.diagonal pivots_14 * lower_14.transpose) 5 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_14_5_4 : MatrixCompute.compressed 14 candidateY_14 candidateZ_14 5 4 =
    (lower_14 * Matrix.diagonal pivots_14 * lower_14.transpose) 5 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_14_5_5 : MatrixCompute.compressed 14 candidateY_14 candidateZ_14 5 5 =
    (lower_14 * Matrix.diagonal pivots_14 * lower_14.transpose) 5 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_14_5_6 : MatrixCompute.compressed 14 candidateY_14 candidateZ_14 5 6 =
    (lower_14 * Matrix.diagonal pivots_14 * lower_14.transpose) 5 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
