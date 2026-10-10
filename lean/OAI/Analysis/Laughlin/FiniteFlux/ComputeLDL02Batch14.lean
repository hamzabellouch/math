import OAI.Analysis.Laughlin.FiniteFlux.Data14

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_14_2_0 : MatrixCompute.compressed 14 candidateY_14 candidateZ_14 2 0 =
    (lower_14 * Matrix.diagonal pivots_14 * lower_14.transpose) 2 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_14_2_1 : MatrixCompute.compressed 14 candidateY_14 candidateZ_14 2 1 =
    (lower_14 * Matrix.diagonal pivots_14 * lower_14.transpose) 2 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_14_2_2 : MatrixCompute.compressed 14 candidateY_14 candidateZ_14 2 2 =
    (lower_14 * Matrix.diagonal pivots_14 * lower_14.transpose) 2 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_14_2_3 : MatrixCompute.compressed 14 candidateY_14 candidateZ_14 2 3 =
    (lower_14 * Matrix.diagonal pivots_14 * lower_14.transpose) 2 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_14_2_4 : MatrixCompute.compressed 14 candidateY_14 candidateZ_14 2 4 =
    (lower_14 * Matrix.diagonal pivots_14 * lower_14.transpose) 2 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_14_2_5 : MatrixCompute.compressed 14 candidateY_14 candidateZ_14 2 5 =
    (lower_14 * Matrix.diagonal pivots_14 * lower_14.transpose) 2 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_14_2_6 : MatrixCompute.compressed 14 candidateY_14 candidateZ_14 2 6 =
    (lower_14 * Matrix.diagonal pivots_14 * lower_14.transpose) 2 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
