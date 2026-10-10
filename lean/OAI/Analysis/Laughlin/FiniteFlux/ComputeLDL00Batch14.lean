import OAI.Analysis.Laughlin.FiniteFlux.Data14

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_14_0_0 : MatrixCompute.compressed 14 candidateY_14 candidateZ_14 0 0 =
    (lower_14 * Matrix.diagonal pivots_14 * lower_14.transpose) 0 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_14_0_1 : MatrixCompute.compressed 14 candidateY_14 candidateZ_14 0 1 =
    (lower_14 * Matrix.diagonal pivots_14 * lower_14.transpose) 0 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_14_0_2 : MatrixCompute.compressed 14 candidateY_14 candidateZ_14 0 2 =
    (lower_14 * Matrix.diagonal pivots_14 * lower_14.transpose) 0 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_14_0_3 : MatrixCompute.compressed 14 candidateY_14 candidateZ_14 0 3 =
    (lower_14 * Matrix.diagonal pivots_14 * lower_14.transpose) 0 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_14_0_4 : MatrixCompute.compressed 14 candidateY_14 candidateZ_14 0 4 =
    (lower_14 * Matrix.diagonal pivots_14 * lower_14.transpose) 0 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_14_0_5 : MatrixCompute.compressed 14 candidateY_14 candidateZ_14 0 5 =
    (lower_14 * Matrix.diagonal pivots_14 * lower_14.transpose) 0 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_14_0_6 : MatrixCompute.compressed 14 candidateY_14 candidateZ_14 0 6 =
    (lower_14 * Matrix.diagonal pivots_14 * lower_14.transpose) 0 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
