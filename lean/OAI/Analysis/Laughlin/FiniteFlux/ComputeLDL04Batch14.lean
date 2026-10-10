import OAI.Analysis.Laughlin.FiniteFlux.Data14

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_14_4_0 : MatrixCompute.compressed 14 candidateY_14 candidateZ_14 4 0 =
    (lower_14 * Matrix.diagonal pivots_14 * lower_14.transpose) 4 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_14_4_1 : MatrixCompute.compressed 14 candidateY_14 candidateZ_14 4 1 =
    (lower_14 * Matrix.diagonal pivots_14 * lower_14.transpose) 4 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_14_4_2 : MatrixCompute.compressed 14 candidateY_14 candidateZ_14 4 2 =
    (lower_14 * Matrix.diagonal pivots_14 * lower_14.transpose) 4 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_14_4_3 : MatrixCompute.compressed 14 candidateY_14 candidateZ_14 4 3 =
    (lower_14 * Matrix.diagonal pivots_14 * lower_14.transpose) 4 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_14_4_4 : MatrixCompute.compressed 14 candidateY_14 candidateZ_14 4 4 =
    (lower_14 * Matrix.diagonal pivots_14 * lower_14.transpose) 4 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_14_4_5 : MatrixCompute.compressed 14 candidateY_14 candidateZ_14 4 5 =
    (lower_14 * Matrix.diagonal pivots_14 * lower_14.transpose) 4 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_14_4_6 : MatrixCompute.compressed 14 candidateY_14 candidateZ_14 4 6 =
    (lower_14 * Matrix.diagonal pivots_14 * lower_14.transpose) 4 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
