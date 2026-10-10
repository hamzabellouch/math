import OAI.Analysis.Laughlin.FiniteFlux.Data16

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_16_1_0 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 1 0 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 1 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_1_1 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 1 1 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 1 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_1_2 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 1 2 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 1 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_1_3 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 1 3 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 1 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_1_4 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 1 4 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 1 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_1_5 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 1 5 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 1 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_1_6 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 1 6 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 1 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_1_7 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 1 7 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 1 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
