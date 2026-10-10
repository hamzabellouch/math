import OAI.Analysis.Laughlin.FiniteFlux.Data16

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_16_3_0 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 3 0 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 3 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_3_1 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 3 1 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 3 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_3_2 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 3 2 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 3 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_3_3 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 3 3 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 3 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_3_4 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 3 4 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 3 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_3_5 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 3 5 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 3 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_3_6 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 3 6 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 3 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_3_7 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 3 7 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 3 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
