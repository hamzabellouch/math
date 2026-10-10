import OAI.Analysis.Laughlin.FiniteFlux.Data16

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_16_5_0 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 5 0 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 5 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_5_1 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 5 1 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 5 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_5_2 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 5 2 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 5 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_5_3 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 5 3 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 5 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_5_4 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 5 4 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 5 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_5_5 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 5 5 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 5 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_5_6 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 5 6 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 5 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_5_7 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 5 7 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 5 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
