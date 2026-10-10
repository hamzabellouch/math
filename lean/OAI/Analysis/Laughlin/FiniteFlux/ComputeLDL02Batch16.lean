import OAI.Analysis.Laughlin.FiniteFlux.Data16

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_16_2_0 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 2 0 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 2 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_2_1 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 2 1 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 2 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_2_2 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 2 2 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 2 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_2_3 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 2 3 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 2 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_2_4 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 2 4 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 2 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_2_5 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 2 5 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 2 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_2_6 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 2 6 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 2 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_2_7 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 2 7 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 2 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
