import OAI.Analysis.Laughlin.FiniteFlux.Data16

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_16_0_0 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 0 0 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 0 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_0_1 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 0 1 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 0 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_0_2 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 0 2 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 0 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_0_3 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 0 3 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 0 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_0_4 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 0 4 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 0 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_0_5 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 0 5 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 0 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_0_6 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 0 6 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 0 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_0_7 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 0 7 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 0 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
