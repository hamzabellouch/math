import OAI.Analysis.Laughlin.FiniteFlux.Data16

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_16_4_0 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 4 0 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 4 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_4_1 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 4 1 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 4 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_4_2 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 4 2 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 4 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_4_3 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 4 3 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 4 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_4_4 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 4 4 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 4 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_4_5 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 4 5 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 4 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_4_6 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 4 6 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 4 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_4_7 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 4 7 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 4 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
