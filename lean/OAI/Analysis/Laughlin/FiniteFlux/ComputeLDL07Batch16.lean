import OAI.Analysis.Laughlin.FiniteFlux.Data16

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_16_7_0 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 7 0 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 7 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_7_1 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 7 1 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 7 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_7_2 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 7 2 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 7 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_7_3 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 7 3 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 7 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_7_4 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 7 4 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 7 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_7_5 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 7 5 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 7 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_7_6 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 7 6 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 7 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_7_7 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 7 7 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 7 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
