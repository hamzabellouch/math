import OAI.Analysis.Laughlin.FiniteFlux.Data16

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_16_6_0 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 6 0 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 6 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_6_1 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 6 1 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 6 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_6_2 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 6 2 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 6 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_6_3 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 6 3 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 6 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_6_4 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 6 4 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 6 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_6_5 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 6 5 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 6 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_6_6 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 6 6 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 6 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_6_7 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 6 7 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 6 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
