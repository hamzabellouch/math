import OAI.Analysis.Laughlin.FiniteFlux.Data12

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_12_3_0 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 3 0 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 3 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_12_3_1 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 3 1 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 3 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_12_3_2 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 3 2 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 3 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_12_3_3 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 3 3 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 3 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_12_3_4 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 3 4 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 3 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_12_3_5 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 3 5 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 3 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
