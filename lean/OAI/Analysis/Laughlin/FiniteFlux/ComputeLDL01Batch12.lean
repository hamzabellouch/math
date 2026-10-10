import OAI.Analysis.Laughlin.FiniteFlux.Data12

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_12_1_0 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 1 0 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 1 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_12_1_1 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 1 1 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 1 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_12_1_2 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 1 2 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 1 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_12_1_3 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 1 3 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 1 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_12_1_4 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 1 4 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 1 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_12_1_5 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 1 5 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 1 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
