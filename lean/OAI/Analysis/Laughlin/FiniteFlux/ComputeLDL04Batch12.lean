import OAI.Analysis.Laughlin.FiniteFlux.Data12

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_12_4_0 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 4 0 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 4 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_12_4_1 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 4 1 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 4 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_12_4_2 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 4 2 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 4 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_12_4_3 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 4 3 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 4 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_12_4_4 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 4 4 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 4 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_12_4_5 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 4 5 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 4 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
