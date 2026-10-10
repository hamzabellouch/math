import OAI.Analysis.Laughlin.FiniteFlux.Data12

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_12_2_0 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 2 0 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 2 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_12_2_1 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 2 1 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 2 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_12_2_2 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 2 2 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 2 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_12_2_3 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 2 3 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 2 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_12_2_4 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 2 4 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 2 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_12_2_5 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 2 5 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 2 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
