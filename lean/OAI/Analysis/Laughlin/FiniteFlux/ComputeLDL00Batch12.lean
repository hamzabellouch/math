import OAI.Analysis.Laughlin.FiniteFlux.Data12

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_12_0_0 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 0 0 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 0 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_12_0_1 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 0 1 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 0 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_12_0_2 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 0 2 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 0 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_12_0_3 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 0 3 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 0 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_12_0_4 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 0 4 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 0 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_12_0_5 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 0 5 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 0 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
