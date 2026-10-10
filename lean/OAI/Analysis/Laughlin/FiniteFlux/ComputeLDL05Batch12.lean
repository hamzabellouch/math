import OAI.Analysis.Laughlin.FiniteFlux.Data12

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_12_5_0 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 5 0 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 5 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_12_5_1 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 5 1 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 5 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_12_5_2 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 5 2 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 5 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_12_5_3 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 5 3 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 5 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_12_5_4 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 5 4 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 5 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_12_5_5 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 5 5 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 5 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
