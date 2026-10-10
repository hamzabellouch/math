import OAI.Analysis.Laughlin.FiniteFlux.Data13

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_13_1_0 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 1 0 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 1 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_1_1 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 1 1 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 1 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_1_2 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 1 2 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 1 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_1_3 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 1 3 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 1 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_1_4 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 1 4 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 1 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_1_5 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 1 5 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 1 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_1_6 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 1 6 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 1 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
