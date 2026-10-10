import OAI.Analysis.Laughlin.FiniteFlux.Data13

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_13_0_0 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 0 0 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 0 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_0_1 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 0 1 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 0 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_0_2 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 0 2 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 0 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_0_3 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 0 3 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 0 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_0_4 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 0 4 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 0 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_0_5 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 0 5 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 0 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_0_6 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 0 6 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 0 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
