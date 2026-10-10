import OAI.Analysis.Laughlin.FiniteFlux.Data13

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_13_2_0 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 2 0 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 2 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_2_1 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 2 1 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 2 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_2_2 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 2 2 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 2 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_2_3 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 2 3 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 2 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_2_4 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 2 4 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 2 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_2_5 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 2 5 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 2 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_2_6 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 2 6 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 2 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
