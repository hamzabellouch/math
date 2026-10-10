import OAI.Analysis.Laughlin.FiniteFlux.Data13

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_13_3_0 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 3 0 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 3 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_3_1 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 3 1 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 3 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_3_2 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 3 2 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 3 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_3_3 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 3 3 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 3 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_3_4 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 3 4 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 3 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_3_5 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 3 5 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 3 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_3_6 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 3 6 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 3 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
