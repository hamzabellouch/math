import OAI.Analysis.Laughlin.FiniteFlux.Data13

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_13_5_0 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 5 0 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 5 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_5_1 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 5 1 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 5 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_5_2 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 5 2 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 5 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_5_3 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 5 3 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 5 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_5_4 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 5 4 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 5 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_5_5 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 5 5 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 5 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_5_6 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 5 6 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 5 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
