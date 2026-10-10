import OAI.Analysis.Laughlin.FiniteFlux.Data13

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_13_6_0 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 6 0 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 6 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_6_1 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 6 1 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 6 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_6_2 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 6 2 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 6 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_6_3 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 6 3 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 6 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_6_4 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 6 4 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 6 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_6_5 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 6 5 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 6 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_6_6 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 6 6 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 6 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
