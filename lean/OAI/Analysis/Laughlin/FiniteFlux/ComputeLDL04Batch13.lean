import OAI.Analysis.Laughlin.FiniteFlux.Data13

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_13_4_0 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 4 0 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 4 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_4_1 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 4 1 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 4 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_4_2 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 4 2 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 4 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_4_3 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 4 3 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 4 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_4_4 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 4 4 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 4 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_4_5 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 4 5 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 4 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_4_6 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 4 6 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 4 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
