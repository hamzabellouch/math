import OAI.Analysis.Laughlin.FiniteFlux.Data14

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_14_6_0 : MatrixCompute.compressed 14 candidateY_14 candidateZ_14 6 0 =
    (lower_14 * Matrix.diagonal pivots_14 * lower_14.transpose) 6 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_14_6_1 : MatrixCompute.compressed 14 candidateY_14 candidateZ_14 6 1 =
    (lower_14 * Matrix.diagonal pivots_14 * lower_14.transpose) 6 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_14_6_2 : MatrixCompute.compressed 14 candidateY_14 candidateZ_14 6 2 =
    (lower_14 * Matrix.diagonal pivots_14 * lower_14.transpose) 6 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_14_6_3 : MatrixCompute.compressed 14 candidateY_14 candidateZ_14 6 3 =
    (lower_14 * Matrix.diagonal pivots_14 * lower_14.transpose) 6 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_14_6_4 : MatrixCompute.compressed 14 candidateY_14 candidateZ_14 6 4 =
    (lower_14 * Matrix.diagonal pivots_14 * lower_14.transpose) 6 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_14_6_5 : MatrixCompute.compressed 14 candidateY_14 candidateZ_14 6 5 =
    (lower_14 * Matrix.diagonal pivots_14 * lower_14.transpose) 6 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_14_6_6 : MatrixCompute.compressed 14 candidateY_14 candidateZ_14 6 6 =
    (lower_14 * Matrix.diagonal pivots_14 * lower_14.transpose) 6 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
