import OAI.Analysis.Laughlin.FiniteFlux.Data15

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_15_6_0 : MatrixCompute.compressed 15 candidateY_15 candidateZ_15 6 0 =
    (lower_15 * Matrix.diagonal pivots_15 * lower_15.transpose) 6 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_15_6_1 : MatrixCompute.compressed 15 candidateY_15 candidateZ_15 6 1 =
    (lower_15 * Matrix.diagonal pivots_15 * lower_15.transpose) 6 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_15_6_2 : MatrixCompute.compressed 15 candidateY_15 candidateZ_15 6 2 =
    (lower_15 * Matrix.diagonal pivots_15 * lower_15.transpose) 6 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_15_6_3 : MatrixCompute.compressed 15 candidateY_15 candidateZ_15 6 3 =
    (lower_15 * Matrix.diagonal pivots_15 * lower_15.transpose) 6 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_15_6_4 : MatrixCompute.compressed 15 candidateY_15 candidateZ_15 6 4 =
    (lower_15 * Matrix.diagonal pivots_15 * lower_15.transpose) 6 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_15_6_5 : MatrixCompute.compressed 15 candidateY_15 candidateZ_15 6 5 =
    (lower_15 * Matrix.diagonal pivots_15 * lower_15.transpose) 6 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_15_6_6 : MatrixCompute.compressed 15 candidateY_15 candidateZ_15 6 6 =
    (lower_15 * Matrix.diagonal pivots_15 * lower_15.transpose) 6 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_15_6_7 : MatrixCompute.compressed 15 candidateY_15 candidateZ_15 6 7 =
    (lower_15 * Matrix.diagonal pivots_15 * lower_15.transpose) 6 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
