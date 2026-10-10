import OAI.Analysis.Laughlin.FiniteFlux.Data15

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_15_1_0 : MatrixCompute.compressed 15 candidateY_15 candidateZ_15 1 0 =
    (lower_15 * Matrix.diagonal pivots_15 * lower_15.transpose) 1 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_15_1_1 : MatrixCompute.compressed 15 candidateY_15 candidateZ_15 1 1 =
    (lower_15 * Matrix.diagonal pivots_15 * lower_15.transpose) 1 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_15_1_2 : MatrixCompute.compressed 15 candidateY_15 candidateZ_15 1 2 =
    (lower_15 * Matrix.diagonal pivots_15 * lower_15.transpose) 1 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_15_1_3 : MatrixCompute.compressed 15 candidateY_15 candidateZ_15 1 3 =
    (lower_15 * Matrix.diagonal pivots_15 * lower_15.transpose) 1 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_15_1_4 : MatrixCompute.compressed 15 candidateY_15 candidateZ_15 1 4 =
    (lower_15 * Matrix.diagonal pivots_15 * lower_15.transpose) 1 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_15_1_5 : MatrixCompute.compressed 15 candidateY_15 candidateZ_15 1 5 =
    (lower_15 * Matrix.diagonal pivots_15 * lower_15.transpose) 1 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_15_1_6 : MatrixCompute.compressed 15 candidateY_15 candidateZ_15 1 6 =
    (lower_15 * Matrix.diagonal pivots_15 * lower_15.transpose) 1 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_15_1_7 : MatrixCompute.compressed 15 candidateY_15 candidateZ_15 1 7 =
    (lower_15 * Matrix.diagonal pivots_15 * lower_15.transpose) 1 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
