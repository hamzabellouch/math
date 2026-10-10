import OAI.Analysis.Laughlin.FiniteFlux.Data15

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_15_2_0 : MatrixCompute.compressed 15 candidateY_15 candidateZ_15 2 0 =
    (lower_15 * Matrix.diagonal pivots_15 * lower_15.transpose) 2 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_15_2_1 : MatrixCompute.compressed 15 candidateY_15 candidateZ_15 2 1 =
    (lower_15 * Matrix.diagonal pivots_15 * lower_15.transpose) 2 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_15_2_2 : MatrixCompute.compressed 15 candidateY_15 candidateZ_15 2 2 =
    (lower_15 * Matrix.diagonal pivots_15 * lower_15.transpose) 2 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_15_2_3 : MatrixCompute.compressed 15 candidateY_15 candidateZ_15 2 3 =
    (lower_15 * Matrix.diagonal pivots_15 * lower_15.transpose) 2 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_15_2_4 : MatrixCompute.compressed 15 candidateY_15 candidateZ_15 2 4 =
    (lower_15 * Matrix.diagonal pivots_15 * lower_15.transpose) 2 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_15_2_5 : MatrixCompute.compressed 15 candidateY_15 candidateZ_15 2 5 =
    (lower_15 * Matrix.diagonal pivots_15 * lower_15.transpose) 2 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_15_2_6 : MatrixCompute.compressed 15 candidateY_15 candidateZ_15 2 6 =
    (lower_15 * Matrix.diagonal pivots_15 * lower_15.transpose) 2 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_15_2_7 : MatrixCompute.compressed 15 candidateY_15 candidateZ_15 2 7 =
    (lower_15 * Matrix.diagonal pivots_15 * lower_15.transpose) 2 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
