import OAI.Analysis.Laughlin.FiniteFlux.Data15

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_15_3_0 : MatrixCompute.compressed 15 candidateY_15 candidateZ_15 3 0 =
    (lower_15 * Matrix.diagonal pivots_15 * lower_15.transpose) 3 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_15_3_1 : MatrixCompute.compressed 15 candidateY_15 candidateZ_15 3 1 =
    (lower_15 * Matrix.diagonal pivots_15 * lower_15.transpose) 3 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_15_3_2 : MatrixCompute.compressed 15 candidateY_15 candidateZ_15 3 2 =
    (lower_15 * Matrix.diagonal pivots_15 * lower_15.transpose) 3 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_15_3_3 : MatrixCompute.compressed 15 candidateY_15 candidateZ_15 3 3 =
    (lower_15 * Matrix.diagonal pivots_15 * lower_15.transpose) 3 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_15_3_4 : MatrixCompute.compressed 15 candidateY_15 candidateZ_15 3 4 =
    (lower_15 * Matrix.diagonal pivots_15 * lower_15.transpose) 3 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_15_3_5 : MatrixCompute.compressed 15 candidateY_15 candidateZ_15 3 5 =
    (lower_15 * Matrix.diagonal pivots_15 * lower_15.transpose) 3 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_15_3_6 : MatrixCompute.compressed 15 candidateY_15 candidateZ_15 3 6 =
    (lower_15 * Matrix.diagonal pivots_15 * lower_15.transpose) 3 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_15_3_7 : MatrixCompute.compressed 15 candidateY_15 candidateZ_15 3 7 =
    (lower_15 * Matrix.diagonal pivots_15 * lower_15.transpose) 3 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
