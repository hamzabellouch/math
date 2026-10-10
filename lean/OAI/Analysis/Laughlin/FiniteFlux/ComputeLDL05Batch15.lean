import OAI.Analysis.Laughlin.FiniteFlux.Data15

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_15_5_0 : MatrixCompute.compressed 15 candidateY_15 candidateZ_15 5 0 =
    (lower_15 * Matrix.diagonal pivots_15 * lower_15.transpose) 5 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_15_5_1 : MatrixCompute.compressed 15 candidateY_15 candidateZ_15 5 1 =
    (lower_15 * Matrix.diagonal pivots_15 * lower_15.transpose) 5 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_15_5_2 : MatrixCompute.compressed 15 candidateY_15 candidateZ_15 5 2 =
    (lower_15 * Matrix.diagonal pivots_15 * lower_15.transpose) 5 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_15_5_3 : MatrixCompute.compressed 15 candidateY_15 candidateZ_15 5 3 =
    (lower_15 * Matrix.diagonal pivots_15 * lower_15.transpose) 5 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_15_5_4 : MatrixCompute.compressed 15 candidateY_15 candidateZ_15 5 4 =
    (lower_15 * Matrix.diagonal pivots_15 * lower_15.transpose) 5 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_15_5_5 : MatrixCompute.compressed 15 candidateY_15 candidateZ_15 5 5 =
    (lower_15 * Matrix.diagonal pivots_15 * lower_15.transpose) 5 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_15_5_6 : MatrixCompute.compressed 15 candidateY_15 candidateZ_15 5 6 =
    (lower_15 * Matrix.diagonal pivots_15 * lower_15.transpose) 5 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_15_5_7 : MatrixCompute.compressed 15 candidateY_15 candidateZ_15 5 7 =
    (lower_15 * Matrix.diagonal pivots_15 * lower_15.transpose) 5 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
