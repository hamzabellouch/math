import OAI.Analysis.Laughlin.FiniteFlux.Data15

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_15_4_0 : MatrixCompute.compressed 15 candidateY_15 candidateZ_15 4 0 =
    (lower_15 * Matrix.diagonal pivots_15 * lower_15.transpose) 4 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_15_4_1 : MatrixCompute.compressed 15 candidateY_15 candidateZ_15 4 1 =
    (lower_15 * Matrix.diagonal pivots_15 * lower_15.transpose) 4 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_15_4_2 : MatrixCompute.compressed 15 candidateY_15 candidateZ_15 4 2 =
    (lower_15 * Matrix.diagonal pivots_15 * lower_15.transpose) 4 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_15_4_3 : MatrixCompute.compressed 15 candidateY_15 candidateZ_15 4 3 =
    (lower_15 * Matrix.diagonal pivots_15 * lower_15.transpose) 4 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_15_4_4 : MatrixCompute.compressed 15 candidateY_15 candidateZ_15 4 4 =
    (lower_15 * Matrix.diagonal pivots_15 * lower_15.transpose) 4 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_15_4_5 : MatrixCompute.compressed 15 candidateY_15 candidateZ_15 4 5 =
    (lower_15 * Matrix.diagonal pivots_15 * lower_15.transpose) 4 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_15_4_6 : MatrixCompute.compressed 15 candidateY_15 candidateZ_15 4 6 =
    (lower_15 * Matrix.diagonal pivots_15 * lower_15.transpose) 4 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_15_4_7 : MatrixCompute.compressed 15 candidateY_15 candidateZ_15 4 7 =
    (lower_15 * Matrix.diagonal pivots_15 * lower_15.transpose) 4 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
