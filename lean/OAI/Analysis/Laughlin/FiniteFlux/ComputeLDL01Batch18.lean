import OAI.Analysis.Laughlin.FiniteFlux.Data18

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_18_1_0 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 1 0 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 1 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_1_1 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 1 1 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 1 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_1_2 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 1 2 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 1 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_1_3 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 1 3 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 1 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_1_4 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 1 4 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 1 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_1_5 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 1 5 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 1 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_1_6 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 1 6 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 1 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_1_7 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 1 7 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 1 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_1_8 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 1 8 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 1 8 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
