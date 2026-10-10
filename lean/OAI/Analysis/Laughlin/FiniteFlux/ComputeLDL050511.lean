import OAI.Analysis.Laughlin.FiniteFlux.Data11

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_11_5_5 : MatrixCompute.compressed 11 candidateY_11 candidateZ_11 5 5 =
    (lower_11 * Matrix.diagonal pivots_11 * lower_11.transpose) 5 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
