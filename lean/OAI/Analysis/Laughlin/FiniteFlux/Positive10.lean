import OAI.Analysis.Laughlin.FiniteFlux.GramData10
import OAI.Analysis.Laughlin.FiniteFlux.LDLData10

namespace OAI

namespace Laughlin.Certificate

theorem ldl_10 : compressedRational 10 =
    lower_10 * Matrix.diagonal pivots_10 * lower_10.transpose := by
  rw [compressedRational_eq_compute, error_10, gram_10]
  exact candidateLDL_10

theorem four_body_10_positive :
    ((compressedRational 10).map (Rat.castHom ℝ)).PosSemidef := by
  apply rational_ldl_positive _ lower_10 pivots_10 ldl_10
  intro i
  fin_cases i <;> norm_num [pivots_10]

end Laughlin.Certificate

end OAI
