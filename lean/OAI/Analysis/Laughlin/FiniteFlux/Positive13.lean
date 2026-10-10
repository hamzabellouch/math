import OAI.Analysis.Laughlin.FiniteFlux.GramData13
import OAI.Analysis.Laughlin.FiniteFlux.LDLData13

namespace OAI

namespace Laughlin.Certificate

theorem ldl_13 : compressedRational 13 =
    lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose := by
  rw [compressedRational_eq_compute, error_13, gram_13]
  exact candidateLDL_13

theorem four_body_13_positive :
    ((compressedRational 13).map (Rat.castHom ℝ)).PosSemidef := by
  apply rational_ldl_positive _ lower_13 pivots_13 ldl_13
  intro i
  fin_cases i <;> norm_num [pivots_13]

end Laughlin.Certificate

end OAI
