import OAI.Analysis.Laughlin.FiniteFlux.GramData11
import OAI.Analysis.Laughlin.FiniteFlux.LDLData11

namespace OAI

namespace Laughlin.Certificate

theorem ldl_11 : compressedRational 11 =
    lower_11 * Matrix.diagonal pivots_11 * lower_11.transpose := by
  rw [compressedRational_eq_compute, error_11, gram_11]
  exact candidateLDL_11

theorem four_body_11_positive :
    ((compressedRational 11).map (Rat.castHom ℝ)).PosSemidef := by
  apply rational_ldl_positive _ lower_11 pivots_11 ldl_11
  intro i
  fin_cases i <;> norm_num [pivots_11]

end Laughlin.Certificate

end OAI
