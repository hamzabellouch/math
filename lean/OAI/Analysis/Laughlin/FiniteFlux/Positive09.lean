import OAI.Analysis.Laughlin.FiniteFlux.GramData09
import OAI.Analysis.Laughlin.FiniteFlux.LDLData09

namespace OAI

namespace Laughlin.Certificate

theorem ldl_9 : compressedRational 9 =
    lower_9 * Matrix.diagonal pivots_9 * lower_9.transpose := by
  rw [compressedRational_eq_compute, error_9, gram_9]
  exact candidateLDL_9

theorem four_body_9_positive :
    ((compressedRational 9).map (Rat.castHom ℝ)).PosSemidef := by
  apply rational_ldl_positive _ lower_9 pivots_9 ldl_9
  intro i
  fin_cases i <;> norm_num [pivots_9]

end Laughlin.Certificate

end OAI
