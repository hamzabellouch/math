import OAI.Analysis.Laughlin.FiniteFlux.GramData17
import OAI.Analysis.Laughlin.FiniteFlux.LDLData17

namespace OAI

namespace Laughlin.Certificate

theorem ldl_17 : compressedRational 17 =
    lower_17 * Matrix.diagonal pivots_17 * lower_17.transpose := by
  rw [compressedRational_eq_compute, error_17, gram_17]
  exact candidateLDL_17

theorem four_body_17_positive :
    ((compressedRational 17).map (Rat.castHom ℝ)).PosSemidef := by
  apply rational_ldl_positive _ lower_17 pivots_17 ldl_17
  intro i
  fin_cases i <;> norm_num [pivots_17]

end Laughlin.Certificate

end OAI
