import OAI.Analysis.Laughlin.FiniteFlux.GramData21
import OAI.Analysis.Laughlin.FiniteFlux.LDLData21

namespace OAI

namespace Laughlin.Certificate

theorem ldl_21 : compressedRational 21 =
    lower_21 * Matrix.diagonal pivots_21 * lower_21.transpose := by
  rw [compressedRational_eq_compute, error_21, gram_21]
  exact candidateLDL_21

theorem four_body_21_positive :
    ((compressedRational 21).map (Rat.castHom ℝ)).PosSemidef := by
  apply rational_ldl_positive _ lower_21 pivots_21 ldl_21
  intro i
  fin_cases i <;> norm_num [pivots_21]

end Laughlin.Certificate

end OAI
