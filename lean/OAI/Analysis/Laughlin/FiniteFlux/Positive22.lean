import OAI.Analysis.Laughlin.FiniteFlux.GramData22
import OAI.Analysis.Laughlin.FiniteFlux.LDLData22

namespace OAI

namespace Laughlin.Certificate

theorem ldl_22 : compressedRational 22 =
    lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose := by
  rw [compressedRational_eq_compute, error_22, gram_22]
  exact candidateLDL_22

theorem four_body_22_positive :
    ((compressedRational 22).map (Rat.castHom ℝ)).PosSemidef := by
  apply rational_ldl_positive _ lower_22 pivots_22 ldl_22
  intro i
  fin_cases i <;> norm_num [pivots_22]

end Laughlin.Certificate

end OAI
