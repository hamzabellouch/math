import OAI.Analysis.Laughlin.FiniteFlux.GramData14
import OAI.Analysis.Laughlin.FiniteFlux.LDLData14

namespace OAI

namespace Laughlin.Certificate

theorem ldl_14 : compressedRational 14 =
    lower_14 * Matrix.diagonal pivots_14 * lower_14.transpose := by
  rw [compressedRational_eq_compute, error_14, gram_14]
  exact candidateLDL_14

theorem four_body_14_positive :
    ((compressedRational 14).map (Rat.castHom ℝ)).PosSemidef := by
  apply rational_ldl_positive _ lower_14 pivots_14 ldl_14
  intro i
  fin_cases i <;> norm_num [pivots_14]

end Laughlin.Certificate

end OAI
