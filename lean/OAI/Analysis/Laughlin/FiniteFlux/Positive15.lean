import OAI.Analysis.Laughlin.FiniteFlux.GramData15
import OAI.Analysis.Laughlin.FiniteFlux.LDLData15

namespace OAI

namespace Laughlin.Certificate

theorem ldl_15 : compressedRational 15 =
    lower_15 * Matrix.diagonal pivots_15 * lower_15.transpose := by
  rw [compressedRational_eq_compute, error_15, gram_15]
  exact candidateLDL_15

theorem four_body_15_positive :
    ((compressedRational 15).map (Rat.castHom ℝ)).PosSemidef := by
  apply rational_ldl_positive _ lower_15 pivots_15 ldl_15
  intro i
  fin_cases i <;> norm_num [pivots_15]

end Laughlin.Certificate

end OAI
