import OAI.Analysis.Laughlin.FiniteFlux.GramData16
import OAI.Analysis.Laughlin.FiniteFlux.LDLData16

namespace OAI

namespace Laughlin.Certificate

theorem ldl_16 : compressedRational 16 =
    lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose := by
  rw [compressedRational_eq_compute, error_16, gram_16]
  exact candidateLDL_16

theorem four_body_16_positive :
    ((compressedRational 16).map (Rat.castHom ℝ)).PosSemidef := by
  apply rational_ldl_positive _ lower_16 pivots_16 ldl_16
  intro i
  fin_cases i <;> norm_num [pivots_16]

end Laughlin.Certificate

end OAI
