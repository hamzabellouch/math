import OAI.Analysis.Laughlin.FiniteFlux.GramData12
import OAI.Analysis.Laughlin.FiniteFlux.LDLData12

namespace OAI

namespace Laughlin.Certificate

theorem ldl_12 : compressedRational 12 =
    lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose := by
  rw [compressedRational_eq_compute, error_12, gram_12]
  exact candidateLDL_12

theorem four_body_12_positive :
    ((compressedRational 12).map (Rat.castHom ℝ)).PosSemidef := by
  apply rational_ldl_positive _ lower_12 pivots_12 ldl_12
  intro i
  fin_cases i <;> norm_num [pivots_12]

end Laughlin.Certificate

end OAI
