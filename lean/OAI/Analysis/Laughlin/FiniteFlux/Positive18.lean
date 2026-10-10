import OAI.Analysis.Laughlin.FiniteFlux.GramData18
import OAI.Analysis.Laughlin.FiniteFlux.LDLData18

namespace OAI

namespace Laughlin.Certificate

theorem ldl_18 : compressedRational 18 =
    lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose := by
  rw [compressedRational_eq_compute, error_18, gram_18]
  exact candidateLDL_18

theorem four_body_18_positive :
    ((compressedRational 18).map (Rat.castHom ℝ)).PosSemidef := by
  apply rational_ldl_positive _ lower_18 pivots_18 ldl_18
  intro i
  fin_cases i <;> norm_num [pivots_18]

end Laughlin.Certificate

end OAI
