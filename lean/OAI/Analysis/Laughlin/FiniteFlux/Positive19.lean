import OAI.Analysis.Laughlin.FiniteFlux.GramData19
import OAI.Analysis.Laughlin.FiniteFlux.LDLData19

namespace OAI

namespace Laughlin.Certificate

theorem ldl_19 : compressedRational 19 =
    lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose := by
  rw [compressedRational_eq_compute, error_19, gram_19]
  exact candidateLDL_19

theorem four_body_19_positive :
    ((compressedRational 19).map (Rat.castHom ℝ)).PosSemidef := by
  apply rational_ldl_positive _ lower_19 pivots_19 ldl_19
  intro i
  fin_cases i <;> norm_num [pivots_19]

end Laughlin.Certificate

end OAI
