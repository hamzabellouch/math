import OAI.Analysis.Laughlin.FiniteFlux.GramData23
import OAI.Analysis.Laughlin.FiniteFlux.LDLData23

namespace OAI

namespace Laughlin.Certificate

theorem ldl_23 : compressedRational 23 =
    lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose := by
  rw [compressedRational_eq_compute, error_23, gram_23]
  exact candidateLDL_23

theorem four_body_23_positive :
    ((compressedRational 23).map (Rat.castHom ℝ)).PosSemidef := by
  apply rational_ldl_positive _ lower_23 pivots_23 ldl_23
  intro i
  fin_cases i <;> norm_num [pivots_23]

end Laughlin.Certificate

end OAI
