import OAI.Analysis.Laughlin.FiniteFlux.GramData20
import OAI.Analysis.Laughlin.FiniteFlux.LDLData20

namespace OAI

namespace Laughlin.Certificate

theorem ldl_20 : compressedRational 20 =
    lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose := by
  rw [compressedRational_eq_compute, error_20, gram_20]
  exact candidateLDL_20

theorem four_body_20_positive :
    ((compressedRational 20).map (Rat.castHom ℝ)).PosSemidef := by
  apply rational_ldl_positive _ lower_20 pivots_20 ldl_20
  intro i
  fin_cases i <;> norm_num [pivots_20]

end Laughlin.Certificate

end OAI
