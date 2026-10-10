import OAI.Analysis.Laughlin.FiniteFlux.Row07
import OAI.Analysis.Laughlin.FourBody.Symmetry

namespace OAI

namespace Laughlin.Certificate

theorem yRow_7_3_1_3 : yRow 7 3 1 (rows[3]!) = (-12918373159386147536445 / 234881024 : ℚ) := by
  rw [yRow_swap 7 3 1 (rows[3]!) (rows_valid _ (by decide +kernel))]
  exact yRow_7_1_3_3

end Laughlin.Certificate

end OAI
