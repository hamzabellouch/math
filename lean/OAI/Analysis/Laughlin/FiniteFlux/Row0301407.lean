import OAI.Analysis.Laughlin.FiniteFlux.Row07
import OAI.Analysis.Laughlin.FourBody.Symmetry

namespace OAI

namespace Laughlin.Certificate

theorem yRow_7_3_1_4 : yRow 7 3 1 (rows[4]!) = (3528819936117742548165 / 58720256 : ℚ) := by
  rw [yRow_swap 7 3 1 (rows[4]!) (rows_valid _ (by decide +kernel))]
  exact yRow_7_1_3_4

end Laughlin.Certificate

end OAI
