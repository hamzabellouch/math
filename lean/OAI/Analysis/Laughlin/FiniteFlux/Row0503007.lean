import OAI.Analysis.Laughlin.FiniteFlux.Row072
import OAI.Analysis.Laughlin.FourBody.Symmetry

namespace OAI

namespace Laughlin.Certificate

theorem yRow_7_5_3_0 : yRow 7 5 3 (rows[0]!) = (11065428419616135 / 1024 : ℚ) := by
  rw [yRow_swap 7 5 3 (rows[0]!) (rows_valid _ (by decide +kernel))]
  exact yRow_7_3_5_0

end Laughlin.Certificate

end OAI
