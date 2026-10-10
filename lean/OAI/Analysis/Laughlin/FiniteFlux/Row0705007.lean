import OAI.Analysis.Laughlin.FiniteFlux.Row072
import OAI.Analysis.Laughlin.FourBody.Symmetry

namespace OAI

namespace Laughlin.Certificate

theorem yRow_7_7_5_0 : yRow 7 7 5 (rows[0]!) = (1153158553770801165 / 128 : ℚ) := by
  rw [yRow_swap 7 7 5 (rows[0]!) (rows_valid _ (by decide +kernel))]
  exact yRow_7_5_7_0

end Laughlin.Certificate

end OAI
