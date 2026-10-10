import OAI.Analysis.Laughlin.FiniteFlux.Row072
import OAI.Analysis.Laughlin.FourBody.Symmetry

namespace OAI

namespace Laughlin.Certificate

theorem yRow_7_7_3_5 : yRow 7 7 3 (rows[5]!) = (51986196748062068309475 / 67108864 : ℚ) := by
  rw [yRow_swap 7 7 3 (rows[5]!) (rows_valid _ (by decide +kernel))]
  exact yRow_7_3_7_5

end Laughlin.Certificate

end OAI
