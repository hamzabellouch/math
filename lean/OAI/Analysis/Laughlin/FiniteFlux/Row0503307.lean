import OAI.Analysis.Laughlin.FiniteFlux.Row072
import OAI.Analysis.Laughlin.FourBody.Symmetry

namespace OAI

namespace Laughlin.Certificate

theorem yRow_7_5_3_3 : yRow 7 5 3 (rows[3]!) = (-14416679890174213591545 / 58720256 : ℚ) := by
  rw [yRow_swap 7 5 3 (rows[3]!) (rows_valid _ (by decide +kernel))]
  exact yRow_7_3_5_3

end Laughlin.Certificate

end OAI
