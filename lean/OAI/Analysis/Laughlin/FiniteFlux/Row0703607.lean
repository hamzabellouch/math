import OAI.Analysis.Laughlin.FiniteFlux.Row072
import OAI.Analysis.Laughlin.FourBody.Symmetry

namespace OAI

namespace Laughlin.Certificate

theorem yRow_7_7_3_6 : yRow 7 7 3 (rows[6]!) = (47466735597972069435 / 1048576 : ℚ) := by
  rw [yRow_swap 7 7 3 (rows[6]!) (rows_valid _ (by decide +kernel))]
  exact yRow_7_3_7_6

end Laughlin.Certificate

end OAI
