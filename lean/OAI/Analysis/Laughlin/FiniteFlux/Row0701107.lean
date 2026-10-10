import OAI.Analysis.Laughlin.FiniteFlux.Row07
import OAI.Analysis.Laughlin.FourBody.Symmetry

namespace OAI

namespace Laughlin.Certificate

theorem yRow_7_7_1_1 : yRow 7 7 1 (rows[1]!) = (34459028886161906571 / 8388608 : ℚ) := by
  rw [yRow_swap 7 7 1 (rows[1]!) (rows_valid _ (by decide +kernel))]
  exact yRow_7_1_7_1

end Laughlin.Certificate

end OAI
