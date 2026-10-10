import OAI.Analysis.Laughlin.FiniteFlux.Row07
import OAI.Analysis.Laughlin.FourBody.Symmetry

namespace OAI

namespace Laughlin.Certificate

theorem yRow_7_3_1_6 : yRow 7 3 1 (rows[6]!) = (-76772184534764046045 / 8388608 : ℚ) := by
  rw [yRow_swap 7 3 1 (rows[6]!) (rows_valid _ (by decide +kernel))]
  exact yRow_7_1_3_6

end Laughlin.Certificate

end OAI
