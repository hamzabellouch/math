import OAI.Analysis.Laughlin.FiniteFlux.Row07
import OAI.Analysis.Laughlin.FourBody.Symmetry

namespace OAI

namespace Laughlin.Certificate

theorem yRow_7_5_1_3 : yRow 7 5 1 (rows[3]!) = (126559883614713029393025 / 117440512 : ℚ) := by
  rw [yRow_swap 7 5 1 (rows[3]!) (rows_valid _ (by decide +kernel))]
  exact yRow_7_1_5_3

end Laughlin.Certificate

end OAI
