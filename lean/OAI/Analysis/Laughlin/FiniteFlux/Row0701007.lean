import OAI.Analysis.Laughlin.FiniteFlux.Row07
import OAI.Analysis.Laughlin.FourBody.Symmetry

namespace OAI

namespace Laughlin.Certificate

theorem yRow_7_7_1_0 : yRow 7 7 1 (rows[0]!) = (15514482988745341335 / 2048 : ℚ) := by
  rw [yRow_swap 7 7 1 (rows[0]!) (rows_valid _ (by decide +kernel))]
  exact yRow_7_1_7_0

end Laughlin.Certificate

end OAI
