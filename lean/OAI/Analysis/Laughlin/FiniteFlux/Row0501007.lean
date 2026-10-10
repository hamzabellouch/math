import OAI.Analysis.Laughlin.FiniteFlux.Row07
import OAI.Analysis.Laughlin.FourBody.Symmetry

namespace OAI

namespace Laughlin.Certificate

theorem yRow_7_5_1_0 : yRow 7 5 1 (rows[0]!) = (205314913297683315 / 256 : ℚ) := by
  rw [yRow_swap 7 5 1 (rows[0]!) (rows_valid _ (by decide +kernel))]
  exact yRow_7_1_5_0

end Laughlin.Certificate

end OAI
