import OAI.Analysis.Laughlin.FiniteFlux.Row07
import OAI.Analysis.Laughlin.FourBody.Symmetry

namespace OAI

namespace Laughlin.Certificate

theorem yRow_7_5_1_1 : yRow 7 5 1 (rows[1]!) = (-2180568515710116549 / 16777216 : ℚ) := by
  rw [yRow_swap 7 5 1 (rows[1]!) (rows_valid _ (by decide +kernel))]
  exact yRow_7_1_5_1

end Laughlin.Certificate

end OAI
