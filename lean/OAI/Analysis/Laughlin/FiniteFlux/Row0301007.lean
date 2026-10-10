import OAI.Analysis.Laughlin.FiniteFlux.Row07
import OAI.Analysis.Laughlin.FourBody.Symmetry

namespace OAI

namespace Laughlin.Certificate

theorem yRow_7_3_1_0 : yRow 7 3 1 (rows[0]!) = (-3670890702116855625 / 8192 : ℚ) := by
  rw [yRow_swap 7 3 1 (rows[0]!) (rows_valid _ (by decide +kernel))]
  exact yRow_7_1_3_0

end Laughlin.Certificate

end OAI
