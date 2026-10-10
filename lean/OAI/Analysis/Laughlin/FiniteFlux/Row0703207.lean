import OAI.Analysis.Laughlin.FiniteFlux.Row072
import OAI.Analysis.Laughlin.FourBody.Symmetry

namespace OAI

namespace Laughlin.Certificate

theorem yRow_7_7_3_2 : yRow 7 7 3 (rows[2]!) = (-3990280684502974026525 / 16777216 : ℚ) := by
  rw [yRow_swap 7 7 3 (rows[2]!) (rows_valid _ (by decide +kernel))]
  exact yRow_7_3_7_2

end Laughlin.Certificate

end OAI
