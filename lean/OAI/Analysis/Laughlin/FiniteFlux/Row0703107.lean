import OAI.Analysis.Laughlin.FiniteFlux.Row072
import OAI.Analysis.Laughlin.FourBody.Symmetry

namespace OAI

namespace Laughlin.Certificate

theorem yRow_7_7_3_1 : yRow 7 7 3 (rows[1]!) = (9225871950243624195 / 4194304 : ℚ) := by
  rw [yRow_swap 7 7 3 (rows[1]!) (rows_valid _ (by decide +kernel))]
  exact yRow_7_3_7_1

end Laughlin.Certificate

end OAI
