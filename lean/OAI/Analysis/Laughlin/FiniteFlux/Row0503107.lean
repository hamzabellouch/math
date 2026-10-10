import OAI.Analysis.Laughlin.FiniteFlux.Row072
import OAI.Analysis.Laughlin.FourBody.Symmetry

namespace OAI

namespace Laughlin.Certificate

theorem yRow_7_5_3_1 : yRow 7 5 3 (rows[1]!) = (2141394541249492635 / 8388608 : ℚ) := by
  rw [yRow_swap 7 5 3 (rows[1]!) (rows_valid _ (by decide +kernel))]
  exact yRow_7_3_5_1

end Laughlin.Certificate

end OAI
