import OAI.Analysis.Laughlin.FiniteFlux.Row07
import OAI.Analysis.Laughlin.FourBody.Symmetry

namespace OAI

namespace Laughlin.Certificate

theorem yRow_7_3_1_2 : yRow 7 3 1 (rows[2]!) = (2988849553778345597235 / 134217728 : ℚ) := by
  rw [yRow_swap 7 3 1 (rows[2]!) (rows_valid _ (by decide +kernel))]
  exact yRow_7_1_3_2

end Laughlin.Certificate

end OAI
