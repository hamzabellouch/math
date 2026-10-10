import OAI.Analysis.Laughlin.FiniteFlux.Row07
import OAI.Analysis.Laughlin.FourBody.Symmetry

namespace OAI

namespace Laughlin.Certificate

theorem yRow_7_5_1_2 : yRow 7 5 1 (rows[2]!) = (50011870045872224797155 / 67108864 : ℚ) := by
  rw [yRow_swap 7 5 1 (rows[2]!) (rows_valid _ (by decide +kernel))]
  exact yRow_7_1_5_2

end Laughlin.Certificate

end OAI
