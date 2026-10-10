import OAI.Analysis.Laughlin.FiniteFlux.Row072
import OAI.Analysis.Laughlin.FourBody.Symmetry

namespace OAI

namespace Laughlin.Certificate

theorem yRow_7_5_3_2 : yRow 7 5 3 (rows[2]!) = (-23803270741598517863565 / 33554432 : ℚ) := by
  rw [yRow_swap 7 5 3 (rows[2]!) (rows_valid _ (by decide +kernel))]
  exact yRow_7_3_5_2

end Laughlin.Certificate

end OAI
