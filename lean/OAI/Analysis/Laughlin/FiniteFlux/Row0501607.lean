import OAI.Analysis.Laughlin.FiniteFlux.Row07
import OAI.Analysis.Laughlin.FourBody.Symmetry

namespace OAI

namespace Laughlin.Certificate

theorem yRow_7_5_1_6 : yRow 7 5 1 (rows[6]!) = (-620279821822140423225 / 33554432 : ℚ) := by
  rw [yRow_swap 7 5 1 (rows[6]!) (rows_valid _ (by decide +kernel))]
  exact yRow_7_1_5_6

end Laughlin.Certificate

end OAI
