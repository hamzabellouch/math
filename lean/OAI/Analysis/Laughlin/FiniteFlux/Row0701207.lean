import OAI.Analysis.Laughlin.FiniteFlux.Row07
import OAI.Analysis.Laughlin.FourBody.Symmetry

namespace OAI

namespace Laughlin.Certificate

theorem yRow_7_7_1_2 : yRow 7 7 1 (rows[2]!) = (207794480500460556638835 / 33554432 : ℚ) := by
  rw [yRow_swap 7 7 1 (rows[2]!) (rows_valid _ (by decide +kernel))]
  exact yRow_7_1_7_2

end Laughlin.Certificate

end OAI
