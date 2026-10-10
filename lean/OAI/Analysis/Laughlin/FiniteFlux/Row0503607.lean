import OAI.Analysis.Laughlin.FiniteFlux.Row072
import OAI.Analysis.Laughlin.FourBody.Symmetry

namespace OAI

namespace Laughlin.Certificate

theorem yRow_7_5_3_6 : yRow 7 5 3 (rows[6]!) = (-50552514240995949885 / 16777216 : ℚ) := by
  rw [yRow_swap 7 5 3 (rows[6]!) (rows_valid _ (by decide +kernel))]
  exact yRow_7_3_5_6

end Laughlin.Certificate

end OAI
