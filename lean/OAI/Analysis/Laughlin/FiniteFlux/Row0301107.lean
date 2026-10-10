import OAI.Analysis.Laughlin.FiniteFlux.Row07
import OAI.Analysis.Laughlin.FourBody.Symmetry

namespace OAI

namespace Laughlin.Certificate

theorem yRow_7_3_1_1 : yRow 7 3 1 (rows[1]!) = (-28502538608116390869 / 33554432 : ℚ) := by
  rw [yRow_swap 7 3 1 (rows[1]!) (rows_valid _ (by decide +kernel))]
  exact yRow_7_1_3_1

end Laughlin.Certificate

end OAI
