import OAI.Analysis.Laughlin.FiniteFlux.Row072
import OAI.Analysis.Laughlin.FourBody.Symmetry

namespace OAI

namespace Laughlin.Certificate

theorem yRow_7_7_1_4 : yRow 7 7 1 (rows[4]!) = (20867558445854020401465 / 33554432 : ℚ) := by
  rw [yRow_swap 7 7 1 (rows[4]!) (rows_valid _ (by decide +kernel))]
  exact yRow_7_1_7_4

end Laughlin.Certificate

end OAI
