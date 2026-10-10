import OAI.Analysis.Laughlin.FiniteFlux.Row072
import OAI.Analysis.Laughlin.FourBody.Symmetry

namespace OAI

namespace Laughlin.Certificate

theorem yRow_7_7_3_0 : yRow 7 7 3 (rows[0]!) = (-1488415248143087355 / 2048 : ℚ) := by
  rw [yRow_swap 7 7 3 (rows[0]!) (rows_valid _ (by decide +kernel))]
  exact yRow_7_3_7_0

end Laughlin.Certificate

end OAI
