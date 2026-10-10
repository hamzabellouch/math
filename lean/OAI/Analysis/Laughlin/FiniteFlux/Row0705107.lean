import OAI.Analysis.Laughlin.FiniteFlux.Row072
import OAI.Analysis.Laughlin.FourBody.Symmetry

namespace OAI

namespace Laughlin.Certificate

theorem yRow_7_7_5_1 : yRow 7 7 5 (rows[1]!) = (398875219468930779 / 2097152 : ℚ) := by
  rw [yRow_swap 7 7 5 (rows[1]!) (rows_valid _ (by decide +kernel))]
  exact yRow_7_5_7_1

end Laughlin.Certificate

end OAI
