import OAI.Analysis.Laughlin.FiniteFlux.Row072
import OAI.Analysis.Laughlin.FourBody.Symmetry

namespace OAI

namespace Laughlin.Certificate

theorem yRow_7_7_1_6 : yRow 7 7 1 (rows[6]!) = (201099333031028464725 / 4194304 : ℚ) := by
  rw [yRow_swap 7 7 1 (rows[6]!) (rows_valid _ (by decide +kernel))]
  exact yRow_7_1_7_6

end Laughlin.Certificate

end OAI
