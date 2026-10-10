import OAI.Analysis.Laughlin.FiniteFlux.Row072
import OAI.Analysis.Laughlin.FourBody.Symmetry

namespace OAI

namespace Laughlin.Certificate

theorem yRow_7_7_5_3 : yRow 7 7 5 (rows[3]!) = (2694741498446716664085 / 2097152 : ℚ) := by
  rw [yRow_swap 7 7 5 (rows[3]!) (rows_valid _ (by decide +kernel))]
  exact yRow_7_5_7_3

end Laughlin.Certificate

end OAI
