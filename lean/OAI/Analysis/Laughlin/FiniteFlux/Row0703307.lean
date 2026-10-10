import OAI.Analysis.Laughlin.FiniteFlux.Row072
import OAI.Analysis.Laughlin.FourBody.Symmetry

namespace OAI

namespace Laughlin.Certificate

theorem yRow_7_7_3_3 : yRow 7 7 3 (rows[3]!) = (-6304209573025048032825 / 4194304 : ℚ) := by
  rw [yRow_swap 7 7 3 (rows[3]!) (rows_valid _ (by decide +kernel))]
  exact yRow_7_3_7_3

end Laughlin.Certificate

end OAI
