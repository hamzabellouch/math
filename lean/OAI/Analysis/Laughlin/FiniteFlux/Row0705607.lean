import OAI.Analysis.Laughlin.FiniteFlux.Row073
import OAI.Analysis.Laughlin.FourBody.Symmetry

namespace OAI

namespace Laughlin.Certificate

theorem yRow_7_7_5_6 : yRow 7 7 5 (rows[6]!) = (21601964370283224165 / 4194304 : ℚ) := by
  rw [yRow_swap 7 7 5 (rows[6]!) (rows_valid _ (by decide +kernel))]
  exact yRow_7_5_7_6

end Laughlin.Certificate

end OAI
