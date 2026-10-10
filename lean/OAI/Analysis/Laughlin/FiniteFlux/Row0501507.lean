import OAI.Analysis.Laughlin.FiniteFlux.Row07
import OAI.Analysis.Laughlin.FourBody.Symmetry

namespace OAI

namespace Laughlin.Certificate

theorem yRow_7_5_1_5 : yRow 7 5 1 (rows[5]!) = (486363383031076447124835 / 1879048192 : ℚ) := by
  rw [yRow_swap 7 5 1 (rows[5]!) (rows_valid _ (by decide +kernel))]
  exact yRow_7_1_5_5

end Laughlin.Certificate

end OAI
