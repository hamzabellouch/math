import OAI.Analysis.Laughlin.FiniteFlux.Row07
import OAI.Analysis.Laughlin.FourBody.Symmetry

namespace OAI

namespace Laughlin.Certificate

theorem yRow_7_3_1_5 : yRow 7 3 1 (rows[5]!) = (-29217720453316236095145 / 939524096 : ℚ) := by
  rw [yRow_swap 7 3 1 (rows[5]!) (rows_valid _ (by decide +kernel))]
  exact yRow_7_1_3_5

end Laughlin.Certificate

end OAI
