import OAI.Analysis.Laughlin.FiniteFlux.Row072
import OAI.Analysis.Laughlin.FourBody.Symmetry

namespace OAI

namespace Laughlin.Certificate

theorem yRow_7_5_3_5 : yRow 7 5 3 (rows[5]!) = (310146766753353391486215 / 939524096 : ℚ) := by
  rw [yRow_swap 7 5 3 (rows[5]!) (rows_valid _ (by decide +kernel))]
  exact yRow_7_3_5_5

end Laughlin.Certificate

end OAI
