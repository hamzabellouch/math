import OAI.Analysis.Laughlin.FiniteFlux.Row072
import OAI.Analysis.Laughlin.FourBody.Symmetry

namespace OAI

namespace Laughlin.Certificate

theorem yRow_7_7_3_4 : yRow 7 7 3 (rows[4]!) = (-1462389462807293524305 / 8388608 : ℚ) := by
  rw [yRow_swap 7 7 3 (rows[4]!) (rows_valid _ (by decide +kernel))]
  exact yRow_7_3_7_4

end Laughlin.Certificate

end OAI
