import OAI.Analysis.Laughlin.FiniteFlux.Row072
import OAI.Analysis.Laughlin.FourBody.Symmetry

namespace OAI

namespace Laughlin.Certificate

theorem yRow_7_7_1_5 : yRow 7 7 1 (rows[5]!) = (-87026179675834894580205 / 134217728 : ℚ) := by
  rw [yRow_swap 7 7 1 (rows[5]!) (rows_valid _ (by decide +kernel))]
  exact yRow_7_1_7_5

end Laughlin.Certificate

end OAI
