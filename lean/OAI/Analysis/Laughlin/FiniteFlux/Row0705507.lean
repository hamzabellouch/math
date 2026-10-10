import OAI.Analysis.Laughlin.FiniteFlux.Row073
import OAI.Analysis.Laughlin.FourBody.Symmetry

namespace OAI

namespace Laughlin.Certificate

theorem yRow_7_7_5_5 : yRow 7 7 5 (rows[5]!) = (-111316765905740996833665 / 134217728 : ℚ) := by
  rw [yRow_swap 7 7 5 (rows[5]!) (rows_valid _ (by decide +kernel))]
  exact yRow_7_5_7_5

end Laughlin.Certificate

end OAI
