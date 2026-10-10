import OAI.Analysis.Laughlin.FiniteFlux.Row073
import OAI.Analysis.Laughlin.FourBody.Symmetry

namespace OAI

namespace Laughlin.Certificate

theorem yRow_7_7_5_4 : yRow 7 7 5 (rows[4]!) = (-3701247860527868239965 / 33554432 : ℚ) := by
  rw [yRow_swap 7 7 5 (rows[4]!) (rows_valid _ (by decide +kernel))]
  exact yRow_7_5_7_4

end Laughlin.Certificate

end OAI
