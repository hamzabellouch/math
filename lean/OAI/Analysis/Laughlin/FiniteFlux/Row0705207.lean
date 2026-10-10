import OAI.Analysis.Laughlin.FiniteFlux.Row072
import OAI.Analysis.Laughlin.FourBody.Symmetry

namespace OAI

namespace Laughlin.Certificate

theorem yRow_7_7_5_2 : yRow 7 7 5 (rows[2]!) = (-3344728266700356251085 / 8388608 : ℚ) := by
  rw [yRow_swap 7 7 5 (rows[2]!) (rows_valid _ (by decide +kernel))]
  exact yRow_7_5_7_2

end Laughlin.Certificate

end OAI
