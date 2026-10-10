import OAI.Analysis.Laughlin.FiniteFlux.Row07
import OAI.Analysis.Laughlin.FourBody.Symmetry

namespace OAI

namespace Laughlin.Certificate

theorem yRow_7_7_1_3 : yRow 7 7 1 (rows[3]!) = (-12487246647748499348535 / 8388608 : ℚ) := by
  rw [yRow_swap 7 7 1 (rows[3]!) (rows_valid _ (by decide +kernel))]
  exact yRow_7_1_7_3

end Laughlin.Certificate

end OAI
