import OAI.Analysis.Laughlin.FiniteFlux.Row072
import OAI.Analysis.Laughlin.FourBody.Symmetry

namespace OAI

namespace Laughlin.Certificate

theorem yRow_7_5_3_4 : yRow 7 5 3 (rows[4]!) = (-54234982718013152865 / 7340032 : ℚ) := by
  rw [yRow_swap 7 5 3 (rows[4]!) (rows_valid _ (by decide +kernel))]
  exact yRow_7_3_5_4

end Laughlin.Certificate

end OAI
