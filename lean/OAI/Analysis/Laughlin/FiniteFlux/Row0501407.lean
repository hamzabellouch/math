import OAI.Analysis.Laughlin.FiniteFlux.Row07
import OAI.Analysis.Laughlin.FourBody.Symmetry

namespace OAI

namespace Laughlin.Certificate

theorem yRow_7_5_1_4 : yRow 7 5 1 (rows[4]!) = (-46679206856806148273295 / 469762048 : ℚ) := by
  rw [yRow_swap 7 5 1 (rows[4]!) (rows_valid _ (by decide +kernel))]
  exact yRow_7_1_5_4

end Laughlin.Certificate

end OAI
