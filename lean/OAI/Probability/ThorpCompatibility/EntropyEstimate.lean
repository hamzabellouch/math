import Mathlib
import OAI.Probability.ThorpCompatibility.ExposureEntropy
import OAI.Probability.ThorpCompatibility.GridDeficits

namespace OAI

open scoped Classical
namespace ThorpCompatibility
open Finset
lemma grid_entropy_estimate {A D : ℕ} (hD : 2 ≤ D) (Q : Law (Grid A D))
    (hQ : ∀ a, 0 < Q.mass a → Compatible a.1 a.2) {m : ℝ}
    (hm : 0 < m) (hl : 1000 ≤ Real.log m)
    (hmgf : uniformMean (fun r : Rows A D =>
      Real.exp ((1/400 * Real.log m) * clumpCount (m^(1/100:ℝ)) r)) ≤ 2) :
    (A : ℝ)*D - totalExposureError A D (m^(1/100:ℝ)) (m^(1/100:ℝ)) - 1 +
      (1 - 1000/Real.log m) * (rowDeficit Q + colDeficit Q) ≤ Q.uniformDeficit := by
  have h := grid_entropy_charge hD Q hQ (Real.rpow_nonneg hm.le (1/100:ℝ))
    (Real.rpow_nonneg hm.le (1/100:ℝ))
  have hj := grid_deficit_decomposition Q
  apply absorb_entropy_losses hl (rowDeficit_nonneg Q) (rowDeficit_le_joint Q)
    (colDeficit_nonneg Q) (heavyTotal_log_bound Q hm (le_trans (by norm_num) hl))
    (clump_deficit_bound Q m hmgf)
  change Q.uniformDeficit = jointRowDeficit Q + colDeficit Q + _ at hj
  change _ - 3 * heavyTotal Q (m^(1/100:ℝ)) - _ ≤ _ at h
  linarith

end ThorpCompatibility

end OAI
