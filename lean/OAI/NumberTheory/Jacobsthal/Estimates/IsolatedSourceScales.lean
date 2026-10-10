import OAI.NumberTheory.Jacobsthal.Primes.CrossingPrimeBin
import OAI.NumberTheory.Jacobsthal.Primes.PaperMissingPrimeWindow

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.IsolatedSourceScales
open _root_.Filter PaperMissingPrimeWindow JacobsthalSourceScale
open scoped Topology

theorem source_isolated_search_scale {alpha : ℝ} (ha : 0 < alpha) :
    ∀ᶠ L : ℝ in atTop,(sourceW L)^((1/4:ℝ)) ≤ alpha*sourceB L := by
  have ht := (tendsto_rpow_atTop (show 0 < (3/4:ℝ) by norm_num)).comp sourceW_tendsto
  filter_upwards [sourceW_le_sourceB_eventually,sourceW_tendsto.eventually_gt_atTop 0,
    ht.eventually_ge_atTop (1/alpha)] with L hB hw hpow
  change 1/alpha ≤ (sourceW L)^((3/4:ℝ)) at hpow
  have hprod : (sourceW L)^((1/4:ℝ))*(sourceW L)^((3/4:ℝ))=sourceW L := by
    rw [← Real.rpow_add hw]
    norm_num
  have hlow := mul_le_mul_of_nonneg_left hpow (Real.rpow_pos_of_pos hw (1/4:ℝ)).le
  rw [hprod] at hlow
  have hmain : (sourceW L)^((1/4:ℝ)) ≤ alpha*sourceW L := by
    have hm := mul_le_mul_of_nonneg_left hlow ha.le
    field_simp [ha.ne'] at hm
    nlinarith
  exact hmain.trans (mul_le_mul_of_nonneg_left hB ha.le)
end NumberTheoryLean.IsolatedSourceScales


end Erdos970

end OAI
