import OAI.Analysis.LienardCycles.Schwarzian

namespace OAI

open Set Filter Metric
open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.ReferenceCharacteristic
lemma D_pos_of_A_nonneg {z k r : ℝ} (hk : 0 < k) (hr : 0 < r)
    (hA : 0 ≤ A ((z,k),r)) : 0 < D ((z,k),r) := by
  apply strictMono_zero_pos hr (D_tendsto_zero z k)
  apply strictMonoOn_of_deriv_pos (convex_Ioc 0 r)
    (fun s hs => (D_deriv hs.1).continuousAt.continuousWithinAt)
  intro s hs
  rw [interior_Ioc] at hs
  rw [(D_deriv (z := z) (k := k) hs.1).deriv]
  exact div_pos (mul_pos (mul_pos (by norm_num) (A_pos_before hk hr hA hs.1 hs.2))
    (D_gap_pos hs.1)) (mul_pos hs.1 (A_gap_pos hs.1))
end QuinticLienard.ReferenceCharacteristic

end OAI
