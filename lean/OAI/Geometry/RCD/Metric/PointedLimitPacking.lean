import OAI.Geometry.RCD.Metric.ApproximatePacking
import OAI.Geometry.RCD.Metric.ApproximationRestriction

namespace OAI

/-! # The exact dimensional packing bound in an arbitrary metric limit -/

open Set Filter Metric MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  [MetricSpace Y] {K : ℝ} {n : ℕ}

theorem NoncollapsedRCD.pointed_limit_packing (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n)
    {q : Y} (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Y)
    (hr : ∀ k, 0 < r k) (hε : Tendsto ε atTop (𝓝 0))
    (hcurv : ∀ k, -1 ≤ K*(4*r k)^2)
    (hV : ∀ k, IsPointedApproximation (p k) q (r k) 5 (ε k) (V k))
    {ι : Type*} [Fintype ι] (v : ι → Y) {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1)
    (hv : ∀ i, dist (v i) q ≤ 1/2) (hsep : Pairwise (fun i j => d ≤ dist (v i) (v j))) :
    (Fintype.card ι:ℝ)*(d/2)^n ≤ Real.cosh 1^(n-1)*8^n := by
  have hpos : 0 < min (d/18) (1/6:ℝ) := lt_min (by positivity) (by norm_num)
  have hs := hε.eventually (gt_mem_nhds hpos)
  obtain ⟨k,hk⟩ := hs.exists
  have he0 : 0 ≤ ε k := dist_nonneg.trans (hV k).1
  have hsmall := lt_min_iff.mp hk
  have hsmallV := (hV k).restrict_radius (hr k) (by norm_num : (0:ℝ)≤1)
    (by norm_num : (1:ℝ)≤5) he0
  exact hX.approximate_target_packing hn (hr k) hd (by linarith) (by linarith [hsmall.1])
    (hcurv k) hsmallV v (fun i => (hv i).trans (by linarith [hsmall.2])) hsep

end RegularPointCoordinates

end

end OAI
