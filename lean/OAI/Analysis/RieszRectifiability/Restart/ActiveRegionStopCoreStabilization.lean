import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionLimitModel

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology

theorem active_region_stop_core_stabilizes_after_two_levels {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
    (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 ≤ ε) (hεtiny : ε ≤ 1 / 268435456)
    (f : S (supportCellRoot μ R hR k z) → Ambient d)
    (hmodel : IsActiveRegionLimitModel μ R hR k z Good S hS ε f)
    (i : SupportCellDescendant μ R hR k z) (hi : i ∈ cellRegionStops μ R hR k z Good)
    (t : ℕ) (ht : i.depth + 2 ≤ t) :
    Set.range f ∩ closedBall i.center (i.radius / 16) =
      activeRegionSurface μ R hR k z Good S hS t ∩ closedBall i.center (i.radius / 16) := by
  obtain ⟨_, _, hUnif, htail, _, _, _⟩ := hmodel
  let B := (17039360 * ε) / 63
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hBsmall : B ≤ 1 := by dsimp [B]; linarith
  have hr := latticeRadius_pos R hR (k + t)
  have hri := i.radius_pos
  have hrad := latticeRadius_antitone R hR.le (Nat.add_le_add_left ht k)
  have hbase : latticeRadius R (k + (i.depth + 2)) = i.radius / 4096 := by
    change latticeRadius R (k + (i.depth + 2)) = latticeRadius R (k + i.depth) / 4096
    rw [show k + (i.depth + 2) = (k + i.depth) + 2 by omega, latticeRadius_add]
    norm_num
    ring
  rw [hbase] at hrad
  have hmul := mul_le_mul_of_nonneg_right hBsmall hr.le
  have hsmall : (B + 5) * latticeRadius R (k + t) < i.radius / 16 := by nlinarith
  apply active_region_limit_eq_finite_of_tail_small μ R hR k z Good S hS f
    (fun u => hUnif.tendsto_at u) B hB htail (closedBall i.center (i.radius / 16))
    (i.radius / 16) ?_ t hsmall
  intro x hx
  exact (cellRegionStoppingScale_stop_core_bounds μ R hR k z Good i hi x hx).1

end

end RieszRectifiability

end OAI
