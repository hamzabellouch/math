import OAI.Analysis.CircleDomains.Topology.FiniteCircleGreen
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Topology.MetricSpace.HausdorffDistance

namespace OAI

/-! The actual distance weight in the Stokes estimate: it is smooth off
the closed round disk and equals the offset on a concentric circle. -/

open Set Function Filter Metric
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem infDist_closedBall_of_dist_gt (c z : ℂ) {r : ℝ} (hr : 0 ≤ r)
    (hz : r < dist z c) :
    infDist z (closedBall c r) = dist z c - r := by
  have hd : 0 < dist z c := hr.trans_lt hz
  have hne : dist z c ≠ 0 := hd.ne'
  let a := r / dist z c
  let p := c + a • (z - c)
  have ha : 0 ≤ a := div_nonneg hr hd.le
  have ha1 : a ≤ 1 := (div_le_one hd).mpr hz.le
  have hp : p ∈ closedBall c r := by
    rw [mem_closedBall, dist_eq_norm]
    dsimp only [p]
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
    rw [← dist_eq_norm, div_mul_cancel₀ r hne]
  have hdist : dist z p = dist z c - r := by
    have heq : z - p = (1 - a) • (z - c) := by dsimp only [p]; module
    rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr ha1), ← dist_eq_norm]
    dsimp only [a]
    rw [sub_mul, one_mul, div_mul_cancel₀ r hne]
  apply le_antisymm
  · exact (infDist_le_dist_of_mem hp).trans_eq hdist
  · apply (le_infDist ⟨c, mem_closedBall_self hr⟩).mpr
    intro y hy
    have htri := dist_triangle z y c
    have hy' := mem_closedBall.mp hy
    linarith

 theorem contDiffOn_infDist_closedBall (c : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z => infDist z (closedBall c r)) (closedBall c r)ᶜ := by
  intro z hz
  have hzr : r < dist z c := lt_of_not_ge hz
  have hzc : z ≠ c := by
    intro he
    subst z
    simp only [dist_self] at hzr
    linarith
  have hs : ContDiffAt ℝ (⊤ : ℕ∞) (fun w : ℂ => dist w c - r) z :=
    (contDiffAt_id.dist ℝ contDiffAt_const hzc).sub contDiffAt_const
  apply (hs.congr_of_eventuallyEq _).contDiffWithinAt
  filter_upwards [isClosed_closedBall.isOpen_compl.mem_nhds hz] with w hw
  exact infDist_closedBall_of_dist_gt c w hr (lt_of_not_ge hw)

 theorem infDist_closedBall_unitCircle_offset (c : ℂ) {r ρ : ℝ}
    (hr : 0 ≤ r) (hρ : 0 < ρ) (t : ℝ) :
    infDist (unitCircleParam c (r + ρ) t) (closedBall c r) = ρ := by
  have hc : dist (unitCircleParam c (r + ρ) t) c = r + ρ :=
    mem_sphere.mp (circleMap_mem_sphere c (by linarith : 0 ≤ r + ρ) _)
  rw [infDist_closedBall_of_dist_gt c _ hr (by rw [hc]; linarith), hc]
  ring

end CircleDomainRigidity

end

end OAI
