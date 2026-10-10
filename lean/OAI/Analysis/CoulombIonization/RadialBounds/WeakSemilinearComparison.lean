import Mathlib
import OAI.Analysis.CoulombIonization.FormDomain.WeakComparison
import OAI.Analysis.CoulombIonization.FieldAnalysis.LocalGreen

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric Laplacian
open scoped BigOperators ContDiff Topology

namespace CoulombAnalysis
open CoulombAtom

theorem weak_semilinear_classical_ball {u v : Space → ℝ} {r R k : ℝ}
    (hr : 0 < r) (hrR : r < R) (hk : 0 < k)
    (hu : ContinuousOn u (closedBall 0 r))
    (hv : ∀ x ∈ ball (0 : Space) R, ContDiffAt ℝ 2 v x)
    (hlv : ContinuousOn (Δ v) (closedBall 0 r))
    (hvp : ∀ x ∈ closedBall (0 : Space) r, 0 < v x)
    (hvs : ∀ x ∈ ball (0 : Space) r, Δ v x ≤ k*(v x)^(3/2:ℝ))
    (hb : ∀ x : Space, ‖x‖ = r → u x ≤ v x)
    (hw : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ ball 0 R →
      (∫ x, u x*Δ g x) = ∫ x, k*(max (u x) 0)^(3/2:ℝ)*g x) :
    ∀ x ∈ closedBall (0 : Space) r, u x ≤ v x := by
  have hvcont : ContinuousOn v (closedBall (0 : Space) r) := fun x hx =>
    (hv x (closedBall_subset_ball hrR hx)).continuousAt.continuousWithinAt
  let F : Space → ℝ := fun x => k*(max (u x) 0)^(3/2:ℝ)-Δ v x
  have hreaction : ContinuousOn (fun x => k*(max (u x) 0)^(3/2:ℝ)) (closedBall 0 r) :=
    continuousOn_const.mul ((Real.continuous_rpow_const (by norm_num : (0:ℝ) ≤ 3/2)).comp_continuousOn
      (hu.sup continuousOn_const))
  have hF : ContinuousOn F (closedBall 0 r) := hreaction.sub hlv
  have hcmp := weak_strict_source_comparison (isCompact_closedBall (0 : Space) r)
    (hu.sub hvcont) hF (fun x hx hp => ?_) (fun x hx hn => ?_) (fun g hg hcg hs _hn => ?_)
  · intro x hx
    exact sub_nonpos.mp (hcmp x hx)
  · rw [interior_closedBall (0 : Space) hr.ne'] at hx
    have hpv := hvp x (ball_subset_closedBall hx)
    have hpu : 0 < u x := hpv.trans (sub_pos.mp hp)
    have hs := hvs x hx
    have ht := mul_lt_mul_of_pos_left (Real.rpow_lt_rpow hpv.le (sub_pos.mp hp) (by norm_num : (0:ℝ) < 3/2)) hk
    dsimp only [F]
    rw [max_eq_left hpu.le]
    linarith
  · rw [interior_closedBall (0 : Space) hr.ne'] at hn
    have hn' : ‖x‖ = r := le_antisymm (by simpa only [mem_closedBall,dist_zero_right] using hx)
      (le_of_not_gt (by simpa only [mem_ball,dist_zero_right] using hn))
    exact sub_nonpos.mpr (hb x hn')
  · have hs' : tsupport g ⊆ ball (0 : Space) r := by
      simpa only [interior_closedBall (0 : Space) hr.ne'] using hs
    have hsk := hs'.trans ball_subset_closedBall
    have hui := continuousOn_mul_integrable_support (isCompact_closedBall 0 r) hu
      (tfLaplacian_continuous hg) ((tfLaplacian_support hg).trans hsk)
    have hvi := continuousOn_mul_integrable_support (isCompact_closedBall 0 r) hvcont
      (tfLaplacian_continuous hg) ((tfLaplacian_support hg).trans hsk)
    have hri := continuousOn_mul_integrable_support (isCompact_closedBall 0 r) hreaction
      hg.continuous ((subset_tsupport g).trans hsk)
    have hlvi := continuousOn_mul_integrable_support (isCompact_closedBall 0 r) hlv
      hg.continuous ((subset_tsupport g).trans hsk)
    have he := hw g hg hcg (hs'.trans (ball_subset_ball hrR.le))
    have hvgreen := local_laplacian_green_ball hr hrR hv hg hcg hs'
    have heq : (∫ x, (u x-v x)*Δ g x) = ∫ x, F x*g x := by
      simp_rw [F,sub_mul]
      rw [integral_sub hui hvi,integral_sub hri hlvi,he,hvgreen]
    exact heq.ge

end CoulombAnalysis

end

end OAI
