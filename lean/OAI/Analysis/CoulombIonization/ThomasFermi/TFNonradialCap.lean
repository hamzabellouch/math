import Mathlib
import OAI.Analysis.CoulombIonization.ThomasFermi.TFNonradialBarrier
import OAI.Analysis.CoulombIonization.RadialBounds.WeakSemilinearComparison

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric Laplacian
open scoped BigOperators ContDiff Topology

namespace CoulombAnalysis
open CoulombAtom

lemma exists_tfCapBarrier_radius {A R q : ℝ} (hA : 0 < A) (hR : 0 < R)
    (hq : q < R) (M : ℝ) : ∃ r, 0 < r ∧ q < r ∧ r < R ∧ M ≤ A*R^4/(R^2-r^2)^4 := by
  let B := max M 0+1
  have hB : 0 < B := by dsimp [B]; linarith [le_max_right M 0]
  have hMB : M ≤ B := by dsimp [B]; linarith [le_max_left M 0]
  have hd : 0 < A*R^4/B := div_pos (mul_pos hA (pow_pos hR _)) hB
  have hc : Continuous (fun r : ℝ => (R^2-r^2)^4) := by fun_prop
  have hev : ∀ᶠ r in 𝓝 R, (R^2-r^2)^4 < A*R^4/B := by
    apply hc.continuousAt.eventually (gt_mem_nhds _)
    simpa only [sub_self,zero_pow (by decide : (4:ℕ) ≠ 0)] using hd
  obtain ⟨a,b,hab,hs⟩ := hev.exists_Ioo_subset
  obtain ⟨r,hrlo,hrR⟩ := exists_between (show max (max a q) 0 < R from
    max_lt (max_lt hab.1 hq) hR)
  have hr : 0 < r := (le_max_right _ _).trans_lt hrlo
  have har : a < r := (le_max_left a q |>.trans (le_max_left _ _)).trans_lt hrlo
  have hqr : q < r := (le_max_right a q |>.trans (le_max_left _ _)).trans_lt hrlo
  refine ⟨r,hr,hqr,hrR,?_⟩
  have hsmall := (lt_div_iff₀ hB).mp (hs ⟨har,hrR.trans hab.2⟩)
  have hdp : 0 < R^2-r^2 := by nlinarith
  apply (le_div_iff₀ (pow_pos hdp 4)).mpr
  calc
    M*(R^2-r^2)^4 ≤ B*(R^2-r^2)^4 :=
      mul_le_mul_of_nonneg_right hMB (pow_nonneg hdp.le _)
    _ ≤ A*R^4 := by nlinarith

theorem weak_tfCapBarrier_bound {u : Space → ℝ} {A R k : ℝ}
    (hA : 0 < A) (hR : 0 < R) (hk : 0 < k) (hkA : 80*A ≤ k*A^(3/2:ℝ))
    (hu : ContinuousOn u (closedBall 0 R))
    (hw : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ ball 0 R →
      (∫ x, u x*Δ g x) = ∫ x, k*(max (u x) 0)^(3/2:ℝ)*g x)
    (x : Space) (hx : ‖x‖ < R) : u x ≤ tfCapBarrier A R x := by
  obtain ⟨z,hz,hmax⟩ := (isCompact_closedBall (0 : Space) R).exists_isMaxOn
    (show (closedBall (0 : Space) R).Nonempty from ⟨0,mem_closedBall_self hR.le⟩) hu
  obtain ⟨r,hr,hxr,hrR,hrM⟩ := exists_tfCapBarrier_radius hA hR hx (u z)
  have hn (w : Space) (hw : w ∈ closedBall (0 : Space) r) : ‖w‖ < R :=
    (show ‖w‖ ≤ r by simpa only [mem_closedBall,dist_zero_right] using hw).trans_lt hrR
  have hl : ContinuousOn (Δ (tfCapBarrier A R)) (closedBall 0 r) := by
    have hc : ContinuousOn
        (fun w : Space => A*R^4*(24*R^2+56*‖w‖^2)/(R^2-‖w‖^2)^6) (closedBall 0 r) :=
      (continuousOn_const.mul (continuousOn_const.add (continuousOn_const.mul (continuous_norm.pow 2).continuousOn))).div
        (continuousOn_const.sub (continuous_norm.pow 2).continuousOn |>.pow 6)
        (fun w hw => pow_ne_zero _ (capDenominator_pos (hn w hw)).ne')
    exact hc.congr (fun w hw => tfCapBarrier_laplacian A (hn w hw))
  apply weak_semilinear_classical_ball hr hrR hk
    (hu.mono (closedBall_subset_closedBall hrR.le))
    (fun w hw => tfCapBarrier_contDiffAt A (by simpa only [mem_ball,dist_zero_right] using hw)) hl
    (fun w hw => tfCapBarrier_pos hA (hn w hw))
    (fun w hw => tfCapBarrier_supersolution hA hkA (hn w (ball_subset_closedBall hw)))
    (fun w hw => ?_) hw x (by simpa only [mem_closedBall,dist_zero_right] using hxr.le)
  change u w ≤ A*R^4/(R^2-‖w‖^2)^4
  rw [hw]
  exact (hmax (by simpa only [mem_closedBall,dist_zero_right,hw] using hrR.le)).trans hrM

lemma tfCapBarrier_inner_quarter {A R : ℝ} (hA : 0 ≤ A) (hR : 0 < R)
    {x : Space} (hx : ‖x‖ ≤ 3*R/4) : tfCapBarrier A R x ≤ (256*A)/R^4 := by
  have hxR : ‖x‖ < R := hx.trans_lt (by linarith)
  have hsq := pow_le_pow_left₀ (norm_nonneg x) hx 2
  have hd : R^2/4 ≤ R^2-‖x‖^2 := by nlinarith [sq_nonneg R]
  calc
    _ ≤ A*R^4/(R^2/4)^4 := div_le_div_of_nonneg_left
      (mul_nonneg hA (pow_nonneg hR.le _)) (pow_pos (by positivity) _)
      (pow_le_pow_left₀ (by positivity) hd 4)
    _ = _ := by field_simp; ring

lemma tfCapBarrier_coefficient {k : ℝ} (hk : 0 < k) :
    0 < (80/k)^2 ∧ 80*((80/k)^2) ≤ k*((80/k)^2)^(3/2:ℝ) := by
  have hp : 0 < 80/k := div_pos (by norm_num) hk
  refine ⟨pow_pos hp _,?_⟩
  have he : ((80/k)^2)^(3/2:ℝ) = (80/k)^3 := by
    rw [←Real.rpow_natCast (80/k) 2,←Real.rpow_mul hp.le]
    norm_num
  rw [he]
  apply le_of_eq
  field_simp

theorem weak_tf_nonradial_cap {u : Space → ℝ} {R k : ℝ} (hR : 0 < R) (hk : 0 < k)
    (hu : ContinuousOn u (closedBall 0 R))
    (hw : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ ball 0 R →
      (∫ x, u x*Δ g x) = ∫ x, k*(max (u x) 0)^(3/2:ℝ)*g x)
    (x : Space) (hx : ‖x‖ ≤ 3*R/4) : u x ≤ (256*(80/k)^2)/R^4 := by
  have hA := tfCapBarrier_coefficient hk
  exact (weak_tfCapBarrier_bound hA.1 hR hk hA.2 hu hw x (hx.trans_lt (by linarith))).trans
    (tfCapBarrier_inner_quarter hA.1.le hR hx)

end CoulombAnalysis

end

end OAI
