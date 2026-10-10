import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.AbsMax

namespace OAI

/-! The positive-real disk estimate used after inversion of a small
reflected slit. Its constant is the hydrodynamic mass at the origin. -/
noncomputable section
open Set Filter Function Metric Complex
open scoped Topology

namespace SLEExactGauge

lemma real_nonneg_of_sphere_nonneg {H : ℂ → ℂ} {R : ℝ} (hR : 0<R)
    (hH : DifferentiableOn ℂ H (closedBall 0 R))
    (hb : ∀ z∈sphere (0:ℂ) R, 0≤(H z).re) :
    ∀ z∈closedBall (0:ℂ) R, 0≤(H z).re := by
  have heD : DifferentiableOn ℂ (fun z => Complex.exp (-H z)) (closedBall 0 R) := hH.neg.cexp
  have he : DiffContOnCl ℂ (fun z => Complex.exp (-H z)) (ball 0 R) := by
    refine ⟨heD.mono ball_subset_closedBall,?_⟩
    rw [closure_ball (0:ℂ) hR.ne']
    exact heD.continuousOn
  intro z hz
  have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball he
    (C := 1) (fun w hw => by
      have hw' : w∈sphere (0:ℂ) R := by rwa [frontier_ball (0:ℂ) hR.ne'] at hw
      rw [Complex.norm_exp,neg_re,Real.exp_le_one_iff]
      exact neg_nonpos.mpr (hb w hw'))
    (show z∈closure (ball (0:ℂ) R) by rwa [closure_ball (0:ℂ) hR.ne'])
  rw [Complex.norm_exp,neg_re,Real.exp_le_one_iff] at hmax
  exact neg_nonpos.mp hmax

theorem positive_real_disk_deviation {H : ℂ → ℂ} {m : ℝ} (hm : 0<m)
    (hH : DifferentiableOn ℂ H (ball 0 1)) (h0 : H 0=(m:ℂ))
    (hpos : ∀ z∈ball (0:ℂ) 1, 0≤(H z).re)
    {w : ℂ} (hw : w∈ball (0:ℂ) 1) :
    ‖H w-(m:ℂ)‖≤2*m*‖w‖/(1-‖w‖) := by
  have hf : DifferentiableOn ℂ (fun z => (m:ℂ)-H z) (ball 0 1) :=
    hH.const_sub (m:ℂ)
  have hb := Complex.borelCaratheodory_zero hm hf (fun z hz => by
    change ((m:ℂ)-H z).re≤m
    simp only [sub_re,ofReal_re]
    linarith [hpos z hz]) zero_lt_one hw
    (by rw [h0,sub_self])
  simpa only [norm_sub_rev] using hb

end SLEExactGauge

end

end OAI
