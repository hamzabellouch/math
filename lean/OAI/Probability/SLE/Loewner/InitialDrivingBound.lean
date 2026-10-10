import OAI.Probability.SLE.Loewner.SlitUniformForwardBound
import OAI.Probability.SLE.Loewner.InitialDrivingLimit

namespace OAI

/-! Every simple slit in a fixed disk has uniformly bounded driving
coordinates, including when the tip approaches either end. -/
noncomputable section
open Set Filter Function Complex
open scoped Topology

namespace SLEExactGauge

theorem initialDrivingValue_bound (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {R : ℝ} (hR : 0<R) (hp : ∀ t : unitInterval, ‖p t‖<R)
    (s : unitInterval) (hs : s<1) :
    |initialDrivingValue p hi h0 hH s hs|≤(512*Real.pi+9)*R := by
  by_cases hs0 : s=0
  · subst s
    rw [initialDrivingValue_zero,abs_zero]
    positivity
  have hl := (initialDrivingValue_spec p hi h0 hH s hs).norm
  rw [Complex.norm_real,Real.norm_eq_abs] at hl
  apply le_of_tendsto hl
  have hd : 0<1-(s:ℝ) := sub_pos.mpr hs
  filter_upwards [self_mem_nhdsWithin,
    Filter.Eventually.filter_mono inf_le_left (gt_mem_nhds hd)] with r hr hrd
  have hz := slitFuturePoint_mem_domain p hi hH s (show r∈Ioo 0 (1-(s:ℝ)) from ⟨hr,hrd⟩)
  rw [initialForwardChart,dite_eq_right hs0]
  change ‖(initialSlitChart p hi h0 hH s hs0).forward
    (p (slitFutureParameter s r))‖≤_
  exact (initialSlitChart p hi h0 hH s hs0).forward_uniform_near
    (initialSubarc_injective hi hs0) (by simpa only [initialSubarc_zero] using h0)
    (initialSubarc_upper hH hs0) hR
    (fun u => hp _) hz ((hp _).le.trans (by linarith))

end SLEExactGauge

end

end OAI
