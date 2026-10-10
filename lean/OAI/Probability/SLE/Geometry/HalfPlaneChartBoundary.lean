import OAI.Probability.SLE.KernelConsistency

namespace OAI

/-! The two exceptional circle values of the centered half-plane chart. -/
noncomputable section
open Set Filter Metric
open scoped Topology

namespace SLEExactGauge

lemma halfPlaneToDisk_zero_norm {v : ℂ} (hv : 0 < v.im) : ‖halfPlaneToDisk v 0‖=1 := by
  have hv0 : v≠0 := by intro h; simp [h] at hv
  simp only [halfPlaneToDisk,zero_sub,norm_div,norm_neg,norm_star]
  exact div_self (norm_ne_zero_iff.mpr hv0)

lemma diskToHalfPlane_continuousAt {v c : ℂ} (hc : c≠1) :
    ContinuousAt (diskToHalfPlane v) c :=
  (continuousAt_const.sub (continuousAt_const.mul continuousAt_id)).div
    (continuousAt_const.sub continuousAt_id) (sub_ne_zero.mpr hc.symm)

lemma diskToHalfPlane_boundary_im {v c : ℂ} (hc : ‖c‖=1) :
    (diskToHalfPlane v c).im=0 := by
  rw [diskToHalfPlane_im,Complex.normSq_eq_norm_sq,hc,one_pow,sub_self,mul_zero,zero_div]

lemma diskToHalfPlane_boundary_ne_zero {v c : ℂ} (hv : 0 < v.im)
    (hc1 : c≠1) (hc0 : c≠halfPlaneToDisk v 0) : diskToHalfPlane v c≠0 := by
  have hv0 : v≠0 := by intro h; simp [h] at hv
  have hstar : star v≠0 := by simpa using hv0
  intro hz
  have hn : v-star v*c=0 := (div_eq_zero_iff.mp hz).resolve_right (sub_ne_zero.mpr hc1.symm)
  have he : c=v/star v := (eq_div_iff hstar).mpr (by linear_combination -hn)
  apply hc0
  simpa only [halfPlaneToDisk,zero_sub,neg_div_neg_eq] using he

end SLEExactGauge

end

end OAI
