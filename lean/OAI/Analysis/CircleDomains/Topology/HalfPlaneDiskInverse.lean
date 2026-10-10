import OAI.Analysis.CircleDomains.Topology.HalfPlaneDisk

namespace OAI

/-! The inverse Cayley coordinate on the punctured closed disk. -/

open Set Function
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

def diskHalfPlane (w : ℂ) : ℂ := Complex.I * (1 + w) / (1 - w)

theorem diskHalfPlane_den_ne_zero {w : ℂ} (hw : w ≠ 1) : 1 - w ≠ 0 := by
  exact sub_ne_zero.mpr hw.symm

theorem diskHalfPlane_add_I {w : ℂ} (hw : w ≠ 1) :
    diskHalfPlane w + Complex.I = (2 * Complex.I) / (1 - w) := by
  unfold diskHalfPlane
  field_simp [diskHalfPlane_den_ne_zero hw]
  ring

theorem diskHalfPlane_add_I_ne_zero {w : ℂ} (hw : w ≠ 1) :
    diskHalfPlane w + Complex.I ≠ 0 := by
  rw [diskHalfPlane_add_I hw]
  exact div_ne_zero (by simp) (diskHalfPlane_den_ne_zero hw)

theorem halfPlaneDisk_diskHalfPlane {w : ℂ} (hw : w ≠ 1) :
    halfPlaneDisk (diskHalfPlane w) = w := by
  rw [halfPlaneDisk, div_eq_iff (diskHalfPlane_add_I_ne_zero hw)]
  unfold diskHalfPlane
  field_simp [diskHalfPlane_den_ne_zero hw]
  ring

theorem diskHalfPlane_halfPlaneDisk {z : ℂ} (hz : 0 ≤ z.im) :
    diskHalfPlane (halfPlaneDisk z) = z := by
  rw [diskHalfPlane, div_eq_iff (diskHalfPlane_den_ne_zero (halfPlaneDisk_ne_one hz))]
  unfold halfPlaneDisk
  field_simp [halfPlaneDisk_den_ne_zero hz]
  ring

theorem diskHalfPlane_nonneg {w : ℂ} (hw : w ≠ 1) (hn : ‖w‖ ≤ 1) :
    0 ≤ (diskHalfPlane w).im := by
  have hh : ‖halfPlaneDisk (diskHalfPlane w)‖ ≤ 1 := by rw [halfPlaneDisk_diskHalfPlane hw]; exact hn
  rw [halfPlaneDisk, norm_div] at hh
  have hb : ‖diskHalfPlane w - Complex.I‖ ≤ ‖diskHalfPlane w + Complex.I‖ :=
    (div_le_one (norm_pos_iff.mpr (diskHalfPlane_add_I_ne_zero hw))).mp hh
  have hs := halfPlaneDisk_normSq (diskHalfPlane w)
  simp only [← Complex.sq_norm] at hs
  nlinarith [norm_nonneg (diskHalfPlane w - Complex.I)]

theorem continuousOn_diskHalfPlane : ContinuousOn diskHalfPlane {w : ℂ | w ≠ 1} :=
  (continuous_const.mul (continuous_const.add continuous_id)).continuousOn.div
    (continuous_const.sub continuous_id).continuousOn (fun _ h => diskHalfPlane_den_ne_zero h)

end CircleDomainRigidity

end

end OAI
