import OAI.Analysis.CircleDomains.Topology.DiskCentering

namespace OAI

/-! The Cayley coordinate for compactifying the upper half-plane rays. -/

open Set Function
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

def halfPlaneDisk (z : ℂ) : ℂ := (z - Complex.I) / (z + Complex.I)

theorem halfPlaneDisk_den_ne_zero {z : ℂ} (hz : 0 ≤ z.im) : z + Complex.I ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp only [Complex.add_im, Complex.I_im, Complex.zero_im] at hi
  linarith

theorem halfPlaneDisk_normSq (z : ℂ) :
    Complex.normSq (z + Complex.I) - Complex.normSq (z - Complex.I) = 4 * z.im := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im]
  ring

theorem halfPlaneDisk_norm_le {z : ℂ} (hz : 0 ≤ z.im) : ‖halfPlaneDisk z‖ ≤ 1 := by
  have hn := halfPlaneDisk_normSq z
  simp only [← Complex.sq_norm] at hn
  have hb : ‖z - Complex.I‖ ≤ ‖z + Complex.I‖ := by
    nlinarith [norm_nonneg (z - Complex.I), norm_nonneg (z + Complex.I)]
  rw [halfPlaneDisk, norm_div]
  exact (div_le_one (norm_pos_iff.mpr (halfPlaneDisk_den_ne_zero hz))).mpr hb

theorem halfPlaneDisk_norm_lt {z : ℂ} (hz : 0 < z.im) : ‖halfPlaneDisk z‖ < 1 := by
  have hn := halfPlaneDisk_normSq z
  simp only [← Complex.sq_norm] at hn
  have hb : ‖z - Complex.I‖ < ‖z + Complex.I‖ := by
    nlinarith [norm_nonneg (z - Complex.I), norm_nonneg (z + Complex.I)]
  rw [halfPlaneDisk, norm_div]
  exact (div_lt_one (norm_pos_iff.mpr (halfPlaneDisk_den_ne_zero hz.le))).mpr hb

theorem halfPlaneDisk_norm_eq {z : ℂ} (hz : z.im = 0) : ‖halfPlaneDisk z‖ = 1 := by
  have hn := halfPlaneDisk_normSq z
  simp only [← Complex.sq_norm, hz, mul_zero] at hn
  have hb : ‖z - Complex.I‖ = ‖z + Complex.I‖ := by
    nlinarith [norm_nonneg (z - Complex.I), norm_nonneg (z + Complex.I)]
  rw [halfPlaneDisk, norm_div, hb,
    div_self (norm_ne_zero_iff.mpr (halfPlaneDisk_den_ne_zero hz.ge))]

theorem continuousOn_halfPlaneDisk : ContinuousOn halfPlaneDisk {z : ℂ | 0 ≤ z.im} :=
  (continuous_id.sub continuous_const).continuousOn.div
    (continuous_id.add continuous_const).continuousOn (fun _ h => halfPlaneDisk_den_ne_zero h)

theorem halfPlaneDisk_injOn : InjOn halfPlaneDisk {z : ℂ | 0 ≤ z.im} := by
  intro z hz w hw he
  have hc := (div_eq_div_iff (halfPlaneDisk_den_ne_zero hz)
    (halfPlaneDisk_den_ne_zero hw)).mp he
  have h : (z - w) * (2 * Complex.I) = 0 := by
    calc
      _ = (z - Complex.I) * (w + Complex.I) - (w - Complex.I) * (z + Complex.I) := by ring
      _ = 0 := sub_eq_zero.mpr hc
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right (by simp))

theorem halfPlaneDisk_sub_one {z : ℂ} (hz : 0 ≤ z.im) :
    halfPlaneDisk z - 1 = (-2 * Complex.I) / (z + Complex.I) := by
  unfold halfPlaneDisk
  field_simp [halfPlaneDisk_den_ne_zero hz]
  ring

theorem halfPlaneDisk_ne_one {z : ℂ} (hz : 0 ≤ z.im) : halfPlaneDisk z ≠ 1 := by
  intro h
  have he := halfPlaneDisk_sub_one hz
  rw [h, sub_self, eq_comm, div_eq_zero_iff] at he
  rcases he with he | he
  · simp at he
  · exact halfPlaneDisk_den_ne_zero hz he

theorem halfPlaneDisk_dist_one_le {z : ℂ} (hz : 0 ≤ z.im) :
    dist (halfPlaneDisk z) 1 ≤ 2 / (z.im + 1) := by
  rw [dist_eq_norm, halfPlaneDisk_sub_one hz, norm_div, norm_mul]
  have hd : z.im + 1 ≤ ‖z + Complex.I‖ := by
    simpa only [Complex.add_im, Complex.I_im] using Complex.im_le_norm (z + Complex.I)
  have hp : 0 < z.im + 1 := by linarith
  simpa using div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2) hp hd

end CircleDomainRigidity

end

end OAI
