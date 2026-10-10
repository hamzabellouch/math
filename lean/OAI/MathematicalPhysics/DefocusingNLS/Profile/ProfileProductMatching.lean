import OAI.MathematicalPhysics.DefocusingNLS.Profile.ProfileExistence
import Mathlib.Topology.UniformSpace.UniformConvergence

namespace OAI

/-! The four-real-dimensional degree step for simultaneous value and slope matching. -/

open Filter
namespace DefocusingNLS.ProfileCertificate

abbrev ProfileMatchingBall := Metric.closedBall (0 : ℂ × ℂ) (radius : ℝ)

noncomputable def profileMatchingParameter (z : ProfileMatchingBall) :
    Metric.closedBall (0 : ℂ) (radius : ℝ) :=
  ⟨z.val.2,by
    have hz : ‖z.val‖ ≤ (radius : ℝ) := by
      simpa only [Metric.mem_closedBall,dist_zero_right] using z.property
    simpa only [Metric.mem_closedBall,dist_zero_right] using (norm_snd_le z.val).trans hz⟩

noncomputable def profileProductLinearEquiv : (ℂ × ℂ) ≃L[ℝ] (ℂ × ℂ) :=
  (ContinuousLinearEquiv.refl ℝ ℂ).prodCongr centralLinearEquiv

theorem profileProductLinearEquiv_inverse_bound (z : ℂ × ℂ) :
    ‖profileProductLinearEquiv.symm z‖ ≤ ‖z‖/(48/1000 : ℝ) := by
  change max ‖z.1‖ ‖centralLinearEquiv.symm z.2‖ ≤ _
  apply max_le
  · apply (norm_fst_le z).trans
    rw [le_div_iff₀ (by norm_num)]
    nlinarith [norm_nonneg z]
  · exact (centralLinearEquiv_inverse_bound z.2).trans
      ((div_le_div_iff_of_pos_right (by norm_num)).mpr (norm_snd_le z))

theorem zero_of_profile_product_error (f : ProfileMatchingBall → ℂ × ℂ)
    (hf : Continuous f)
    (he : ∀ z, ‖f z-profileProductLinearEquiv z.val‖ ≤ (50/1000000000000 : ℝ)) :
    ∃ z, f z=0 := by
  apply zero_of_near_invertible_linear_map profileProductLinearEquiv (radius : ℝ)
    ((50/1000000000000)/(48/1000)) (by norm_num [radius]) (by norm_num [radius]) f hf
  intro z
  have hid : profileProductLinearEquiv.symm (f z)-z.val=
      profileProductLinearEquiv.symm (f z-profileProductLinearEquiv z.val) := by
    rw [map_sub,profileProductLinearEquiv.symm_apply_apply]
  rw [hid]
  exact (profileProductLinearEquiv_inverse_bound _).trans
    ((div_le_div_iff_of_pos_right (by norm_num)).mpr (he z))

theorem zero_of_profile_product_limit (f : ℕ → ProfileMatchingBall → ℂ × ℂ)
    (hf : ∀ᶠ n in atTop, Continuous (f n))
    (hlim : TendstoUniformly f (fun z => (z.val.1,diskProfile (profileMatchingParameter z))) atTop) :
    ∀ᶠ n in atTop, ∃ z, f n z=0 := by
  have hclose := (Metric.tendstoUniformly_iff.mp hlim)
    (25/1000000000000) (by norm_num)
  filter_upwards [hf,hclose] with n hn he
  apply zero_of_profile_product_error (f n) hn
  intro z
  have herr : ‖(z.val.1,diskProfile (profileMatchingParameter z))-
      profileProductLinearEquiv z.val‖ ≤ (25/1000000000000 : ℝ) := by
    change max ‖z.val.1-z.val.1‖
      ‖diskProfile (profileMatchingParameter z)-centralLinearEquiv z.val.2‖ ≤ _
    rw [sub_self,norm_zero,max_eq_right (norm_nonneg _)]
    exact (diskProfile_linear_error (profileMatchingParameter z)).le
  have hsmall : ‖f n z-(z.val.1,diskProfile (profileMatchingParameter z))‖ <
      (25/1000000000000 : ℝ) := by
    simpa only [dist_comm,dist_eq_norm] using he z
  have htri := norm_add_le
    (f n z-(z.val.1,diskProfile (profileMatchingParameter z)))
    ((z.val.1,diskProfile (profileMatchingParameter z))-profileProductLinearEquiv z.val)
  rw [sub_add_sub_cancel] at htri
  linarith

end DefocusingNLS.ProfileCertificate

end OAI
