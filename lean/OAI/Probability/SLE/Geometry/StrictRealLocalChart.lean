import OAI.Probability.SLE.Loewner.SlitReciprocalChart
import OAI.Probability.SLE.DiskHalfPlane

namespace OAI

/-! A reflection-symmetric analytic germ tangent to the identity preserves
the upper side in a sufficiently small neighborhood. -/
noncomputable section
open Set Filter Complex Function Metric
open scoped Topology ComplexConjugate

namespace SLEExactGauge

lemma strict_real_germ_maps_upper {D : Set ℂ} (hD : D ∈ 𝓝 (0:ℂ))
    {f : ℂ → ℂ} (hf : HasStrictDerivAt f 1 0)
    (hs : ∀ z ∈ D, f (conj z)=conj (f z)) :
    ∃ r : ℝ, 0<r ∧ MapsTo f (ball 0 r ∩ upperHalfPlane) upperHalfPlane := by
  have hd : HasStrictFDerivAt (fun z : ℂ => f z-z) (0:ℂ →L[ℂ] ℂ) 0 := by
    convert! (hf.sub (hasStrictDerivAt_id (0:ℂ))).hasStrictFDerivAt using 1
    simp
  obtain ⟨S,hS,hL⟩ := hd.exists_lipschitzOnWith_of_nnnorm_lt (1/2) (by simp)
  obtain ⟨r,hr,hrS⟩ := Metric.mem_nhds_iff.mp (inter_mem hS hD)
  refine ⟨r,hr,?_⟩
  intro z hz
  have hcz : conj z ∈ ball (0:ℂ) r := by
    simpa only [mem_ball,dist_zero_right,norm_conj] using hz.1
  have hbound := hL.norm_sub_le (hrS hz.1).1 (hrS hcz).1
  have hnorm : ‖z-conj z‖=2*z.im := by
    simpa only [star_def] using norm_sub_conj_of_im_pos hz.2
  rw [hnorm] at hbound
  have hlo := (neg_le_abs _).trans
    (Complex.abs_im_le_norm (f z-z-(f (conj z)-conj z)))
  rw [hs z (hrS hz.1).2] at hlo hbound
  simp only [sub_im,conj_im] at hlo
  change 0 < (f z).im
  have hzH : 0 < z.im := hz.2
  norm_num at hbound
  linarith

end SLEExactGauge

end

end OAI
