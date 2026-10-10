import OAI.Probability.SLE.Geometry.ExteriorHerglotzAnalytic
import OAI.Probability.SLE.Geometry.PositiveRealDiskEstimate

namespace OAI

/-! The normalized height inequality becomes positivity of the real
part after inversion. -/
noncomputable section
open Set Filter Function Complex Metric
open scoped Topology ComplexConjugate

namespace SLEExactGauge

lemma exteriorHerglotzTransform_sphere_re {G : ℂ → ℂ} {R c : ℝ}
    {w : ℂ} (hw : ‖w‖=1) :
    (exteriorHerglotzTransform G R c w).re=
      2*w.im*(G ((R:ℂ)/w)-(R:ℂ)/w).im := by
  have hw0 : w≠0 := by intro he; simp [he] at hw
  have he : ((1:ℂ)-w^2)/w=conj w-w := by
    rw [← Complex.inv_eq_conj hw]
    field_simp [hw0]
  rw [exteriorHerglotzTransform_eq_raw hw0]
  simp only [exteriorHerglotzRaw,he,mul_re,sub_re,sub_im,conj_re,conj_im]
  ring

theorem exteriorHerglotzTransform_nonneg {G : ℂ → ℂ} {R c : ℝ}
    (hR : 0<R) (hG : ∀ z : ℂ, R≤‖z‖ → DifferentiableAt ℂ G z)
    (hc : Tendsto (fun z : ℂ => z*(G z-z)) (cocompact ℂ) (𝓝 (c:ℂ)))
    (hs : ∀ z : ℂ, R≤‖z‖ → z.im*(G z-z).im≤0) :
    ∀ w∈closedBall (0:ℂ) 1, 0≤(exteriorHerglotzTransform G R c w).re := by
  apply real_nonneg_of_sphere_nonneg zero_lt_one
    (exteriorHerglotzTransform_differentiableOn hR hG hc)
  intro w hw
  have hwn : ‖w‖=1 := by simpa only [mem_sphere,dist_zero_right] using hw
  have hz : ‖(R:ℂ)/w‖=R := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hR,hwn,div_one]
  have him : ((R:ℂ)/w).im= -R*w.im := by
    rw [div_eq_mul_inv,Complex.inv_eq_conj hwn]
    simp only [mul_im,ofReal_re,ofReal_im,conj_im,zero_mul,add_zero]
    ring
  have hh := hs ((R:ℂ)/w) hz.ge
  rw [him] at hh
  rw [exteriorHerglotzTransform_sphere_re hwn]
  have hp : 0≤w.im*(G ((R:ℂ)/w)-(R:ℂ)/w).im := by nlinarith
  nlinarith

end SLEExactGauge

end

end OAI
