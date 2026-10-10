import OAI.Probability.SLE.Loewner.ReflectedChartLocalBound
import OAI.Probability.SLE.Loewner.CapacityRadiusBound

namespace OAI

/-! A numerical, slit-radius bound on all near-boundary forward
coordinates. It is independent of the shape of the simple slit. -/
noncomputable section
open Set Filter Function Complex Metric
open scoped Topology ComplexConjugate

namespace SLEExactGauge

lemma SimpleSlitChart.forward_on_two_radius {p : C(unitInterval,ℂ)}
    (P : SimpleSlitChart p) (hi : Injective p) (h0 : p 0=0)
    (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {R : ℝ} (hR : 0<R) (hp : ∀ t : unitInterval, ‖p t‖<R)
    {z : ℂ} (hzH : z∈upperHalfPlane) (hz : ‖z‖=2*R) :
    ‖P.forward z‖≤5*R := by
  have hb := P.forward_kernel_remainder hi h0 hH hR hp hzH hz.ge
  have hc := P.capacity_le_radius_sq hR (fun t => (hp t).le)
  have hdiv : ‖(P.capacity:ℂ)/z‖=P.capacity/(2*R) := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos P.capacity_pos,hz]
  have htri := norm_sub_le_norm_sub_add_norm_sub (P.forward z-z) ((P.capacity:ℂ)/z) 0
  simp only [sub_zero] at htri
  rw [hdiv] at htri
  rw [hz] at hb
  have he : 10*P.capacity*R/(2*R)^2+P.capacity/(2*R)=3*P.capacity/R := by
    field_simp
    ring
  have hcost : 10*P.capacity*R/(2*R)^2+P.capacity/(2*R)≤3*R := by
    rw [he]
    apply (div_le_iff₀ hR).mpr
    nlinarith
  have hdelta : ‖P.forward z-z‖≤3*R := by linarith
  have hsum := norm_le_norm_sub_add (P.forward z) z
  rw [hz] at hsum
  linarith

lemma ReflectedCapacityChart.normalizing_constant_bound {p : C(unitInterval,ℂ)}
    (Q : ReflectedCapacityChart p) (hi : Injective p) (h0 : p 0=0)
    (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {R : ℝ} (hR : 0<R) (hp : ∀ t : unitInterval, ‖p t‖<R) :
    ‖deriv (slitInfinityFactor Q.diskMap Q.slope) 0‖≤(256*Real.pi+7)*R := by
  let z : ℂ := (2*R:ℝ)*Complex.I
  have hzn : ‖z‖=2*R := by
    change ‖((2*R:ℝ):ℂ)*Complex.I‖=2*R
    rw [norm_mul,norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs]
    exact abs_of_pos (by positivity : 0<2*R)
  have hzH : z∈upperHalfPlane := by
    change 0<z.im
    simpa only [z,mul_im,ofReal_re,I_im,mul_one,ofReal_im,zero_mul,add_zero] using
      (by positivity : 0<2*R)
  have hnot : z∉reflectedArcSet p := by
    intro hh
    have hn := reflectedArcSet_norm_lt hp hh
    rw [hzn] at hn
    linarith
  have hJ := Q.joukowski_scaled_bound h0 (by positivity : 0<2*R)
    (fun t => (hp t).trans (by linarith)) hnot hzn.le
  have hG := Q.chart.forward_on_two_radius hi h0 hH hR hp hzH hzn
  have he : deriv (slitInfinityFactor Q.diskMap Q.slope) 0=
      (Q.slope:ℂ)*exteriorJoukowski (slitExteriorMap Q.diskMap z)-Q.chart.forward z := by
    rw [Q.forward_eq]
    simp only [slitHydrodynamicMap]
    ring
  rw [he]
  have ht := norm_sub_le ((Q.slope:ℂ)*exteriorJoukowski (slitExteriorMap Q.diskMap z))
    (Q.chart.forward z)
  nlinarith

lemma ReflectedCapacityChart.forward_bounded_in_two_radius {p : C(unitInterval,ℂ)}
    (Q : ReflectedCapacityChart p) (hi : Injective p) (h0 : p 0=0)
    (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {R : ℝ} (hR : 0<R) (hp : ∀ t : unitInterval, ‖p t‖<R)
    {z : ℂ} (hz : z∉reflectedArcSet p) (hzR : ‖z‖≤2*R) :
    ‖Q.chart.forward z‖≤(512*Real.pi+9)*R := by
  have hJ := Q.joukowski_scaled_bound h0 (by positivity : 0<2*R)
    (fun t => (hp t).trans (by linarith)) hz hzR
  have hb := Q.normalizing_constant_bound hi h0 hH hR hp
  rw [Q.forward_eq]
  change ‖(Q.slope:ℂ)*exteriorJoukowski (slitExteriorMap Q.diskMap z)-
    deriv (slitInfinityFactor Q.diskMap Q.slope) 0‖≤_
  have ht := norm_sub_le ((Q.slope:ℂ)*exteriorJoukowski (slitExteriorMap Q.diskMap z))
    (deriv (slitInfinityFactor Q.diskMap Q.slope) 0)
  nlinarith

lemma not_reflectedArcSet_of_mem_slit_domain {p : C(unitInterval,ℂ)} (h0 : p 0=0)
    (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {z : ℂ} (hz : z∈upperHalfPlane \ range p) : z∉reflectedArcSet p := by
  rintro (hp|⟨w,⟨t,rfl⟩,rfl⟩)
  · exact hz.2 hp
  · have hn : 0≤(p t).im := by
      by_cases ht : t=0
      · simp only [ht,h0,zero_im,le_refl]
      · exact (hH t ht).le
    have hh : 0 < -(p t).im := by
      have hx := hz.1
      change 0 < (conj (p t)).im at hx
      simpa only [conj_im] using hx
    linarith

theorem SimpleSlitChart.forward_uniform_near {p : C(unitInterval,ℂ)}
    (P : SimpleSlitChart p) (hi : Injective p) (h0 : p 0=0)
    (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {R : ℝ} (hR : 0<R) (hp : ∀ t : unitInterval, ‖p t‖<R)
    {z : ℂ} (hz : z∈upperHalfPlane \ range p) (hzR : ‖z‖≤2*R) :
    ‖P.forward z‖≤(512*Real.pi+9)*R := by
  obtain ⟨Q⟩ := exists_reflectedCapacityChart p hi h0 hH
  rw [(P.unique_on_domain Q.chart).1 hz]
  exact Q.forward_bounded_in_two_radius hi h0 hH hR hp
    (not_reflectedArcSet_of_mem_slit_domain h0 hH hz) hzR

end SLEExactGauge

end

end OAI
