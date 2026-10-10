import OAI.Probability.SLE.Loewner.InverseCircleArea
import OAI.Probability.SLE.Geometry.AnalyticCircleSquare

namespace OAI

/-! Circle averages of signed holomorphic area densities. -/
noncomputable section
open Set Filter Metric Function Complex MeasureTheory InnerProductSpace Real
open scoped Topology Laplacian ComplexConjugate

namespace SLEExactGauge

def holomorphicAreaDensity (f : ℂ → ℂ) (z : ℂ) : ℝ :=
  2*(z*deriv f z*conj (f z)).re

lemma holomorphic_flux_eq_area_average {f : ℂ → ℂ} {r : ℝ}
    (hf : AnalyticOnNhd ℂ f (sphere (0:ℂ) |r|)) :
    (∫ θ in -Real.pi..Real.pi, radialLaplacianFlux (fun z => ‖f z‖^2) (r,θ))=
      2*Real.pi*circleAverage (holomorphicAreaDensity f) 0 r := by
  rw [circleAverage_eq_neg_pi_integral,smul_eq_mul]
  have hpoint (θ : ℝ) : radialLaplacianFlux (fun z => ‖f z‖^2) (r,θ)=
      holomorphicAreaDensity f (polarPoint r θ) :=
    holomorphic_radial_flux (hf _ (by
      rw [polarPoint_eq_circleMap]; exact circleMap_mem_sphere' 0 r θ))
  simp_rw [hpoint]
  field_simp

lemma inverse_chart_area_average {f C : ℂ → ℂ} {r : ℝ} (hr : 0<r)
    (hC : AnalyticOnNhd ℂ C (closedBall (0:ℂ) r⁻¹))
    (he : ∀ z∈sphere (0:ℂ) r, f z=z+C z⁻¹)
    (hd : ∀ z∈sphere (0:ℂ) r, deriv f z=1-z⁻¹^2*deriv C z⁻¹) :
    circleAverage (holomorphicAreaDensity f) 0 r=
      2*r^2-circleAverage (holomorphicAreaDensity C) 0 r⁻¹ := by
  let A (w : ℂ) := w*C w-w^2*deriv C w
  let H (w : ℂ) := 2*r^2+2*r^2*(A w).re-holomorphicAreaDensity C w
  have hCA : AnalyticOnNhd ℂ A (closedBall (0:ℂ) r⁻¹) :=
    (analyticOnNhd_id.mul hC).sub ((analyticOnNhd_id.pow 2).mul hC.deriv)
  have hAmean : circleAverage A 0 r⁻¹=0 := by
    have hh := (show HarmonicOnNhd A (closedBall (0:ℂ) |r⁻¹|) from
      fun z hz => (hCA z (by simpa only [abs_of_pos (inv_pos.mpr hr)] using hz)).harmonicAt).circleAverage_eq
    simpa [A] using hh
  have hAr : ContinuousOn (fun w => (A w).re) (sphere (0:ℂ) |r⁻¹|) :=
    (Complex.continuous_re.comp_continuousOn hCA.continuousOn).mono
      (by rw [abs_of_pos (inv_pos.mpr hr)]; exact sphere_subset_closedBall)
  have hD : ContinuousOn (holomorphicAreaDensity C) (sphere (0:ℂ) |r⁻¹|) := by
    have hc := hC.continuousOn.mono (sphere_subset_closedBall (x := (0:ℂ)) (ε := r⁻¹))
    have hdc := hC.deriv.continuousOn.mono (sphere_subset_closedBall (x := (0:ℂ)) (ε := r⁻¹))
    rw [abs_of_pos (inv_pos.mpr hr)]
    exact (Complex.continuous_re.comp_continuousOn
      ((continuousOn_id.mul hdc).mul (Complex.continuous_conj.comp_continuousOn hc))).const_mul 2
  have hReA : circleAverage (fun w => (A w).re) 0 r⁻¹=0 := by
    have hh := Complex.reCLM.circleAverage_comp_comm
      ((hCA.continuousOn.mono (by rw [abs_of_pos (inv_pos.mpr hr)]; exact sphere_subset_closedBall)).circleIntegrable')
    simpa only [Function.comp_def,Complex.reCLM_apply,hAmean,Complex.zero_re] using hh
  calc
    _ = circleAverage (fun z => H z⁻¹) 0 r := by
      apply circleAverage_congr_sphere
      intro z hz
      have hzr : ‖z‖=r := by simpa only [abs_of_pos hr,mem_sphere,dist_zero_right] using hz
      have hz' : z∈sphere (0:ℂ) r := by simpa only [abs_of_pos hr] using hz
      have hz0 : z≠0 := norm_ne_zero_iff.mp (by rw [hzr]; exact hr.ne')
      dsimp only [holomorphicAreaDensity]
      rw [he z hz',hd z hz']
      have halg : z*(1-z⁻¹^2*deriv C z⁻¹)=z-z⁻¹*deriv C z⁻¹ := by
        field_simp
      rw [halg,inverse_area_density_identity z (C z⁻¹) (deriv C z⁻¹) hz0,hzr]
      rfl
    _ = circleAverage H 0 r⁻¹ := circleAverage_inv_radius H r
    _ = _ := by
      dsimp only [H]
      rw [circleAverage_fun_sub (f₁ := fun w => 2*r^2+2*r^2*(A w).re)
        (f₂ := holomorphicAreaDensity C)
        ((continuousOn_const.add (hAr.const_mul (2*r^2))).circleIntegrable') hD.circleIntegrable',
        circleAverage_fun_add (f₁ := fun _ => 2*r^2) (f₂ := fun w => 2*r^2*(A w).re)
          (circleIntegrable_const (2*r^2) 0 r⁻¹) (hAr.const_mul (2*r^2)).circleIntegrable']
      have hm : circleAverage (fun w => 2*r^2*(A w).re) 0 r⁻¹=
          2*r^2*circleAverage (fun w => (A w).re) 0 r⁻¹ := by
        simpa only [smul_eq_mul] using (circleAverage_fun_smul (a := (2*r^2 : ℝ))
          (f := fun w => (A w).re) (c := (0:ℂ)) (R := r⁻¹))
      rw [circleAverage_const,hm,hReA,mul_zero,add_zero]

end SLEExactGauge

end

end OAI
