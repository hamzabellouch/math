import OAI.Probability.SLE.Geometry.PolarLaplacianFlux

namespace OAI

/-! The ordinary angular integral of radial flux is a circle average of
the derivative applied to the position vector. -/
noncomputable section
open Set Filter Metric Function Complex MeasureTheory InnerProductSpace Real
open scoped Topology Laplacian

namespace SLEExactGauge

lemma circleAverage_eq_neg_pi_integral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℂ → E) (r : ℝ) :
    circleAverage f 0 r=(2*Real.pi)⁻¹ • ∫ θ in -Real.pi..Real.pi, f (polarPoint r θ) := by
  have h := circleAverage_eq_integral_add (f := f) (c := (0:ℂ)) (R := r) (-Real.pi)
  have hs := intervalIntegral.integral_comp_add_right (fun θ => f (circleMap 0 r θ))
    (a := (0:ℝ)) (b := 2*Real.pi) (-Real.pi)
  rw [hs] at h
  have hend : 2*Real.pi+ -Real.pi=Real.pi := by ring
  simpa only [zero_add,hend,←polarPoint_eq_circleMap] using h

lemma polar_integral_eq_circleAverage (g : ℂ → ℝ) (r : ℝ) :
    (∫ θ in -Real.pi..Real.pi, r*g (polarPoint r θ))=
      2*Real.pi*r*circleAverage g 0 r := by
  rw [intervalIntegral.integral_const_mul,circleAverage_eq_neg_pi_integral,smul_eq_mul]
  field_simp

lemma radial_flux_eq_circleAverage (u : ℂ → ℝ) (r : ℝ) :
    (∫ θ in -Real.pi..Real.pi, radialLaplacianFlux u (r,θ))=
      2*Real.pi*circleAverage (fun z => fderiv ℝ u z z) 0 r := by
  rw [circleAverage_eq_neg_pi_integral,smul_eq_mul]
  have hpoint (θ : ℝ) : radialLaplacianFlux u (r,θ)=
      fderiv ℝ u (polarPoint r θ) (polarPoint r θ) := by
    unfold radialLaplacianFlux
    conv_rhs => arg 2; rw [polarPoint]
    simp only [map_smul,smul_eq_mul]
  simp_rw [hpoint]
  field_simp

lemma radial_flux_continuousOn {u : ℂ → ℝ} {R : ℝ}
    (hu : ∀ z∈closedBall (0:ℂ) R, ContDiffAt ℝ 2 u z) :
    ContinuousOn (fun r => ∫ θ in -Real.pi..Real.pi, radialLaplacianFlux u (r,θ)) (Icc 0 R) := by
  have hc : ContinuousOn (fun z => fderiv ℝ u z z)
      {z : ℂ | ‖z-(0:ℂ)‖∈Icc 0 R} := by
    intro z hz
    have hzR : z∈closedBall (0:ℂ) R := by
      rw [mem_closedBall,dist_eq_norm]
      exact hz.2
    have hh := ((hu z hzR).fderiv_right (m := 1) (by norm_num)).continuousAt
    exact (hh.clm_apply continuousAt_id).continuousWithinAt
  have hav := hc.circleAverage (fun r hr => hr.1)
  simp_rw [radial_flux_eq_circleAverage]
  exact hav.const_mul _

@[simp] lemma radial_flux_zero (u : ℂ → ℝ) :
    (∫ θ in -Real.pi..Real.pi, radialLaplacianFlux u (0,θ))=0 := by
  simp [radialLaplacianFlux]

end SLEExactGauge

end

end OAI
