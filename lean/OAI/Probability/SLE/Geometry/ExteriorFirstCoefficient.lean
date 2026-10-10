import OAI.Probability.SLE.Geometry.HolomorphicAreaAverage
import OAI.Probability.SLE.Geometry.AnalyticFluxEnergy

namespace OAI

/-! The first inverse-radius coefficient of a univalent exterior map is
bounded by its nonnegative signed boundary area. -/
noncomputable section
open Set Filter Metric Function Complex MeasureTheory InnerProductSpace Real
open scoped Topology Laplacian ComplexConjugate

namespace SLEExactGauge

lemma exterior_first_coefficient_le_one {f C : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f {z : ℂ | 1<‖z‖})
    (hC : DifferentiableOn ℂ C (ball 0 1))
    (he : ∀ z : ℂ, 1<‖z‖ → f z=z+C z⁻¹)
    (hflux : ∀ r : ℝ, 1<r → 0≤∫ θ in -Real.pi..Real.pi,
      radialLaplacianFlux (fun z => ‖f z‖^2) (r,θ)) :
    ‖deriv C 0‖≤1 := by
  have hbound (r : ℝ) (hr : 1<r) : ‖deriv C 0‖≤r^2 := by
    have hr0 : 0<r := zero_lt_one.trans hr
    have hri : 0<r⁻¹ := inv_pos.mpr hr0
    have hri1 : r⁻¹<1 := inv_lt_one_of_one_lt₀ hr
    have hCa : AnalyticOnNhd ℂ C (closedBall (0:ℂ) r⁻¹) := by
      intro z hz
      apply hC.analyticAt
      apply isOpen_ball.mem_nhds
      exact (closedBall_subset_ball hri1) hz
    have hfa : AnalyticOnNhd ℂ f (sphere (0:ℂ) |r|) := by
      intro z hz
      apply hf.analyticAt
      apply (isOpen_lt continuous_const continuous_norm).mem_nhds
      have hzr : ‖z‖=r := by simpa only [mem_sphere,dist_zero_right,abs_of_pos hr0] using hz
      change 1<‖z‖
      rwa [hzr]
    have hval (z : ℂ) (hz : z∈sphere (0:ℂ) r) : f z=z+C z⁻¹ := by
      apply he z
      rwa [show ‖z‖=r by simpa only [mem_sphere,dist_zero_right] using hz]
    have hder (z : ℂ) (hz : z∈sphere (0:ℂ) r) :
        deriv f z=1-z⁻¹^2*deriv C z⁻¹ := by
      have hzr : ‖z‖=r := by simpa only [mem_sphere,dist_zero_right] using hz
      have hz0 : z≠0 := (norm_ne_zero_iff (a := z)).mp (by rw [hzr]; exact hr0.ne')
      have hzi : z⁻¹∈ball (0:ℂ) 1 := by
        rw [mem_ball_zero_iff,norm_inv,hzr]
        exact hri1
      have hdC := (hC.differentiableAt (isOpen_ball.mem_nhds hzi)).hasDerivAt
      have hd := (hasDerivAt_id z).add (hdC.comp z (hasDerivAt_inv hz0))
      have heloc : f =ᶠ[𝓝 z] (fun z => z+C z⁻¹) := by
        filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds
          (show 1<‖z‖ by rwa [hzr])] with w hw
        exact he w hw
      have hh := (hd.congr_of_eventuallyEq heloc).deriv
      convert! hh using 1
      ring
    have harea := inverse_chart_area_average hr0 hCa hval hder
    have hfp := hflux r hr
    rw [holomorphic_flux_eq_area_average hfa,harea] at hfp
    have hcp := analytic_flux_ge_first_coefficient hri hCa
    rw [holomorphic_flux_eq_area_average (hCa.mono (by
      rw [abs_of_pos hri]; exact sphere_subset_closedBall))] at hcp
    have hs : r⁻¹^2*‖deriv C 0‖^2≤r^2 := by
      apply (mul_le_mul_iff_right₀ (show 0<4*Real.pi by positivity)).mp
      nlinarith only [hfp,hcp]
    have hrnorm : r⁻¹*‖deriv C 0‖≤r := by
      apply (sq_le_sq₀ (mul_nonneg hri.le (norm_nonneg _)) hr0.le).mp
      nlinarith only [hs]
    have hh : ‖deriv C 0‖≤r*r := by
      apply (div_le_iff₀ hr0).mp
      simpa only [div_eq_mul_inv,mul_comm] using hrnorm
    simpa only [pow_two] using hh
  let r (n : ℕ) := 1+1/((n:ℝ)+1)
  have hr (n : ℕ) : 1<r n := by
    dsimp [r]
    have : 0 < 1 / ((n:ℝ)+1) := by positivity
    linarith
  have ht : Tendsto r atTop (𝓝 1) := by
    simpa only [r,add_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add 1
  have ht2 : Tendsto (fun n => (r n)^2) atTop (𝓝 (1:ℝ)) := by simpa using ht.pow 2
  exact ge_of_tendsto ht2 (Eventually.of_forall (fun n => hbound (r n) (hr n)))

end SLEExactGauge

end

end OAI
