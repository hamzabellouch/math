import OAI.MathematicalPhysics.DefocusingNLS.Profile.SlowParameterDomination
import OAI.MathematicalPhysics.DefocusingNLS.Profile.SlowParameterKernel

namespace OAI

/-! # Parameter holomorphy up to the imaginary spatial boundary -/

open MeasureTheory Filter Topology

namespace DefocusingNLS

theorem continuousOn_slowKernelParameterDerivative (q : ℂ) (m : ℕ) (x : ℂ)
    (hx : 0 ≤ x.re) :
    ContinuousOn (slowKernelParameterDerivative q m x) (Set.Ioi 0) := by
  have hu : ContinuousOn (fun u : ℝ => (u : ℂ) ^ (q - 1)) (Set.Ioi 0) :=
    Complex.continuous_ofReal.continuousOn.cpow_const fun u hu =>
      Complex.ofReal_mem_slitPlane.mpr hu
  have hb : Continuous (fun u : ℝ => 1 + (u : ℂ) / x) := by fun_prop
  have hp : ContinuousOn
      (fun u : ℝ => (1 + (u : ℂ) / x) ^ ((m : ℂ) - 1 - q)) (Set.Ioi 0) :=
    hb.continuousOn.cpow_const fun _ hu => one_add_real_div_mem_slitPlane x hx hu.le
  have hl : ContinuousOn (fun u : ℝ => Complex.log (u : ℂ)) (Set.Ioi 0) :=
    Complex.continuous_ofReal.continuousOn.clog fun u hu =>
      Complex.ofReal_mem_slitPlane.mpr hu
  have hbl : ContinuousOn (fun u : ℝ => Complex.log (1 + (u : ℂ) / x)) (Set.Ioi 0) :=
    hb.continuousOn.clog fun _ hu => one_add_real_div_mem_slitPlane x hx hu.le
  exact ((show ContinuousOn (fun u : ℝ => Complex.exp (-(u : ℂ))) (Set.Ioi 0) by
    fun_prop).mul hu).mul ((hl.mul (hp.sub continuousOn_const)).sub (hbl.mul hp))

theorem hasDerivAt_integral_regularizedSlowKernel_parameter (q : ℂ) (m : ℕ) (x : ℂ)
    (hq : -1 < q.re) (hx : 0 ≤ x.re) (hx0 : x ≠ 0) :
    HasDerivAt (fun z : ℂ => ∫ u : ℝ in Set.Ioi 0, regularizedSlowKernel z m x u)
      (∫ u : ℝ in Set.Ioi 0, slowKernelParameterDerivative q m x u) q := by
  let ρ : ℝ := (q.re + 1) / 4
  let a : ℝ := q.re - 2 * ρ
  let b : ℝ := q.re + 2 * ρ
  let M : ℝ := ‖(m : ℂ) - 1 - q‖ + 2 * ρ
  have hρ : 0 < ρ := by dsimp [ρ]; linarith
  have ha : -1 < a := by dsimp [a, ρ]; linarith
  have hab : a ≤ b := by dsimp [a, b]; linarith
  have hM : 0 ≤ M := by dsimp [M]; positivity
  obtain ⟨bound, hbound, hle⟩ := exists_regularizedSlowKernel_majorant m x a b M ha hM hab hx hx0
  have hparams (z : ℂ) (hz : ‖z - q‖ ≤ 2 * ρ) :
      a ≤ z.re ∧ z.re ≤ b ∧ ‖(m : ℂ) - 1 - z‖ ≤ M := by
    have hu := (Complex.re_le_norm (z - q)).trans hz
    have hl : (q - z).re ≤ 2 * ρ := by
      apply (Complex.re_le_norm (q - z)).trans
      simpa only [norm_sub_rev] using hz
    have hr : ‖(m : ℂ) - 1 - z‖ ≤ ‖(m : ℂ) - 1 - q‖ + ‖z - q‖ := by
      calc
        _ = ‖((m : ℂ) - 1 - q) - (z - q)‖ := by congr 1; ring
        _ ≤ _ := norm_sub_le _ _
    simp only [Complex.sub_re] at hu hl
    exact ⟨by dsimp [a]; linarith, by dsimp [b]; linarith, by dsimp [M]; linarith⟩
  have hderiv (z : ℂ) (hz : z ∈ Metric.ball q ρ) (u : ℝ) (hu : 0 < u) :
      ‖slowKernelParameterDerivative z m x u‖ ≤ bound u / ρ := by
    have hd : Differentiable ℂ (fun w : ℂ => regularizedSlowKernel w m x u) :=
      fun w => (hasDerivAt_regularizedSlowKernel_parameter w m x hx hu).differentiableAt
    have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ hd.diffContOnCl
      (C := bound u) (c := z) (by
        intro w hw
        have hwq : ‖w - q‖ ≤ 2 * ρ := by
          have htri := dist_triangle w z q
          have hwz : dist w z = ρ := Metric.mem_sphere.mp hw
          have hzq : dist z q < ρ := Metric.mem_ball.mp hz
          rw [dist_eq_norm] at htri
          linarith
        obtain ⟨hwa, hwb, hwm⟩ := hparams w hwq
        exact hle w hwa hwb hwm u hu)
    rwa [(hasDerivAt_regularizedSlowKernel_parameter z m x hx hu).deriv] at h
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioi (0 : ℝ)))
    (F := fun z u => regularizedSlowKernel z m x u)
    (F' := fun z u => slowKernelParameterDerivative z m x u)
    (bound := fun u => bound u / ρ) (Metric.ball_mem_nhds q hρ)
    (Eventually.of_forall fun z => (measurable_regularizedSlowKernel z m x).aestronglyMeasurable.restrict)
    (integrable_regularizedSlowKernel q m x hq hx hx0)
    ((continuousOn_slowKernelParameterDerivative q m x hx).aestronglyMeasurable measurableSet_Ioi)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      intro z hz
      exact hderiv z hz u hu)
    (hbound.div_const ρ)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      intro z _
      exact hasDerivAt_regularizedSlowKernel_parameter z m x hx hu)).2

/-- This includes the purely imaginary spatial arguments used in matching. -/
theorem differentiableAt_regularizedSlowSolution_parameter_closed (q : ℂ) (m : ℕ) (x : ℂ)
    (hq : -1 < q.re) (hx : 0 ≤ x.re) (hx0 : x ≠ 0) :
    DifferentiableAt ℂ (fun z : ℂ => regularizedSlowSolution z m x) q := by
  have hp := ((hasDerivAt_id q).neg).const_cpow (c := x) (Or.inl hx0)
  have hi := (hasDerivAt_integral_regularizedSlowKernel_parameter q m x hq hx hx0).differentiableAt
  have h := hp.differentiableAt.mul
    (((Complex.differentiable_one_div_Gamma q).mul hi).const_add 1)
  convert! h using 1

end DefocusingNLS

end OAI
