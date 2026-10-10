import OAI.MathematicalPhysics.DefocusingNLS.Profile.SlowKummerEquation

namespace OAI

/-! # Holomorphic dependence of the Euler integral on its parameter

The logarithm introduced by parameter differentiation is absorbed by a
positive shift in the real exponent. The majorant is another convergent
Euler integral, so no endpoint logarithmic estimates are needed.
-/

open MeasureTheory Filter Topology

namespace DefocusingNLS

noncomputable def slowEulerParameterDerivative (q : ℂ) (m : ℕ) (x : ℂ) (u : ℝ) : ℂ :=
  slowEulerKernel q m x u * (Complex.log (u : ℂ) - Complex.log (1 + (u : ℂ)))

theorem hasDerivAt_slowEulerKernel_parameter (q : ℂ) (m : ℕ) (x : ℂ)
    {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun z : ℂ => slowEulerKernel z m x u)
      (slowEulerParameterDerivative q m x u) q := by
  have hu0 : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
  have hb0 : 1 + (u : ℂ) ≠ 0 := by
    have : 0 < (1 + (u : ℂ)).re := by simp; linarith
    intro h
    simp [h] at this
  have hp := ((hasDerivAt_id q).sub_const 1).const_cpow (c := (u : ℂ)) (Or.inl hu0)
  have hb := ((hasDerivAt_const q ((m : ℂ) - 1)).sub (hasDerivAt_id q)).const_cpow
    (c := 1 + (u : ℂ)) (Or.inl hb0)
  have h := (hp.fun_mul hb).const_mul (Complex.exp (-x * (u : ℂ)))
  convert! h using 1
  · funext z
    simp only [slowEulerKernel, Pi.sub_apply, id_eq]
    ring
  · simp only [slowEulerParameterDerivative, slowEulerKernel, Pi.sub_apply, id_eq, mul_one, zero_sub]
    ring

theorem norm_slowEulerKernel_parameter_ratio (q : ℂ) (a : ℝ) (m : ℕ) (x : ℂ)
    {u : ℝ} (hu : 0 < u) :
    ‖slowEulerKernel q m x u‖ =
      ‖slowEulerKernel (a : ℂ) m x u‖ * (u / (1 + u)) ^ (q.re - a) := by
  have hu1 : 0 < 1 + u := by linarith
  have hp : u ^ (q.re - 1) = u ^ (a - 1) * u ^ (q.re - a) := by
    rw [← Real.rpow_add hu]
    congr 1
    ring
  have hb : (1 + u) ^ ((m : ℝ) - 1 - q.re) =
      (1 + u) ^ ((m : ℝ) - 1 - a) * (1 + u) ^ (-(q.re - a)) := by
    rw [← Real.rpow_add hu1]
    congr 1
    ring
  rw [norm_slowEulerKernel q m x hu, norm_slowEulerKernel (a : ℂ) m x hu,
    Complex.ofReal_re, hp, hb, Real.div_rpow hu.le hu1.le, Real.rpow_neg hu1.le]
  ring

theorem norm_slowEulerParameterDerivative (q : ℂ) (m : ℕ) (x : ℂ)
    {u : ℝ} (hu : 0 < u) :
    ‖slowEulerParameterDerivative q m x u‖ =
      ‖slowEulerKernel q m x u‖ * |Real.log (u / (1 + u))| := by
  have hu1 : 0 < 1 + u := by linarith
  have hbase : (1 : ℂ) + (u : ℂ) = ((1 + u : ℝ) : ℂ) := by push_cast; rfl
  rw [slowEulerParameterDerivative, norm_mul, hbase,
    ← Complex.ofReal_log hu.le, ← Complex.ofReal_log hu1.le,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    Real.log_div hu.ne' hu1.ne']

theorem slowEulerParameterDerivative_majorant (q : ℂ) (a δ : ℝ) (m : ℕ) (x : ℂ)
    (hδ : 0 < δ) (hq : a + δ ≤ q.re) {u : ℝ} (hu : 0 < u) :
    ‖slowEulerParameterDerivative q m x u‖ ≤
      (1 / δ) * ‖slowEulerKernel (a : ℂ) m x u‖ := by
  have hr : 0 < u / (1 + u) := div_pos hu (by linarith)
  have hr1 : u / (1 + u) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
  have hs : 0 < q.re - a := by linarith
  have hb : (u / (1 + u)) ^ (q.re - a) * |Real.log (u / (1 + u))| ≤ 1 / δ := by
    calc
      _ = |Real.log (u / (1 + u)) * (u / (1 + u)) ^ (q.re - a)| := by
        rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hr _)]
        ring
      _ ≤ 1 / (q.re - a) := (Real.abs_log_mul_self_rpow_lt _ _ hr hr1 hs).le
      _ ≤ 1 / δ := one_div_le_one_div_of_le hδ (by linarith)
  rw [norm_slowEulerParameterDerivative q m x hu, norm_slowEulerKernel_parameter_ratio q a m x hu]
  calc
    _ = ‖slowEulerKernel (a : ℂ) m x u‖ *
        ((u / (1 + u)) ^ (q.re - a) * |Real.log (u / (1 + u))|) := by ring
    _ ≤ ‖slowEulerKernel (a : ℂ) m x u‖ * (1 / δ) :=
      mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ = _ := mul_comm _ _

theorem continuousOn_slowEulerParameterDerivative (q : ℂ) (m : ℕ) (x : ℂ) :
    ContinuousOn (slowEulerParameterDerivative q m x) (Set.Ioi 0) := by
  apply (continuousOn_slowEulerKernel q m x).mul
  apply ContinuousOn.sub
  · exact Complex.continuous_ofReal.continuousOn.clog fun u hu =>
      Complex.ofReal_mem_slitPlane.mpr hu
  · apply (continuous_const.add Complex.continuous_ofReal).continuousOn.clog
    intro u hu
    apply Complex.mem_slitPlane_iff.mpr
    left
    change 0 < 1 + u
    linarith [show 0 < u from hu]

theorem hasDerivAt_slowEulerIntegral_parameter (q : ℂ) (m : ℕ) (x : ℂ)
    (hq : 0 < q.re) (hx : 0 < x.re) :
    HasDerivAt (fun z : ℂ => slowEulerIntegral z m x)
      (∫ u : ℝ in Set.Ioi 0, slowEulerParameterDerivative q m x u) q := by
  let a : ℝ := q.re / 4
  have ha : 0 < a := by dsimp [a]; positivity
  let s : Set ℂ := {z | q.re / 2 < z.re}
  have hs : s ∈ 𝓝 q := (isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    (by dsimp [s]; linarith)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioi (0 : ℝ)))
    (F := fun z u => slowEulerKernel z m x u)
    (F' := fun z u => slowEulerParameterDerivative z m x u)
    (bound := fun u => (1 / a) * ‖slowEulerKernel (a : ℂ) m x u‖) hs
    (Eventually.of_forall fun z =>
      (continuousOn_slowEulerKernel z m x).aestronglyMeasurable measurableSet_Ioi)
    (integrable_slowEulerKernel q m x hq hx)
    ((continuousOn_slowEulerParameterDerivative q m x).aestronglyMeasurable measurableSet_Ioi)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      intro z hz
      apply slowEulerParameterDerivative_majorant z a a m x ha _ hu
      dsimp [s, a] at hz ⊢
      linarith)
    ((integrable_slowEulerKernel (a : ℂ) m x (by simpa using ha) hx).norm.const_mul (1 / a))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      intro z _
      exact hasDerivAt_slowEulerKernel_parameter z m x hu)).2

/-- Holomorphy in the parameter includes the regularized point `q=0`. -/
theorem differentiableAt_regularizedSlowSolution_parameter (q : ℂ) (m : ℕ) (x : ℂ)
    (hq : -1 < q.re) (hx : 0 < x.re) :
    DifferentiableAt ℂ (fun z : ℂ => regularizedSlowSolution z m x) q := by
  have hq' : 0 < (q + 1).re := by change 0 < q.re + 1; linarith
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx
  have hshift : DifferentiableAt ℂ (fun z : ℂ => z + 1) q :=
    differentiableAt_id.add_const 1
  have hi (n : ℕ) : DifferentiableAt ℂ
      (fun z : ℂ => (Complex.Gamma (z + 1))⁻¹ * slowEulerIntegral (z + 1) n x) q := by
    exact ((Complex.differentiable_one_div_Gamma (q + 1)).mul
      (hasDerivAt_slowEulerIntegral_parameter (q + 1) n x hq' hx).differentiableAt).comp q hshift
  have hf := ((hi (m + 1)).const_mul x).sub
    (((differentiableAt_const ((m : ℂ) - 1)).sub differentiableAt_id).mul (hi m))
  apply hf.congr_of_eventuallyEq
  have hs : {z : ℂ | -1 < z.re} ∈ 𝓝 q :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hq
  filter_upwards [hs] with z hz
  have hz' : 0 < (z + 1).re := by change 0 < z.re + 1; linarith
  rw [regularizedSlowSolution_contiguous z m x hz hx.le hx0,
    regularizedSlowSolution_eq_euler_complex (z + 1) (m + 1) x hz' hx,
    regularizedSlowSolution_eq_euler_complex (z + 1) m x hz' hx]
  rfl

theorem differentiableOn_regularizedSlowSolution_parameter (m : ℕ) (x : ℂ)
    (hx : 0 < x.re) :
    DifferentiableOn ℂ (fun q : ℂ => regularizedSlowSolution q m x) {q : ℂ | -1 < q.re} := by
  intro q hq
  exact (differentiableAt_regularizedSlowSolution_parameter q m x hq hx).differentiableWithinAt

end DefocusingNLS

end OAI
