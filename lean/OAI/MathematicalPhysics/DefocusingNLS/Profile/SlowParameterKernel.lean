import OAI.MathematicalPhysics.DefocusingNLS.Profile.SlowKernelDerivative

namespace OAI

/-! # Pointwise differentiation of the regularized kernel in its parameter -/

namespace DefocusingNLS

noncomputable def slowKernelParameterDerivative (q : ℂ) (m : ℕ) (x : ℂ)
    (u : ℝ) : ℂ :=
  Complex.exp (-(u : ℂ)) * (u : ℂ) ^ (q - 1) *
    (Complex.log (u : ℂ) * regularizingBracket ((m : ℂ) - 1 - q) x u -
      Complex.log (1 + (u : ℂ) / x) * (1 + (u : ℂ) / x) ^ ((m : ℂ) - 1 - q))

theorem hasDerivAt_regularizingBracket_parameter (q : ℂ) (m : ℕ) (x : ℂ)
    (hx : 0 ≤ x.re) {u : ℝ} (hu : 0 ≤ u) :
    HasDerivAt (fun z : ℂ => regularizingBracket ((m : ℂ) - 1 - z) x u)
      (-(Complex.log (1 + (u : ℂ) / x) *
        (1 + (u : ℂ) / x) ^ ((m : ℂ) - 1 - q))) q := by
  have hbase : 1 + (u : ℂ) / x ≠ 0 :=
    Complex.slitPlane_ne_zero (one_add_real_div_mem_slitPlane x hx hu)
  have h := (((hasDerivAt_const q ((m : ℂ) - 1)).sub (hasDerivAt_id q)).const_cpow
    (c := 1 + (u : ℂ) / x) (Or.inl hbase)).sub_const 1
  convert! h using 1
  simp only [Pi.sub_apply, id_eq, zero_sub]
  ring

theorem hasDerivAt_regularizedSlowKernel_parameter (q : ℂ) (m : ℕ) (x : ℂ)
    (hx : 0 ≤ x.re) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun z : ℂ => regularizedSlowKernel z m x u)
      (slowKernelParameterDerivative q m x u) q := by
  have hp := ((hasDerivAt_id q).sub_const 1).const_cpow (c := (u : ℂ))
    (Or.inl (Complex.ofReal_ne_zero.mpr hu.ne'))
  have hb := hasDerivAt_regularizingBracket_parameter q m x hx hu.le
  have h := (hp.fun_mul hb).const_mul (Complex.exp (-(u : ℂ)))
  convert! h using 1
  · funext z
    simp only [regularizedSlowKernel, id_eq]
    ring
  · simp only [slowKernelParameterDerivative, mul_one, id_eq]
    ring

end DefocusingNLS

end OAI
