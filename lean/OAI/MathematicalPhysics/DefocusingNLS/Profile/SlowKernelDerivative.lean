import OAI.MathematicalPhysics.DefocusingNLS.Profile.SlowKernelIntegrability

namespace OAI

/-! # Pointwise spatial differentiation of the outgoing kernel -/

namespace DefocusingNLS

theorem one_add_real_div_mem_slitPlane (x : ℂ) (hx : 0 ≤ x.re)
    {u : ℝ} (hu : 0 ≤ u) : 1 + (u : ℂ) / x ∈ Complex.slitPlane := by
  apply Complex.mem_slitPlane_iff.mpr
  left
  simp only [Complex.add_re, Complex.one_re, Complex.div_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, zero_div, add_zero]
  have : 0 ≤ u * x.re / Complex.normSq x :=
    div_nonneg (mul_nonneg hu hx) (Complex.normSq_nonneg x)
  linarith

noncomputable def slowKernelSpatialDerivative (q : ℂ) (m : ℕ) (x : ℂ)
    (u : ℝ) : ℂ :=
  Complex.exp (-(u : ℂ)) * (u : ℂ) ^ (q - 1) *
    (((m : ℂ) - 1 - q) * (1 + (u : ℂ) / x) ^ ((m : ℂ) - 2 - q) *
      (-(u : ℂ) / x ^ 2))

theorem hasDerivAt_regularizingBracket_spatial (r x : ℂ)
    (hx : 0 ≤ x.re) (hx0 : x ≠ 0) {u : ℝ} (hu : 0 ≤ u) :
    HasDerivAt (fun y : ℂ => regularizingBracket r y u)
      (r * (1 + (u : ℂ) / x) ^ (r - 1) * (-(u : ℂ) / x ^ 2)) x := by
  have hi : HasDerivAt (fun y : ℂ => (u : ℂ) / y) (-(u : ℂ) / x ^ 2) x := by
    simpa only [div_eq_mul_inv, mul_neg, neg_mul] using
      (hasDerivAt_inv hx0).const_mul (u : ℂ)
  have h := (hi.const_add 1).cpow_const (c := r)
    (one_add_real_div_mem_slitPlane x hx hu)
  simpa only [regularizingBracket, mul_one] using h.sub_const 1

theorem hasDerivAt_regularizedSlowKernel_spatial (q : ℂ) (m : ℕ) (x : ℂ)
    (hx : 0 ≤ x.re) (hx0 : x ≠ 0) {u : ℝ} (hu : 0 ≤ u) :
    HasDerivAt (fun y : ℂ => regularizedSlowKernel q m y u)
      (slowKernelSpatialDerivative q m x u) x := by
  have h := (hasDerivAt_regularizingBracket_spatial ((m : ℂ) - 1 - q)
    x hx hx0 hu).const_mul (Complex.exp (-(u : ℂ)) * (u : ℂ) ^ (q - 1))
  have he : (m : ℂ) - 1 - q - 1 = (m : ℂ) - 2 - q := by ring
  simpa only [regularizedSlowKernel, slowKernelSpatialDerivative, he] using h

/-- The spatial derivative is a shifted regularized kernel plus the gamma
integrand. This retains the endpoint cancellation instead of separating
two individually divergent terms at the original parameter. -/
theorem slowKernelSpatialDerivative_eq (q : ℂ) (m : ℕ) (x : ℂ)
    {u : ℝ} (hu : 0 < u) :
    slowKernelSpatialDerivative q m x u =
      (-((m : ℂ) - 1 - q) / x ^ 2) *
        (regularizedSlowKernel (q + 1) m x u +
          Complex.exp (-(u : ℂ)) * (u : ℂ) ^ q) := by
  have he : (m : ℂ) - 1 - (q + 1) = (m : ℂ) - 2 - q := by ring
  have hp : (u : ℂ) ^ (q - 1) * (u : ℂ) = (u : ℂ) ^ q := by
    calc
      (u : ℂ) ^ (q - 1) * (u : ℂ) = (u : ℂ) ^ (q - 1) * (u : ℂ) ^ (1 : ℂ) := by
        rw [Complex.cpow_one]
      _ = (u : ℂ) ^ (q - 1 + 1) :=
        (Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hu.ne')).symm
      _ = (u : ℂ) ^ q := by congr 1; ring
  simp only [slowKernelSpatialDerivative, regularizedSlowKernel,
    regularizingBracket, add_sub_cancel_right, he]
  calc
    _ = (-((m : ℂ) - 1 - q) / x ^ 2) *
        (Complex.exp (-(u : ℂ)) * ((u : ℂ) ^ (q - 1) * (u : ℂ)) *
          (1 + (u : ℂ) / x) ^ ((m : ℂ) - 2 - q)) := by ring
    _ = _ := by rw [hp]; ring

theorem integrable_slowKernelSpatialDerivative (q : ℂ) (m : ℕ) (x : ℂ)
    (hq : -1 < q.re) (hx : 0 ≤ x.re) (hx0 : x ≠ 0) :
    MeasureTheory.IntegrableOn (slowKernelSpatialDerivative q m x) (Set.Ioi 0) := by
  have hq' : 0 < (q + 1).re := by simp only [Complex.add_re, Complex.one_re]; linarith
  have hg : MeasureTheory.IntegrableOn
      (fun u : ℝ => Complex.exp (-(u : ℂ)) * (u : ℂ) ^ q) (Set.Ioi 0) := by
    simpa only [Complex.ofReal_exp, Complex.ofReal_neg, add_sub_cancel_right] using
      Complex.GammaIntegral_convergent hq'
  have hi := ((integrable_regularizedSlowKernel (q + 1) m x (by linarith) hx hx0).add hg).const_mul
    (-((m : ℂ) - 1 - q) / x ^ 2)
  apply hi.congr
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
  exact (slowKernelSpatialDerivative_eq q m x hu).symm

end DefocusingNLS

end OAI
