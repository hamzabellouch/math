import OAI.MathematicalPhysics.DefocusingNLS.Profile.SlowEulerParameter

namespace OAI

/-! # The defining integral off the negative spatial ray -/

open MeasureTheory Filter Topology

namespace DefocusingNLS

theorem one_add_real_div_mem_slitPlane_of_slit (x : ℂ) (hx : x ∈ Complex.slitPlane)
    {u : ℝ} (hu : 0 ≤ u) : 1 + (u : ℂ) / x ∈ Complex.slitPlane := by
  rcases Complex.mem_slitPlane_iff.mp hx with hre | him
  · exact one_add_real_div_mem_slitPlane x hre.le hu
  · rcases hu.eq_or_lt with rfl | hu
    · simp
    · apply Complex.mem_slitPlane_iff.mpr
      right
      have hx0 : x ≠ 0 := Complex.slitPlane_ne_zero hx
      simp only [Complex.add_im, Complex.one_im, Complex.div_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, zero_add, zero_div, zero_sub]
      exact neg_ne_zero.mpr (div_ne_zero (mul_ne_zero hu.ne' him)
        (Complex.normSq_pos.mpr hx0).ne')

theorem continuousOn_regularizedSlowKernel_of_slit (q : ℂ) (m : ℕ) (x : ℂ)
    (hx : x ∈ Complex.slitPlane) :
    ContinuousOn (regularizedSlowKernel q m x) (Set.Ioi 0) := by
  have hp : ContinuousOn (fun u : ℝ => (u : ℂ) ^ (q - 1)) (Set.Ioi 0) :=
    Complex.continuous_ofReal.continuousOn.cpow_const fun u hu =>
      Complex.ofReal_mem_slitPlane.mpr hu
  have hb : Continuous (fun u : ℝ => 1 + (u : ℂ) / x) := by fun_prop
  have hr : ContinuousOn
      (fun u : ℝ => regularizingBracket ((m : ℂ) - 1 - q) x u) (Set.Ioi 0) :=
    (hb.continuousOn.cpow_const fun _ hu =>
      one_add_real_div_mem_slitPlane_of_slit x hx (le_of_lt hu)).sub continuousOn_const
  exact (show ContinuousOn (fun u : ℝ => Complex.exp (-(u : ℂ))) (Set.Ioi 0) by
    fun_prop).mul hp |>.mul hr

theorem integrable_regularizedSlowKernel_of_slit (q : ℂ) (m : ℕ) (x : ℂ)
    (hq : -1 < q.re) (hx : x ∈ Complex.slitPlane) :
    IntegrableOn (regularizedSlowKernel q m x) (Set.Ioi 0) := by
  apply integrableOn_Ioi_iff_integrableAtFilter_atTop_nhdsWithin.mpr
  exact ⟨regularizedSlowKernel_integrableAt_infty q m x (Complex.slitPlane_ne_zero hx),
    regularizedSlowKernel_integrableAt_zero q m x hq,
    (continuousOn_regularizedSlowKernel_of_slit q m x hx).locallyIntegrableOn measurableSet_Ioi⟩

theorem hasDerivAt_regularizedSlowKernel_spatial_of_slit (q : ℂ) (m : ℕ) (x : ℂ)
    (hx : x ∈ Complex.slitPlane) {u : ℝ} (hu : 0 ≤ u) :
    HasDerivAt (fun y : ℂ => regularizedSlowKernel q m y u)
      (slowKernelSpatialDerivative q m x u) x := by
  have hx0 := Complex.slitPlane_ne_zero hx
  have hi : HasDerivAt (fun y : ℂ => (u : ℂ) / y) (-(u : ℂ) / x ^ 2) x := by
    simpa only [div_eq_mul_inv, mul_neg, neg_mul] using
      (hasDerivAt_inv hx0).const_mul (u : ℂ)
  have h := (((hi.const_add 1).cpow_const (c := (m : ℂ) - 1 - q)
    (one_add_real_div_mem_slitPlane_of_slit x hx hu)).sub_const 1).const_mul
      (Complex.exp (-(u : ℂ)) * (u : ℂ) ^ (q - 1))
  have he : (m : ℂ) - 1 - q - 1 = (m : ℂ) - 2 - q := by ring
  simpa only [regularizedSlowKernel, slowKernelSpatialDerivative, regularizingBracket, he] using h

theorem integrable_slowKernelSpatialDerivative_of_slit (q : ℂ) (m : ℕ) (x : ℂ)
    (hq : -1 < q.re) (hx : x ∈ Complex.slitPlane) :
    IntegrableOn (slowKernelSpatialDerivative q m x) (Set.Ioi 0) := by
  have hq' : 0 < (q + 1).re := by change 0 < q.re + 1; linarith
  have hg : IntegrableOn
      (fun u : ℝ => Complex.exp (-(u : ℂ)) * (u : ℂ) ^ q) (Set.Ioi 0) := by
    simpa only [Complex.ofReal_exp, Complex.ofReal_neg, add_sub_cancel_right] using
      Complex.GammaIntegral_convergent hq'
  have hi := ((integrable_regularizedSlowKernel_of_slit (q + 1) m x
    (by change -1 < q.re + 1; linarith) hx).add hg).const_mul
      (-((m : ℂ) - 1 - q) / x ^ 2)
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact (slowKernelSpatialDerivative_eq q m x hu).symm

end DefocusingNLS

end OAI
