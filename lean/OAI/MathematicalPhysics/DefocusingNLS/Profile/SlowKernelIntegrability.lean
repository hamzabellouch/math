import OAI.MathematicalPhysics.DefocusingNLS.Profile.SlowKernelEndpoint
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.ComplexPowerBound

namespace OAI

/-! # Integrability of the regularized outgoing integral -/

open MeasureTheory Filter Topology Asymptotics

namespace DefocusingNLS

theorem regularizedSlowKernel_isBigO_infty (q : ℂ) (m : ℕ) (x : ℂ) (hx : x ≠ 0) :
    regularizedSlowKernel q m x =O[atTop]
      (fun u : ℝ => Real.exp (-u) * u ^
        (q.re - 1 + max ((m : ℂ) - 1 - q).re 0)) := by
  obtain ⟨C, _, hC⟩ := regularizingBracket_polynomial_bound ((m : ℂ) - 1 - q) x hx
  refine isBigO_iff.mpr ⟨C, ?_⟩
  filter_upwards [eventually_ge_atTop (max 1 (2 * ‖x‖))] with u hu
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hu)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le
    (Real.rpow_nonneg hu0.le _))]
  calc
    ‖regularizedSlowKernel q m x u‖ = Real.exp (-u) * u ^ (q.re - 1) *
        ‖regularizingBracket ((m : ℂ) - 1 - q) x u‖ := by
      simp only [regularizedSlowKernel, norm_mul, Complex.norm_exp, Complex.neg_re,
        Complex.ofReal_re, Complex.norm_cpow_eq_rpow_re_of_pos hu0, Complex.sub_re,
        Complex.one_re]
    _ ≤ Real.exp (-u) * u ^ (q.re - 1) *
        (C * u ^ (max ((m : ℂ) - 1 - q).re 0)) := by gcongr; exact hC u hu
    _ = C * (Real.exp (-u) * u ^
        (q.re - 1 + max ((m : ℂ) - 1 - q).re 0)) := by
      rw [Real.rpow_add hu0]
      ring

theorem regularizedSlowKernel_integrableAt_infty (q : ℂ) (m : ℕ) (x : ℂ)
    (hx : x ≠ 0) : IntegrableAtFilter (regularizedSlowKernel q m x) atTop := by
  have hsmall := isLittleO_exp_mul_rpow_of_lt
    (q.re - 1 + max ((m : ℂ) - 1 - q).re 0)
    (a := -1) (b := -(1 / 2)) (by norm_num)
  have hbig : regularizedSlowKernel q m x =O[atTop]
      (fun u : ℝ => Real.exp (-(1 / 2) * u)) := by
    apply (regularizedSlowKernel_isBigO_infty q m x hx).trans
    simpa only [neg_one_mul] using hsmall.isBigO
  apply hbig.integrableAtFilter
  · exact ⟨Set.univ, univ_mem, (measurable_regularizedSlowKernel q m x).aestronglyMeasurable.restrict⟩
  · exact ⟨Set.Ioi 0, Ioi_mem_atTop 0,
      integrableOn_exp_mul_Ioi (by norm_num : -(1 / 2 : ℝ) < 0) 0⟩

theorem continuousOn_regularizedSlowKernel (q : ℂ) (m : ℕ) (x : ℂ)
    (hx : 0 ≤ x.re) : ContinuousOn (regularizedSlowKernel q m x) (Set.Ioi 0) := by
  have hpower : ContinuousOn (fun u : ℝ => (u : ℂ) ^ (q - 1)) (Set.Ioi 0) :=
    Complex.continuous_ofReal.continuousOn.cpow_const (by
      intro u hu
      exact Complex.ofReal_mem_slitPlane.mpr hu)
  have hbase : Continuous (fun u : ℝ => 1 + (u : ℂ) / x) := by fun_prop
  have hbracket : ContinuousOn
      (fun u : ℝ => regularizingBracket ((m : ℂ) - 1 - q) x u) (Set.Ioi 0) := by
    apply (hbase.continuousOn.cpow_const ?_).sub continuousOn_const
    intro u hu
    apply Complex.mem_slitPlane_iff.mpr
    left
    simp only [Complex.add_re, Complex.one_re, Complex.div_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, zero_div, add_zero]
    have : 0 ≤ u * x.re / Complex.normSq x :=
      div_nonneg (mul_nonneg (le_of_lt hu) hx) (Complex.normSq_nonneg x)
    linarith
  exact (show ContinuousOn (fun u : ℝ => Complex.exp (-(u : ℂ))) (Set.Ioi 0) by
      fun_prop).mul hpower |>.mul hbracket

/-- Absolute Bochner integrability for the entire parameter domain used by
the free matching argument, including its nonzero imaginary boundary. -/
theorem integrable_regularizedSlowKernel (q : ℂ) (m : ℕ) (x : ℂ)
    (hq : -1 < q.re) (hx : 0 ≤ x.re) (hx0 : x ≠ 0) :
    IntegrableOn (regularizedSlowKernel q m x) (Set.Ioi 0) := by
  apply integrableOn_Ioi_iff_integrableAtFilter_atTop_nhdsWithin.mpr
  exact ⟨regularizedSlowKernel_integrableAt_infty q m x hx0,
    regularizedSlowKernel_integrableAt_zero q m x hq,
    (continuousOn_regularizedSlowKernel q m x hx).locallyIntegrableOn measurableSet_Ioi⟩

end DefocusingNLS

end OAI
