import OAI.NumberTheory.Jacobsthal.Sieve.ExponentialIntegral

namespace OAI

namespace Erdos970

section

open Real Set MeasureTheory Filter Topology

namespace ErdosAverageCertificates

noncomputable section

theorem laplace_ode_solution
    {F : ℝ → ℝ}
    (hF : DifferentiableOn ℝ F (Set.Ioi 0))
    (hpos : ∀ s : ℝ, 0 < s → 0 < 1 + F s)
    (hode : ∀ s : ℝ, 0 < s →
      s * deriv F s + Real.exp (-s) * (1 + F s) = 0)
    (hinfty : Tendsto F atTop (nhds 0)) :
    ∀ s : ℝ, 0 < s →
      1 + F s = Real.exp
        (∫ t in Set.Ioi s, Real.exp (-t) / t) := by
  intro s hs
  have hlogDeriv : ∀ x ∈ Set.Ici s,
      HasDerivAt (fun y : ℝ ↦ Real.log (1 + F y))
        (-Real.exp (-x) / x) x := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hs hx
    have hFx : DifferentiableAt ℝ F x :=
      hF.differentiableAt (Ioi_mem_nhds hx0)
    have hinner : HasDerivAt (fun y : ℝ ↦ 1 + F y) (deriv F x) x :=
      hFx.hasDerivAt.const_add 1
    have hlog := (Real.hasDerivAt_log (hpos x hx0).ne').comp x hinner
    have hxne : x ≠ 0 := hx0.ne'
    have hHne : 1 + F x ≠ 0 := (hpos x hx0).ne'
    have hratio : (1 + F x)⁻¹ * deriv F x = -Real.exp (-x) / x := by
      rw [inv_mul_eq_div]
      field_simp [hxne, hHne]
      nlinarith [hode x hx0]
    exact hlog.congr_deriv hratio
  have hlogLim : Tendsto (fun x : ℝ ↦ Real.log (1 + F x))
      atTop (nhds 0) := by
    have hinner : Tendsto (fun x : ℝ ↦ 1 + F x) atTop (nhds 1) := by
      simpa using (tendsto_const_nhds.add hinfty)
    change Tendsto (Real.log ∘ fun x : ℝ ↦ 1 + F x) atTop (nhds 0)
    simpa only [Real.log_one] using
      (Real.continuousAt_log one_ne_zero).tendsto.comp hinner
  have hneg : ∀ x ∈ Set.Ioi s, -Real.exp (-x) / x ≤ 0 := by
    intro x hx
    have hx0 : 0 < x := hs.trans hx
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Real.exp_pos _).le) hx0.le
  have hint := MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonpos'
    hlogDeriv hneg hlogLim
  have hlogEq : Real.log (1 + F s) =
      ∫ t in Set.Ioi s, Real.exp (-t) / t := by
    have hrewrite : (fun x : ℝ ↦ -Real.exp (-x) / x) =
        fun x : ℝ ↦ -(Real.exp (-x) / x) := by
      funext x
      ring
    rw [hrewrite, integral_neg] at hint
    linarith
  rw [← hlogEq, Real.exp_log (hpos s hs)]

end

end ErdosAverageCertificates

end

end Erdos970

end OAI
