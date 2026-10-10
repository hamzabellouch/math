import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Probability.Moments.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory Real Filter Topology

lemma exp_derivative_domination {c x t : ℝ} (hc : 0 < c) (hx : 0 ≤ x)
    (ht : t < c/2) : |exp (t*x)*x| ≤ (2/c)*exp (c*x) := by
  have hxbound : x ≤ (2/c)*exp ((c/2)*x) := by
    have hh := Real.add_one_le_exp ((c/2)*x)
    calc
      x ≤ (2*exp ((c/2)*x))/c := (le_div_iff₀ hc).mpr (by nlinarith)
      _ = (2/c)*exp ((c/2)*x) := by ring
  rw [abs_of_nonneg (mul_nonneg (exp_pos _).le hx), mul_comm (exp (t*x)) x]
  calc
    x*exp (t*x) ≤ ((2/c)*exp ((c/2)*x))*exp (t*x) :=
      mul_le_mul_of_nonneg_right hxbound (exp_pos _).le
    _ = (2/c)*exp ((c/2+t)*x) := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    _ ≤ (2/c)*exp (c*x) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right (by linarith : c/2+t ≤ c) hx

/-- A nonnegative measurable function with a positive exponential moment is
integrable, and its moment-generating function has derivative equal to its mean
at zero. Finiteness of the measure follows by domination. -/
theorem hasDerivAt_integral_exp_zero {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {F : Ω → ℝ} (hF : Measurable F)
    (hpos : ∀ᵐ ω ∂P, 0 ≤ F ω) {c : ℝ} (hc : 0 < c)
    (hexp : Integrable (fun ω => exp (c*F ω)) P) :
    Integrable F P ∧
      HasDerivAt (fun t : ℝ => ∫ ω, exp (t*F ω) ∂P) (∫ ω, F ω ∂P) 0 := by
  have hone : Integrable (fun _ : Ω => (1 : ℝ)) P := by
    apply hexp.mono' (by fun_prop)
    filter_upwards [hpos] with ω hω
    simpa only [norm_one] using Real.one_le_exp (mul_nonneg hc.le hω)
  have hmeas : ∀ᶠ t : ℝ in 𝓝 0,
      AEStronglyMeasurable (fun ω => exp (t*F ω)) P :=
    Eventually.of_forall fun t => (by fun_prop : Measurable (fun ω => exp (t*F ω))).aestronglyMeasurable
  have hint : Integrable (fun ω => exp ((0 : ℝ)*F ω)) P := by simpa using hone
  have hdmeas : AEStronglyMeasurable (fun ω => exp ((0 : ℝ)*F ω)*F ω) P := by
    fun_prop
  have hbound : ∀ᵐ ω ∂P, ∀ t ∈ Set.Ioo (-c/2) (c/2),
      ‖exp (t*F ω)*F ω‖ ≤ (2/c)*exp (c*F ω) := by
    filter_upwards [hpos] with ω hω
    intro t ht
    rw [Real.norm_eq_abs]
    exact exp_derivative_domination hc hω ht.2
  have hdiff : ∀ᵐ ω ∂P, ∀ t ∈ Set.Ioo (-c/2) (c/2),
      HasDerivAt (fun s : ℝ => exp (s*F ω)) (exp (t*F ω)*F ω) t := by
    filter_upwards [] with ω
    intro t _
    simpa using ((hasDerivAt_id t).mul_const (F ω)).exp
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Ioo_mem_nhds (by linarith : -c/2 < (0 : ℝ)) (by linarith : (0 : ℝ) < c/2))
    hmeas hint hdmeas hbound (hexp.const_mul (2/c)) hdiff
  simpa only [zero_mul, Real.exp_zero, one_mul] using h

/-- The probability cgf has derivative EF at zero, by the real log chain rule. -/
theorem hasDerivAt_cgf_zero_of_nonneg_exp {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {F : Ω → ℝ}
    (hF : Measurable F) (hpos : ∀ᵐ ω ∂P, 0 ≤ F ω) {c : ℝ} (hc : 0 < c)
    (hexp : Integrable (fun ω => exp (c*F ω)) P) :
    HasDerivAt (cgf F P) (∫ ω, F ω ∂P) 0 := by
  have hd := (hasDerivAt_integral_exp_zero hF hpos hc hexp).2
  have hzero : (∫ ω, exp ((0 : ℝ)*F ω) ∂P) = 1 := by simp
  have hl := hd.log (by rw [hzero]; exact one_ne_zero)
  change HasDerivAt (fun t : ℝ => log (∫ ω, exp (t*F ω) ∂P)) (∫ ω, F ω ∂P) 0
  simpa only [hzero, div_one] using hl

end GammaFPP

end OAI
