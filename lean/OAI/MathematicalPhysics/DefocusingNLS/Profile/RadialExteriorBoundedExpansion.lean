import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorExpansionEquation

namespace OAI

/-! Bounded extensions of the finite exterior expansion and its normalized residual. -/

open Set Filter Polynomial
open scoped BoundedContinuousFunction
namespace DefocusingNLS

noncomputable def radialExteriorClampedVariable (t : ℝ) : ℝ :=
  Real.exp (-2*max t 0)

theorem radialExteriorClampedVariable_mem (t : ℝ) :
    radialExteriorClampedVariable t ∈ Icc (0 : ℝ) 1 := by
  refine ⟨(Real.exp_pos _).le,?_⟩
  apply Real.exp_le_one_iff.mpr
  nlinarith [le_max_right t 0]

noncomputable def boundedRadialPolynomial (P : ℂ[X]) : ℝ →ᵇ ℂ := by
  classical
  have hc : Continuous (fun x : ℝ => P.eval (x : ℂ)) := by fun_prop
  have hb := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn hc.continuousOn
  exact BoundedContinuousFunction.ofNormedAddCommGroup
    (fun t => P.eval (radialExteriorClampedVariable t : ℂ))
    (by unfold radialExteriorClampedVariable; fun_prop) (Classical.choose hb)
    (fun t => Classical.choose_spec hb _ (radialExteriorClampedVariable_mem t))

theorem boundedRadialPolynomial_apply (P : ℂ[X]) (t : ℝ) :
    boundedRadialPolynomial P t=P.eval (radialExteriorClampedVariable t : ℂ) := rfl

theorem boundedRadialPolynomial_nonneg (P : ℂ[X]) (t : ℝ) (ht : 0 ≤ t) :
    boundedRadialPolynomial P t=radialExteriorPolynomialFunction P t := by
  simp only [boundedRadialPolynomial_apply,radialExteriorClampedVariable,max_eq_left ht,
    radialExteriorPolynomialFunction]

theorem radialExteriorPolynomialFunction_tendsto (P : ℂ[X]) :
    Tendsto (radialExteriorPolynomialFunction P) atTop (nhds (P.coeff 0)) := by
  have hx : Tendsto (fun t : ℝ => Real.exp (-2*t)) atTop (nhds 0) := by
    convert Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2)) using 1
    funext t
    simp [neg_mul]
  have hc : Continuous (fun x : ℝ => P.eval (x : ℂ)) := by fun_prop
  simpa only [radialExteriorPolynomialFunction,Function.comp_def,Complex.ofReal_zero,
    Polynomial.coeff_zero_eq_eval_zero] using! hc.continuousAt.tendsto.comp hx

end DefocusingNLS

end OAI
