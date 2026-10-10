import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialLinearOperator
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialDirichletLinearity
import Mathlib.Analysis.Calculus.TangentCone.Real

namespace OAI

/-! Every regular radial Poisson solution has the same Green representation, including endpoint derivatives. -/

open Set
namespace DefocusingNLS

theorem radial_poisson_representation (R : ℝ) (hR : 0 < R) (hR2 : R^2 ≤ 11)
    (A f : ℝ → ℝ) (hA : Differentiable ℝ A) (hf : Continuous f)
    (hDA : ∀ r ∈ Ioo 0 R, DifferentiableAt ℝ (deriv A) r)
    (hA0 : deriv A 0=0)
    (hEq : ∀ r ∈ Ioo 0 R, deriv (deriv A) r+11/r*deriv A r=f r) :
    EqOn A (fun r => A R-radialDirichletKernel R f r) (Icc 0 R) := by
  let K := radialDirichletKernel R f
  let U := fun r => A R-K r
  have hK : Differentiable ℝ K := fun r => (hasDerivAt_radialDirichletKernel R f hf r).differentiableAt
  have hU : Differentiable ℝ U := (differentiable_const (A R)).sub hK
  have hdK : deriv K=fun r => -r*radialAverage f r :=
    funext (fun r => (hasDerivAt_radialDirichletKernel R f hf r).deriv)
  have hDK : ∀ r ∈ Ioo 0 R, DifferentiableAt ℝ (deriv K) r := by
    intro r hr
    rw [hdK]
    exact ((hasDerivAt_id r).neg.mul (hasDerivAt_radialAverage f hf r hr.1.ne')).differentiableAt
  have hdU : deriv U=fun r => r*radialAverage f r := by
    funext r
    have h := ((hasDerivAt_radialDirichletKernel R f hf r).const_sub (A R)).deriv
    simpa only [U,K,neg_mul,neg_neg] using h
  have hDU : ∀ r ∈ Ioo 0 R, DifferentiableAt ℝ (deriv U) r := by
    intro r hr
    rw [hdU]
    exact ((hasDerivAt_id r).mul (hasDerivAt_radialAverage f hf r hr.1.ne')).differentiableAt
  have hU0 : deriv U 0=0 := by rw [hdU]; simp
  have hUR : U R=A R := by simp [U,K,radialDirichletKernel]
  have hconst : deriv (fun _ : ℝ => A R)=fun _ => 0 := by funext r; simp
  have hLU : ∀ r ∈ Ioo 0 R, radialLinearOperator 0 0 U r= -f r := by
    intro r hr
    have h := radialLinearOperator_sub (0 : ℝ → ℝ) 0 (fun _ => A R) K (differentiable_const (A R)) hK r
      (by rw [hconst]; exact differentiableAt_const 0) (hDK r hr)
    change radialLinearOperator 0 0 U r=_ at h
    rw [h]
    simp only [radialLinearOperator,hconst,deriv_const,Pi.zero_apply,sub_zero,mul_zero,
      zero_add,neg_zero]
    have hk := radialDirichletKernel_poisson R f hf r hr.1.ne'
    change -deriv (deriv K) r-11/r*deriv K r=f r at hk
    linarith
  have hLA : ∀ r ∈ Ioo 0 R, radialLinearOperator 0 0 A r= -f r := by
    intro r hr
    simp only [radialLinearOperator,Pi.zero_apply,sub_self,zero_mul,add_zero]
    linarith [hEq r hr]
  have hAU := radialLinearOperator_compare R hR hR2 (0 : ℝ → ℝ) 0 A U hA hU hDA hDU hA0 hU0
    hUR.ge (fun _ _ => by norm_num) (fun _ _ => by norm_num)
    (fun r hr => le_of_eq ((hLA r hr).trans (hLU r hr).symm))
  have hUA := radialLinearOperator_compare R hR hR2 (0 : ℝ → ℝ) 0 U A hU hA hDU hDA hU0 hA0
    hUR.le (fun _ _ => by norm_num) (fun _ _ => by norm_num)
    (fun r hr => le_of_eq ((hLU r hr).trans (hLA r hr).symm))
  intro r hr
  exact le_antisymm (hAU r hr) (hUA r hr)

theorem radial_poisson_derivative (R : ℝ) (hR : 0 < R) (hR2 : R^2 ≤ 11)
    (A f : ℝ → ℝ) (hA : Differentiable ℝ A) (hf : Continuous f)
    (hDA : ∀ r ∈ Ioo 0 R, DifferentiableAt ℝ (deriv A) r)
    (hA0 : deriv A 0=0)
    (hEq : ∀ r ∈ Ioo 0 R, deriv (deriv A) r+11/r*deriv A r=f r) :
    ∀ r ∈ Icc 0 R, deriv A r=r*radialAverage f r := by
  have he := radial_poisson_representation R hR hR2 A f hA hf hDA hA0 hEq
  intro r hr
  have hU := (hasDerivAt_radialDirichletKernel R f hf r).const_sub (A R)
  have hD := derivWithin_congr he (he hr)
  have hu : UniqueDiffWithinAt ℝ (Icc 0 R) r := uniqueDiffOn_Icc hR r hr
  rw [(hA r).derivWithin hu,hU.differentiableAt.derivWithin hu,hU.deriv] at hD
  simpa only [neg_mul,neg_neg] using hD

end DefocusingNLS

end OAI
