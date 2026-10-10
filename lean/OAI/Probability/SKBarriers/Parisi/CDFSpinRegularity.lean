import Mathlib
import OAI.Probability.SKBarriers.Scalar.DyadicCDFStability
import OAI.Probability.SKBarriers.Gaussian.BoundedPrimitive

namespace OAI

section

noncomputable section
open scoped Topology NNReal
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarCDFValue_lipschitz (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ s, α s ∈ Icc (0:ℝ) 1) (hmono : Monotone α)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) : LipschitzWith 1 (scalarCDFValue β α s t) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun x => (scalarCDFValue_hasDerivAt β hα hmono s t ht x).differentiableAt)
  intro x
  rw [(scalarCDFValue_hasDerivAt β hα hmono s t ht x).deriv]
  exact_mod_cast (scalarCDF_derivative_bounds β hα hmono s t ht x).1

theorem scalarCDFHessian_abs_le_one (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ s, α s ∈ Icc (0:ℝ) 1) (hmono : Monotone α)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (x : ℝ) :
    |scalarCDFHessian β α s t x| ≤ 1 := by
  have H := scalarCDF_derivative_bounds β hα hmono s t ht x
  rw [abs_of_nonneg H.2.1]
  linarith [H.2.2,sq_nonneg (scalarCDFGradient β α s t x)]

theorem scalarCDFGradient_lipschitz (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ s, α s ∈ Icc (0:ℝ) 1) (hmono : Monotone α)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) : LipschitzWith 1 (scalarCDFGradient β α s t) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun x => (scalarCDFGradient_hasDerivAt β hα hmono s t ht x).differentiableAt)
  intro x
  rw [(scalarCDFGradient_hasDerivAt β hα hmono s t ht x).deriv]
  exact_mod_cast scalarCDFHessian_abs_le_one β hα hmono s t ht x

theorem scalarCDFValue_regular (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ s, α s ∈ Icc (0:ℝ) 1) (hmono : Monotone α)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) : BoundedDerivs (scalarCDFValue β α s t) :=
  boundedDerivs_of_derivatives (scalarCDFValue_hasDerivAt β hα hmono s t ht)
    (scalarCDFGradient_hasDerivAt β hα hmono s t ht)
    (scalarCDFHessian_lipschitz β hα hmono s t ht).continuous
    (B:=1) (C:=1) (fun x => (scalarCDF_derivative_bounds β hα hmono s t ht x).1)
    (scalarCDFHessian_abs_le_one β hα hmono s t ht)

theorem scalarCDFGradient_cdf_stability (β : ℝ) {α γ : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0:ℝ) 1) (hαm : Monotone α)
    (hγ : ∀ z, γ z ∈ Icc (0:ℝ) 1) (hγm : Monotone γ)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (x h : ℝ) (hh : 0<h) :
    |scalarCDFGradient β α s t x-scalarCDFGradient β γ s t x| ≤
      2*(scalarTimeMassConstant β*(∫ z in s..s+t, |α z-γ z|))/h+2*h := by
  have H := derivative_bound_of_uniform_value_and_lipschitz _ _ (1+1) _
    (fun z => (scalarCDFValue_hasDerivAt β hα hαm s t ht z).sub
      (scalarCDFValue_hasDerivAt β hγ hγm s t ht z))
    ((scalarCDFGradient_lipschitz β hα hαm s t ht).sub
       (scalarCDFGradient_lipschitz β hγ hγm s t ht))
    (scalarCDFValue_cdf_lipschitz β hα hαm hγ hγm s t ht) x h hh
  norm_num only [NNReal.coe_add,NNReal.coe_one,one_add_one_eq_two] at H
  exact H

theorem scalarCDFHessian_cdf_stability (β : ℝ) {α γ : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0:ℝ) 1) (hαm : Monotone α)
    (hγ : ∀ z, γ z ∈ Icc (0:ℝ) 1) (hγm : Monotone γ)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (x h k : ℝ) (hh : 0<h) (hk : 0<k) :
    |scalarCDFHessian β α s t x-scalarCDFHessian β γ s t x| ≤
      2*(2*(scalarTimeMassConstant β*(∫ z in s..s+t, |α z-γ z|))/h+2*h)/k+
        2*(susceptibilityLipschitzConstant:ℝ)*k := by
  have H := derivative_bound_of_uniform_value_and_lipschitz _ _
    (susceptibilityLipschitzConstant+susceptibilityLipschitzConstant) _
    (fun z => (scalarCDFGradient_hasDerivAt β hα hαm s t ht z).sub
      (scalarCDFGradient_hasDerivAt β hγ hγm s t ht z))
    ((scalarCDFHessian_lipschitz β hα hαm s t ht).sub
       (scalarCDFHessian_lipschitz β hγ hγm s t ht))
    (fun z => scalarCDFGradient_cdf_stability β hα hαm hγ hγm s t ht z h hh) x k hk
  simpa only [NNReal.coe_add,two_mul] using H

theorem scalarCDFGradient_sq_regular (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ s, α s ∈ Icc (0:ℝ) 1) (hmono : Monotone α)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) :
    (∀ x, HasDerivAt (fun y => (scalarCDFGradient β α s t y)^2)
      (2*scalarCDFGradient β α s t x*scalarCDFHessian β α s t x) x) ∧
    Continuous (fun x => 2*scalarCDFGradient β α s t x*scalarCDFHessian β α s t x) ∧
    (∀ x, |(scalarCDFGradient β α s t x)^2| ≤ (1:ℝ)) ∧
    (∀ x, |2*scalarCDFGradient β α s t x*scalarCDFHessian β α s t x| ≤ (2:ℝ)) := by
  refine ⟨?_,continuous_const.mul (scalarCDFGradient_lipschitz β hα hmono s t ht).continuous |>.mul
    (scalarCDFHessian_lipschitz β hα hmono s t ht).continuous,?_,?_⟩
  · intro x
    convert (scalarCDFGradient_hasDerivAt β hα hmono s t ht x).pow 2 using 1
    norm_num
  · intro x
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (scalarCDF_derivative_bounds β hα hmono s t ht x).1
  · intro x
    calc
      _ = 2*|scalarCDFGradient β α s t x| * |scalarCDFHessian β α s t x| := by simp only [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
      _ ≤ 2*1*1 := mul_le_mul (mul_le_mul_of_nonneg_left
        (scalarCDF_derivative_bounds β hα hmono s t ht x).1 (by norm_num))
        (scalarCDFHessian_abs_le_one β hα hmono s t ht x) (abs_nonneg _) (by norm_num)
      _ = 2 := by norm_num

end SK.Analytic

end
end

end OAI
