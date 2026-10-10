import Mathlib
import OAI.Probability.SKBarriers.Gaussian.BoundedObservableCurvature

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem quadratic_bound_of_secondDeriv_le {f g h : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (g x) x) (hg : ∀ x, HasDerivAt g (h x) x)
    (hh : ∀ x, h x ≤ 1) (L : ℝ) : f L ≤ f 0+L*g 0+L^2/2 := by
  let F : ℝ → ℝ := fun x => f x-x^2/2
  have hF (x : ℝ) : HasDerivAt F (g x-x) x := by
    convert (hf x).sub (((hasDerivAt_id x).pow 2).div_const 2) using 1 <;>
      first | rfl | (simp only [id_eq]; ring)
  have hG (x : ℝ) : HasDerivAt (fun x => g x-x) (h x-1) x := (hg x).sub (hasDerivAt_id x)
  have hD : deriv F=fun x => g x-x := funext (fun x => (hF x).deriv)
  have hconc : ConcaveOn ℝ univ F := concaveOn_univ_of_deriv2_nonpos
    (fun x => (hF x).differentiableAt)
    (by rw [hD]; exact fun x => (hG x).differentiableAt)
    (fun x => by simpa only [Function.iterate_succ_apply,Function.iterate_zero_apply,hD,(hG x).deriv] using sub_nonpos.mpr (hh x))
  rcases lt_trichotomy 0 L with hL|hL|hL
  · have H := hconc.slope_le_of_hasDerivAt (mem_univ _) (mem_univ _) hL (hF 0)
    rw [slope_def_field,sub_zero,sub_zero,div_le_iff₀ hL] at H
    dsimp only [F] at H
    nlinarith
  · subst L
    simp
  · have H := hconc.le_slope_of_hasDerivAt (mem_univ _) (mem_univ _) hL (hF 0)
    rw [slope_def_field,sub_zero,le_div_iff₀ (sub_pos.mpr hL)] at H
    dsimp only [F] at H
    nlinarith

attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem rootBoundedCurvature_quadratic {f : ℝ → ℝ} (hf : BoundedDerivs f)
    (h : RootBoundedCurvature 0 f) (L : ℝ) :
    f L ≤ f 0+L*rootGradient 0 f 0+L^2/2 := by
  have hd (x : ℝ) : HasDerivAt f (rootGradient 0 f x) x := by
    simpa only [parameterAxis,smul_eq_mul,mul_one,zero_add] using rootLine_hasDerivAt 0 hf 0 x
  have hdd (x : ℝ) : HasDerivAt (rootGradient 0 f) (rootHessian 0 f x) x := by
    simpa only [parameterAxis,smul_eq_mul,mul_one,zero_add] using rootGradientLine_hasDerivAt 0 hf 0 x
  exact quadratic_bound_of_secondDeriv_le hd hdd
    (fun x => (h x).2.trans (sub_le_self _ (sq_nonneg _))) L

theorem hierarchy_bounded_observable_quadratic {S : Type} [Fintype S] [Nonempty S]
    (n : ℕ) (m : Fin n → ℝ) (hm : ∀ i, m i ∈ Icc (0:ℝ) 1)
    (c : S → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ)
    (hU : ∀ s, |U s (parameterAxis n)| ≤ 1) (L : ℝ) :
    hierarchyPressure n m (affineLogPartition c U) L ≤
      hierarchyPressure n m (affineLogPartition c U) 0+
      L*rootGradient 0 (hierarchyPressure n m (affineLogPartition c U)) 0+L^2/2 :=
  rootBoundedCurvature_quadratic
    (hierarchyPressure_boundedDerivs n m _ (affineLogPartition_boundedDerivs c U))
    (hierarchy_bounded_observable_curvature n m hm c U hU) L

end SK.Analytic

end
end

end OAI
