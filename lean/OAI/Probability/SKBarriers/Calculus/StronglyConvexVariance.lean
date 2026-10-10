import Mathlib
import OAI.Probability.SKBarriers.Calculus.CubeMoments
import OAI.Probability.SKBarriers.Calculus.CoordinateBounds

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
namespace SK.Analytic

theorem stronglyConvex_linear_variance_le (n : ℕ) (V : ParameterSpace n → ℝ)
    (hV : ContDiff ℝ 2 V) (hV₀ : ∀ z, parameterDerivative n V z = 0)
    (L : ParameterSpace n →L[ℝ] ℝ) (hL₀ : L (parameterAxis n) = 0)
    {c A : ℝ} (hc : 0 < c) (hA : 0 ≤ A)
    (hL : ∀ u, (L u)^2 ≤ A*coordinateSquare n u)
    (hH : ∀ z u, c*coordinateSquare n u ≤ Hessian V z u u) :
    let Z := ∫ z, Real.exp (-V z) ∂fiberMeasure n 0
    (∫ z, (L z)^2*Real.exp (-V z) ∂fiberMeasure n 0)/Z -
      ((∫ z, L z*Real.exp (-V z) ∂fiberMeasure n 0)/Z)^2 ≤ A/c := by
  obtain ⟨hI₀,hIq⟩ := integrable_stronglyConvex_density n V hV hc hH
  have hI₂ : Integrable (fun z => (L z)^2*Real.exp (-V z)) (fiberMeasure n 0) := by
    apply (hIq.const_mul A).mono' ((L.continuous.pow 2).mul hV.neg.exp.continuous).aestronglyMeasurable
    filter_upwards [] with z
    change ‖(L z)^2*Real.exp (-V z)‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)]
    exact (mul_le_mul_of_nonneg_right (hL z) (Real.exp_pos _).le).trans_eq (mul_assoc _ _ _)
  have hI₁ : Integrable (fun z => L z*Real.exp (-V z)) (fiberMeasure n 0) := by
    apply (hI₀.add hI₂).mono' (L.continuous.mul hV.neg.exp.continuous).aestronglyMeasurable
    filter_upwards [] with z
    change ‖L z*Real.exp (-V z)‖ ≤ Real.exp (-V z)+(L z)^2*Real.exp (-V z)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hle : |L z| ≤ 1+(L z)^2 := by nlinarith [sq_nonneg (|L z|-1), sq_abs (L z)]
    nlinarith [mul_le_mul_of_nonneg_right hle (Real.exp_pos (-V z)).le]
  exact linear_variance_le n V hV hV₀ L hL₀ hc hA hL hH hI₀ hI₁ hI₂

section HessianComposition
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem hessian_comp_linear (V : F → ℝ) (hV : ContDiff ℝ 2 V) (T : E →L[ℝ] F)
    (x u v : E) : Hessian (fun z => V (T z)) x u v = Hessian V (T x) (T u) (T v) := by
  have hD : fderiv ℝ (fun z => V (T z)) = fun z => (fderiv ℝ V (T z)).comp T := by
    funext z
    exact ((hV.differentiable (by norm_num) (T z)).hasFDerivAt.comp z T.hasFDerivAt).fderiv
  have hdV := (hV.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hd := ((hdV (T x)).hasFDerivAt.comp x T.hasFDerivAt).clm_comp (hasFDerivAt_const T x)
  simp only [Function.comp_def] at hd
  rw [Hessian, hD, hd.fderiv]
  simp [Hessian]

theorem hessian_linear (L : E →L[ℝ] ℝ) (x u v : E) : Hessian L x u v = 0 := by
  have hD : fderiv ℝ (fun z => L z) = fun _ => L := funext (fun _ => L.hasFDerivAt.fderiv)
  change Hessian (fun z => L z) x u v = 0
  simp [Hessian, hD]

end HessianComposition

theorem contDiff_coordinateSquare (n : ℕ) : ContDiff ℝ 2 (coordinateSquare n) := by
  induction n with
  | zero => exact contDiff_const
  | succ n ih => exact (ih.comp contDiff_fst).add (contDiff_snd.pow 2)

theorem hessian_coordinateSquare (n : ℕ) (x u : ParameterSpace n) :
    Hessian (coordinateSquare n) x u u = 2*coordinateSquare n u := by
  induction n with
  | zero => simp [coordinateSquare, Hessian]
  | succ n ih =>
    let fst := ContinuousLinearMap.fst ℝ (ParameterSpace n) ℝ
    let snd := ContinuousLinearMap.snd ℝ (ParameterSpace n) ℝ
    change Hessian (fun z => coordinateSquare n (fst z)+(snd z)^2) x u u = _
    have hf : ContDiff ℝ 2 (fun z => coordinateSquare n (fst z)) := (contDiff_coordinateSquare n).comp fst.contDiff
    rw [hessian_add hf (snd.contDiff.pow 2),
      hessian_comp_linear _ (contDiff_coordinateSquare n) fst]
    have hsq : (fun z => (snd z)^2) = fun z => snd z*snd z := by funext z; ring
    rw [hsq, hessian_linear_product, ih]
    change 2*coordinateSquare n u.1 + (u.2*u.2+u.2*u.2) = 2*(coordinateSquare n u.1+u.2^2)
    ring

end SK.Analytic

end
end
end
end
end

end OAI
