import Mathlib
import OAI.Probability.SKBarriers.Calculus.StronglyConvexVariance

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

theorem hessian_nonneg_of_convex
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : E → ℝ) (hV : ContDiff ℝ 2 V) (hc : ConvexOn ℝ univ V) (x u : E) :
    0 ≤ Hessian V x u u := by
  let f : ℝ → ℝ := fun t => V (x+t • u)
  have hfc : ConvexOn ℝ univ f := by
    refine ⟨convex_univ, ?_⟩
    intro a _ b _ s t hs ht hst
    have h := hc.2 (mem_univ (x+a • u)) (mem_univ (x+b • u)) hs ht hst
    have he : s • (x+a • u)+t • (x+b • u) = x+(s*a+t*b) • u := by
      simp only [smul_add, smul_smul]
      rw [add_add_add_comm, ← add_smul, ← add_smul, hst, one_smul]
    simpa only [he, f, smul_eq_mul] using h
  have hdf (t : ℝ) := hasDerivAt_affine_comp V (hV.differentiable (by norm_num)) x u t
  have hd : deriv f = fun t => fderiv ℝ V (x+t • u) u := funext (fun t => (hdf t).deriv)
  have hm : Monotone (deriv f) := fun a b hab =>
    hfc.monotoneOn_deriv (fun t _ => (hdf t).differentiableAt) (mem_univ a) (mem_univ b) hab
  have hh := hm.deriv_nonneg (x := 0)
  rw [hd, (hasDerivAt_affine_score V hV x u u 0).deriv] at hh
  simpa only [zero_smul, add_zero] using hh

theorem coordinateSquare_add_parameterAxis (n : ℕ) (z : ParameterSpace n) (t : ℝ) :
    coordinateSquare n (z+t • parameterAxis n) = coordinateSquare n z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change coordinateSquare n (z.1+t • parameterAxis n)+(z.2+t*(0:ℝ))^2 =
      coordinateSquare n z.1+z.2^2
    rw [ih, mul_zero, add_zero]

theorem parameterDerivative_coordinateSquare (n : ℕ) (z : ParameterSpace n) :
    parameterDerivative n (coordinateSquare n) z = 0 := by
  have hh := hasDerivAt_affine_comp (coordinateSquare n)
    ((contDiff_coordinateSquare n).differentiable (by norm_num)) z (parameterAxis n) 0
  have he : (fun t : ℝ => coordinateSquare n (z+t • parameterAxis n)) =
      fun _ => coordinateSquare n z := funext (coordinateSquare_add_parameterAxis n z)
  rw [he, zero_smul, add_zero] at hh
  exact hh.unique (hasDerivAt_const 0 (coordinateSquare n z))

theorem gaussian_convex_tilt_linear_variance (n : ℕ) (G : ParameterSpace n → ℝ)
    (hG : ContDiff ℝ 2 G) (hGc : ConvexOn ℝ univ G)
    (hG₀ : ∀ z, parameterDerivative n G z = 0)
    (U L : ParameterSpace n →L[ℝ] ℝ)
    (hU₀ : U (parameterAxis n) = 0) (hL₀ : L (parameterAxis n) = 0)
    {A : ℝ} (hA : 0 ≤ A) (hL : ∀ u, (L u)^2 ≤ A*coordinateSquare n u) :
    let V := fun z => (1/2 : ℝ)*coordinateSquare n z-U z+G z
    let Z := ∫ z, Real.exp (-V z) ∂fiberMeasure n 0
    (∫ z, (L z)^2*Real.exp (-V z) ∂fiberMeasure n 0)/Z -
      ((∫ z, L z*Real.exp (-V z) ∂fiberMeasure n 0)/Z)^2 ≤ A := by
  let V := fun z => (1/2 : ℝ)*coordinateSquare n z-U z+G z
  have hq := contDiff_coordinateSquare n
  have hV : ContDiff ℝ 2 V := ((contDiff_const.mul hq).sub U.contDiff).add hG
  have hV₀ : ∀ z, parameterDerivative n V z = 0 := by
    intro z
    have hd : HasFDerivAt V ((1/2 : ℝ) • fderiv ℝ (coordinateSquare n) z - U + fderiv ℝ G z) z :=
      (((hq.differentiable (by norm_num) z).hasFDerivAt.const_mul (1/2 : ℝ)).sub
        U.hasFDerivAt).add (hG.differentiable (by norm_num) z).hasFDerivAt
    change fderiv ℝ V z (parameterAxis n) = 0
    rw [hd.fderiv]
    change (1/2 : ℝ)*parameterDerivative n (coordinateSquare n) z - U (parameterAxis n) +
      parameterDerivative n G z = 0
    rw [parameterDerivative_coordinateSquare, hU₀, hG₀]
    ring
  have hH : ∀ z u, (1:ℝ)*coordinateSquare n u ≤ Hessian V z u u := by
    intro z u
    have he : V = fun z => ((1/2 : ℝ)*coordinateSquare n z + (-1)*U z)+G z := by
      funext z; dsimp only [V]; ring
    rw [he, hessian_add ((contDiff_const.mul hq).add (contDiff_const.mul U.contDiff)) hG,
      hessian_add (contDiff_const.mul hq) (contDiff_const.mul U.contDiff),
      hessian_const_mul hq, hessian_const_mul U.contDiff, hessian_linear,
      hessian_coordinateSquare]
    nlinarith [hessian_nonneg_of_convex G hG hGc z u]
  simpa only [div_one] using stronglyConvex_linear_variance_le n V hV hV₀ L hL₀
    (by norm_num : (0:ℝ)<1) hA hL hH

end SK.Analytic

noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology

end
end
end
end
end
end

end OAI
