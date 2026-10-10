import Mathlib
import OAI.Probability.SKBarriers.Calculus.CubeMeasures

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

theorem hessian_tangent_lower
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : E → ℝ) (hV : ContDiff ℝ 2 V) (x u : E) {C : ℝ}
    (hH : ∀ t : ℝ, C ≤ Hessian V (x+t • u) u u) :
    V x + fderiv ℝ V x u + C/2 ≤ V (x+u) := by
  let f : ℝ → ℝ := fun t => V (x+t • u) - C/2*t^2
  let f₁ : ℝ → ℝ := fun t => fderiv ℝ V (x+t • u) u - C*t
  have hd (t : ℝ) : HasDerivAt f (f₁ t) t := by
    have hq : HasDerivAt (fun s : ℝ => C/2*s^2) (C*t) t := by
      convert! (((hasDerivAt_id t).pow 2).const_mul (C/2)) using 1
      dsimp
      ring
    exact (hasDerivAt_affine_comp V (hV.differentiable (by norm_num)) x u t).sub hq
  have hd₁ (t : ℝ) : HasDerivAt f₁ (Hessian V (x+t • u) u u-C) t := by
    convert! (hasDerivAt_affine_score V hV x u u t).sub ((hasDerivAt_id t).const_mul C) using 1
    ring
  have he : deriv f = f₁ := funext (fun t => (hd t).deriv)
  have hconv : ConvexOn ℝ univ f := convexOn_univ_of_deriv2_nonneg
    (fun t => (hd t).differentiableAt)
    (by rw [he]; exact fun t => (hd₁ t).differentiableAt)
    (by intro t; change 0 ≤ deriv (deriv f) t; rw [he, (hd₁ t).deriv]; exact sub_nonneg.mpr (hH t))
  have hs := hconv.le_slope_of_hasDerivAt (mem_univ (0 : ℝ)) (mem_univ (1 : ℝ))
      (by norm_num : (0 : ℝ) < 1) (hd 0)
  dsimp [slope, f, f₁] at hs
  simp only [zero_smul, add_zero, one_smul, zero_pow (by omega : 2 ≠ 0),
    one_pow, mul_zero, mul_one, sub_zero, inv_one, one_mul] at hs
  linarith

theorem integrable_coordinateGaussian (n : ℕ) (x : ℝ) {c : ℝ} (hc : 0 < c) :
    Integrable (fun z => Real.exp (-c*coordinateSquare n z)) (fiberMeasure n x) := by
  induction n with
  | zero => simp [coordinateSquare, fiberMeasure]
  | succ n ih =>
    have hi := ih.mul_prod (integrable_exp_neg_mul_sq hc)
    convert! hi using 1
    funext z
    change Real.exp (-c*(coordinateSquare n z.1+z.2^2)) =
      Real.exp (-c*coordinateSquare n z.1)*Real.exp (-c*z.2^2)
    rw [mul_add, Real.exp_add]

theorem integrable_coordinateSquare_gaussian (n : ℕ) (x : ℝ) {c : ℝ} (hc : 0 < c) :
    Integrable (fun z => coordinateSquare n z * Real.exp (-c*coordinateSquare n z))
      (fiberMeasure n x) := by
  induction n with
  | zero => simp [coordinateSquare]
  | succ n ih =>
    have hi₀ := integrable_coordinateGaussian n x hc
    have hi₁ := integrable_exp_neg_mul_sq hc
    have hi₂ : Integrable (fun y : ℝ => y^2*Real.exp (-c*y^2)) := by
      simpa only [Real.rpow_natCast] using
        (integrable_rpow_mul_exp_neg_mul_sq hc (s := (2 : ℕ)) (by norm_num))
    have hi := (ih.mul_prod hi₁).add (hi₀.mul_prod hi₂)
    convert! hi using 1
    funext z
    change (coordinateSquare n z.1+z.2^2)*Real.exp (-c*(coordinateSquare n z.1+z.2^2)) = _
    rw [mul_add, Real.exp_add]
    dsimp only [Pi.add_apply]
    ring

end SK.Analytic

end
end
end
end
end

end OAI
