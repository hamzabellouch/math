import Mathlib

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma phase_derivative_lipschitz (S : E → ℂ) (hS : ContDiff ℝ ∞ S)
    {c x : E} {r C : ℝ} (hr : 0 ≤ r) (hx : x ∈ Metric.closedBall c r)
    (hC : ∀ z ∈ Metric.closedBall c r, ‖iteratedFDeriv ℝ 2 S z‖ ≤ C) :
    ‖fderiv ℝ S x-fderiv ℝ S c‖ ≤ C*‖x-c‖ := by
  apply (convex_closedBall c r).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => (hS.fderiv_right (m := ∞) (by simp)).differentiable (by simp) z)
    (fun z hz => ?_) (Metric.mem_closedBall_self hr) hx
  rw [←norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
  exact hC z hz

lemma phase_endpoint_linear_error (S : E → ℂ) (hS : ContDiff ℝ ∞ S)
    {c x y : E} {r C δ n : ℝ} (hr : 0 ≤ r) (hC0 : 0 ≤ C) (hn : 0 ≤ n)
    (hx : x ∈ Metric.closedBall c r) (hy : y ∈ Metric.closedBall c r)
    (hC : ∀ z ∈ Metric.closedBall c r, ‖iteratedFDeriv ℝ 2 S z‖ ≤ C)
    (L : E →L[ℝ] ℂ) (hL : ‖fderiv ℝ S c-L‖ ≤ δ) :
    ‖(n : ℂ)*(S y-S x)-(n : ℂ)*L (y-x)‖ ≤ n*(C*r+δ)*‖y-x‖ := by
  have hbound (z) (hz : z ∈ Metric.closedBall c r) :
      ‖fderiv ℝ (fun t => S t-L t) z‖ ≤ C*r+δ := by
    rw [fderiv_fun_sub (hS.differentiable (by simp) z) L.differentiableAt,L.fderiv]
    calc
      ‖fderiv ℝ S z-L‖ = ‖(fderiv ℝ S z-fderiv ℝ S c)+(fderiv ℝ S c-L)‖ := by congr 1; abel
      _ ≤ ‖fderiv ℝ S z-fderiv ℝ S c‖+‖fderiv ℝ S c-L‖ := norm_add_le _ _
      _ ≤ C*‖z-c‖+δ := add_le_add (phase_derivative_lipschitz S hS hr hz hC) hL
      _ ≤ C*r+δ := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left (by simpa only [Metric.mem_closedBall,dist_eq_norm] using hz) hC0
        · exact le_rfl
  have hh := (convex_closedBall c r).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => (hS.sub L.contDiff).differentiable (by simp) z) hbound hx hy
  have heq : (S y-L y)-(S x-L x) = S y-S x-L (y-x) := by rw [map_sub]; ring
  rw [heq] at hh
  rw [←mul_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hn]
  exact (mul_le_mul_of_nonneg_left hh hn).trans_eq (by ring)

end YauCounterexamples
end

end OAI
