import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.Calculus

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma convexOn_of_quadratic_lower_supports {f : E → ℝ} {S : Set E}
    (hS : Convex ℝ S) (B : ℝ)
    (hs : ∀ x∈S, ∃ L : E →L[ℝ] ℝ, ∀ y∈S,
      f x+L (y-x)-B*‖y-x‖^2≤f y) :
    ConvexOn ℝ S (fun x => f x+B*‖x‖^2) := by
  apply convexOn_of_affine_lower_supports hS
  intro x hx
  obtain ⟨L,hL⟩ := hs x hx
  refine ⟨L+(2*B) • innerSL ℝ x,?_⟩
  intro y hy
  have H := hL y hy
  simp only [_root_.add_apply,_root_.smul_apply,innerSL_apply_apply,inner_sub_right,
    smul_eq_mul,real_inner_self_eq_norm_sq]
  rw [norm_sub_sq_real] at H
  have hi : inner ℝ y x=inner ℝ x y := real_inner_comm _ _
  rw [hi] at H
  nlinarith

end WeakMTWTransport

end

end OAI
