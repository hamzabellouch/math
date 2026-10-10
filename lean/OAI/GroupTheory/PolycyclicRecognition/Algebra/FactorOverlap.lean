import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Tactic.Group

namespace OAI

/-! # Comparing nonunique factor lifts

The error between two lifts is an actual element of the overlap of the
two factor images. No centrality or discreteness of the overlap is used.
-/

namespace PolycyclicRecognition

theorem factor_overlap_difference
    {N D G : Type*} [Group N] [Group D] [Group G]
    (φ : D →* MulAut N) (ι : N →* G) (κ : D →* G)
    (hc : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
    (u v a : N) (d e b : D)
    (he : ι v * κ e = (ι u * κ d) * (ι a * κ b)) :
    ∃ z : N, ι z = κ (d * b * e⁻¹) ∧ u⁻¹ * v = φ d a * z := by
  let z := (φ d a)⁻¹ * (u⁻¹ * v)
  refine ⟨z, ?_, by simp [z]⟩
  have ht : ι v * κ e = (ι u * ι (φ d a)) * κ (d * b) := by
    rw [he, hc, map_mul]
    group
  have hh := congrArg (fun w : G => (ι u * ι (φ d a))⁻¹ * w * (κ e)⁻¹) ht
  simpa [z, map_mul, map_inv, mul_assoc] using hh

end PolycyclicRecognition

end OAI
