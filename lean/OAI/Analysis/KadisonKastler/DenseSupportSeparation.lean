import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Topology.Sequences

namespace OAI

/-! # Dense support tests for a bounded closed convex set

A dense family of Hilbert-space support tests suffices when the candidate
set is uniformly bounded. This is used for self-adjoint operator balls.
-/

namespace KadisonKastler

open Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The uniform bound lets dense tests recover every separating functional. -/
theorem mem_closed_convex_of_dense_support {C D : Set E} {y : E} {B : ℝ}
    (hC : IsClosed C) (hconv : Convex ℝ C) (hD : Dense D)
    (hB : ∀ x ∈ C, ‖x‖ ≤ B)
    (htest : ∀ h ∈ D, ∃ x ∈ C, inner ℝ h y ≤ inner ℝ h x) : y ∈ C := by
  classical
  by_contra hy
  obtain ⟨f, u, hfu, huy⟩ := geometric_hahn_banach_closed_point hconv hC hy
  let h := (InnerProductSpace.toDual ℝ E).symm f
  have hf (v : E) : f v = inner ℝ h v :=
    (InnerProductSpace.toDual_symm_apply (x := v) (y := f)).symm
  obtain ⟨v, hvD, hv⟩ := mem_closure_iff_seq_limit.mp (hD h)
  have hb (n : ℕ) : inner ℝ (v n) y ≤ u + ‖v n - h‖ * B := by
    obtain ⟨x, hx, hxy⟩ := htest (v n) (hvD n)
    have hi := real_inner_le_norm (v n - h) x
    have hm := mul_le_mul_of_nonneg_left (hB x hx) (norm_nonneg (v n - h))
    have hu := (hfu x hx).le
    rw [hf] at hu
    rw [inner_sub_left] at hi
    linarith
  have hl : Tendsto (fun n => inner ℝ (v n) y) atTop (𝓝 (f y)) := by
    rw [hf]
    exact hv.inner tendsto_const_nhds
  have hr : Tendsto (fun n => u + ‖v n - h‖ * B) atTop (𝓝 u) := by
    have hd : Tendsto (fun n => ‖v n - h‖) atTop (𝓝 0) := by
      simpa using (hv.sub (tendsto_const_nhds (x := h))).norm
    simpa using tendsto_const_nhds.add (hd.mul_const B)
  exact huy.not_ge (le_of_tendsto_of_tendsto hl hr (Eventually.of_forall hb))

end KadisonKastler

end OAI
