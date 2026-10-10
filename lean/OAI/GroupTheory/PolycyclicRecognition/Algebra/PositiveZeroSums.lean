import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

namespace OAI

/-! # The finite positive-sum obstruction to a character hemisphere

Carathéodory reduces the obstruction to at most dimension plus one characters.
This is the precise convex step needed after a homological tameness estimate.
-/

noncomputable section
namespace PolycyclicRecognition
variable {E : Type} [AddCommGroup E] [Module ℝ E]

theorem zero_not_mem_convexHull_of_no_positive_sum (C : Set E)
    (h : ∀ (ι : Type) [Fintype ι] (z : ι → E) (w : ι → ℝ),
      (∀ i, z i ∈ C) → (∀ i, 0 < w i) → (∑ i, w i) = 1 →
      (∑ i, w i • z i) ≠ 0) :
    (0 : E) ∉ convexHull ℝ C := by
  intro hc
  obtain ⟨ι, hi, z, w, hz, _, hw, hsum, hzero⟩ := eq_pos_convex_span_of_mem_convexHull hc
  let := hi
  exact h ι z w (fun i => hz (Set.mem_range_self i)) hw hsum hzero

theorem zero_not_mem_convexHull_of_no_small_positive_sum [FiniteDimensional ℝ E]
    (C : Set E)
    (h : ∀ (ι : Type) [Fintype ι] (z : ι → E) (w : ι → ℝ),
      Fintype.card ι ≤ Module.finrank ℝ E + 1 →
      (∀ i, z i ∈ C) → (∀ i, 0 < w i) → (∑ i, w i) = 1 →
      (∑ i, w i • z i) ≠ 0) :
    (0 : E) ∉ convexHull ℝ C := by
  intro hc
  obtain ⟨ι, hi, z, w, hz, haff, hw, hsum, hzero⟩ := eq_pos_convex_span_of_mem_convexHull hc
  let := hi
  have hcard : Fintype.card ι ≤ Module.finrank ℝ E + 1 :=
    haff.card_le_finrank_succ.trans (Nat.add_le_add_right (Submodule.finrank_le _) 1)
  exact h ι z w hcard (fun i => hz (Set.mem_range_self i)) hw hsum hzero

end PolycyclicRecognition

end

end OAI
