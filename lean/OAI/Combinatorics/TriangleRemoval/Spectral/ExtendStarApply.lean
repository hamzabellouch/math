import Mathlib
import OAI.Combinatorics.TriangleRemoval.Spectral.StarInclusion

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators NNReal
open Matrix InnerProductSpace
open scoped BigOperators
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix

namespace SharpTerminalLeave

variable {E : Type*} [Fintype E] [DecidableEq E]

omit [Fintype E] in

theorem extendStar_apply (S : Finset E) (M : Matrix S S ℝ) (i j : E) :
    extendStar S M i j = if hi : i ∈ S then if hj : j ∈ S then
      M ⟨i,hi⟩ ⟨j,hj⟩ else 0 else 0 := by
  simp only [extendStar,Matrix.mul_apply,Matrix.conjTranspose_apply,starInclusion,
    star_trivial]
  by_cases hi : i ∈ S
  · by_cases hj : j ∈ S
    · have hei : ∀ x : S, i = x.val ↔ x = ⟨i,hi⟩ := fun x => by
        rw [Subtype.ext_iff]
        exact eq_comm
      have hej : ∀ x : S, j = x.val ↔ x = ⟨j,hj⟩ := fun x => by
        rw [Subtype.ext_iff]
        exact eq_comm
      simp [hi,hj,hei,hej]
    · have hej : ∀ x : S, j ≠ x.val := fun x hx => hj (hx.symm ▸ x.property)
      simp [hi,hj,hej]
  · have hei : ∀ x : S, i ≠ x.val := fun x hx => hi (hx.symm ▸ x.property)
    simp [hi,hei]

end SharpTerminalLeave

open scoped BigOperators Topology NNReal Matrix.Norms.Operator
open MeasureTheory

end
end

end OAI
