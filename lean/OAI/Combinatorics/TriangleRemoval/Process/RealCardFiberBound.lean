import Mathlib

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

section FiberCount
variable {α β : Type*} [DecidableEq α] [DecidableEq β]

omit [DecidableEq α] in
lemma real_card_le_fiber_bound (s : Finset α) (t : Finset β) (f : α → β)
    (hf : ∀ a ∈ s, f a ∈ t) (b : ℝ)
    (hb : ∀ y ∈ t, ((s.filter (fun a => f a = y)).card : ℝ) ≤ b) :
    (s.card : ℝ) ≤ b * t.card := by
  have he : s.card = ∑ y ∈ t, (s.filter (fun a => f a = y)).card :=
    Finset.card_eq_sum_card_fiberwise hf
  rw [he,Nat.cast_sum]
  calc
    _ ≤ ∑ _y ∈ t, b := Finset.sum_le_sum hb
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring

end FiberCount
end SharpTerminalLeave

end

end OAI
