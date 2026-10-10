import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace OAI

namespace RyserCoveringCounterexample.Construction

open scoped BigOperators

theorem card_le_sum_capacity
    {ι V : Type*} (E : Finset ι) (C : Finset V)
    (R : V → ι → Prop) [∀ v, DecidablePred (R v)]
    (capacity : V → ℕ)
    (hcover : ∀ e ∈ E, ∃ v ∈ C, R v e)
    (hcapacity : ∀ v ∈ C, (E.filter (R v)).card ≤ capacity v) :
    E.card ≤ ∑ v ∈ C, capacity v := by
  classical
  calc
    E.card ≤ (C.biUnion fun v => E.filter (R v)).card := by
      apply Finset.card_le_card
      intro e he
      obtain ⟨v, hv, hve⟩ := hcover e he
      exact Finset.mem_biUnion.mpr
        ⟨v, hv, Finset.mem_filter.mpr ⟨he, hve⟩⟩
    _ ≤ ∑ v ∈ C, (E.filter (R v)).card := Finset.card_biUnion_le
    _ ≤ ∑ v ∈ C, capacity v := Finset.sum_le_sum hcapacity

theorem card_le_mul_resource_card
    {ι V : Type*} (E : Finset ι) (C : Finset V)
    (R : V → ι → Prop) [∀ v, DecidablePred (R v)]
    (b : ℕ)
    (hcover : ∀ e ∈ E, ∃ v ∈ C, R v e)
    (hcapacity : ∀ v ∈ C, (E.filter (R v)).card ≤ b) :
    E.card ≤ b * C.card := by
  calc
    E.card ≤ ∑ _v ∈ C, b :=
      card_le_sum_capacity E C R (fun _ => b) hcover hcapacity
    _ = C.card * b :=
      Finset.sum_const_nat (s := C) (m := b) (f := fun _ : V => b)
        (fun _ _ => rfl)
    _ = b * C.card := Nat.mul_comm _ _

end RyserCoveringCounterexample.Construction

end OAI
