import Mathlib

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv
attribute [local instance] Classical.propDecidable
variable {D : Type*}

/-- Restricting an equivalence relation to an invariant part and its complement
partitions its actual quotient, not merely its representatives. -/
theorem card_quotient_split [Finite D] (s : Setoid D) (P : D → Prop)
    (hP : ∀ {x y}, s x y → (P x ↔ P y)) :
    Nat.card (Quotient s) =
      Nat.card (Quotient (s.comap (Subtype.val : Subtype P → D))) +
      Nat.card (Quotient (s.comap (Subtype.val : {x : D // ¬ P x} → D))) := by
  classical
  let qP : Quotient s → Prop := Quotient.lift P (fun _ _ h => propext (hP h))
  let e₁ := Equiv.subtypeQuotientEquivQuotientSubtype P (s₁ := s)
    (s₂ := s.comap Subtype.val) qP (fun _ => Iff.rfl) (fun _ _ => Iff.rfl)
  let e₂ := Equiv.subtypeQuotientEquivQuotientSubtype (fun x => ¬ P x) (s₁ := s)
    (s₂ := s.comap Subtype.val) (fun q => ¬ qP q) (fun _ => Iff.rfl) (fun _ _ => Iff.rfl)
  have hc := Nat.card_congr (Equiv.Set.sumCompl {q : Quotient s | qP q})
  rw [Nat.card_sum] at hc
  rw [← Nat.card_congr e₁,← Nat.card_congr e₂]
  exact hc.symm

/-- For invariant subsets, taking the join of equivalence relations commutes
with restriction. The invariant hypothesis is essential. -/
theorem comap_sup_of_invariant (r s : Setoid D) (P : D → Prop)
    (hr : ∀ {x y}, r x y → (P x ↔ P y))
    (hs : ∀ {x y}, s x y → (P x ↔ P y)) :
    (r ⊔ s).comap (Subtype.val : Subtype P → D) =
      r.comap Subtype.val ⊔ s.comap Subtype.val := by
  classical
  let t : Setoid (Subtype P) := r.comap Subtype.val ⊔ s.comap Subtype.val
  let f : D → Option (Quotient t) := fun x => if h : P x then some (Quotient.mk t ⟨x,h⟩) else none
  have hf : ∀ (u : Setoid D), (∀ {x y}, u x y → (P x ↔ P y)) →
      u.comap (Subtype.val : Subtype P → D) ≤ t → u ≤ Setoid.ker f := by
    intro u hu ht x y hxy
    change f x = f y
    by_cases hx : P x
    · have hy := (hu hxy).mp hx
      simp only [f,dite_eq_left hx,dite_eq_left hy]
      exact congrArg some (Quotient.sound (ht hxy))
    · have hy : ¬ P y := fun hy => hx ((hu hxy).mpr hy)
      simp only [f,dite_eq_right hx,dite_eq_right hy]
  have hjoin : r ⊔ s ≤ Setoid.ker f := sup_le (hf r hr le_sup_left) (hf s hs le_sup_right)
  apply le_antisymm
  · intro x y hxy
    have he := hjoin hxy
    change f x.val = f y.val at he
    simp only [f,dite_eq_left x.property,dite_eq_left y.property,Option.some.injEq] at he
    exact Quotient.exact he
  · apply sup_le
    · intro x y hxy; exact (le_sup_left : r ≤ r ⊔ s) hxy
    · intro x y hxy; exact (le_sup_right : s ≤ r ⊔ s) hxy

end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI
