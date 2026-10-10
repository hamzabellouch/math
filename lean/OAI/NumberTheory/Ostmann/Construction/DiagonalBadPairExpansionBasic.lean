import OAI.NumberTheory.Ostmann.Construction.DiagonalBadPairInverse
import OAI.NumberTheory.Ostmann.Construction.DiagonalCounterpartReindexFixed

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction
attribute [local instance] Classical.propDecidable

theorem finite_dependent_subtype_sum {α M : Type*} [Fintype α] [AddCommMonoid M]
    (P : α → Prop) [DecidablePred P] (F : (a : α) → P a → M) :
    (∑ a : {a // P a}, F a.val a.property) =
      ∑ a, if h : P a then F a h else 0 := by
  let g : α → M := fun a => if h : P a then F a h else 0
  have he := Fintype.sum_subtype_add_sum_subtype P g
  have hp : (∑ a : {a // P a}, g a.val) = ∑ a : {a // P a}, F a.val a.property := by
    apply Finset.sum_congr rfl
    intro a ha
    simp only [g,dite_eq_left a.property]
  have hn : (∑ a : {a // ¬P a}, g a.val) = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    simp only [g,dite_eq_right a.property]
  rw [hp,hn,add_zero] at he
  exact he

theorem badCounterpartPair_sum_eq {M : Type*} [AddCommMonoid M]
    (sources : SourceFamily) (T : List SourceSlot) (giant : PrimeSource)
    (B : Equiv.Perm (RemainingIndex T) → Prop)
    (F : (x : RemainingSample sources T giant) → (e : Equiv.Perm (RemainingIndex T)) →
      CounterpartCompatible sources T giant x e → B e → M) :
    (∑ z : BadCounterpartPair sources T giant B, F z.val.1 z.val.2 z.property.1 z.property.2) =
      ∑ e, if hb : B e then
        ∑ x, if hc : CounterpartCompatible sources T giant x e then F x e hc hb else 0
      else 0 := by
  have hs := finite_dependent_subtype_sum
    (fun z : RemainingSample sources T giant × Equiv.Perm (RemainingIndex T) =>
      CounterpartCompatible sources T giant z.1 z.2 ∧ B z.2)
    (fun z hz => F z.1 z.2 hz.1 hz.2)
  calc
    _ = ∑ z : RemainingSample sources T giant × Equiv.Perm (RemainingIndex T),
        if hz : CounterpartCompatible sources T giant z.1 z.2 ∧ B z.2 then
          F z.1 z.2 hz.1 hz.2 else 0 := hs
    _ = _ := by
      rw [Fintype.sum_prod_type,Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e he
      by_cases hb : B e
      · rw [dite_eq_left hb]
        apply Finset.sum_congr rfl
        intro x hx
        by_cases hc : CounterpartCompatible sources T giant x e
        · simp only [hc,hb,and_self,dite_eq_left]
        · simp only [hc,false_and,dite_eq_right,not_false_eq_true]
      · simp only [hb,and_false,dite_eq_right,not_false_eq_true,Finset.sum_const_zero]
end Ostmann.Construction

end

end OAI
