import OAI.NumberTheory.Ostmann.Construction.DiagonalCounterpartReindex

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Construction

theorem finite_subtype_sum_eq_dite {α : Type*} [Fintype α] (P : α→Prop)
    (F : (a : α)→P a→ℂ) :
    (∑a : {a // P a},F a.val a.property)=∑a,if h : P a then F a h else 0 := by
  let g : α→ℂ := fun a => if h : P a then F a h else 0
  have he := Fintype.sum_subtype_add_sum_subtype P g
  have hp : (∑a : {a // P a},g a.val)=∑a : {a // P a},F a.val a.property := by
    apply Finset.sum_congr rfl
    intro a ha
    simp only [g,dite_eq_left a.property]
  have hn : (∑a : {a // ¬P a},g a.val)=0 := by
    apply Finset.sum_eq_zero
    intro a ha
    simp only [g,dite_eq_right a.property]
  rw [hp,hn,add_zero] at he
  exact he

def fixedCounterpartTerm (sources : SourceFamily) (T : List SourceSlot) (giant : PrimeSource)
    (x : RemainingSample sources T giant) (F : RemainingSample sources T giant→ℂ)
    (e : Equiv.Perm (RemainingIndex T)) : ℂ :=
  if he : CounterpartCompatible sources T giant x e then
    if PreservesRemainingBands T e then
      let y := reconstructCounterpart sources T giant x e he
      ((remainingPrior sources T giant).mass y:ℂ)*F y
    else 0
  else 0

theorem bandCounterpartSum_eq_fixed (sources : SourceFamily) (T : List SourceSlot)
    (giant : PrimeSource) (x : RemainingSample sources T giant)
    (F : RemainingSample sources T giant→ℂ) :
    bandCounterpartSum sources T giant x F=
      ∑e : Equiv.Perm (RemainingIndex T),fixedCounterpartTerm sources T giant x F e := by
  exact finite_subtype_sum_eq_dite (CounterpartCompatible sources T giant x)
    (fun e he => if PreservesRemainingBands T e then
      ((remainingPrior sources T giant).mass (reconstructCounterpart sources T giant x e he):ℂ)*
        F (reconstructCounterpart sources T giant x e he) else 0)

theorem fixedCounterpartTerm_nonzero (sources : SourceFamily) (T : List SourceSlot)
    (giant : PrimeSource) (x : RemainingSample sources T giant)
    (F : RemainingSample sources T giant→ℂ) (e : Equiv.Perm (RemainingIndex T))
    (he : fixedCounterpartTerm sources T giant x F e≠0) :
    CounterpartCompatible sources T giant x e ∧ PreservesRemainingBands T e ∧ e 0=0 := by
  unfold fixedCounterpartTerm at he
  split_ifs at he with hc hb
  · exact ⟨hc,hb,hb.fixes_giant⟩
  · exact (he rfl).elim
  · exact (he rfl).elim

end Ostmann.Construction

end

end OAI
