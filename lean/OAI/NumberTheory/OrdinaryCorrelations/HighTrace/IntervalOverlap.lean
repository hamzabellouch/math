import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.Rerooting
open Finset Classical
noncomputable section
variable {α : Type*} [DecidableEq α]

theorem interval_overlap (s : Finset α) (left right : α → ℕ) (J : ℕ)
    (_ : ∀ p∈s,left p≤right p)
    (hinj : Set.InjOn left s)
    (hJ : ∀ x : ℕ,(s.filter (fun p => left p≤x ∧ x<right p)).card≤J) (x : ℕ) :
    (s.filter (fun p => left p≤x ∧ x≤right p)).card≤2*J+1 := by
  let prev := s.filter (fun p => left p≤x-1 ∧ x-1<right p)
  let next := s.filter (fun p => left p≤x ∧ x<right p)
  let single := s.filter (fun p => left p=x ∧ right p=x)
  have hs : single.card≤1 := by
    apply card_le_one.mpr
    intro p hp q hq
    exact hinj (mem_filter.mp hp).1 (mem_filter.mp hq).1
      ((mem_filter.mp hp).2.1.trans (mem_filter.mp hq).2.1.symm)
  have hsub : s.filter (fun p => left p≤x ∧ x≤right p) ⊆ (prev∪next)∪single := by
    intro p hp
    obtain ⟨hps,hpl,hpr⟩ := mem_filter.mp hp
    by_cases hleft : left p<x
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hps,by omega,by omega⟩))
    · by_cases hright : x<right p
      · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hps,hpl,hright⟩))
      · exact mem_union_right _ (mem_filter.mpr ⟨hps,by omega,by omega⟩)
  calc
    _ ≤ ((prev∪next)∪single).card := card_le_card hsub
    _ ≤ prev.card+next.card+single.card := (card_union_le ..).trans (Nat.add_le_add_right (card_union_le ..) _)
    _ ≤ J+J+1 := Nat.add_le_add (Nat.add_le_add (hJ (x-1)) (hJ x)) hs
    _ = _ := by omega

end
end OrdinaryCorrelations.Rerooting

end

end OAI
