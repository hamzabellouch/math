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
variable {α β : Type*} [DecidableEq α] [LinearOrder β]

theorem disjoint_intervals (left right : α → β) (q : ℕ) (s : Finset α)
    (hne : ∀ p∈s,left p ≤ right p)
    (hoverlap : ∀ x : β,(s.filter (fun p => left p ≤ x ∧ x ≤ right p)).card ≤ q) :
    ∃ t ⊆ s,s.card ≤ q*t.card ∧ (t : Set α).Pairwise (fun p r => right p<left r ∨ right r<left p) := by
  revert hne hoverlap
  induction s using Finset.strongInductionOn
  rename_i s ih
  intro hne hoverlap
  by_cases hs : s.Nonempty
  · obtain ⟨p,hps,hpmin⟩ := exists_min_image s right hs
    let u := s.filter (fun r => right p<left r)
    have hpu : p∉u := by simp [u,not_lt.mpr (hne p hps)]
    have hus : u  ⊂  s := Finset.ssubset_iff_subset_ne.mpr ⟨filter_subset _ _,fun he => hpu (he.symm ▸ hps)⟩
    have hune : ∀ r∈u,left r ≤ right r := fun r hr => hne r (mem_filter.mp hr).1
    have huoverlap : ∀ x : β,(u.filter (fun r => left r ≤ x ∧ x ≤ right r)).card ≤ q := by
      intro x
      apply (card_le_card ?_).trans (hoverlap x)
      intro r hr
      exact mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp hr).1).1,(mem_filter.mp hr).2⟩
    obtain ⟨t,htu,htcard,ht⟩ := ih u hus hune huoverlap
    have hdiff : (s\u).card ≤ q := by
      apply (card_le_card ?_).trans (hoverlap (right p))
      intro r hr
      obtain ⟨hrs,hru⟩ := mem_sdiff.mp hr
      have hleft : left r ≤ right p := le_of_not_gt (fun he => hru (mem_filter.mpr ⟨hrs,he⟩))
      exact mem_filter.mpr ⟨hrs,hleft,hpmin r hrs⟩
    have hpt : p∉t := fun hp => hpu (htu hp)
    refine ⟨insert p t,insert_subset hps (htu.trans hus.subset),?_,?_⟩
    · rw [card_insert_of_notMem hpt]
      have hc := card_sdiff_add_card_eq_card hus.subset
      nlinarith
    · rw [coe_insert,Set.pairwise_insert]
      refine ⟨ht,?_⟩
      intro r hr hpr
      have he := (mem_filter.mp (htu hr)).2
      exact ⟨Or.inl he,Or.inr he⟩
  · refine ⟨∅,empty_subset _,?_,by simp⟩
    have he : s=∅ := not_nonempty_iff_eq_empty.mp hs
    simp [he]

end
end OrdinaryCorrelations.Rerooting

end

end OAI
