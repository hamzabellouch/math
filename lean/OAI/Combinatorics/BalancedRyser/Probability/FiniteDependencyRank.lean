import OAI.Combinatorics.BalancedRyser.Local.LocalAcyclicSpecifications

namespace OAI

namespace Balanced.Local.ConditionSpec

noncomputable section
open scoped Classical

theorem exists_nat_rank_of_wellFounded {α : Type*} [Fintype α]
    (R : α → α → Prop) (hR : WellFounded R) :
    ∃ rank : α → ℕ, ∀ x y, R x y → rank x < rank y := by
  let pred : α → Finset α := fun x =>
    Finset.univ.filter (fun z => Relation.TransGen R z x)
  refine ⟨fun x => (pred x).card, ?_⟩
  intro x y hxy
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro z hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (Finset.mem_filter.mp hz).2.trans (Relation.TransGen.single hxy)⟩
  · intro heq
    have hx : x ∈ pred y := Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, Relation.TransGen.single hxy⟩
    rw [← heq] at hx
    have hxx := (Finset.mem_filter.mp hx).2
    exact hR.transGen.asymmetric x x hxx hxx

theorem exists_nat_rank_on_finset {α : Type*} [DecidableEq α]
    (T : Finset α) (R : α → α → Prop)
    (hR : WellFounded (fun x y : {v // v ∈ T} => R x.val y.val)) :
    ∃ rank : α → ℕ, ∀ x ∈ T, ∀ y ∈ T, R x y → rank x < rank y := by
  obtain ⟨rank, hrank⟩ := exists_nat_rank_of_wellFounded
    (fun x y : {v // v ∈ T} => R x.val y.val) hR
  refine ⟨fun x => if h : x ∈ T then rank ⟨x, h⟩ else 0, ?_⟩
  intro x hx y hy hxy
  simpa only [dite_eq_left hx, dite_eq_left hy] using hrank ⟨x, hx⟩ ⟨y, hy⟩ hxy

end
end Balanced.Local.ConditionSpec

end OAI
