import OAI.Probability.BenjaminiSchramm.LayerFrontierLocalization

namespace OAI

noncomputable section
open Set
open scoped Classical

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

lemma neighbor_card_le_degree (hl : LocallyFinite G) (x : V) :
    (finite_neighbors hl x).toFinset.card ≤ degree G x := by
  let f : Step G x → {y // Adj G x y} := fun d => ⟨d.1.2,d.1.1,d.2⟩
  have hf : Function.Surjective f := by
    rintro ⟨y,e,he⟩
    exact ⟨⟨(e,y),he⟩,rfl⟩
  let : Fintype (Step G x) := (finite_steps G hl x).fintype
  have hh := Nat.card_le_card_of_surjective f hf
  have hcard : Nat.card {y // Adj G x y}=(finite_neighbors hl x).toFinset.card :=
    (Nat.card_coe_set_eq _).trans (Set.ncard_eq_toFinset_card _ (finite_neighbors hl x))
  rw [hcard] at hh
  exact hh

lemma exists_neighbor_card_bound (hl : LocallyFinite G) (hq : QuasiTransitive G) :
    ∃ d : ℕ, ∀ x, (finite_neighbors hl x).toFinset.card ≤ d := by
  obtain ⟨d,_,hd⟩ := exists_degree_bound G hq
  exact ⟨d,fun x => (neighbor_card_le_degree G hl x).trans (hd x)⟩

end Percolation.BenjaminiSchramm

end

end OAI
