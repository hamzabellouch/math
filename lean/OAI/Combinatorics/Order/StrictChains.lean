import OAI.Combinatorics.Order.ChainToggle
import Mathlib.Data.Finset.Sort

namespace OAI

namespace FiniteChain

open Finset

variable {α : Type*} [DecidableEq α] [SemilatticeSup α]

/-- Every unordered finite chain has exactly one strictly increasing enumeration. -/
theorem exists_unique_strict_enumeration (s : Finset α) (hs : Ordered s) :
    ∃! l : List α, l.Pairwise (· < ·) ∧ l.toFinset = s := by
  classical
  let : LinearOrder s := {
    (inferInstance : PartialOrder s) with
    le_total := fun a b => hs a a.2 b b.2
    toDecidableLE := Classical.decRel _
    toDecidableLT := Classical.decRel _
    toDecidableEq := Classical.decEq _ }
  let l : List α := (Finset.univ.sort : List s).map Subtype.val
  have hl : l.Pairwise (· < ·) := by
    exact List.pairwise_map.mpr (Finset.sortedLT_sort (Finset.univ : Finset s)).pairwise
  have he : l.toFinset = s := by
    ext a
    simp [l]
  refine ⟨l, ⟨hl, he⟩, ?_⟩
  intro k hk
  have hn : k.Nodup := hk.1.imp (fun h => ne_of_lt h)
  have hn' : l.Nodup := hl.imp (fun h => ne_of_lt h)
  have hp : k.Perm l := (List.perm_ext_iff_of_nodup hn hn').mpr (by
    intro a
    have := congrArg (fun t : Finset α => a ∈ t) (hk.2.trans he.symm)
    simpa using this)
  exact List.Perm.eq_of_pairwise' (hk.1.imp le_of_lt) (hl.imp le_of_lt) hp

/-- Conversely, an actual strictly increasing list gives a finite chain. -/
theorem ordered_toFinset {l : List α} (hl : l.Pairwise (· < ·)) : Ordered l.toFinset := by
  induction l with
  | nil => simp [Ordered]
  | cons a l ih =>
    have ht := hl.tail
    intro x hx y hy
    simp only [List.toFinset_cons, Finset.mem_insert] at hx hy
    rcases hx with rfl | hx
    · rcases hy with rfl | hy
      · exact Or.inl le_rfl
      · exact Or.inl (le_of_lt (hl.rel_head_tail (List.mem_toFinset.mp hy)))
    · rcases hy with rfl | hy
      · exact Or.inr (le_of_lt (hl.rel_head_tail (List.mem_toFinset.mp hx)))
      · exact ih ht x hx y hy

variable [OrderBot α]

/-- Adding the initial bottom gives a strict chain whose length after bottom equals
the cardinality of the nonbottom nodes, including the empty chain. -/
theorem full_chain_enumeration (s : Finset α) (hs : Ordered s)
    (hn : ∀ x ∈ s, x ≠ ⊥) :
    ∃ l : List α, l.toFinset = s ∧ (⊥ :: l).Pairwise (· < ·) ∧ l.length = s.card := by
  obtain ⟨l, hl, _⟩ := exists_unique_strict_enumeration s hs
  refine ⟨l, hl.2, ?_, ?_⟩
  · apply List.pairwise_cons.mpr
    refine ⟨?_, hl.1⟩
    intro x hx
    exact lt_of_le_of_ne bot_le (Ne.symm (hn x (hl.2 ▸ List.mem_toFinset.mpr hx)))
  · rw [← hl.2]
    exact (List.toFinset_card_of_nodup (hl.1.imp (fun h => ne_of_lt h))).symm

variable [Fintype α]

/-- The nodes after the initial bottom in a strict chain. The empty list gives
the chain containing only bottom. -/
def StrictChain (allowed : α → Prop) :=
  {l : List α // l.Pairwise (· < ·) ∧ ∀ x ∈ l, x ≠ ⊥ ∧ allowed x}

noncomputable def strictToFinset (allowed : α → Prop) (l : StrictChain allowed) :
    {s : Finset α // s ∈ chains allowed} := by
  classical
  refine ⟨l.val.toFinset, ?_⟩
  exact mem_filter.mpr ⟨mem_powerset.mpr (subset_univ _), ordered_toFinset l.property.1,
    fun x hx => l.property.2 x (List.mem_toFinset.mp hx)⟩

noncomputable def strictChainEquiv (allowed : α → Prop) :
    StrictChain allowed ≃ {s : Finset α // s ∈ chains allowed} := by
  classical
  apply Equiv.ofBijective (strictToFinset allowed)
  constructor
  · intro a b hab
    have he : a.val.toFinset = b.val.toFinset := congrArg Subtype.val hab
    have hp : a.val.Perm b.val := (List.perm_ext_iff_of_nodup
      (a.property.1.imp (fun h => ne_of_lt h))
      (b.property.1.imp (fun h => ne_of_lt h))).mpr (by
        intro x
        have hx := congrArg (fun s : Finset α => x ∈ s) he
        simpa using hx)
    apply Subtype.ext
    exact List.Perm.eq_of_pairwise' (a.property.1.imp le_of_lt)
      (b.property.1.imp le_of_lt) hp
  · intro s
    have hs : Admissible allowed s.val := (mem_filter.mp s.property).2
    obtain ⟨l, hl, _⟩ := exists_unique_strict_enumeration s.val hs.1
    have ha : ∀ x ∈ l, x ≠ ⊥ ∧ allowed x := by
      intro x hx
      exact hs.2 x (hl.2 ▸ List.mem_toFinset.mpr hx)
    refine ⟨⟨l, hl.1, ha⟩, ?_⟩
    exact Subtype.ext hl.2

noncomputable instance strictChainFintype (allowed : α → Prop) : Fintype (StrictChain allowed) := by
  classical
  letI : DecidableEq α := Classical.decEq α
  exact Fintype.ofEquiv {s : Finset α // s ∈ chains allowed} (strictChainEquiv allowed).symm

/-- Strict enumeration preserves chain length and the signed sum over all chains. -/
theorem strict_list_weight_eq (allowed : α → Prop) :
    (∑ l : StrictChain allowed, (-1 : ℤ)^l.val.length) =
      ∑ s ∈ chains allowed, (-1 : ℤ)^s.card := by
  classical
  calc
    (∑ l : StrictChain allowed, (-1 : ℤ)^l.val.length) =
        ∑ s : {s : Finset α // s ∈ chains allowed}, (-1 : ℤ)^s.val.card := by
      apply Fintype.sum_equiv (strictChainEquiv allowed)
      intro l
      change (-1 : ℤ)^l.val.length = (-1 : ℤ)^l.val.toFinset.card
      rw [List.toFinset_card_of_nodup (l.property.1.imp (fun h => ne_of_lt h))]
    _ = ∑ s ∈ chains allowed, (-1 : ℤ)^s.card :=
      Finset.sum_coe_sort (chains allowed) (fun s : Finset α => (-1 : ℤ)^s.card)

end FiniteChain

end OAI
