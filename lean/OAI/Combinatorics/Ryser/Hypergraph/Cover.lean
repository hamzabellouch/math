import OAI.Combinatorics.Ryser.Hypergraph.Definitions
import Mathlib.Data.Finset.Union

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample

variable {V : Type*} [instDecidableEqV : DecidableEq V] {H : Hypergraph V}

theorem IsCover.mono {C D : Finset V} (hC : IsCover H C) (hCD : C ⊆ D) :
    IsCover H D := let _ := instDecidableEqV; by
  intro e he
  obtain ⟨v, hvC, hve⟩ := hC e he
  exact ⟨v, hCD hvC, hve⟩

theorem IsCover.nonemptyEdges {C : Finset V} (hC : IsCover H C) :
    NonemptyEdges H := let _ := instDecidableEqV; by
  intro e he
  obtain ⟨v, _, hve⟩ := hC e he
  exact ⟨v, hve⟩

theorem NonemptyEdges.isCover_biUnion (hH : NonemptyEdges H) :
    IsCover H (H.biUnion id) := by
  intro e he
  obtain ⟨v, hve⟩ := hH e he
  exact ⟨v, Finset.mem_biUnion.mpr ⟨e, he, hve⟩, hve⟩

theorem NonemptyEdges.exists_cover (hH : NonemptyEdges H) :
    ∃ C : Finset V, IsCover H C :=
  ⟨H.biUnion id, hH.isCover_biUnion⟩

theorem exists_cover_iff_nonemptyEdges :
    (∃ C : Finset V, IsCover H C) ↔ NonemptyEdges H :=
  ⟨fun ⟨_, hC⟩ => hC.nonemptyEdges, NonemptyEdges.exists_cover⟩

theorem nonemptyEdges_iff_empty_not_mem : NonemptyEdges H ↔ ∅ ∉ H := let _ := instDecidableEqV; by
  constructor
  · intro hH he
    obtain ⟨v, hv⟩ := hH ∅ he
    exact Finset.notMem_empty v hv
  · intro hH e he
    apply Finset.nonempty_iff_ne_empty.mpr
    intro heq
    apply hH
    simpa only [heq] using he

theorem IsCover.coverNumber_le {C : Finset V} (hC : IsCover H C) :
    coverNumber H ≤ C.card := let _ := instDecidableEqV;
  Nat.sInf_le ⟨C, hC, rfl⟩

theorem exists_minimum_cover_of_exists (hH : ∃ C : Finset V, IsCover H C) :
    ∃ C : Finset V, IsCover H C ∧ C.card = coverNumber H := let _ := instDecidableEqV; by
  apply Nat.sInf_mem (s := coverCardinalities H)
  obtain ⟨C, hC⟩ := hH
  exact ⟨C.card, C, hC, rfl⟩

theorem exists_minimum_cover (hH : NonemptyEdges H) :
    ∃ C : Finset V, IsCover H C ∧ C.card = coverNumber H :=
  exists_minimum_cover_of_exists hH.exists_cover

theorem le_coverNumber_of_exists (hH : ∃ C : Finset V, IsCover H C) (k : ℕ)
    (hk : ∀ C : Finset V, IsCover H C → k ≤ C.card) : k ≤ coverNumber H := by
  obtain ⟨C, hC, hcard⟩ := exists_minimum_cover_of_exists hH
  rw [← hcard]
  exact hk C hC

theorem le_coverNumber (hH : NonemptyEdges H) (k : ℕ)
    (hk : ∀ C : Finset V, IsCover H C → k ≤ C.card) : k ≤ coverNumber H :=
  le_coverNumber_of_exists hH.exists_cover k hk

theorem coverNumber_le_iff (hH : NonemptyEdges H) (k : ℕ) :
    coverNumber H ≤ k ↔ ∃ C : Finset V, IsCover H C ∧ C.card ≤ k := by
  constructor
  · intro hk
    obtain ⟨C, hC, hcard⟩ := exists_minimum_cover hH
    exact ⟨C, hC, hcard.le.trans hk⟩
  · rintro ⟨C, hC, hcard⟩
    exact hC.coverNumber_le.trans hcard

theorem coverNumber_eq_zero_of_empty_mem (he : ∅ ∈ H) : coverNumber H = 0 := let _ := instDecidableEqV; by
  have hempty : coverCardinalities H = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro k ⟨C, hC, _⟩
    obtain ⟨v, _, hv⟩ := hC ∅ he
    exact Finset.notMem_empty v hv
  rw [coverNumber, hempty, Nat.sInf_empty]

@[simp] theorem coverNumber_empty : coverNumber (∅ : Hypergraph V) = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact (show IsCover (∅ : Hypergraph V) ∅ from by simp [IsCover]).coverNumber_le

theorem coverNumber_pos (hH : NonemptyEdges H) (hne : H.Nonempty) :
    0 < coverNumber H := by
  apply Nat.lt_of_lt_of_le Nat.zero_lt_one
  apply le_coverNumber hH 1
  intro C hC
  obtain ⟨e, he⟩ := hne
  obtain ⟨v, hv, _⟩ := hC e he
  exact Finset.card_pos.mpr ⟨v, hv⟩

theorem Intersecting.isCover_edge (hI : Intersecting H) (hH : NonemptyEdges H)
    {e : Finset V} (he : e ∈ H) : IsCover H e := by
  intro f hf
  by_cases hef : e = f
  · subst f
    obtain ⟨v, hv⟩ := hH e he
    exact ⟨v, hv, hv⟩
  · obtain ⟨v, hv⟩ := hI e he f hf hef
    exact ⟨v, (Finset.mem_inter.mp hv).1, (Finset.mem_inter.mp hv).2⟩

theorem coverNumber_le_edge_card (hI : Intersecting H) (hH : NonemptyEdges H)
    {e : Finset V} (he : e ∈ H) : coverNumber H ≤ e.card :=
  (hI.isCover_edge hH he).coverNumber_le

theorem coverNumber_eq_rank_of_no_small_cover {r : ℕ} (hr : 0 < r)
    (hU : Uniform r H) (hne : H.Nonempty) (hI : Intersecting H)
    (hsmall : ∀ C : Finset V, C.card ≤ r - 1 → ¬ IsCover H C) :
    coverNumber H = r := by
  have hH : NonemptyEdges H := by
    intro e he
    apply Finset.card_pos.mp
    rw [hU e he]
    exact hr
  apply le_antisymm
  · obtain ⟨e, he⟩ := hne
    exact (coverNumber_le_edge_card hI hH he).trans_eq (hU e he)
  · apply le_coverNumber hH r
    intro C hC
    by_contra hlt
    exact hsmall C (Nat.le_sub_one_of_lt (lt_of_not_ge hlt)) hC

end RyserCoveringCounterexample

end

end OAI
