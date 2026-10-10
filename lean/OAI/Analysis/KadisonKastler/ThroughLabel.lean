import Mathlib.Data.Sym.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Multiset.AddSub
import Mathlib.Tactic

namespace OAI

/-! # Counting projection words containing one prescribed label

The labels form actual finite multisets (`Sym`). Distinct multisets containing
one label are counted by a binomial coefficient. Repeated multisets admit a
uniform bound of twice the appropriate power of the alphabet size.
-/

namespace KadisonKastler

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Multisets containing a prescribed label. -/
abbrev ThroughLabel (a : α) (r : ℕ) := {s : Sym α r // a ∈ s}

/-- Multisets containing a prescribed label, with no repeated label. -/
abbrev DistinctThroughLabel (a : α) (r : ℕ) :=
  {s : Sym α r // a ∈ s ∧ (s : Multiset α).Nodup}

/-- Multisets containing a prescribed label and at least one repetition. -/
abbrev RepeatedThroughLabel (a : α) (r : ℕ) :=
  {s : Sym α r // a ∈ s ∧ ¬ (s : Multiset α).Nodup}

/-- Erasing one occurrence of the prescribed label. -/
def throughLabelEquiv (a : α) (r : ℕ) : ThroughLabel a (r + 1) ≃ Sym α r where
  toFun s := s.val.erase a s.property
  invFun s := ⟨Sym.cons a s, Sym.mem_cons_self a s⟩
  left_inv s := by apply Subtype.ext; exact Sym.cons_erase s.property
  right_inv s := Sym.erase_cons_head s a

theorem card_throughLabel (a : α) (r : ℕ) :
    Fintype.card (ThroughLabel a (r + 1)) = (Fintype.card α + r - 1).choose r := by
  rw [Fintype.card_congr (throughLabelEquiv a r), Sym.card_sym_eq_choose]

/-- Distinct multisets are exactly finite subsets with the same cardinality. -/
def distinctThroughLabelEquiv (a : α) (r : ℕ) :
    DistinctThroughLabel a r ≃ {s : Finset α // a ∈ s ∧ s.card = r} where
  toFun s := ⟨s.val.val.toFinset, by
    constructor
    · exact Multiset.mem_toFinset.mpr s.property.1
    · exact (Multiset.toFinset_card_of_nodup s.property.2).trans s.val.property⟩
  invFun s := ⟨⟨s.val.val, s.property.2⟩, s.property.1, s.val.nodup⟩
  left_inv s := by
    apply Subtype.ext
    apply Subtype.ext
    exact s.property.2.dedup
  right_inv s := by apply Subtype.ext; exact Finset.val_toFinset s.val

theorem card_distinctThroughLabel (a : α) (r : ℕ) :
    Fintype.card (DistinctThroughLabel a (r + 1)) = (Fintype.card α - 1).choose r := by
  rw [Fintype.card_congr (distinctThroughLabelEquiv a (r + 1))]
  let S := (Finset.univ.powersetCard (r + 1)).filter ({a} ⊆ ·)
  have hcard : Fintype.card {s : Finset α // a ∈ s ∧ s.card = r + 1} = S.card := by
    apply Fintype.card_of_subtype S
    intro s
    simp only [S, Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ,
      true_and, Finset.singleton_subset_iff]
    exact and_comm
  rw [hcard]
  have hc := Finset.card_filter_powersetCard_subset ({a} : Finset α) Finset.univ
    (r + 1) (Finset.subset_univ _) (by simp)
  simpa only [S, Finset.card_univ, Finset.card_singleton, Nat.add_sub_cancel] using hc

/-- Stars-and-bars is bounded by the count of all ordered words. -/
theorem card_sym_le_pow [Nonempty α] (r : ℕ) :
    Fintype.card (Sym α r) ≤ Fintype.card α ^ r := by
  rw [Sym.card_sym_eq_choose]
  have hc := Nat.choose_le_sub_pow (Fintype.card α + r - 1) r
  have hn := Fintype.card_pos (α := α)
  have he : Fintype.card α + r - 1 + 1 - r = Fintype.card α := by omega
  simpa only [he] using hc

/-- A repeated multiset can be written with a repeated pair at its front. -/
theorem exists_repeated_pair {r : ℕ} (s : Sym α (r + 2))
    (hs : ¬ (s : Multiset α).Nodup) :
    ∃ b : α, ∃ t : Sym α r, s = Sym.cons b (Sym.cons b t) := by
  have hn : ∃ b, 2 ≤ Multiset.count b (s : Multiset α) := by
    by_contra! h
    exact hs (Multiset.nodup_iff_count_le_one.mpr (fun b => by have := h b; omega))
  obtain ⟨b, hb⟩ := hn
  have hmem : b ∈ s := Multiset.count_pos.mp (lt_of_lt_of_le (by decide : 0 < 2) hb)
  let t := s.erase b hmem
  have hmem' : b ∈ t := by
    apply Multiset.count_pos.mp
    change 0 < Multiset.count b ((s : Multiset α).erase b)
    rw [Multiset.count_erase_self]
    omega
  refine ⟨b, t.erase b hmem', ?_⟩
  rw [Sym.cons_erase hmem', Sym.cons_erase hmem]

/-- Every repeated multiset through `a` is either `aa` followed by a remainder,
or `abb` followed by a remainder. -/
def repeatedThroughCode (a : α) (r : ℕ) :
    Sym α (r + 1) ⊕ (α × Sym α r) → RepeatedThroughLabel a (r + 3)
  | Sum.inl t => ⟨Sym.cons a (Sym.cons a t), by
      simp [Sym.coe_cons, Multiset.nodup_cons]⟩
  | Sum.inr (b, t) => ⟨Sym.cons a (Sym.cons b (Sym.cons b t)), by
      simp [Sym.coe_cons, Multiset.nodup_cons]⟩

theorem repeatedThroughCode_surjective (a : α) (r : ℕ) :
    Function.Surjective (repeatedThroughCode a r) := by
  intro s
  let t := s.val.erase a s.property.1
  by_cases ha : a ∈ t
  · refine ⟨Sum.inl (t.erase a ha), ?_⟩
    apply Subtype.ext
    change Sym.cons a (Sym.cons a (t.erase a ha)) = s.val
    rw [Sym.cons_erase ha]
    exact Sym.cons_erase s.property.1
  · have hn : ¬ (t : Multiset α).Nodup := by
      intro ht
      apply s.property.2
      rw [← Sym.cons_erase s.property.1, Sym.coe_cons]
      exact Multiset.nodup_cons.mpr ⟨ha, ht⟩
    obtain ⟨b, v, hv⟩ := exists_repeated_pair t hn
    refine ⟨Sum.inr (b, v), ?_⟩
    apply Subtype.ext
    change Sym.cons a (Sym.cons b (Sym.cons b v)) = s.val
    rw [← hv]
    exact Sym.cons_erase s.property.1

/-- The repeated contribution loses one degree compared with all words. -/
theorem card_repeatedThroughLabel_add_three (a : α) (r : ℕ) :
    Fintype.card (RepeatedThroughLabel a (r + 3)) ≤ 2 * Fintype.card α ^ (r + 1) := by
  have : Nonempty α := ⟨a⟩
  have hc := Fintype.card_le_of_surjective _ (repeatedThroughCode_surjective a r)
  have hb : Fintype.card (RepeatedThroughLabel a (r + 3)) ≤
      Fintype.card (Sym α (r + 1)) + Fintype.card α * Fintype.card (Sym α r) := by
    simpa only [Fintype.card_sum, Fintype.card_prod] using hc
  calc
    _ ≤ Fintype.card α ^ (r + 1) + Fintype.card α * Fintype.card α ^ r :=
      hb.trans (Nat.add_le_add (card_sym_le_pow _) (Nat.mul_le_mul_left _ (card_sym_le_pow _)))
    _ = 2 * Fintype.card α ^ (r + 1) := by rw [pow_succ]; ring

/-- There is exactly one repeated two-letter multiset through `a`. -/
theorem card_repeatedThroughLabel_two (a : α) :
    Fintype.card (RepeatedThroughLabel a 2) = 1 := by
  let e : RepeatedThroughLabel a 2 := ⟨Sym.cons a (Sym.cons a Sym.nil), by
    simp [Sym.coe_cons, Multiset.nodup_cons]⟩
  have he : ∀ s : RepeatedThroughLabel a 2, s = e := by
    intro s
    obtain ⟨b, t, ht⟩ := exists_repeated_pair s.val s.property.2
    have hz : t = Sym.nil := Subsingleton.elim _ _
    rw [hz] at ht
    have hab : a = b := by simpa [ht] using s.property.1
    subst b
    apply Subtype.ext
    exact ht
  let equiv : RepeatedThroughLabel a 2 ≃ Unit := {
    toFun := fun _ => ()
    invFun := fun _ => e
    left_inv := fun s => (he s).symm
    right_inv := fun u => by cases u; rfl }
  simpa using Fintype.card_congr equiv

/-- A uniform repeated-label bound, including the length-two endpoint. -/
theorem card_repeatedThroughLabel (a : α) (r : ℕ) (hr : 2 ≤ r) :
    Fintype.card (RepeatedThroughLabel a r) ≤ 2 * Fintype.card α ^ (r - 2) := by
  obtain rfl | hr' := eq_or_lt_of_le hr
  · simp [card_repeatedThroughLabel_two]
  · obtain ⟨k, rfl⟩ : ∃ k, r = k + 3 := ⟨r - 3, by omega⟩
    simpa using card_repeatedThroughLabel_add_three a k

end

end KadisonKastler

end OAI
