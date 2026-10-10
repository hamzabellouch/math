import OAI.Probability.MatroidProphet.Pivots.Greedy
import OAI.Probability.MatroidProphet.Pivots.Count

namespace OAI

namespace MatroidProphet
namespace Pivots

open Set Finset

variable {α : Type*} [Fintype α]

abbrev Occurrence (r s : ℕ) := Fin r ⊕ Fin s

def occurrenceLabel {r s : ℕ} (b : ℕ → α) (a : Fin s → α) : Occurrence r s → α :=
  Sum.elim (fun i => b i.val) a

def OldOrdered {r s : ℕ} (time : Occurrence r s → ℕ) : Prop :=
  ∀ i j : Fin r, i < j → time (Sum.inl i) < time (Sum.inl j)

noncomputable def retained {r s : ℕ} (M : Matroid α) (b : ℕ → α) (a : Fin s → α)
    (time : Occurrence r s → ℕ) : Finset (Occurrence r s) := by
  classical
  exact Finset.univ.filter (fun o => occurrenceLabel b a o ∉
    M.closure (occurrenceLabel b a '' {p | time p < time o}))

noncomputable def retainedFamily {r s : ℕ} (M : Matroid α) (b : ℕ → α)
    (a : Fin s → α) : Finset (Finset (Occurrence r s)) := by
  classical
  exact Finset.univ.filter (fun J => ∃ time, OldOrdered time ∧ retained M b a time = J)

lemma before_old_subset
    {α : Type u_1} [Fintype α] {r s : ℕ} (b : ℕ → α) (a : Fin s → α)
    (time : Occurrence r s → ℕ) (horder : OldOrdered time) (i : Fin r) :
    occurrenceLabel b a '' {p | time p < time (Sum.inl i)} ⊆
      oldPrefix b i.val ∪ Set.range a := by
  rintro x ⟨o, ho, rfl⟩
  cases o with
  | inl j =>
    left
    have hji : j < i := by
      by_contra hji
      rcases lt_or_eq_of_le (le_of_not_gt hji) with hij | rfl
      · exact Nat.lt_asymm (horder i j hij) ho
      · exact Nat.lt_irrefl _ ho
    exact ⟨j.val, hji, rfl⟩
  | inr j => exact Or.inr ⟨j, rfl⟩

lemma retains_nonomittable_old {r s : ℕ} (M : Matroid α) (b : ℕ → α)
    (a : Fin s → α) (time : Occurrence r s → ℕ) (horder : OldOrdered time)
    (i : Fin r) (hi : i.val ∉ omittable M b (Set.range a) r) :
    Sum.inl i ∈ retained M b a time := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  exact notMem_closure_before_nonomittable M b (Set.range a) _ r i.val i.isLt hi
    (before_old_subset b a time horder i)

lemma card_retainedFamily_le {r s : ℕ} (M : Matroid α) (b : ℕ → α)
    (a : Fin s → α) (he : ∀ k < r, b k ∈ M.E)
    (hind : ∀ k < r, b k ∉ M.closure (oldPrefix b k)) :
    (retainedFamily (r := r) M b a).card ≤ 4 ^ s := by
  classical
  let old : Finset (Occurrence r s) := Finset.univ.image Sum.inl
  let movable : Finset (Occurrence r s) := Finset.univ.image Sum.inr
  let omissions : Finset (Occurrence r s) := old.filter (fun o =>
    match o with
    | Sum.inl i => i.val ∈ omittable M b (Set.range a) r
    | Sum.inr _ => False)
  have hmov : movable.card ≤ s := by
    simp [movable, Finset.card_image_of_injective, Sum.inr_injective]
  have homit : omissions.card ≤ (omittable M b (Set.range a) r).card := by
    apply Finset.card_le_card_of_injOn
      (fun o : Occurrence r s => Sum.elim Fin.val (fun _ => 0) o)
    · intro o ho
      rcases Finset.mem_filter.mp ho with ⟨_, ho⟩
      cases o with
      | inl i => exact ho
      | inr j => exact False.elim ho
    · intro o ho p hp hop
      have ho' := (Finset.mem_filter.mp ho).2
      have hp' := (Finset.mem_filter.mp hp).2
      cases o with
      | inr i => exact False.elim ho'
      | inl i =>
        cases p with
        | inr j => exact False.elim hp'
        | inl j => exact congrArg Sum.inl (Fin.ext hop)
  have hrank : natRank M (Set.range a) ≤ (Set.range a).ncard := by
    exact ENat.toNat_le_toNat (M.eRk_le_encard _)
      (Set.toFinite (Set.range a)).encard_lt_top.ne
  have hrange : (Set.range a).ncard ≤ s := by
    simpa using (Set.ncard_image_le (f := a) (s := Set.univ))
  apply card_retained_family (retainedFamily M b a) old movable omissions s hmov
    (homit.trans ((card_omittable_le_rank M b (Set.range a) r he hind).trans
      (hrank.trans hrange)))
  · intro J hJ o ho
    obtain ⟨time, horder, rfl⟩ := (Finset.mem_filter.mp hJ).2
    have hoo := (Finset.mem_sdiff.mp ho).1
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hoo
    apply retains_nonomittable_old M b a time horder i
    intro hi
    exact (Finset.mem_sdiff.mp ho).2 (Finset.mem_filter.mpr ⟨hoo, hi⟩)
  · intro J hJ o ho
    cases o with
    | inl i => exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    | inr j => exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)

end Pivots
end MatroidProphet

end OAI
