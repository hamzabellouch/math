import OAI.Probability.MatroidProphet.Pivots.Interleavings

namespace OAI

namespace MatroidProphet
namespace Pivots

open Set Finset

variable {α : Type*} [Fintype α]

lemma oldPrefix_subset_before
    {α : Type u_1} [Fintype α] {r s : ℕ} (b : ℕ → α) (a : Fin s → α)
    (time : Occurrence r s → ℕ) (horder : OldOrdered time) (i : Fin r) :
    oldPrefix b i.val ⊆ occurrenceLabel b a '' {p | time p < time (Sum.inl i)} := by
  rintro x ⟨k, hk, rfl⟩
  let j : Fin r := ⟨k, lt_trans hk i.isLt⟩
  exact ⟨Sum.inl j, horder j i hk, rfl⟩

lemma retained_old_initially_nonredundant {r s : ℕ} (M : Matroid α) (b : ℕ → α)
    (a : Fin s → α) (time : Occurrence r s → ℕ) (horder : OldOrdered time)
    (i : Fin r) (hi : Sum.inl i ∈ retained M b a time) :
    b i.val ∉ M.closure (oldPrefix b i.val) := by
  classical
  intro hdep
  exact (Finset.mem_filter.mp hi).2
    (M.closure_subset_closure (oldPrefix_subset_before b a time horder i) hdep)

lemma card_retainedFamily_arbitrary_old {r s : ℕ} (M : Matroid α) (b : ℕ → α)
    (a : Fin s → α) (he : ∀ k < r, b k ∈ M.E) :
    (retainedFamily (r := r) M b a).card ≤ 4 ^ s := by
  classical
  let old : Finset (Occurrence r s) :=
    (Finset.univ.filter (fun i : Fin r => b i.val ∉ M.closure (oldPrefix b i.val))).image Sum.inl
  let movable : Finset (Occurrence r s) := Finset.univ.image Sum.inr
  let omissions : Finset (Occurrence r s) := old.filter (fun o =>
    match o with
    | Sum.inl i => i.val ∈ vulnerable M b (Set.range a) r
    | Sum.inr _ => False)
  have hmov : movable.card ≤ s := by
    simp [movable, Finset.card_image_of_injective, Sum.inr_injective]
  have homit : omissions.card ≤ (vulnerable M b (Set.range a) r).card := by
    apply Finset.card_le_card_of_injOn
      (fun o : Occurrence r s => Sum.elim Fin.val (fun _ => 0) o)
    · intro o ho
      have ho' := (Finset.mem_filter.mp ho).2
      cases o with
      | inl i => exact ho'
      | inr j => exact False.elim ho'
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
    (homit.trans ((card_vulnerable_le_rank M b (Set.range a) r he).trans
      (hrank.trans hrange)))
  · intro J hJ o ho
    obtain ⟨time, horder, rfl⟩ := (Finset.mem_filter.mp hJ).2
    have hoo := (Finset.mem_sdiff.mp ho).1
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hoo
    have hind := (Finset.mem_filter.mp hi).2
    apply retains_nonomittable_old M b a time horder i
    intro hom
    have hom' := (Finset.mem_filter.mp hom).2
    have hv : i.val ∈ vulnerable M b (Set.range a) r :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr i.isLt, hind, hom'⟩
    exact (Finset.mem_sdiff.mp ho).2 (Finset.mem_filter.mpr ⟨hoo, hv⟩)
  · intro J hJ o ho
    obtain ⟨time, horder, rfl⟩ := (Finset.mem_filter.mp hJ).2
    cases o with
    | inl i =>
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        retained_old_initially_nonredundant M b a time horder i ho⟩, rfl⟩
    | inr j => exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)

end Pivots
end MatroidProphet

end OAI
