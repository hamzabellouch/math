import OAI.Combinatorics.BinaryEdit.TaggedExtraction
import OAI.Combinatorics.BinaryEdit.BlockExtraction
import OAI.Combinatorics.BinaryEdit.TaggedRowLCS

namespace OAI

/-! Literal array-to-slice hypotheses for the common tagged alignment lemma. -/
namespace TreeEdit.BinaryLower.TaggedExtraction

open scoped BigOperators

/-- A blockwise deficit bound gives the local slice capacity,
with all slices taken from the actual nested concatenation. -/
theorem local_slice_capacity {α : Type*} {T m B : ℕ}
    (X Y : Fin T → Fin m → Word α B) (tag : α → Fin m)
    (hX : ∀ (a : Fin T) (i : Fin m) (s : α), s ∈ (X a i).val → tag s = i)
    (hY : ∀ (a : Fin T) (i : Fin m) (s : α), s ∈ (Y a i).val → tag s = i)
    {d : ℝ} (hd : ∀ a b, d ≤ ∑ i, (deficit B (X a i).val (Y b i).val : ℝ))
    (a b : Fin T) :
    (lcs (((rows X).drop (a.val * (m * B))).take (m * B))
      (((rows Y).drop (b.val * (m * B))).take (m * B)) : ℝ) ≤
        (m : ℝ) * B - d := by
  change (lcs (((BlockExtraction.concatenateRows X).drop (a.val * (m * B))).take (m * B))
    (((BlockExtraction.concatenateRows Y).drop (b.val * (m * B))).take (m * B)) : ℝ) ≤ _
  rw [BlockExtraction.extract_row, BlockExtraction.extract_row]
  exact TaggedRow.lcs_row_le_capacity_sub tag
    (fun i => (X a i).val) (fun i => (Y b i).val)
    (hX a) (hY b) (fun i => (X a i).property) (hd a b)

/-- Pairwise disjoint alphabets admit a common tag decoder. -/
theorem exists_array_decoder {α : Type*} {T m B : ℕ}
    (X Y : Fin T → Fin m → Word α B) (hm : 0 < m)
    (Γ : Fin m → Set α) (hΓ : Pairwise fun i j => Disjoint (Γ i) (Γ j))
    (hX : ∀ (a : Fin T) (i : Fin m) (s : α), s ∈ (X a i).val → s ∈ Γ i)
    (hY : ∀ (a : Fin T) (i : Fin m) (s : α), s ∈ (Y a i).val → s ∈ Γ i) :
    ∃ tag : α → Fin m,
      (∀ (a : Fin T) (i : Fin m) (s : α), s ∈ (X a i).val → tag s = i) ∧
      (∀ (a : Fin T) (i : Fin m) (s : α), s ∈ (Y a i).val → tag s = i) := by
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  obtain ⟨tag, ht⟩ := TaggedRow.exists_tag_of_pairwise_disjoint Γ hΓ
  refine ⟨tag, ?_, ?_⟩
  · intro a i s hs
    exact ht i s (hX a i s hs)
  · intro a i s hs
    exact ht i s (hY a i s hs)

end TreeEdit.BinaryLower.TaggedExtraction

end OAI
