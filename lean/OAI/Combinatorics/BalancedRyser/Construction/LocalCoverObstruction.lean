import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import OAI.Combinatorics.BalancedRyser.Construction.Construction

namespace OAI

namespace Balanced.Configuration

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable (C : Configuration F)

def labelLocalPiece : BlockLabel F → LocalPiece F
  | Sum.inl l => Sum.inr (Sum.inl l)
  | Sum.inr (Sum.inl d) => Sum.inr (Sum.inr d)
  | Sum.inr (Sum.inr s) => Sum.inl (C.blockPoints (Sum.inr (Sum.inr s)))

theorem blockPoints_subset_labelLocalPiece (b : BlockLabel F) :
    C.blockPoints b ⊆ C.localPiecePoints (C.labelLocalPiece b) := by
  rcases b with l | d | ⟨s, bit⟩
  · exact Finset.inter_subset_left
  · exact Finset.inter_subset_left
  · cases bit <;> exact Finset.Subset.refl _

theorem labelLocalPiece_allowed (p : Point F) (b : BlockLabel F)
    (h : C.IsBlockLabel b) : C.AllowedLocalPiece p (C.labelLocalPiece b) := by
  classical
  rcases b with l | d | ⟨s, bit⟩
  · change l ∉ C.splitLinesAt p ∪ constituentLines C.merged
    intro hl
    apply h
    rcases Finset.mem_union.mp hl with hs | hm
    · exact Finset.mem_union_left _ (Finset.mem_filter.mp hs).1
    · exact Finset.mem_union_right _ hm
  · trivial
  · cases bit <;> change (Finset.card {_, _} ≤ 2) <;> simpa using (Finset.card_insert_le _ {_})

theorem block_family_to_local_pieces
    (p : Point F) (labels : Finset (BlockLabel F))
    (hlabels : ∀ b ∈ labels, C.IsBlockLabel b) :
    ∃ pieces : Finset (LocalPiece F), pieces.card ≤ labels.card ∧
      (∀ a ∈ pieces, C.AllowedLocalPiece p a) ∧
      labels.biUnion C.blockPoints ⊆ pieces.biUnion C.localPiecePoints := by
  classical
  refine ⟨labels.image C.labelLocalPiece, Finset.card_image_le, ?_, ?_⟩
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    exact C.labelLocalPiece_allowed p b (hlabels b hb)
  · intro x hx
    obtain ⟨b, hb, hxb⟩ := Finset.mem_biUnion.mp hx
    exact Finset.mem_biUnion.mpr ⟨C.labelLocalPiece b,
      Finset.mem_image.mpr ⟨b, hb, rfl⟩,
      C.blockPoints_subset_labelLocalPiece b hxb⟩

theorem local_condition_excludes_block_cover
    (hlocal : C.LocalCondition) (p : Point F)
    (hb : 3 ≤ C.splitMultiplicity p)
    (labels : Finset (BlockLabel F))
    (hlabels : ∀ b ∈ labels, C.IsBlockLabel b)
    (hcard : labels.card ≤ C.splitMultiplicity p - 1) :
    ¬ C.designatedAt p ⊆ C.partnerSet p ∪ labels.biUnion C.blockPoints := by
  intro hcover
  obtain ⟨pieces, hsize, hallowed, hpoints⟩ :=
    C.block_family_to_local_pieces p labels hlabels
  apply hlocal p hb
  refine ⟨pieces, hsize.trans hcard, hallowed, ?_⟩
  intro x hx
  rcases Finset.mem_union.mp (hcover hx) with hz | hr
  · exact Finset.mem_union_left _ hz
  · exact Finset.mem_union_right _ (hpoints hr)

theorem designatedAt_subset_points (p : Point F) : C.designatedAt p ⊆ C.points := by
  classical
  intro x hx
  obtain ⟨s, hs, hxs⟩ := Finset.mem_biUnion.mp hx
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
    ⟨s, Finset.mem_univ s, hxs⟩)

theorem residual_cover_after_forcing
    (p : Point F) (labels forced : Finset (BlockLabel F))
    (hcover : C.points ⊆ labels.biUnion C.blockPoints)
    (hforced : C.designatedAt p ∩ forced.biUnion C.blockPoints ⊆ C.partnerSet p) :
    C.designatedAt p ⊆ C.partnerSet p ∪ (labels \ forced).biUnion C.blockPoints := by
  classical
  intro x hx
  obtain ⟨b, hb, hxb⟩ := Finset.mem_biUnion.mp
    (hcover (C.designatedAt_subset_points p hx))
  by_cases hbf : b ∈ forced
  · exact Finset.mem_union_left _ (hforced (Finset.mem_inter.mpr
      ⟨hx, Finset.mem_biUnion.mpr ⟨b, hbf, hxb⟩⟩))
  · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨b, Finset.mem_sdiff.mpr ⟨hb, hbf⟩, hxb⟩)

theorem large_affine_pencil_cover_impossible
    (hlocal : C.LocalCondition) (p : Point F)
    (hb : 3 ≤ C.splitMultiplicity p)
    (hbupper : C.splitMultiplicity p ≤ Fintype.card F + 1)
    (labels forced : Finset (BlockLabel F))
    (hlabels : ∀ b ∈ labels, C.IsBlockLabel b)
    (hsize : labels.card ≤ Fintype.card F)
    (hsubset : forced ⊆ labels)
    (hcount : forced.card = Fintype.card F + 1 - C.splitMultiplicity p)
    (hforced : C.designatedAt p ∩ forced.biUnion C.blockPoints ⊆ C.partnerSet p) :
    ¬ C.points ⊆ labels.biUnion C.blockPoints := by
  classical
  intro hcover
  have hremaining : (labels \ forced).card ≤ C.splitMultiplicity p - 1 := by
    have hsum := Finset.card_sdiff_add_card_eq_card hsubset
    omega
  exact C.local_condition_excludes_block_cover hlocal p hb (labels \ forced)
    (fun b hb => hlabels b (Finset.mem_sdiff.mp hb).1) hremaining
    (C.residual_cover_after_forcing p labels forced hcover hforced)

end
end Balanced.Configuration

end OAI
