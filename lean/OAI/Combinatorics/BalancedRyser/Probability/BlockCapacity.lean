import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import OAI.Combinatorics.BalancedRyser.Construction.Construction
import OAI.Combinatorics.BalancedRyser.Incidence.AffineIncidence

namespace OAI

namespace Balanced.Configuration

open scoped BigOperators
noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable (C : Configuration F)

theorem linePoints_inter_card_le_one (l m : Line F) (hne : l ≠ m) :
    (linePoints l ∩ linePoints m).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  rcases Finset.mem_inter.mp hx with ⟨hxl, hxm⟩
  rcases Finset.mem_inter.mp hy with ⟨hyl, hym⟩
  exact common_point_eq_of_lines_ne l m hne x y
    (Finset.mem_filter.mp hxl).2 (Finset.mem_filter.mp hxm).2
    (Finset.mem_filter.mp hyl).2 (Finset.mem_filter.mp hym).2

theorem valid_split_not_constituent (hvalid : C.Valid)
    (l : Line F) (hl : l ∈ C.splitLines) : l ∉ constituentLines C.merged := by
  obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hl
  exact (hvalid.2 s).2.1

theorem constituent_not_splitLinesAt (hvalid : C.Valid)
    (p : Point F) (d : Direction F) (bit : Bool) :
    constituent C.merged d bit ∉ C.splitLinesAt p := by
  intro h
  apply C.valid_split_not_constituent hvalid _ (Finset.mem_filter.mp h).1
  exact Finset.mem_image.mpr ⟨(d, bit), Finset.mem_univ _, rfl⟩

theorem designatedAt_subset_splitLinesAt_union (hvalid : C.Valid) (p : Point F) :
    C.designatedAt p ⊆ (C.splitLinesAt p).biUnion linePoints := by
  intro x hx
  obtain ⟨s, hs, hxs⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hxs
  rcases hvalid.2 s with ⟨_, _, _, _, _, hpoints, _, _, _⟩
  refine Finset.mem_biUnion.mpr ⟨(C.choice s).line, ?_, ?_⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr
      ⟨s, Finset.mem_univ _, rfl⟩, (Finset.mem_filter.mp hs).2⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpoints i⟩

theorem designatedAt_inter_line_card_le (hvalid : C.Valid)
    (p : Point F) (l : Line F) (hline : l ∉ C.splitLinesAt p) :
    (C.designatedAt p ∩ linePoints l).card ≤ C.splitMultiplicity p := by
  have hsub : C.designatedAt p ∩ linePoints l ⊆
      (C.splitLinesAt p).biUnion (fun m => linePoints m ∩ linePoints l) := by
    intro x hx
    obtain ⟨hxd, hxl⟩ := Finset.mem_inter.mp hx
    obtain ⟨m, hm, hxm⟩ := Finset.mem_biUnion.mp
      (C.designatedAt_subset_splitLinesAt_union hvalid p hxd)
    exact Finset.mem_biUnion.mpr ⟨m, hm, Finset.mem_inter.mpr ⟨hxm, hxl⟩⟩
  calc
    (C.designatedAt p ∩ linePoints l).card ≤
        ((C.splitLinesAt p).biUnion (fun m => linePoints m ∩ linePoints l)).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ m ∈ C.splitLinesAt p, (linePoints m ∩ linePoints l).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _m ∈ C.splitLinesAt p, 1 := by
      apply Finset.sum_le_sum
      intro m hm
      exact linePoints_inter_card_le_one m l (by intro heq; exact hline (heq ▸ hm))
    _ = C.splitMultiplicity p := by simp [splitMultiplicity]

theorem designatedAt_inter_merged_card_le (hvalid : C.Valid)
    (p : Point F) (d : Direction F) :
    (C.designatedAt p ∩ mergedPoints C.merged d).card ≤ 2 * C.splitMultiplicity p := by
  rw [mergedPoints, Finset.inter_union_distrib_left]
  calc
    _ ≤ (C.designatedAt p ∩ linePoints (constituent C.merged d false)).card +
        (C.designatedAt p ∩ linePoints (constituent C.merged d true)).card :=
      Finset.card_union_le _ _
    _ ≤ C.splitMultiplicity p + C.splitMultiplicity p :=
      Nat.add_le_add
        (C.designatedAt_inter_line_card_le hvalid p _
          (C.constituent_not_splitLinesAt hvalid p d false))
        (C.designatedAt_inter_line_card_le hvalid p _
          (C.constituent_not_splitLinesAt hvalid p d true))
    _ = 2 * C.splitMultiplicity p := by omega

theorem designatedAt_inter_block_card_le (hvalid : C.Valid)
    (p : Point F) (hb : 1 ≤ C.splitMultiplicity p)
    (label : BlockLabel F) (hlabel : C.IsBlockLabel label) :
    (C.designatedAt p ∩ C.blockPoints label).card ≤ 2 * C.splitMultiplicity p := by
  classical
  rcases label with l | d | ⟨s, bit⟩
  · have hline : l ∉ C.splitLinesAt p := by
      intro hl
      exact hlabel (Finset.mem_union_left _ (Finset.mem_filter.mp hl).1)
    have hsub : C.designatedAt p ∩ C.blockPoints (Sum.inl l) ⊆
        C.designatedAt p ∩ linePoints l := by
      intro x hx
      exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1,
        (Finset.mem_inter.mp (Finset.mem_inter.mp hx).2).1⟩
    exact (Finset.card_le_card hsub).trans
      ((C.designatedAt_inter_line_card_le hvalid p l hline).trans (by omega))
  · have hsub : C.designatedAt p ∩ C.blockPoints (Sum.inr (Sum.inl d)) ⊆
        C.designatedAt p ∩ mergedPoints C.merged d := by
      intro x hx
      exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1,
        (Finset.mem_inter.mp (Finset.mem_inter.mp hx).2).1⟩
    exact (Finset.card_le_card hsub).trans (C.designatedAt_inter_merged_card_le hvalid p d)
  · have hsmall : (C.blockPoints (Sum.inr (Sum.inr (s, bit)))).card ≤ 2 := by
      cases bit <;> exact Finset.card_le_two
    exact (Finset.card_le_card Finset.inter_subset_right).trans (hsmall.trans (by omega))

theorem two_split_block_capacity (hvalid : C.Valid)
    (p : Point F) (hb : C.splitMultiplicity p = 2)
    (label : BlockLabel F) (hlabel : C.IsBlockLabel label) :
    (C.designatedAt p ∩ C.blockPoints label).card ≤ 4 := by
  simpa [hb] using C.designatedAt_inter_block_card_le hvalid p (by omega) label hlabel

end
end Balanced.Configuration

end OAI
