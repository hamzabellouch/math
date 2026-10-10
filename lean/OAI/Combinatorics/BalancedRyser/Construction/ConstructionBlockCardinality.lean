import OAI.Combinatorics.BalancedRyser.Probability.ConfigurationStructure

namespace OAI

namespace Balanced
open scoped _root_.Balanced
namespace BlockCardinality

open ConfigurationStructure

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable (C : Configuration F)

theorem block_nonempty {ρ : ℝ} {B : ℕ}
    (hρ : 0 < ρ) (hO : C.Occupancy ρ B)
    (b : Configuration.BlockLabel F) (hb : b ∈ C.blockLabels) :
    (C.blockPoints b).Nonempty := by
  classical
  have hq : 0 < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  have hρq : 0 < ρ * Fintype.card F := mul_pos hρ hq
  rcases b with l | (d | ⟨s, k⟩)
  · have hreg : l ∉ C.splitLines ∪ constituentLines C.merged :=
      (Finset.mem_filter.mp hb).2
    have hnotD : l ∉ C.deletedLines := by
      intro hl
      rcases Finset.mem_union.mp hl with hlS | hlM
      · exact hreg (Finset.mem_union_left _ hlS)
      · obtain ⟨g, _, heq⟩ := Finset.mem_image.mp hlM
        exact hreg (Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨(g, true), Finset.mem_univ _, heq⟩))
    have hcard : 0 < (linePoints l ∩ C.core).card := by
      exact_mod_cast lt_of_lt_of_le hρq (hO.2.1 l hnotD)
    obtain ⟨p, hp⟩ := Finset.card_pos.mp hcard
    obtain ⟨hpl, hpc⟩ := Finset.mem_inter.mp hp
    exact ⟨p, Finset.mem_inter.mpr ⟨hpl, core_subset_points C hpc⟩⟩
  · have hcard : 0 < (linePoints (constituent C.merged d true) ∩ C.retained).card := by
      exact_mod_cast lt_of_lt_of_le hρq (hO.2.2 d)
    obtain ⟨p, hp⟩ := Finset.card_pos.mp hcard
    obtain ⟨hpl, hpr⟩ := Finset.mem_inter.mp hp
    exact ⟨p, Finset.mem_inter.mpr
      ⟨Finset.mem_union_right _ hpl, retained_subset_points C hpr⟩⟩
  · cases k <;> exact Finset.insert_nonempty _ _

omit [Field F] in

theorem lines_in_direction_card (g : Direction F) : (linesInDirection g).card = Fintype.card F := by
  have heq : linesInDirection g = Finset.univ.image (fun a : F => (g, a)) := by
    ext l
    rcases l with ⟨d, a⟩
    simp [linesInDirection, Prod.ext_iff, eq_comm]
  rw [heq, Finset.card_image_of_injective]
  · simp
  · intro a b h
    exact congrArg Prod.snd h

omit [Field F] in

theorem constituents_in_direction (g : Direction F) :
    (constituentLines C.merged).filter (fun l => l.1 = g) =
      {constituent C.merged g false, constituent C.merged g true} := by
  ext l
  constructor
  · intro hl
    obtain ⟨hlM, hdir⟩ := Finset.mem_filter.mp hl
    obtain ⟨⟨d, b⟩, _, rfl⟩ := Finset.mem_image.mp hlM
    change d = g at hdir
    subst d
    cases b <;> simp
  · intro hl
    rcases Finset.mem_insert.mp hl with rfl | hl
    · exact Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr ⟨(g, false), Finset.mem_univ _, rfl⟩, rfl⟩
    · have hl' := Finset.mem_singleton.mp hl
      subst l
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr ⟨(g, true), Finset.mem_univ _, rfl⟩, rfl⟩

theorem constituents_in_direction_card (hV : C.Valid) (g : Direction F) :
    ((constituentLines C.merged).filter (fun l => l.1 = g)).card = 2 := by
  rw [constituents_in_direction C g]
  have hne : constituent C.merged g false ≠ constituent C.merged g true := by
    intro h
    exact hV.1 g (congrArg Prod.snd h)
  simp [hne]

theorem split_constituents_disjoint (hV : C.Valid) :
    Disjoint C.splitLines (constituentLines C.merged) := by
  apply Finset.disjoint_left.mpr
  intro l hlS hlM
  obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hlS
  exact (hV.2 s).2.1 hlM

theorem nonregular_in_direction_card (hV : C.Valid) (hC : C.Compatible)
    (g : Direction F) :
    ((C.splitLines ∪ constituentLines C.merged).filter (fun l => l.1 = g)).card = 4 := by
  rw [Finset.filter_union, Finset.card_union_of_disjoint]
  · rw [split_lines_in_direction_card C hV hC g, constituents_in_direction_card C hV g]
  · exact (split_constituents_disjoint C hV).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)

theorem regular_lines_card (hV : C.Valid) (hC : C.Compatible) (g : Direction F) :
    (linesInDirection g \ (C.splitLines ∪ constituentLines C.merged)).card =
      Fintype.card F - 4 := by
  rw [Finset.card_sdiff, lines_in_direction_card]
  have heq : (C.splitLines ∪ constituentLines C.merged) ∩ linesInDirection g =
      (C.splitLines ∪ constituentLines C.merged).filter (fun l => l.1 = g) := by
    ext l
    simp [linesInDirection]
  rw [heq, nonregular_in_direction_card C hV hC g]

theorem four_le_field_card (hV : C.Valid) (hC : C.Compatible) :
    4 ≤ Fintype.card F := by
  have hsub : (C.splitLines ∪ constituentLines C.merged).filter (fun l => l.1 = none) ⊆
      linesInDirection (none : Direction F) := by
    intro l hl
    simpa only [linesInDirection, Finset.mem_filter, Finset.mem_univ, true_and]
      using (Finset.mem_filter.mp hl).2
  have hcard := Finset.card_le_card hsub
  rw [nonregular_in_direction_card C hV hC none, lines_in_direction_card] at hcard
  exact hcard

def splitLabels (g : Direction F) : Finset (Configuration.BlockLabel F) :=
  Finset.univ.image (fun z : Bool × Bool => Sum.inr (Sum.inr ((g, z.1), z.2)))

theorem labels_in_direction_eq (g : Direction F) :
    C.labelsInDirection g =
      ((linesInDirection g \ (C.splitLines ∪ constituentLines C.merged)).image Sum.inl ∪
        {Sum.inr (Sum.inl g)}) ∪ splitLabels g := by
  classical
  ext b
  simp only [Configuration.labelsInDirection, Finset.mem_filter,
    Configuration.blockLabels, Finset.mem_univ, true_and]
  rcases b with l | (d | ⟨⟨d, s⟩, k⟩)
  · rcases l with ⟨d, a⟩
    simp [Configuration.IsBlockLabel, Configuration.blockDirection, linesInDirection,
      splitLabels, and_comm, and_left_comm, Prod.ext_iff]
    constructor <;> rintro ⟨h, hm, hs⟩ <;> subst d <;> exact ⟨rfl, hm, hs⟩
  · simp [Configuration.IsBlockLabel, Configuration.blockDirection, splitLabels]
  · simp [Configuration.IsBlockLabel, Configuration.blockDirection, splitLabels,
      Prod.ext_iff, eq_comm]

omit [Field F] [Fintype F] in

theorem split_labels_card (g : Direction F) : (splitLabels g).card = 4 := by
  rw [splitLabels, Finset.card_image_of_injective]
  · simp
  · intro z w h
    have hp := Sum.inr.inj (Sum.inr.inj h)
    exact Prod.ext (congrArg (fun a : (Direction F × Bool) × Bool => a.1.2) hp)
      (congrArg (fun a : (Direction F × Bool) × Bool => a.2) hp)

theorem labels_in_direction_card (hV : C.Valid) (hC : C.Compatible) (g : Direction F) :
    (C.labelsInDirection g).card = Fintype.card F + 1 := by
  classical
  rw [labels_in_direction_eq C g]
  have hregMerge : Disjoint
      ((linesInDirection g \ (C.splitLines ∪ constituentLines C.merged)).image
        (Sum.inl : Line F → Configuration.BlockLabel F))
      {Sum.inr (Sum.inl g)} := by
    apply Finset.disjoint_left.mpr
    intro b hb hm
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hb
    simp at hm
  have hsplitDisj : Disjoint
      (((linesInDirection g \ (C.splitLines ∪ constituentLines C.merged)).image
        (Sum.inl : Line F → Configuration.BlockLabel F)) ∪ {Sum.inr (Sum.inl g)})
      (splitLabels g) := by
    apply Finset.disjoint_left.mpr
    intro b hb hs
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hs
    rcases Finset.mem_union.mp hb with hr | hm
    · obtain ⟨l, _, heq⟩ := Finset.mem_image.mp hr
      cases heq
    · simp at hm
  rw [Finset.card_union_of_disjoint hsplitDisj, Finset.card_union_of_disjoint hregMerge,
    Finset.card_image_of_injective _ Sum.inl_injective,
    regular_lines_card C hV hC g, Finset.card_singleton, split_labels_card]
  have hfour := four_le_field_card C hV hC
  omega

end BlockCardinality
end Balanced

end OAI
