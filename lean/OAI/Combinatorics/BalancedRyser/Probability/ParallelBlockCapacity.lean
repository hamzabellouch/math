import OAI.Combinatorics.BalancedRyser.Probability.BlockCapacity

namespace OAI

namespace Balanced.Configuration

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable (C : Configuration F)

def parallelDesignated (g : Direction F) : Finset (Point F) :=
  designated C.merged (C.choice (g, false)) ∪ designated C.merged (C.choice (g, true))

theorem designated_subset_choice_line (hvalid : C.Valid) (s : Slot F) :
    designated C.merged (C.choice s) ⊆ linePoints (C.choice s).line := by
  intro x hx
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
  rcases hvalid.2 s with ⟨_, _, _, _, _, hpoints, _, _, _⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpoints i⟩

theorem designated_card_four (hvalid : C.Valid) (s : Slot F) :
    (designated C.merged (C.choice s)).card = 4 := by
  rcases hvalid.2 s with ⟨_, _, _, _, hinj, _, _, _, _⟩
  simpa [designated] using Finset.card_image_of_injective
    (Finset.univ : Finset (Fin 4)) hinj

theorem designated_disjoint_of_slots_ne (hvalid : C.Valid) (hcompat : C.Compatible)
    (s t : Slot F) (hne : s ≠ t) :
    Disjoint (designated C.merged (C.choice s)) (designated C.merged (C.choice t)) := by
  apply Finset.disjoint_left.mpr
  intro x hxs hxt
  exact hcompat.1 s t hne x hxt
    (Finset.mem_filter.mp (C.designated_subset_choice_line hvalid s hxs)).2

theorem parallelDesignated_card (hvalid : C.Valid) (hcompat : C.Compatible)
    (g : Direction F) : (C.parallelDesignated g).card = 8 := by
  rw [parallelDesignated, Finset.card_union_of_disjoint
    (C.designated_disjoint_of_slots_ne hvalid hcompat (g, false) (g, true) (by simp))]
  rw [C.designated_card_four hvalid, C.designated_card_four hvalid]

theorem designated_inter_line_card_le_one (hvalid : C.Valid)
    (s : Slot F) (l : Line F) (hne : (C.choice s).line ≠ l) :
    (designated C.merged (C.choice s) ∩ linePoints l).card ≤ 1 := by
  apply (Finset.card_le_card ?_).trans (linePoints_inter_card_le_one (C.choice s).line l hne)
  intro x hx
  exact Finset.mem_inter.mpr
    ⟨C.designated_subset_choice_line hvalid s (Finset.mem_inter.mp hx).1,
      (Finset.mem_inter.mp hx).2⟩

theorem designated_inter_merged_card_le_two (hvalid : C.Valid)
    (s : Slot F) (d : Direction F) :
    (designated C.merged (C.choice s) ∩ mergedPoints C.merged d).card ≤ 2 := by
  have hne (bit : Bool) : (C.choice s).line ≠ constituent C.merged d bit := by
    intro heq
    apply (hvalid.2 s).2.1
    rw [heq]
    exact Finset.mem_image.mpr ⟨(d, bit), Finset.mem_univ _, rfl⟩
  rw [mergedPoints, Finset.inter_union_distrib_left]
  exact (Finset.card_union_le _ _).trans (by
    have h0 := C.designated_inter_line_card_le_one hvalid s _ (hne false)
    have h1 := C.designated_inter_line_card_le_one hvalid s _ (hne true)
    omega)

theorem parallelDesignated_inter_merged_card_le_two
    (hvalid : C.Valid) (hcompat : C.Compatible) (g d : Direction F) :
    (C.parallelDesignated g ∩ mergedPoints C.merged d).card ≤ 2 := by
  have h0 := C.designated_inter_merged_card_le_two hvalid (g, false) d
  have h1 := C.designated_inter_merged_card_le_two hvalid (g, true) d
  have hc0 := hcompat.2.2 (g, false) (g, true) (by simp) rfl d
  have hc1 := hcompat.2.2 (g, true) (g, false) (by simp) rfl d
  rw [parallelDesignated, Finset.union_inter_distrib_right]
  exact (Finset.card_union_le _ _).trans (by omega)

theorem parallelDesignated_inter_regular_card_le_two
    (hvalid : C.Valid) (g : Direction F) (l : Line F)
    (hlabel : C.IsBlockLabel (Sum.inl l)) :
    (C.parallelDesignated g ∩ linePoints l).card ≤ 2 := by
  have hne (bit : Bool) : (C.choice (g, bit)).line ≠ l := by
    intro heq
    apply hlabel
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨(g, bit), Finset.mem_univ _, heq⟩
  rw [parallelDesignated, Finset.union_inter_distrib_right]
  exact (Finset.card_union_le _ _).trans (by
    have h0 := C.designated_inter_line_card_le_one hvalid (g, false) l (hne false)
    have h1 := C.designated_inter_line_card_le_one hvalid (g, true) l (hne true)
    omega)

theorem parallelDesignated_block_capacity
    (hvalid : C.Valid) (hcompat : C.Compatible) (g : Direction F)
    (label : BlockLabel F) (hlabel : C.IsBlockLabel label) :
    (C.parallelDesignated g ∩ C.blockPoints label).card ≤ 2 := by
  classical
  rcases label with l | d | ⟨s, bit⟩
  · have hsub : C.parallelDesignated g ∩ C.blockPoints (Sum.inl l) ⊆
        C.parallelDesignated g ∩ linePoints l := by
      intro x hx
      exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1,
        (Finset.mem_inter.mp (Finset.mem_inter.mp hx).2).1⟩
    exact (Finset.card_le_card hsub).trans
      (C.parallelDesignated_inter_regular_card_le_two hvalid g l hlabel)
  · have hsub : C.parallelDesignated g ∩ C.blockPoints (Sum.inr (Sum.inl d)) ⊆
        C.parallelDesignated g ∩ mergedPoints C.merged d := by
      intro x hx
      exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1,
        (Finset.mem_inter.mp (Finset.mem_inter.mp hx).2).1⟩
    exact (Finset.card_le_card hsub).trans
      (C.parallelDesignated_inter_merged_card_le_two hvalid hcompat g d)
  · apply (Finset.card_le_card Finset.inter_subset_right).trans
    cases bit <;> exact Finset.card_le_two

theorem parallelDesignated_subset_points (g : Direction F) :
    C.parallelDesignated g ⊆ C.points := by
  intro x hx
  apply Finset.mem_union_right
  rcases Finset.mem_union.mp hx with h0 | h1
  · exact Finset.mem_biUnion.mpr ⟨(g, false), Finset.mem_univ _, h0⟩
  · exact Finset.mem_biUnion.mpr ⟨(g, true), Finset.mem_univ _, h1⟩

end
end Balanced.Configuration

end OAI
