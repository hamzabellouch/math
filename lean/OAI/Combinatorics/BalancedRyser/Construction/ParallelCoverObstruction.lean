import OAI.Combinatorics.BalancedRyser.Construction.CoverObstruction
import OAI.Combinatorics.BalancedRyser.Probability.CoreRepresentatives
import OAI.Combinatorics.BalancedRyser.Probability.ParallelBlockCapacity

namespace OAI

namespace Balanced.Configuration

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable (C : Configuration F)

theorem parallelDesignated_disjoint_parallel_line
    (hvalid : C.Valid) (g : Direction F) (l : Line F)
    (hdir : l.1 = g) (hnot : l ∉ C.splitLines) :
    Disjoint (C.parallelDesignated g) (linePoints l) := by
  apply Finset.disjoint_left.mpr
  intro x hx hxl
  have hline : OnLine x l := (Finset.mem_filter.mp hxl).2
  have hmiss (bit : Bool) (hxd : x ∈ designated C.merged (C.choice (g, bit))) : False := by
    have hs : OnLine x (C.choice (g, bit)).line :=
      (Finset.mem_filter.mp (C.designated_subset_choice_line hvalid _ hxd)).2
    have heq : l = (C.choice (g, bit)).line :=
      eq_of_onLine_same_direction x l (C.choice (g, bit)).line
        (hdir.trans (hvalid.2 (g, bit)).1.symm) hline hs
    exact hnot (Finset.mem_image.mpr ⟨(g, bit), Finset.mem_univ _, heq.symm⟩)
  rcases Finset.mem_union.mp hx with h0 | h1
  · exact hmiss false h0
  · exact hmiss true h1

theorem represented_parallel_block_disjoint
    (hvalid : C.Valid) (g : Direction F) (label : BlockLabel F)
    (hlabel : C.IsBlockLabel label)
    (hrep : C.RepresentedThrough (Sum.inr g) label) :
    Disjoint (C.parallelDesignated g) (C.blockPoints label) := by
  classical
  rcases label with l | d | s
  · have hd : l.1 = g := by simpa [RepresentedThrough, coreRepresentative, ThroughProjective] using hrep
    have hnot : l ∉ C.splitLines := fun hl => hlabel (Finset.mem_union_left _ hl)
    exact (C.parallelDesignated_disjoint_parallel_line hvalid g l hd hnot).mono_right
      Finset.inter_subset_left
  · have hd : d = g := by
      simpa [RepresentedThrough, coreRepresentative, ThroughProjective, constituent] using hrep
    subst d
    have h0 := C.parallelDesignated_disjoint_parallel_line hvalid g
      (constituent C.merged g false) rfl (C.constituent_not_split hvalid g false)
    have h1 := C.parallelDesignated_disjoint_parallel_line hvalid g
      (constituent C.merged g true) rfl (C.constituent_not_split hvalid g true)
    have hm : Disjoint (C.parallelDesignated g) (mergedPoints C.merged g) :=
      Finset.disjoint_union_right.mpr ⟨h0, h1⟩
    exact hm.mono_right Finset.inter_subset_left
  · simp [RepresentedThrough, coreRepresentative] at hrep

theorem parallel_cover_impossible_of_forced_count
    (hvalid : C.Valid) (hcompat : C.Compatible)
    (hq : 3 ≤ Fintype.card F)
    (g : Direction F) (labels : Finset (BlockLabel F))
    (hlabels : ∀ b ∈ labels, C.IsBlockLabel b)
    (hsize : labels.card ≤ Fintype.card F)
    (hforced : Fintype.card F - 3 ≤
      (labels.filter (C.RepresentedThrough (Sum.inr g))).card) :
    ¬ C.points ⊆ labels.biUnion C.blockPoints := by
  classical
  intro hcover
  let pencil := labels.filter (C.RepresentedThrough (Sum.inr g))
  have hpsub : pencil ⊆ labels := Finset.filter_subset _ _
  have hremaining : (labels \ pencil).card ≤ 3 := by
    have hsum := Finset.card_sdiff_add_card_eq_card hpsub
    change Fintype.card F - 3 ≤ pencil.card at hforced
    omega
  have hpencil : ∀ b ∈ pencil, Disjoint (C.parallelDesignated g) (C.blockPoints b) := by
    intro b hb
    exact C.represented_parallel_block_disjoint hvalid g b
      (hlabels b (Finset.mem_filter.mp hb).1) (Finset.mem_filter.mp hb).2
  have htarget : C.parallelDesignated g ⊆ labels.biUnion C.blockPoints :=
    (C.parallelDesignated_subset_points g).trans hcover
  have hres := CoverObstruction.cover_by_remaining_of_forced_disjoint
    (C.parallelDesignated g) labels pencil C.blockPoints htarget hpencil
  exact CoverObstruction.eight_points_not_covered_by_three_pairs
    (C.parallelDesignated g) (labels \ pencil) C.blockPoints
    (C.parallelDesignated_card hvalid hcompat g) hremaining
    (fun b hb => C.parallelDesignated_block_capacity hvalid hcompat g b
      (hlabels b (Finset.mem_sdiff.mp hb).1)) hres

end
end Balanced.Configuration

end OAI
