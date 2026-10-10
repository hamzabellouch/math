import Mathlib.Tactic
import OAI.Combinatorics.BalancedRyser.Construction.Construction

namespace OAI

namespace Balanced.Configuration

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable (C : Configuration F)

lemma choice_line_direction (hV : C.Valid) (s : Slot F) :
    (C.choice s).line.1 = s.1 := (hV.2 s).1

lemma choice_line_not_constituent (hV : C.Valid) (s : Slot F) :
    (C.choice s).line ∉ constituentLines C.merged := (hV.2 s).2.1

lemma tuplePoint_on_choice (hV : C.Valid) (s : Slot F) (i : Fin 4) :
    OnLine (tuplePoint C.merged (C.choice s).tuple i) (C.choice s).line :=
  (hV.2 s).2.2.2.2.2.1 i

omit [Field F] in
lemma constituent_mem_lines (d : Direction F) (s : Bool) :
    constituent C.merged d s ∈ constituentLines C.merged := by
  exact Finset.mem_image.mpr ⟨(d, s), Finset.mem_univ _, rfl⟩

lemma choice_line_injective (hV : C.Valid) (hC : C.Compatible) :
    Function.Injective (fun s => (C.choice s).line) := by
  intro i j hij
  by_contra hne
  let p := tuplePoint C.merged (C.choice j).tuple 0
  have hp : p ∈ designated C.merged (C.choice j) :=
    Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  apply hC.1 i j hne p hp
  simpa [hij] using C.tuplePoint_on_choice hV j 0

lemma constituent_ne_choice (hV : C.Valid) (d : Direction F) (b : Bool) (s : Slot F) :
    constituent C.merged d b ≠ (C.choice s).line := by
  intro h
  exact C.choice_line_not_constituent hV s (h ▸ C.constituent_mem_lines d b)

lemma split_disjoint_constituent (hV : C.Valid) :
    Disjoint C.splitLines (constituentLines C.merged) := by
  rw [Finset.disjoint_left]
  intro l hl hm
  rcases Finset.mem_image.mp hl with ⟨s, _, rfl⟩
  exact C.choice_line_not_constituent hV s hm

lemma split_line_same_direction_iff (hV : C.Valid) (d : Direction F) (l : Line F)
    (hld : l.1 = d) :
    l ∈ C.splitLines ↔ l = (C.choice (d, false)).line ∨ l = (C.choice (d, true)).line := by
  constructor
  · intro hl
    rcases Finset.mem_image.mp hl with ⟨⟨g, b⟩, _, rfl⟩
    have hgd : g = d := (C.choice_line_direction hV (g, b)).symm.trans hld
    subst g
    cases b <;> simp
  · rintro (rfl | rfl) <;> exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩

omit [Field F] in
lemma constituent_line_same_direction_iff (d : Direction F) (l : Line F)
    (hld : l.1 = d) :
    l ∈ constituentLines C.merged ↔
      l = constituent C.merged d false ∨ l = constituent C.merged d true := by
  constructor
  · intro hl
    rcases Finset.mem_image.mp hl with ⟨⟨g, b⟩, _, rfl⟩
    change g = d at hld
    subst g
    cases b <;> simp
  · rintro (rfl | rfl) <;> exact C.constituent_mem_lines _ _

def specialLines (d : Direction F) : Finset (Line F) :=
  {(C.choice (d, false)).line, (C.choice (d, true)).line,
    constituent C.merged d false, constituent C.merged d true}

lemma specialLines_card (hV : C.Valid) (hC : C.Compatible) (d : Direction F) :
    (C.specialLines d).card = 4 := by
  have hsplit : (C.choice (d, false)).line ≠ (C.choice (d, true)).line := by
    intro h
    have := C.choice_line_injective hV hC h
    simp at this
  have hmerge : constituent C.merged d false ≠ constituent C.merged d true := by
    intro h
    exact hV.1 d (congrArg Prod.snd h)
  have h00 := (C.constituent_ne_choice hV d false (d, false)).symm
  have h01 := (C.constituent_ne_choice hV d true (d, false)).symm
  have h10 := (C.constituent_ne_choice hV d false (d, true)).symm
  have h11 := (C.constituent_ne_choice hV d true (d, true)).symm
  simp [specialLines, hsplit, hmerge, h00, h01, h10, h11]

lemma specialLines_subset_direction (hV : C.Valid) (d : Direction F) :
    C.specialLines d ⊆ linesInDirection d := by
  intro l hl
  simp only [specialLines, Finset.mem_insert, Finset.mem_singleton] at hl
  rcases hl with rfl | rfl | rfl | rfl
  all_goals simp [linesInDirection, C.choice_line_direction hV, constituent]

omit [Field F] in
lemma linesInDirection_card (d : Direction F) :
    (linesInDirection d).card = Fintype.card F := by
  have heq : linesInDirection d = Finset.univ.image (fun b : F => (d, b)) := by
    ext l
    rcases l with ⟨g, b⟩
    simp [linesInDirection, Prod.mk.injEq, eq_comm]
  rw [heq, Finset.card_image_of_injective]
  · simp
  · intro b b' h
    exact (Prod.mk.inj h).2

def regularLines (d : Direction F) : Finset (Line F) :=
  (linesInDirection d).filter (fun l => C.IsBlockLabel (Sum.inl l))

lemma regularLines_eq_sdiff (hV : C.Valid) (d : Direction F) :
    C.regularLines d = linesInDirection d \ C.specialLines d := by
  ext l
  simp only [regularLines, Finset.mem_filter, Finset.mem_sdiff]
  by_cases hld : l.1 = d
  · have hs := C.split_line_same_direction_iff hV d l hld
    have hm := C.constituent_line_same_direction_iff d l hld
    simp [linesInDirection, hld, IsBlockLabel, specialLines, hs, hm, and_assoc]
  · simp [linesInDirection, hld]

lemma regularLines_card (hV : C.Valid) (hC : C.Compatible) (d : Direction F) :
    (C.regularLines d).card = Fintype.card F - 4 := by
  rw [C.regularLines_eq_sdiff hV, Finset.card_sdiff_of_subset
    (C.specialLines_subset_direction hV d), C.specialLines_card hV hC,
    linesInDirection_card]

def splitLabels (d : Direction F) : Finset (Slot F × Bool) :=
  Finset.univ.image (fun b : Bool × Bool => ((d, b.1), b.2))

omit [Field F] [Fintype F] in
lemma mem_splitLabels (d : Direction F) (s : Slot F) (b : Bool) :
    (s, b) ∈ splitLabels d ↔ s.1 = d := by
  rcases s with ⟨g, a⟩
  simp [splitLabels, Prod.mk.injEq, eq_comm]

omit [Field F] [Fintype F] in
lemma splitLabels_card (d : Direction F) : (splitLabels d).card = 4 := by
  rw [splitLabels, Finset.card_image_of_injective]
  · simp
  · rintro ⟨a, b⟩ ⟨a', b'⟩ h
    simpa only [Prod.mk.injEq, true_and] using h

omit [Field F] in
lemma labelsInDirection_decomposition (d : Direction F) :
    C.labelsInDirection d = (C.regularLines d).disjSum
      (({d} : Finset (Direction F)).disjSum (splitLabels d)) := by
  ext label
  simp only [labelsInDirection, blockLabels, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases label with line | (direction | ⟨slot, side⟩)
  · simp [regularLines, linesInDirection, blockDirection, and_comm]
  · simp [IsBlockLabel, blockDirection]
  · simp [IsBlockLabel, blockDirection, mem_splitLabels]

theorem labelsInDirection_card (hV : C.Valid) (hC : C.Compatible)
    (hq : 4 ≤ Fintype.card F) (d : Direction F) :
    (C.labelsInDirection d).card = Fintype.card F + 1 := by
  rw [C.labelsInDirection_decomposition]
  simp only [Finset.card_disjSum, Finset.card_singleton, splitLabels_card,
    C.regularLines_card hV hC]
  omega

lemma core_subset_points : C.core ⊆ C.points := by
  intro p hp
  apply Finset.mem_union.mpr
  left
  simp only [core, retained, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
  intro l hl
  exact hp l (Finset.mem_union_left _ hl)

omit [Field F] in
lemma deletedLines_subset_special : C.deletedLines ⊆ C.splitLines ∪ constituentLines C.merged := by
  intro l hl
  rcases Finset.mem_union.mp hl with hs | hm
  · exact Finset.mem_union_left _ hs
  · rcases Finset.mem_image.mp hm with ⟨d, _, rfl⟩
    exact Finset.mem_union_right _ (C.constituent_mem_lines d true)

lemma zero_constituent_not_deleted (hV : C.Valid) (d : Direction F) :
    constituent C.merged d false ∉ C.deletedLines := by
  intro hl
  rcases Finset.mem_union.mp hl with hs | hm
  · exact Finset.disjoint_left.mp (C.split_disjoint_constituent hV) hs
      (C.constituent_mem_lines d false)
  · rcases Finset.mem_image.mp hm with ⟨g, _, heq⟩
    have hgd : g = d := congrArg Prod.fst heq
    subst g
    exact hV.1 d (congrArg Prod.snd heq).symm

lemma core_line_nonempty {ρ : ℝ} {B : ℕ} (hρ : 0 < ρ) (hO : C.Occupancy ρ B)
    (l : Line F) (hl : l ∉ C.deletedLines) : (linePoints l ∩ C.core).Nonempty := by
  have hq : 0 < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  have hpos : 0 < ((linePoints l ∩ C.core).card : ℝ) :=
    lt_of_lt_of_le (mul_pos hρ hq) (hO.2.1 l hl)
  apply Finset.card_pos.mp
  exact_mod_cast hpos

theorem blockPoints_nonempty (hV : C.Valid) {ρ : ℝ} {B : ℕ}
    (hρ : 0 < ρ) (hO : C.Occupancy ρ B)
    (b : BlockLabel F) (hb : C.IsBlockLabel b) : (C.blockPoints b).Nonempty := by
  rcases b with l | (d | ⟨s, b⟩)
  · have hld : l ∉ C.deletedLines := fun h => hb (C.deletedLines_subset_special h)
    rcases C.core_line_nonempty hρ hO l hld with ⟨p, hp⟩
    rcases Finset.mem_inter.mp hp with ⟨hlp, hpc⟩
    exact ⟨p, Finset.mem_inter.mpr ⟨hlp, C.core_subset_points hpc⟩⟩
  · rcases C.core_line_nonempty hρ hO (constituent C.merged d false)
      (C.zero_constituent_not_deleted hV d) with ⟨p, hp⟩
    rcases Finset.mem_inter.mp hp with ⟨hlp, hpc⟩
    exact ⟨p, Finset.mem_inter.mpr
      ⟨Finset.mem_union_left _ hlp, C.core_subset_points hpc⟩⟩
  · cases b <;> simp [blockPoints]

lemma designated_subset_points (s : Slot F) :
    designated C.merged (C.choice s) ⊆ C.points := by
  intro p hp
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨s, Finset.mem_univ _, hp⟩)

lemma blockPoints_subset_points (b : BlockLabel F) : C.blockPoints b ⊆ C.points := by
  rcases b with l | (d | ⟨s, b⟩)
  · exact Finset.inter_subset_right
  · exact Finset.inter_subset_right
  · have hi : ∀ i : Fin 4, tuplePoint C.merged (C.choice s).tuple i ∈ C.points := by
      intro i
      exact C.designated_subset_points s (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    cases b <;> simp [blockPoints, Finset.insert_subset_iff, hi]

lemma core_nonempty (hV : C.Valid) {ρ : ℝ} {B : ℕ}
    (hρ : 0 < ρ) (hO : C.Occupancy ρ B) : C.core.Nonempty := by
  rcases C.core_line_nonempty hρ hO (constituent C.merged none false)
    (C.zero_constituent_not_deleted hV none) with ⟨p, hp⟩
  exact ⟨p, (Finset.mem_inter.mp hp).2⟩

lemma points_nonempty_of_occupancy (hV : C.Valid) {ρ : ℝ} {B : ℕ}
    (hρ : 0 < ρ) (hO : C.Occupancy ρ B) : C.points.Nonempty := by
  rcases C.core_nonempty hV hρ hO with ⟨p, hp⟩
  exact ⟨p, C.core_subset_points hp⟩

end
end Balanced.Configuration

end OAI
