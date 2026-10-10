import Mathlib
import OAI.Combinatorics.BalancedRyser.Construction.Construction

namespace OAI

namespace Balanced
open scoped _root_.Balanced
namespace ConfigurationStructure

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable (C : Configuration F)

omit [Field F] in

theorem choice_line_mem_split (s : Slot F) : (C.choice s).line ∈ C.splitLines := by
  exact Finset.mem_image.mpr ⟨s, Finset.mem_univ _, rfl⟩

theorem choice_designated_subset (hV : C.Valid) (s : Slot F) :
    designated C.merged (C.choice s) ⊆ linePoints (C.choice s).line := by
  intro p hp
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
  have hOn := (hV.2 s).2.2.2.2.2.1 i
  simpa only [linePoints, Finset.mem_filter, Finset.mem_univ, true_and] using hOn

theorem choice_designated_card (hV : C.Valid) (s : Slot F) :
    (designated C.merged (C.choice s)).card = 4 := by
  rw [designated, Finset.card_image_of_injective _ (hV.2 s).2.2.2.2.1]
  simp

theorem choice_designated_disjoint (hV : C.Valid) (hC : C.Compatible)
    {i j : Slot F} (hij : i ≠ j) :
    Disjoint (designated C.merged (C.choice i)) (designated C.merged (C.choice j)) := by
  apply Finset.disjoint_left.mpr
  intro p hpi hpj
  have hpOn : OnLine p (C.choice i).line := by
    simpa only [linePoints, Finset.mem_filter, Finset.mem_univ, true_and]
      using choice_designated_subset C hV i hpi
  exact hC.1 i j hij p hpj hpOn

theorem designated_slot_unique (hC : C.Compatible) {i j : Slot F} {p : Point F}
    (hpi : p ∈ designated C.merged (C.choice i)) (hpj : OnLine p (C.choice j).line) :
    i = j := by
  by_contra hij
  exact hC.1 j i (Ne.symm hij) p hpi hpj

theorem choice_line_injective (hV : C.Valid) (hC : C.Compatible) :
    Function.Injective (fun s => (C.choice s).line) := by
  intro i j hij
  change (C.choice i).line = (C.choice j).line at hij
  apply designated_slot_unique C hC (p := tuplePoint C.merged (C.choice i).tuple 0)
  · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  · rw [← hij]
    exact (hV.2 i).2.2.2.2.2.1 0

theorem retained_subset_points : C.retained ⊆ C.points := Finset.subset_union_left

theorem core_subset_retained : C.core ⊆ C.retained := by
  intro p hp
  simp only [Configuration.core, Finset.mem_filter, Finset.mem_univ, true_and] at hp
  simp only [Configuration.retained, Finset.mem_filter, Finset.mem_univ, true_and]
  intro l hl
  exact hp l (Finset.mem_union_left _ hl)

theorem core_subset_points : C.core ⊆ C.points :=
  (core_subset_retained C).trans (retained_subset_points C)

theorem designated_subset_points (s : Slot F) :
    designated C.merged (C.choice s) ⊆ C.points := by
  intro p hp
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨s, Finset.mem_univ _, hp⟩)

theorem split_inter_points (hV : C.Valid) (hC : C.Compatible) (s : Slot F) :
    linePoints (C.choice s).line ∩ C.points = designated C.merged (C.choice s) := by
  ext p
  constructor
  · intro hp
    obtain ⟨hpLine, hpX⟩ := Finset.mem_inter.mp hp
    have hpOn : OnLine p (C.choice s).line := by
      simpa only [linePoints, Finset.mem_filter, Finset.mem_univ, true_and] using hpLine
    rcases Finset.mem_union.mp hpX with hpR | hpF
    · have hpAvoid := (Finset.mem_filter.mp hpR).2
      exact False.elim (hpAvoid _ (choice_line_mem_split C s) hpOn)
    · obtain ⟨t, _, hpt⟩ := Finset.mem_biUnion.mp hpF
      have hts := designated_slot_unique C hC hpt hpOn
      simpa only [hts] using hpt
  · intro hp
    exact Finset.mem_inter.mpr
      ⟨choice_designated_subset C hV s hp, designated_subset_points C s hp⟩

theorem split_lines_card (hV : C.Valid) (hC : C.Compatible) :
    C.splitLines.card = 2 * (Fintype.card F + 1) := by
  rw [Configuration.splitLines,
    Finset.card_image_of_injective _ (choice_line_injective C hV hC)]
  simp [Slot, Direction, Nat.mul_comm]

theorem split_multiplicity_eq_slots (hV : C.Valid) (hC : C.Compatible) (p : Point F) :
    C.splitMultiplicity p =
      (Finset.univ.filter (fun s : Slot F => OnLine p (C.choice s).line)).card := by
  unfold Configuration.splitMultiplicity Configuration.splitLinesAt Configuration.splitLines
  rw [Finset.filter_image,
    Finset.card_image_of_injective _ (choice_line_injective C hV hC)]

theorem designated_at_card (hV : C.Valid) (hC : C.Compatible) (p : Point F) :
    (C.designatedAt p).card = 4 * C.splitMultiplicity p := by
  unfold Configuration.designatedAt
  rw [Finset.card_biUnion]
  · rw [Finset.sum_congr rfl (fun s _ => choice_designated_card C hV s)]
    simp only [Finset.sum_const, smul_eq_mul]
    rw [split_multiplicity_eq_slots C hV hC p]
    omega
  · intro i _ j _ hij
    exact choice_designated_disjoint C hV hC hij

theorem split_multiplicity_le_one_of_designated (hC : C.Compatible)
    {s : Slot F} {p : Point F} (hp : p ∈ designated C.merged (C.choice s)) :
    C.splitMultiplicity p ≤ 1 := by
  have hsub : C.splitLinesAt p ⊆ {(C.choice s).line} := by
    intro l hl
    obtain ⟨hlS, hpl⟩ := Finset.mem_filter.mp hl
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hlS
    have hst := designated_slot_unique C hC hp hpl
    simp only [Finset.mem_singleton]
    rw [hst]
  have hc := Finset.card_le_card hsub
  simpa only [Finset.card_singleton, Configuration.splitMultiplicity] using hc

theorem center_not_designated (hC : C.Compatible) {p : Point F}
    (hb : 2 ≤ C.splitMultiplicity p) (s : Slot F) :
    p ∉ designated C.merged (C.choice s) := by
  intro hp
  have hle := split_multiplicity_le_one_of_designated C hC hp
  omega

theorem split_lines_in_direction (hV : C.Valid) (g : Direction F) :
    C.splitLines.filter (fun l => l.1 = g) =
      {(C.choice (g, false)).line, (C.choice (g, true)).line} := by
  ext l
  constructor
  · intro hl
    obtain ⟨hlS, hdir⟩ := Finset.mem_filter.mp hl
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hlS
    have hs : s.1 = g := (hV.2 s).1.symm.trans hdir
    rcases s with ⟨d, b⟩
    dsimp at hs
    subst d
    cases b <;> simp
  · intro hl
    rcases Finset.mem_insert.mp hl with rfl | hl
    · exact Finset.mem_filter.mpr
        ⟨choice_line_mem_split C (g, false), (hV.2 (g, false)).1⟩
    · have heq := Finset.mem_singleton.mp hl
      subst l
      exact Finset.mem_filter.mpr
        ⟨choice_line_mem_split C (g, true), (hV.2 (g, true)).1⟩

theorem split_pair_ne (hV : C.Valid) (hC : C.Compatible) (g : Direction F) :
    (C.choice (g, false)).line ≠ (C.choice (g, true)).line := by
  intro h
  have hslots := choice_line_injective C hV hC h
  have hb := congrArg Prod.snd hslots
  cases hb

theorem split_lines_in_direction_card (hV : C.Valid) (hC : C.Compatible)
    (g : Direction F) : (C.splitLines.filter (fun l => l.1 = g)).card = 2 := by
  rw [split_lines_in_direction C hV g]
  simp [split_pair_ne C hV hC g]

theorem choice_line_ne_constituent (hV : C.Valid) (s : Slot F)
    (d : Direction F) (b : Bool) :
    (C.choice s).line ≠ constituent C.merged d b := by
  intro h
  apply (hV.2 s).2.1
  exact Finset.mem_image.mpr ⟨(d, b), Finset.mem_univ _, h.symm⟩

theorem deleted_lines_in_direction (hV : C.Valid) (g : Direction F) :
    C.deletedLines.filter (fun l => l.1 = g) =
      {(C.choice (g, false)).line, (C.choice (g, true)).line,
        constituent C.merged g true} := by
  ext l
  constructor
  · intro hl
    obtain ⟨hlD, hdir⟩ := Finset.mem_filter.mp hl
    rcases Finset.mem_union.mp hlD with hlS | hlM
    · have hp : l ∈ C.splitLines.filter (fun L => L.1 = g) :=
        Finset.mem_filter.mpr ⟨hlS, hdir⟩
      rw [split_lines_in_direction C hV g] at hp
      rcases Finset.mem_insert.mp hp with h | h
      · simp only [Finset.mem_insert, Finset.mem_singleton]
        exact Or.inl h
      · simp only [Finset.mem_singleton] at h
        simp only [Finset.mem_insert, Finset.mem_singleton]
        exact Or.inr (Or.inl h)
    · obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hlM
      change d = g at hdir
      subst d
      simp
  · intro hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl
    · exact Finset.mem_filter.mpr
        ⟨Finset.mem_union_left _ (choice_line_mem_split C (g, false)),
          (hV.2 (g, false)).1⟩
    · exact Finset.mem_filter.mpr
        ⟨Finset.mem_union_left _ (choice_line_mem_split C (g, true)),
          (hV.2 (g, true)).1⟩
    · exact Finset.mem_filter.mpr
        ⟨Finset.mem_union_right _ (Finset.mem_image.mpr ⟨g, Finset.mem_univ _, rfl⟩), rfl⟩

theorem deleted_lines_in_direction_card (hV : C.Valid) (hC : C.Compatible)
    (g : Direction F) : (C.deletedLines.filter (fun l => l.1 = g)).card = 3 := by
  rw [deleted_lines_in_direction C hV g]
  simp [split_pair_ne C hV hC g,
    choice_line_ne_constituent C hV (g, false) g true,
    choice_line_ne_constituent C hV (g, true) g true]

end ConfigurationStructure
end Balanced

end OAI
