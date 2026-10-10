import OAI.GameTheory.SnakyConditional.Templates.Level29Part04
import OAI.GameTheory.SnakyConditional.Templates.Level29Part06
import OAI.GameTheory.SnakyConditional.Templates.Level36Part01

namespace OAI

namespace SnakyConditional
def nearBlock : Finset Cell := {(-1,-1),(-1,0),(-1,1),(0,-1),(0,0),(0,1),(1,-1),(1,0),(1,1)}
def nearPoint (i : Fin 8) : Cell := ![(-1,-1),(-1,0),(-1,1),(0,-1),(0,1),(1,-1),(1,0),(1,1)] i
theorem nearPoint_cover : nearBlock.erase (0, 0) = Finset.univ.image nearPoint := by decide
def distantEnvelopes : Fin 24 → Finset Cell := ![(placedSet 0 (orient 0 (1, 0)) envelope_557), (placedSet 1 (orient 1 (1, 0)) envelope_557), (placedSet 2 (orient 2 (1, 0)) envelope_557), (placedSet 3 (orient 3 (1, 0)) envelope_557), (placedSet 4 (orient 4 (1, 0)) envelope_557), (placedSet 5 (orient 5 (1, 0)) envelope_557), (placedSet 6 (orient 6 (1, 0)) envelope_557), (placedSet 7 (orient 7 (1, 0)) envelope_557), (placedSet 0 (orient 0 (1, 0)) envelope_595), (placedSet 1 (orient 1 (1, 0)) envelope_595), (placedSet 2 (orient 2 (1, 0)) envelope_595), (placedSet 3 (orient 3 (1, 0)) envelope_595), (placedSet 4 (orient 4 (1, 0)) envelope_595), (placedSet 5 (orient 5 (1, 0)) envelope_595), (placedSet 6 (orient 6 (1, 0)) envelope_595), (placedSet 7 (orient 7 (1, 0)) envelope_595), (placedSet 0 (orient 0 (1, 0)) envelope_603), (placedSet 1 (orient 1 (1, 0)) envelope_603), (placedSet 2 (orient 2 (1, 0)) envelope_603), (placedSet 3 (orient 3 (1, 0)) envelope_603), (placedSet 4 (orient 4 (1, 0)) envelope_603), (placedSet 5 (orient 5 (1, 0)) envelope_603), (placedSet 6 (orient 6 (1, 0)) envelope_603), (placedSet 7 (orient 7 (1, 0)) envelope_603)]
theorem distant_required_0 : placedSet 0 (orient 0 (1, 0)) required_557 = {(0, 0)} := by decide
theorem distant_required_1 : placedSet 1 (orient 1 (1, 0)) required_557 = {(0, 0)} := by decide
theorem distant_required_2 : placedSet 2 (orient 2 (1, 0)) required_557 = {(0, 0)} := by decide
theorem distant_required_3 : placedSet 3 (orient 3 (1, 0)) required_557 = {(0, 0)} := by decide
theorem distant_required_4 : placedSet 4 (orient 4 (1, 0)) required_557 = {(0, 0)} := by decide
theorem distant_required_5 : placedSet 5 (orient 5 (1, 0)) required_557 = {(0, 0)} := by decide
theorem distant_required_6 : placedSet 6 (orient 6 (1, 0)) required_557 = {(0, 0)} := by decide
theorem distant_required_7 : placedSet 7 (orient 7 (1, 0)) required_557 = {(0, 0)} := by decide
theorem distant_required_8 : placedSet 0 (orient 0 (1, 0)) required_595 = {(0, 0)} := by decide
theorem distant_required_9 : placedSet 1 (orient 1 (1, 0)) required_595 = {(0, 0)} := by decide
theorem distant_required_10 : placedSet 2 (orient 2 (1, 0)) required_595 = {(0, 0)} := by decide
theorem distant_required_11 : placedSet 3 (orient 3 (1, 0)) required_595 = {(0, 0)} := by decide
theorem distant_required_12 : placedSet 4 (orient 4 (1, 0)) required_595 = {(0, 0)} := by decide
theorem distant_required_13 : placedSet 5 (orient 5 (1, 0)) required_595 = {(0, 0)} := by decide
theorem distant_required_14 : placedSet 6 (orient 6 (1, 0)) required_595 = {(0, 0)} := by decide
theorem distant_required_15 : placedSet 7 (orient 7 (1, 0)) required_595 = {(0, 0)} := by decide
theorem distant_required_16 : placedSet 0 (orient 0 (1, 0)) required_603 = {(0, 0)} := by decide
theorem distant_required_17 : placedSet 1 (orient 1 (1, 0)) required_603 = {(0, 0)} := by decide
theorem distant_required_18 : placedSet 2 (orient 2 (1, 0)) required_603 = {(0, 0)} := by decide
theorem distant_required_19 : placedSet 3 (orient 3 (1, 0)) required_603 = {(0, 0)} := by decide
theorem distant_required_20 : placedSet 4 (orient 4 (1, 0)) required_603 = {(0, 0)} := by decide
theorem distant_required_21 : placedSet 5 (orient 5 (1, 0)) required_603 = {(0, 0)} := by decide
theorem distant_required_22 : placedSet 6 (orient 6 (1, 0)) required_603 = {(0, 0)} := by decide
theorem distant_required_23 : placedSet 7 (orient 7 (1, 0)) required_603 = {(0, 0)} := by decide
theorem distant_works : ∀ j, Template HasSnaky 27 {(0, 0)} (distantEnvelopes j) := by
  intro j
  fin_cases j
  · change Template HasSnaky 27 {(0, 0)} (placedSet 0 (orient 0 (1, 0)) envelope_557)
    simpa only [distant_required_0] using
      (placed_template_map row_works_557 0 (orient 0 (1, 0))).mono (by decide : 19 ≤ 27)
  · change Template HasSnaky 27 {(0, 0)} (placedSet 1 (orient 1 (1, 0)) envelope_557)
    simpa only [distant_required_1] using
      (placed_template_map row_works_557 1 (orient 1 (1, 0))).mono (by decide : 19 ≤ 27)
  · change Template HasSnaky 27 {(0, 0)} (placedSet 2 (orient 2 (1, 0)) envelope_557)
    simpa only [distant_required_2] using
      (placed_template_map row_works_557 2 (orient 2 (1, 0))).mono (by decide : 19 ≤ 27)
  · change Template HasSnaky 27 {(0, 0)} (placedSet 3 (orient 3 (1, 0)) envelope_557)
    simpa only [distant_required_3] using
      (placed_template_map row_works_557 3 (orient 3 (1, 0))).mono (by decide : 19 ≤ 27)
  · change Template HasSnaky 27 {(0, 0)} (placedSet 4 (orient 4 (1, 0)) envelope_557)
    simpa only [distant_required_4] using
      (placed_template_map row_works_557 4 (orient 4 (1, 0))).mono (by decide : 19 ≤ 27)
  · change Template HasSnaky 27 {(0, 0)} (placedSet 5 (orient 5 (1, 0)) envelope_557)
    simpa only [distant_required_5] using
      (placed_template_map row_works_557 5 (orient 5 (1, 0))).mono (by decide : 19 ≤ 27)
  · change Template HasSnaky 27 {(0, 0)} (placedSet 6 (orient 6 (1, 0)) envelope_557)
    simpa only [distant_required_6] using
      (placed_template_map row_works_557 6 (orient 6 (1, 0))).mono (by decide : 19 ≤ 27)
  · change Template HasSnaky 27 {(0, 0)} (placedSet 7 (orient 7 (1, 0)) envelope_557)
    simpa only [distant_required_7] using
      (placed_template_map row_works_557 7 (orient 7 (1, 0))).mono (by decide : 19 ≤ 27)
  · change Template HasSnaky 27 {(0, 0)} (placedSet 0 (orient 0 (1, 0)) envelope_595)
    simpa only [distant_required_8] using
      (placed_template_map row_works_595 0 (orient 0 (1, 0))).mono (by decide : 27 ≤ 27)
  · change Template HasSnaky 27 {(0, 0)} (placedSet 1 (orient 1 (1, 0)) envelope_595)
    simpa only [distant_required_9] using
      (placed_template_map row_works_595 1 (orient 1 (1, 0))).mono (by decide : 27 ≤ 27)
  · change Template HasSnaky 27 {(0, 0)} (placedSet 2 (orient 2 (1, 0)) envelope_595)
    simpa only [distant_required_10] using
      (placed_template_map row_works_595 2 (orient 2 (1, 0))).mono (by decide : 27 ≤ 27)
  · change Template HasSnaky 27 {(0, 0)} (placedSet 3 (orient 3 (1, 0)) envelope_595)
    simpa only [distant_required_11] using
      (placed_template_map row_works_595 3 (orient 3 (1, 0))).mono (by decide : 27 ≤ 27)
  · change Template HasSnaky 27 {(0, 0)} (placedSet 4 (orient 4 (1, 0)) envelope_595)
    simpa only [distant_required_12] using
      (placed_template_map row_works_595 4 (orient 4 (1, 0))).mono (by decide : 27 ≤ 27)
  · change Template HasSnaky 27 {(0, 0)} (placedSet 5 (orient 5 (1, 0)) envelope_595)
    simpa only [distant_required_13] using
      (placed_template_map row_works_595 5 (orient 5 (1, 0))).mono (by decide : 27 ≤ 27)
  · change Template HasSnaky 27 {(0, 0)} (placedSet 6 (orient 6 (1, 0)) envelope_595)
    simpa only [distant_required_14] using
      (placed_template_map row_works_595 6 (orient 6 (1, 0))).mono (by decide : 27 ≤ 27)
  · change Template HasSnaky 27 {(0, 0)} (placedSet 7 (orient 7 (1, 0)) envelope_595)
    simpa only [distant_required_15] using
      (placed_template_map row_works_595 7 (orient 7 (1, 0))).mono (by decide : 27 ≤ 27)
  · change Template HasSnaky 27 {(0, 0)} (placedSet 0 (orient 0 (1, 0)) envelope_603)
    simpa only [distant_required_16] using
      (placed_template_map row_works_603 0 (orient 0 (1, 0))).mono (by decide : 27 ≤ 27)
  · change Template HasSnaky 27 {(0, 0)} (placedSet 1 (orient 1 (1, 0)) envelope_603)
    simpa only [distant_required_17] using
      (placed_template_map row_works_603 1 (orient 1 (1, 0))).mono (by decide : 27 ≤ 27)
  · change Template HasSnaky 27 {(0, 0)} (placedSet 2 (orient 2 (1, 0)) envelope_603)
    simpa only [distant_required_18] using
      (placed_template_map row_works_603 2 (orient 2 (1, 0))).mono (by decide : 27 ≤ 27)
  · change Template HasSnaky 27 {(0, 0)} (placedSet 3 (orient 3 (1, 0)) envelope_603)
    simpa only [distant_required_19] using
      (placed_template_map row_works_603 3 (orient 3 (1, 0))).mono (by decide : 27 ≤ 27)
  · change Template HasSnaky 27 {(0, 0)} (placedSet 4 (orient 4 (1, 0)) envelope_603)
    simpa only [distant_required_20] using
      (placed_template_map row_works_603 4 (orient 4 (1, 0))).mono (by decide : 27 ≤ 27)
  · change Template HasSnaky 27 {(0, 0)} (placedSet 5 (orient 5 (1, 0)) envelope_603)
    simpa only [distant_required_21] using
      (placed_template_map row_works_603 5 (orient 5 (1, 0))).mono (by decide : 27 ≤ 27)
  · change Template HasSnaky 27 {(0, 0)} (placedSet 6 (orient 6 (1, 0)) envelope_603)
    simpa only [distant_required_22] using
      (placed_template_map row_works_603 6 (orient 6 (1, 0))).mono (by decide : 27 ≤ 27)
  · change Template HasSnaky 27 {(0, 0)} (placedSet 7 (orient 7 (1, 0)) envelope_603)
    simpa only [distant_required_23] using
      (placed_template_map row_works_603 7 (orient 7 (1, 0))).mono (by decide : 27 ≤ 27)
theorem Internal.SnakyOpening.opening_commonEnvelope_subset_of_escape {n : ℕ}
    (D : Fin (n + 1) → Finset Cell) (H : Finset Cell)
    (h : ∀ q ∈ D 0, q ∈ H ∨ ∃ j, q ∉ D j) :
    commonEnvelope D ⊆ H := by
  intro q hq
  have hq' : q ∈ D 0 ∧ ∀ j, q ∈ D j := Finset.mem_filter.mp hq
  rcases h q hq'.1 with howned | ⟨j, hmissing⟩
  · exact howned
  · exact False.elim (hmissing (hq'.2 j))
theorem Internal.SnakyOpening.opening_commonEnvelope_subset_of_placed_escape {n : ℕ}
    (D : Fin (n + 1) → Finset Cell) (H A : Finset Cell)
    (r : Fin 8) (t : Cell) (h0 : D 0 = placedSet r t A)
    (h : ∀ p ∈ A,
      placement r t p ∈ H ∨ ∃ j, placement r t p ∉ D j) :
    commonEnvelope D ⊆ H := by
  apply Internal.SnakyOpening.opening_commonEnvelope_subset_of_escape D H
  intro q hq
  rw [h0] at hq
  obtain ⟨p, hp, hpq⟩ := Finset.mem_map.mp hq
  change placement r t p = q at hpq
  rw [← hpq]
  exact h p hp
theorem Internal.SnakyOpening.opening_escape_point_000 :
    placement 0 (orient 0 (1, 0)) (-6, -1) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (-6, -1) ∉ distantEnvelopes j := by
  exact Or.inr ⟨9, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_001 :
    placement 0 (orient 0 (1, 0)) (-6, 0) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (-6, 0) ∉ distantEnvelopes j := by
  exact Or.inr ⟨16, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_002 :
    placement 0 (orient 0 (1, 0)) (-6, 1) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (-6, 1) ∉ distantEnvelopes j := by
  exact Or.inr ⟨13, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_003 :
    placement 0 (orient 0 (1, 0)) (-6, 3) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (-6, 3) ∉ distantEnvelopes j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_004 :
    placement 0 (orient 0 (1, 0)) (-6, 4) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (-6, 4) ∉ distantEnvelopes j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_005 :
    placement 0 (orient 0 (1, 0)) (-5, -1) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (-5, -1) ∉ distantEnvelopes j := by
  exact Or.inr ⟨9, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_006 :
    placement 0 (orient 0 (1, 0)) (-5, 0) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (-5, 0) ∉ distantEnvelopes j := by
  exact Or.inr ⟨16, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_007 :
    placement 0 (orient 0 (1, 0)) (-5, 1) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (-5, 1) ∉ distantEnvelopes j := by
  exact Or.inr ⟨13, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_008 :
    placement 0 (orient 0 (1, 0)) (-5, 2) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (-5, 2) ∉ distantEnvelopes j := by
  exact Or.inr ⟨2, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_009 :
    placement 0 (orient 0 (1, 0)) (-5, 3) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (-5, 3) ∉ distantEnvelopes j := by
  exact Or.inr ⟨2, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_010 :
    placement 0 (orient 0 (1, 0)) (-5, 4) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (-5, 4) ∉ distantEnvelopes j := by
  exact Or.inr ⟨2, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_011 :
    placement 0 (orient 0 (1, 0)) (-4, -1) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (-4, -1) ∉ distantEnvelopes j := by
  exact Or.inr ⟨9, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_012 :
    placement 0 (orient 0 (1, 0)) (-4, 0) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (-4, 0) ∉ distantEnvelopes j := by
  exact Or.inr ⟨16, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_013 :
    placement 0 (orient 0 (1, 0)) (-4, 1) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (-4, 1) ∉ distantEnvelopes j := by
  exact Or.inr ⟨13, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_014 :
    placement 0 (orient 0 (1, 0)) (-4, 2) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (-4, 2) ∉ distantEnvelopes j := by
  exact Or.inr ⟨2, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_015 :
    placement 0 (orient 0 (1, 0)) (-4, 3) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (-4, 3) ∉ distantEnvelopes j := by
  exact Or.inr ⟨2, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_016 :
    placement 0 (orient 0 (1, 0)) (-4, 4) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (-4, 4) ∉ distantEnvelopes j := by
  exact Or.inr ⟨2, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_017 :
    placement 0 (orient 0 (1, 0)) (-4, 5) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (-4, 5) ∉ distantEnvelopes j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_018 :
    placement 0 (orient 0 (1, 0)) (-4, 6) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (-4, 6) ∉ distantEnvelopes j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_019 :
    placement 0 (orient 0 (1, 0)) (-3, -1) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (-3, -1) ∉ distantEnvelopes j := by
  exact Or.inr ⟨9, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_020 :
    placement 0 (orient 0 (1, 0)) (-3, 0) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (-3, 0) ∉ distantEnvelopes j := by
  exact Or.inr ⟨16, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_021 :
    placement 0 (orient 0 (1, 0)) (-3, 1) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (-3, 1) ∉ distantEnvelopes j := by
  exact Or.inr ⟨13, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_022 :
    placement 0 (orient 0 (1, 0)) (-3, 2) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (-3, 2) ∉ distantEnvelopes j := by
  exact Or.inr ⟨2, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_023 :
    placement 0 (orient 0 (1, 0)) (-3, 3) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (-3, 3) ∉ distantEnvelopes j := by
  exact Or.inr ⟨2, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_024 :
    placement 0 (orient 0 (1, 0)) (-3, 4) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (-3, 4) ∉ distantEnvelopes j := by
  exact Or.inr ⟨2, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_025 :
    placement 0 (orient 0 (1, 0)) (-3, 5) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (-3, 5) ∉ distantEnvelopes j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_026 :
    placement 0 (orient 0 (1, 0)) (-3, 6) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (-3, 6) ∉ distantEnvelopes j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_027 :
    placement 0 (orient 0 (1, 0)) (-3, 7) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (-3, 7) ∉ distantEnvelopes j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_028 :
    placement 0 (orient 0 (1, 0)) (-3, 8) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (-3, 8) ∉ distantEnvelopes j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_029 :
    placement 0 (orient 0 (1, 0)) (-2, -5) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (-2, -5) ∉ distantEnvelopes j := by
  exact Or.inr ⟨8, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_030 :
    placement 0 (orient 0 (1, 0)) (-2, -4) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (-2, -4) ∉ distantEnvelopes j := by
  exact Or.inr ⟨8, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_031 :
    placement 0 (orient 0 (1, 0)) (-2, -3) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (-2, -3) ∉ distantEnvelopes j := by
  exact Or.inr ⟨8, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_032 :
    placement 0 (orient 0 (1, 0)) (-2, -2) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (-2, -2) ∉ distantEnvelopes j := by
  exact Or.inr ⟨8, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_033 :
    placement 0 (orient 0 (1, 0)) (-2, -1) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (-2, -1) ∉ distantEnvelopes j := by
  exact Or.inl (by decide)
theorem Internal.SnakyOpening.opening_escape_point_034 :
    placement 0 (orient 0 (1, 0)) (-2, 0) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (-2, 0) ∉ distantEnvelopes j := by
  exact Or.inl (by decide)
theorem Internal.SnakyOpening.opening_escape_point_035 :
    placement 0 (orient 0 (1, 0)) (-2, 1) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (-2, 1) ∉ distantEnvelopes j := by
  exact Or.inl (by decide)
theorem Internal.SnakyOpening.opening_escape_point_036 :
    placement 0 (orient 0 (1, 0)) (-2, 2) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (-2, 2) ∉ distantEnvelopes j := by
  exact Or.inr ⟨10, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_037 :
    placement 0 (orient 0 (1, 0)) (-2, 3) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (-2, 3) ∉ distantEnvelopes j := by
  exact Or.inr ⟨10, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_038 :
    placement 0 (orient 0 (1, 0)) (-2, 4) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (-2, 4) ∉ distantEnvelopes j := by
  exact Or.inr ⟨10, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_039 :
    placement 0 (orient 0 (1, 0)) (-2, 5) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (-2, 5) ∉ distantEnvelopes j := by
  exact Or.inr ⟨10, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_040 :
    placement 0 (orient 0 (1, 0)) (-2, 6) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (-2, 6) ∉ distantEnvelopes j := by
  exact Or.inr ⟨2, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_041 :
    placement 0 (orient 0 (1, 0)) (-2, 7) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (-2, 7) ∉ distantEnvelopes j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_042 :
    placement 0 (orient 0 (1, 0)) (-1, -5) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (-1, -5) ∉ distantEnvelopes j := by
  exact Or.inr ⟨17, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_043 :
    placement 0 (orient 0 (1, 0)) (-1, -4) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (-1, -4) ∉ distantEnvelopes j := by
  exact Or.inr ⟨17, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_044 :
    placement 0 (orient 0 (1, 0)) (-1, -3) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (-1, -3) ∉ distantEnvelopes j := by
  exact Or.inr ⟨17, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_045 :
    placement 0 (orient 0 (1, 0)) (-1, -2) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (-1, -2) ∉ distantEnvelopes j := by
  exact Or.inr ⟨17, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_046 :
    placement 0 (orient 0 (1, 0)) (-1, -1) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (-1, -1) ∉ distantEnvelopes j := by
  exact Or.inl (by decide)
theorem Internal.SnakyOpening.opening_escape_point_047 :
    placement 0 (orient 0 (1, 0)) (-1, 0) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (-1, 0) ∉ distantEnvelopes j := by
  exact Or.inl (by decide)
theorem Internal.SnakyOpening.opening_escape_point_048 :
    placement 0 (orient 0 (1, 0)) (-1, 1) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (-1, 1) ∉ distantEnvelopes j := by
  exact Or.inl (by decide)
theorem Internal.SnakyOpening.opening_escape_point_049 :
    placement 0 (orient 0 (1, 0)) (-1, 2) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (-1, 2) ∉ distantEnvelopes j := by
  exact Or.inr ⟨21, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_050 :
    placement 0 (orient 0 (1, 0)) (-1, 3) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (-1, 3) ∉ distantEnvelopes j := by
  exact Or.inr ⟨21, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_051 :
    placement 0 (orient 0 (1, 0)) (-1, 4) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (-1, 4) ∉ distantEnvelopes j := by
  exact Or.inr ⟨21, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_052 :
    placement 0 (orient 0 (1, 0)) (-1, 5) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (-1, 5) ∉ distantEnvelopes j := by
  exact Or.inr ⟨21, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_053 :
    placement 0 (orient 0 (1, 0)) (-1, 6) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (-1, 6) ∉ distantEnvelopes j := by
  exact Or.inr ⟨2, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_054 :
    placement 0 (orient 0 (1, 0)) (-1, 7) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (-1, 7) ∉ distantEnvelopes j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_055 :
    placement 0 (orient 0 (1, 0)) (-1, 8) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (-1, 8) ∉ distantEnvelopes j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_056 :
    placement 0 (orient 0 (1, 0)) (0, -5) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (0, -5) ∉ distantEnvelopes j := by
  exact Or.inr ⟨12, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_057 :
    placement 0 (orient 0 (1, 0)) (0, -4) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (0, -4) ∉ distantEnvelopes j := by
  exact Or.inr ⟨12, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_058 :
    placement 0 (orient 0 (1, 0)) (0, -3) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (0, -3) ∉ distantEnvelopes j := by
  exact Or.inr ⟨12, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_059 :
    placement 0 (orient 0 (1, 0)) (0, -2) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (0, -2) ∉ distantEnvelopes j := by
  exact Or.inr ⟨12, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_060 :
    placement 0 (orient 0 (1, 0)) (0, -1) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (0, -1) ∉ distantEnvelopes j := by
  exact Or.inl (by decide)
theorem Internal.SnakyOpening.opening_escape_point_061 :
    placement 0 (orient 0 (1, 0)) (0, 0) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (0, 0) ∉ distantEnvelopes j := by
  exact Or.inl (by decide)
theorem Internal.SnakyOpening.opening_escape_point_062 :
    placement 0 (orient 0 (1, 0)) (0, 1) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (0, 1) ∉ distantEnvelopes j := by
  exact Or.inl (by decide)
theorem Internal.SnakyOpening.opening_escape_point_063 :
    placement 0 (orient 0 (1, 0)) (0, 2) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (0, 2) ∉ distantEnvelopes j := by
  exact Or.inr ⟨14, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_064 :
    placement 0 (orient 0 (1, 0)) (0, 3) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (0, 3) ∉ distantEnvelopes j := by
  exact Or.inr ⟨14, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_065 :
    placement 0 (orient 0 (1, 0)) (0, 4) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (0, 4) ∉ distantEnvelopes j := by
  exact Or.inr ⟨14, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_066 :
    placement 0 (orient 0 (1, 0)) (0, 5) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (0, 5) ∉ distantEnvelopes j := by
  exact Or.inr ⟨14, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_067 :
    placement 0 (orient 0 (1, 0)) (0, 6) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (0, 6) ∉ distantEnvelopes j := by
  exact Or.inr ⟨2, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_068 :
    placement 0 (orient 0 (1, 0)) (0, 7) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (0, 7) ∉ distantEnvelopes j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_069 :
    placement 0 (orient 0 (1, 0)) (0, 8) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (0, 8) ∉ distantEnvelopes j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_070 :
    placement 0 (orient 0 (1, 0)) (1, -5) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (1, -5) ∉ distantEnvelopes j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_071 :
    placement 0 (orient 0 (1, 0)) (1, -4) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (1, -4) ∉ distantEnvelopes j := by
  exact Or.inr ⟨3, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_072 :
    placement 0 (orient 0 (1, 0)) (1, -3) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (1, -3) ∉ distantEnvelopes j := by
  exact Or.inr ⟨3, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_073 :
    placement 0 (orient 0 (1, 0)) (1, -2) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (1, -2) ∉ distantEnvelopes j := by
  exact Or.inr ⟨3, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_074 :
    placement 0 (orient 0 (1, 0)) (1, -1) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (1, -1) ∉ distantEnvelopes j := by
  exact Or.inr ⟨11, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_075 :
    placement 0 (orient 0 (1, 0)) (1, 0) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (1, 0) ∉ distantEnvelopes j := by
  exact Or.inr ⟨20, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_076 :
    placement 0 (orient 0 (1, 0)) (1, 1) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (1, 1) ∉ distantEnvelopes j := by
  exact Or.inr ⟨15, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_077 :
    placement 0 (orient 0 (1, 0)) (1, 2) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (1, 2) ∉ distantEnvelopes j := by
  exact Or.inr ⟨6, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_078 :
    placement 0 (orient 0 (1, 0)) (1, 3) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (1, 3) ∉ distantEnvelopes j := by
  exact Or.inr ⟨6, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_079 :
    placement 0 (orient 0 (1, 0)) (1, 4) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (1, 4) ∉ distantEnvelopes j := by
  exact Or.inr ⟨6, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_080 :
    placement 0 (orient 0 (1, 0)) (1, 5) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (1, 5) ∉ distantEnvelopes j := by
  exact Or.inr ⟨3, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_081 :
    placement 0 (orient 0 (1, 0)) (1, 6) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (1, 6) ∉ distantEnvelopes j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_082 :
    placement 0 (orient 0 (1, 0)) (1, 7) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (1, 7) ∉ distantEnvelopes j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_083 :
    placement 0 (orient 0 (1, 0)) (2, -4) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (2, -4) ∉ distantEnvelopes j := by
  exact Or.inr ⟨3, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_084 :
    placement 0 (orient 0 (1, 0)) (2, -3) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (2, -3) ∉ distantEnvelopes j := by
  exact Or.inr ⟨3, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_085 :
    placement 0 (orient 0 (1, 0)) (2, -2) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (2, -2) ∉ distantEnvelopes j := by
  exact Or.inr ⟨3, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_086 :
    placement 0 (orient 0 (1, 0)) (2, -1) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (2, -1) ∉ distantEnvelopes j := by
  exact Or.inr ⟨11, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_087 :
    placement 0 (orient 0 (1, 0)) (2, 0) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (2, 0) ∉ distantEnvelopes j := by
  exact Or.inr ⟨20, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_088 :
    placement 0 (orient 0 (1, 0)) (2, 1) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (2, 1) ∉ distantEnvelopes j := by
  exact Or.inr ⟨15, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_089 :
    placement 0 (orient 0 (1, 0)) (2, 2) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (2, 2) ∉ distantEnvelopes j := by
  exact Or.inr ⟨6, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_090 :
    placement 0 (orient 0 (1, 0)) (2, 3) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (2, 3) ∉ distantEnvelopes j := by
  exact Or.inr ⟨6, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_091 :
    placement 0 (orient 0 (1, 0)) (2, 4) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (2, 4) ∉ distantEnvelopes j := by
  exact Or.inr ⟨6, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_092 :
    placement 0 (orient 0 (1, 0)) (2, 5) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (2, 5) ∉ distantEnvelopes j := by
  exact Or.inr ⟨2, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_093 :
    placement 0 (orient 0 (1, 0)) (2, 6) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (2, 6) ∉ distantEnvelopes j := by
  exact Or.inr ⟨2, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_094 :
    placement 0 (orient 0 (1, 0)) (2, 7) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (2, 7) ∉ distantEnvelopes j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_095 :
    placement 0 (orient 0 (1, 0)) (2, 8) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (2, 8) ∉ distantEnvelopes j := by
  exact Or.inr ⟨1, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_096 :
    placement 0 (orient 0 (1, 0)) (3, -4) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (3, -4) ∉ distantEnvelopes j := by
  exact Or.inr ⟨3, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_097 :
    placement 0 (orient 0 (1, 0)) (3, -3) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (3, -3) ∉ distantEnvelopes j := by
  exact Or.inr ⟨3, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_098 :
    placement 0 (orient 0 (1, 0)) (3, -2) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (3, -2) ∉ distantEnvelopes j := by
  exact Or.inr ⟨3, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_099 :
    placement 0 (orient 0 (1, 0)) (3, -1) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (3, -1) ∉ distantEnvelopes j := by
  exact Or.inr ⟨11, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_100 :
    placement 0 (orient 0 (1, 0)) (3, 0) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (3, 0) ∉ distantEnvelopes j := by
  exact Or.inr ⟨20, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_101 :
    placement 0 (orient 0 (1, 0)) (3, 1) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (3, 1) ∉ distantEnvelopes j := by
  exact Or.inr ⟨15, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_102 :
    placement 0 (orient 0 (1, 0)) (3, 2) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (3, 2) ∉ distantEnvelopes j := by
  exact Or.inr ⟨6, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_103 :
    placement 0 (orient 0 (1, 0)) (3, 3) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (3, 3) ∉ distantEnvelopes j := by
  exact Or.inr ⟨6, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_104 :
    placement 0 (orient 0 (1, 0)) (3, 4) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (3, 4) ∉ distantEnvelopes j := by
  exact Or.inr ⟨6, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_105 :
    placement 0 (orient 0 (1, 0)) (3, 5) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (3, 5) ∉ distantEnvelopes j := by
  exact Or.inr ⟨2, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_106 :
    placement 0 (orient 0 (1, 0)) (3, 6) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (3, 6) ∉ distantEnvelopes j := by
  exact Or.inr ⟨2, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_107 :
    placement 0 (orient 0 (1, 0)) (4, -1) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (4, -1) ∉ distantEnvelopes j := by
  exact Or.inr ⟨11, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_108 :
    placement 0 (orient 0 (1, 0)) (4, 0) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (4, 0) ∉ distantEnvelopes j := by
  exact Or.inr ⟨20, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_109 :
    placement 0 (orient 0 (1, 0)) (4, 1) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (4, 1) ∉ distantEnvelopes j := by
  exact Or.inr ⟨15, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_110 :
    placement 0 (orient 0 (1, 0)) (4, 2) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (4, 2) ∉ distantEnvelopes j := by
  exact Or.inr ⟨2, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_111 :
    placement 0 (orient 0 (1, 0)) (4, 3) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (4, 3) ∉ distantEnvelopes j := by
  exact Or.inr ⟨2, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_112 :
    placement 0 (orient 0 (1, 0)) (4, 4) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (4, 4) ∉ distantEnvelopes j := by
  exact Or.inr ⟨2, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_113 :
    placement 0 (orient 0 (1, 0)) (5, -1) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (5, -1) ∉ distantEnvelopes j := by
  exact Or.inr ⟨3, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_114 :
    placement 0 (orient 0 (1, 0)) (5, 0) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (5, 0) ∉ distantEnvelopes j := by
  exact Or.inr ⟨3, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_115 :
    placement 0 (orient 0 (1, 0)) (5, 1) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (5, 1) ∉ distantEnvelopes j := by
  exact Or.inr ⟨3, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_116 :
    placement 0 (orient 0 (1, 0)) (5, 3) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (5, 3) ∉ distantEnvelopes j := by
  exact Or.inr ⟨2, by decide⟩
theorem Internal.SnakyOpening.opening_escape_point_117 :
    placement 0 (orient 0 (1, 0)) (5, 4) ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) (5, 4) ∉ distantEnvelopes j := by
  exact Or.inr ⟨2, by decide⟩
theorem Internal.SnakyOpening.opening_escape_chunk_000 :
    ∀ p ∈ ([(-6, -1), (-6, 0), (-6, 1), (-6, 3), (-6, 4), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3)] : List Cell), placement 0 (orient 0 (1, 0)) p ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) p ∉ distantEnvelopes j := by
  exact List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_000, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_001, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_002, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_003, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_004, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_005, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_006, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_007, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_008, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_009, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_010, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_011, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_012, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_013, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_014, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_015, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyOpening.opening_escape_chunk_001 :
    ∀ p ∈ ([(-4, 4), (-4, 5), (-4, 6), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-2, -5), (-2, -4), (-2, -3)] : List Cell), placement 0 (orient 0 (1, 0)) p ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) p ∉ distantEnvelopes j := by
  exact List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_016, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_017, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_018, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_019, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_020, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_021, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_022, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_023, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_024, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_025, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_026, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_027, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_028, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_029, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_030, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_031, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyOpening.opening_escape_chunk_002 :
    ∀ p ∈ ([(-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0)] : List Cell), placement 0 (orient 0 (1, 0)) p ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) p ∉ distantEnvelopes j := by
  exact List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_032, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_033, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_034, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_035, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_036, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_037, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_038, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_039, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_040, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_041, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_042, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_043, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_044, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_045, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_046, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_047, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyOpening.opening_escape_chunk_003 :
    ∀ p ∈ ([(-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2)] : List Cell), placement 0 (orient 0 (1, 0)) p ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) p ∉ distantEnvelopes j := by
  exact List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_048, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_049, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_050, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_051, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_052, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_053, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_054, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_055, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_056, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_057, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_058, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_059, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_060, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_061, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_062, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_063, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyOpening.opening_escape_chunk_004 :
    ∀ p ∈ ([(0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4)] : List Cell), placement 0 (orient 0 (1, 0)) p ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) p ∉ distantEnvelopes j := by
  exact List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_064, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_065, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_066, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_067, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_068, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_069, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_070, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_071, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_072, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_073, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_074, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_075, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_076, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_077, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_078, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_079, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyOpening.opening_escape_chunk_005 :
    ∀ p ∈ ([(1, 5), (1, 6), (1, 7), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8)] : List Cell), placement 0 (orient 0 (1, 0)) p ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) p ∉ distantEnvelopes j := by
  exact List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_080, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_081, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_082, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_083, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_084, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_085, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_086, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_087, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_088, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_089, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_090, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_091, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_092, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_093, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_094, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_095, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyOpening.opening_escape_chunk_006 :
    ∀ p ∈ ([(3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3)] : List Cell), placement 0 (orient 0 (1, 0)) p ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) p ∉ distantEnvelopes j := by
  exact List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_096, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_097, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_098, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_099, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_100, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_101, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_102, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_103, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_104, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_105, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_106, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_107, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_108, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_109, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_110, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_111, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyOpening.opening_escape_chunk_007 :
    ∀ p ∈ ([(4, 4), (5, -1), (5, 0), (5, 1), (5, 3), (5, 4)] : List Cell), placement 0 (orient 0 (1, 0)) p ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) p ∉ distantEnvelopes j := by
  exact List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_112, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_113, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_114, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_115, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_116, List.forall_mem_cons.mpr ⟨Internal.SnakyOpening.opening_escape_point_117, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem Internal.SnakyOpening.opening_escape_source :
    ∀ p ∈ envelope_557, placement 0 (orient 0 (1, 0)) p ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) p ∉ distantEnvelopes j := by
  change ∀ p ∈ (([(-6, -1), (-6, 0), (-6, 1), (-6, 3), (-6, 4), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3)] : List Cell) ++ (([(-4, 4), (-4, 5), (-4, 6), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-2, -5), (-2, -4), (-2, -3)] : List Cell) ++ (([(-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0)] : List Cell) ++ (([(-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2)] : List Cell) ++ (([(0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4)] : List Cell) ++ (([(1, 5), (1, 6), (1, 7), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8)] : List Cell) ++ (([(3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3)] : List Cell) ++ ([(4, 4), (5, -1), (5, 0), (5, 1), (5, 3), (5, 4)] : List Cell)))))))), placement 0 (orient 0 (1, 0)) p ∈ nearBlock ∨ ∃ j : Fin 24, placement 0 (orient 0 (1, 0)) p ∉ distantEnvelopes j
  exact List.forall_mem_append.mpr ⟨Internal.SnakyOpening.opening_escape_chunk_000, List.forall_mem_append.mpr ⟨Internal.SnakyOpening.opening_escape_chunk_001, List.forall_mem_append.mpr ⟨Internal.SnakyOpening.opening_escape_chunk_002, List.forall_mem_append.mpr ⟨Internal.SnakyOpening.opening_escape_chunk_003, List.forall_mem_append.mpr ⟨Internal.SnakyOpening.opening_escape_chunk_004, List.forall_mem_append.mpr ⟨Internal.SnakyOpening.opening_escape_chunk_005, List.forall_mem_append.mpr ⟨Internal.SnakyOpening.opening_escape_chunk_006, Internal.SnakyOpening.opening_escape_chunk_007⟩⟩⟩⟩⟩⟩⟩
theorem distant_common_sub : commonEnvelope distantEnvelopes ⊆ nearBlock := by
  exact Internal.SnakyOpening.opening_commonEnvelope_subset_of_placed_escape distantEnvelopes
    nearBlock envelope_557 0 (orient 0 (1, 0)) rfl Internal.SnakyOpening.opening_escape_source
def localPair : Finset Cell := {(0, 0), (1, 0)}
theorem row615_owned : insert (0, 0) required_615 = localPair := by decide
def Internal.SnakyOpening.opening_negative615_list_6 : List Cell := ([(-15, 0), (-15, 2), (-14, 0), (-14, 1), (-14, 2), (-13, -4), (-13, -3), (-13, -2), (-13, -1), (-13, 0)] : List Cell)
theorem Internal.SnakyOpening.opening_negative615_list_6_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_6 := by decide
def Internal.SnakyOpening.opening_negative615_list_7 : List Cell := ([(-13, 1), (-13, 2), (-13, 3), (-13, 4), (-12, -5), (-12, -4), (-12, -3), (-12, -2), (-12, -1), (-12, 0), (-12, 1)] : List Cell)
theorem Internal.SnakyOpening.opening_negative615_list_7_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_7 := by decide
def Internal.SnakyOpening.opening_negative615_list_5 : List Cell := Internal.SnakyOpening.opening_negative615_list_6 ++ Internal.SnakyOpening.opening_negative615_list_7
theorem Internal.SnakyOpening.opening_negative615_list_5_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_5 :=
  List.not_mem_append (a := (1, -1)) (s := Internal.SnakyOpening.opening_negative615_list_6) (t := Internal.SnakyOpening.opening_negative615_list_7)
    Internal.SnakyOpening.opening_negative615_list_6_not_mem Internal.SnakyOpening.opening_negative615_list_7_not_mem
def Internal.SnakyOpening.opening_negative615_list_9 : List Cell := ([(-12, 2), (-12, 3), (-12, 4), (-12, 5), (-11, -5), (-11, -4), (-11, -3), (-11, -2), (-11, -1), (-11, 0)] : List Cell)
theorem Internal.SnakyOpening.opening_negative615_list_9_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_9 := by decide
def Internal.SnakyOpening.opening_negative615_list_10 : List Cell := ([(-11, 1), (-11, 2), (-11, 3), (-11, 4), (-11, 5), (-10, -9), (-10, -8), (-10, -7), (-10, -6), (-10, -5), (-10, -4)] : List Cell)
theorem Internal.SnakyOpening.opening_negative615_list_10_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_10 := by decide
def Internal.SnakyOpening.opening_negative615_list_8 : List Cell := Internal.SnakyOpening.opening_negative615_list_9 ++ Internal.SnakyOpening.opening_negative615_list_10
theorem Internal.SnakyOpening.opening_negative615_list_8_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_8 :=
  List.not_mem_append (a := (1, -1)) (s := Internal.SnakyOpening.opening_negative615_list_9) (t := Internal.SnakyOpening.opening_negative615_list_10)
    Internal.SnakyOpening.opening_negative615_list_9_not_mem Internal.SnakyOpening.opening_negative615_list_10_not_mem
def Internal.SnakyOpening.opening_negative615_list_4 : List Cell := Internal.SnakyOpening.opening_negative615_list_5 ++ Internal.SnakyOpening.opening_negative615_list_8
theorem Internal.SnakyOpening.opening_negative615_list_4_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_4 :=
  List.not_mem_append (a := (1, -1)) (s := Internal.SnakyOpening.opening_negative615_list_5) (t := Internal.SnakyOpening.opening_negative615_list_8)
    Internal.SnakyOpening.opening_negative615_list_5_not_mem Internal.SnakyOpening.opening_negative615_list_8_not_mem
def Internal.SnakyOpening.opening_negative615_list_13 : List Cell := ([(-10, -3), (-10, -2), (-10, -1), (-10, 0), (-10, 1), (-10, 2), (-10, 3), (-10, 4), (-10, 5), (-10, 6)] : List Cell)
theorem Internal.SnakyOpening.opening_negative615_list_13_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_13 := by decide
def Internal.SnakyOpening.opening_negative615_list_14 : List Cell := ([(-10, 7), (-10, 8), (-10, 9), (-9, -9), (-9, -8), (-9, -7), (-9, -6), (-9, -5), (-9, -4), (-9, -3), (-9, -2)] : List Cell)
theorem Internal.SnakyOpening.opening_negative615_list_14_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_14 := by decide
def Internal.SnakyOpening.opening_negative615_list_12 : List Cell := Internal.SnakyOpening.opening_negative615_list_13 ++ Internal.SnakyOpening.opening_negative615_list_14
theorem Internal.SnakyOpening.opening_negative615_list_12_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_12 :=
  List.not_mem_append (a := (1, -1)) (s := Internal.SnakyOpening.opening_negative615_list_13) (t := Internal.SnakyOpening.opening_negative615_list_14)
    Internal.SnakyOpening.opening_negative615_list_13_not_mem Internal.SnakyOpening.opening_negative615_list_14_not_mem
def Internal.SnakyOpening.opening_negative615_list_16 : List Cell := ([(-9, -1), (-9, 0), (-9, 1), (-9, 2), (-9, 3), (-9, 4), (-9, 5), (-9, 6), (-9, 7), (-9, 8), (-9, 9)] : List Cell)
theorem Internal.SnakyOpening.opening_negative615_list_16_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_16 := by decide
def Internal.SnakyOpening.opening_negative615_list_17 : List Cell := ([(-8, -10), (-8, -9), (-8, -8), (-8, -7), (-8, -6), (-8, -5), (-8, -4), (-8, -3), (-8, -2), (-8, -1), (-8, 0)] : List Cell)
theorem Internal.SnakyOpening.opening_negative615_list_17_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_17 := by decide
def Internal.SnakyOpening.opening_negative615_list_15 : List Cell := Internal.SnakyOpening.opening_negative615_list_16 ++ Internal.SnakyOpening.opening_negative615_list_17
theorem Internal.SnakyOpening.opening_negative615_list_15_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_15 :=
  List.not_mem_append (a := (1, -1)) (s := Internal.SnakyOpening.opening_negative615_list_16) (t := Internal.SnakyOpening.opening_negative615_list_17)
    Internal.SnakyOpening.opening_negative615_list_16_not_mem Internal.SnakyOpening.opening_negative615_list_17_not_mem
def Internal.SnakyOpening.opening_negative615_list_11 : List Cell := Internal.SnakyOpening.opening_negative615_list_12 ++ Internal.SnakyOpening.opening_negative615_list_15
theorem Internal.SnakyOpening.opening_negative615_list_11_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_11 :=
  List.not_mem_append (a := (1, -1)) (s := Internal.SnakyOpening.opening_negative615_list_12) (t := Internal.SnakyOpening.opening_negative615_list_15)
    Internal.SnakyOpening.opening_negative615_list_12_not_mem Internal.SnakyOpening.opening_negative615_list_15_not_mem
def Internal.SnakyOpening.opening_negative615_list_3 : List Cell := Internal.SnakyOpening.opening_negative615_list_4 ++ Internal.SnakyOpening.opening_negative615_list_11
theorem Internal.SnakyOpening.opening_negative615_list_3_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_3 :=
  List.not_mem_append (a := (1, -1)) (s := Internal.SnakyOpening.opening_negative615_list_4) (t := Internal.SnakyOpening.opening_negative615_list_11)
    Internal.SnakyOpening.opening_negative615_list_4_not_mem Internal.SnakyOpening.opening_negative615_list_11_not_mem
def Internal.SnakyOpening.opening_negative615_list_21 : List Cell := ([(-8, 1), (-8, 2), (-8, 3), (-8, 4), (-8, 5), (-8, 6), (-8, 7), (-8, 8), (-8, 9), (-8, 10)] : List Cell)
theorem Internal.SnakyOpening.opening_negative615_list_21_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_21 := by decide
def Internal.SnakyOpening.opening_negative615_list_22 : List Cell := ([(-7, -11), (-7, -10), (-7, -9), (-7, -8), (-7, -7), (-7, -6), (-7, -5), (-7, -4), (-7, -3), (-7, -2), (-7, -1)] : List Cell)
theorem Internal.SnakyOpening.opening_negative615_list_22_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_22 := by decide
def Internal.SnakyOpening.opening_negative615_list_20 : List Cell := Internal.SnakyOpening.opening_negative615_list_21 ++ Internal.SnakyOpening.opening_negative615_list_22
theorem Internal.SnakyOpening.opening_negative615_list_20_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_20 :=
  List.not_mem_append (a := (1, -1)) (s := Internal.SnakyOpening.opening_negative615_list_21) (t := Internal.SnakyOpening.opening_negative615_list_22)
    Internal.SnakyOpening.opening_negative615_list_21_not_mem Internal.SnakyOpening.opening_negative615_list_22_not_mem
def Internal.SnakyOpening.opening_negative615_list_24 : List Cell := ([(-7, 0), (-7, 1), (-7, 2), (-7, 3), (-7, 4), (-7, 5), (-7, 6), (-7, 7), (-7, 8), (-7, 9), (-7, 10)] : List Cell)
theorem Internal.SnakyOpening.opening_negative615_list_24_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_24 := by decide
def Internal.SnakyOpening.opening_negative615_list_25 : List Cell := ([(-7, 11), (-6, -11), (-6, -10), (-6, -9), (-6, -8), (-6, -7), (-6, -6), (-6, -5), (-6, -4), (-6, -3), (-6, -2)] : List Cell)
theorem Internal.SnakyOpening.opening_negative615_list_25_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_25 := by decide
def Internal.SnakyOpening.opening_negative615_list_23 : List Cell := Internal.SnakyOpening.opening_negative615_list_24 ++ Internal.SnakyOpening.opening_negative615_list_25
theorem Internal.SnakyOpening.opening_negative615_list_23_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_23 :=
  List.not_mem_append (a := (1, -1)) (s := Internal.SnakyOpening.opening_negative615_list_24) (t := Internal.SnakyOpening.opening_negative615_list_25)
    Internal.SnakyOpening.opening_negative615_list_24_not_mem Internal.SnakyOpening.opening_negative615_list_25_not_mem
def Internal.SnakyOpening.opening_negative615_list_19 : List Cell := Internal.SnakyOpening.opening_negative615_list_20 ++ Internal.SnakyOpening.opening_negative615_list_23
theorem Internal.SnakyOpening.opening_negative615_list_19_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_19 :=
  List.not_mem_append (a := (1, -1)) (s := Internal.SnakyOpening.opening_negative615_list_20) (t := Internal.SnakyOpening.opening_negative615_list_23)
    Internal.SnakyOpening.opening_negative615_list_20_not_mem Internal.SnakyOpening.opening_negative615_list_23_not_mem
def Internal.SnakyOpening.opening_negative615_list_28 : List Cell := ([(-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-6, 5), (-6, 6), (-6, 7), (-6, 8)] : List Cell)
theorem Internal.SnakyOpening.opening_negative615_list_28_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_28 := by decide
def Internal.SnakyOpening.opening_negative615_list_29 : List Cell := ([(-6, 9), (-6, 10), (-6, 11), (-5, -12), (-5, -11), (-5, -10), (-5, -9), (-5, -8), (-5, -7), (-5, -6), (-5, -5)] : List Cell)
theorem Internal.SnakyOpening.opening_negative615_list_29_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_29 := by decide
def Internal.SnakyOpening.opening_negative615_list_27 : List Cell := Internal.SnakyOpening.opening_negative615_list_28 ++ Internal.SnakyOpening.opening_negative615_list_29
theorem Internal.SnakyOpening.opening_negative615_list_27_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_27 :=
  List.not_mem_append (a := (1, -1)) (s := Internal.SnakyOpening.opening_negative615_list_28) (t := Internal.SnakyOpening.opening_negative615_list_29)
    Internal.SnakyOpening.opening_negative615_list_28_not_mem Internal.SnakyOpening.opening_negative615_list_29_not_mem
def Internal.SnakyOpening.opening_negative615_list_31 : List Cell := ([(-5, -4), (-5, -3), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6)] : List Cell)
theorem Internal.SnakyOpening.opening_negative615_list_31_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_31 := by decide
def Internal.SnakyOpening.opening_negative615_list_32 : List Cell := ([(-5, 7), (-5, 8), (-5, 9), (-5, 10), (-5, 11), (-5, 12), (-4, -14), (-4, -13), (-4, -12), (-4, -11), (-4, -10)] : List Cell)
theorem Internal.SnakyOpening.opening_negative615_list_32_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_32 := by decide
def Internal.SnakyOpening.opening_negative615_list_30 : List Cell := Internal.SnakyOpening.opening_negative615_list_31 ++ Internal.SnakyOpening.opening_negative615_list_32
theorem Internal.SnakyOpening.opening_negative615_list_30_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_30 :=
  List.not_mem_append (a := (1, -1)) (s := Internal.SnakyOpening.opening_negative615_list_31) (t := Internal.SnakyOpening.opening_negative615_list_32)
    Internal.SnakyOpening.opening_negative615_list_31_not_mem Internal.SnakyOpening.opening_negative615_list_32_not_mem
def Internal.SnakyOpening.opening_negative615_list_26 : List Cell := Internal.SnakyOpening.opening_negative615_list_27 ++ Internal.SnakyOpening.opening_negative615_list_30
theorem Internal.SnakyOpening.opening_negative615_list_26_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_26 :=
  List.not_mem_append (a := (1, -1)) (s := Internal.SnakyOpening.opening_negative615_list_27) (t := Internal.SnakyOpening.opening_negative615_list_30)
    Internal.SnakyOpening.opening_negative615_list_27_not_mem Internal.SnakyOpening.opening_negative615_list_30_not_mem
def Internal.SnakyOpening.opening_negative615_list_18 : List Cell := Internal.SnakyOpening.opening_negative615_list_19 ++ Internal.SnakyOpening.opening_negative615_list_26
theorem Internal.SnakyOpening.opening_negative615_list_18_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_18 :=
  List.not_mem_append (a := (1, -1)) (s := Internal.SnakyOpening.opening_negative615_list_19) (t := Internal.SnakyOpening.opening_negative615_list_26)
    Internal.SnakyOpening.opening_negative615_list_19_not_mem Internal.SnakyOpening.opening_negative615_list_26_not_mem
def Internal.SnakyOpening.opening_negative615_list_2 : List Cell := Internal.SnakyOpening.opening_negative615_list_3 ++ Internal.SnakyOpening.opening_negative615_list_18
theorem Internal.SnakyOpening.opening_negative615_list_2_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_2 :=
  List.not_mem_append (a := (1, -1)) (s := Internal.SnakyOpening.opening_negative615_list_3) (t := Internal.SnakyOpening.opening_negative615_list_18)
    Internal.SnakyOpening.opening_negative615_list_3_not_mem Internal.SnakyOpening.opening_negative615_list_18_not_mem
def Internal.SnakyOpening.opening_negative615_list_37 : List Cell := ([(-4, -9), (-4, -8), (-4, -7), (-4, -6), (-4, -5), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0)] : List Cell)
theorem Internal.SnakyOpening.opening_negative615_list_37_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_37 := by decide
def Internal.SnakyOpening.opening_negative615_list_38 : List Cell := ([(-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-4, 9), (-4, 10), (-4, 11)] : List Cell)
theorem Internal.SnakyOpening.opening_negative615_list_38_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_38 := by decide
def Internal.SnakyOpening.opening_negative615_list_36 : List Cell := Internal.SnakyOpening.opening_negative615_list_37 ++ Internal.SnakyOpening.opening_negative615_list_38
theorem Internal.SnakyOpening.opening_negative615_list_36_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_36 :=
  List.not_mem_append (a := (1, -1)) (s := Internal.SnakyOpening.opening_negative615_list_37) (t := Internal.SnakyOpening.opening_negative615_list_38)
    Internal.SnakyOpening.opening_negative615_list_37_not_mem Internal.SnakyOpening.opening_negative615_list_38_not_mem
def Internal.SnakyOpening.opening_negative615_list_40 : List Cell := ([(-4, 12), (-4, 13), (-4, 14), (-3, -14), (-3, -13), (-3, -12), (-3, -11), (-3, -10), (-3, -9), (-3, -8), (-3, -7)] : List Cell)
theorem Internal.SnakyOpening.opening_negative615_list_40_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_40 := by decide
def Internal.SnakyOpening.opening_negative615_list_41 : List Cell := ([(-3, -6), (-3, -5), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4)] : List Cell)
theorem Internal.SnakyOpening.opening_negative615_list_41_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_41 := by decide
def Internal.SnakyOpening.opening_negative615_list_39 : List Cell := Internal.SnakyOpening.opening_negative615_list_40 ++ Internal.SnakyOpening.opening_negative615_list_41
theorem Internal.SnakyOpening.opening_negative615_list_39_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_39 :=
  List.not_mem_append (a := (1, -1)) (s := Internal.SnakyOpening.opening_negative615_list_40) (t := Internal.SnakyOpening.opening_negative615_list_41)
    Internal.SnakyOpening.opening_negative615_list_40_not_mem Internal.SnakyOpening.opening_negative615_list_41_not_mem
def Internal.SnakyOpening.opening_negative615_list_35 : List Cell := Internal.SnakyOpening.opening_negative615_list_36 ++ Internal.SnakyOpening.opening_negative615_list_39
theorem Internal.SnakyOpening.opening_negative615_list_35_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_35 :=
  List.not_mem_append (a := (1, -1)) (s := Internal.SnakyOpening.opening_negative615_list_36) (t := Internal.SnakyOpening.opening_negative615_list_39)
    Internal.SnakyOpening.opening_negative615_list_36_not_mem Internal.SnakyOpening.opening_negative615_list_39_not_mem
def Internal.SnakyOpening.opening_negative615_list_44 : List Cell := ([(-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11), (-3, 12), (-3, 13), (-3, 14)] : List Cell)
theorem Internal.SnakyOpening.opening_negative615_list_44_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_44 := by decide
def Internal.SnakyOpening.opening_negative615_list_45 : List Cell := ([(-2, -16), (-2, -15), (-2, -14), (-2, -13), (-2, -12), (-2, -11), (-2, -10), (-2, -9), (-2, -8), (-2, -7), (-2, -6)] : List Cell)
theorem Internal.SnakyOpening.opening_negative615_list_45_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_45 := by decide
def Internal.SnakyOpening.opening_negative615_list_43 : List Cell := Internal.SnakyOpening.opening_negative615_list_44 ++ Internal.SnakyOpening.opening_negative615_list_45
theorem Internal.SnakyOpening.opening_negative615_list_43_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_43 :=
  List.not_mem_append (a := (1, -1)) (s := Internal.SnakyOpening.opening_negative615_list_44) (t := Internal.SnakyOpening.opening_negative615_list_45)
    Internal.SnakyOpening.opening_negative615_list_44_not_mem Internal.SnakyOpening.opening_negative615_list_45_not_mem
def Internal.SnakyOpening.opening_negative615_list_47 : List Cell := ([(-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5)] : List Cell)
theorem Internal.SnakyOpening.opening_negative615_list_47_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_47 := by decide
def Internal.SnakyOpening.opening_negative615_list_48 : List Cell := ([(-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-2, 12), (-2, 13), (-2, 14), (-2, 15), (-2, 16)] : List Cell)
theorem Internal.SnakyOpening.opening_negative615_list_48_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_48 := by decide
def Internal.SnakyOpening.opening_negative615_list_46 : List Cell := Internal.SnakyOpening.opening_negative615_list_47 ++ Internal.SnakyOpening.opening_negative615_list_48
theorem Internal.SnakyOpening.opening_negative615_list_46_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_46 :=
  List.not_mem_append (a := (1, -1)) (s := Internal.SnakyOpening.opening_negative615_list_47) (t := Internal.SnakyOpening.opening_negative615_list_48)
    Internal.SnakyOpening.opening_negative615_list_47_not_mem Internal.SnakyOpening.opening_negative615_list_48_not_mem
def Internal.SnakyOpening.opening_negative615_list_42 : List Cell := Internal.SnakyOpening.opening_negative615_list_43 ++ Internal.SnakyOpening.opening_negative615_list_46
theorem Internal.SnakyOpening.opening_negative615_list_42_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_42 :=
  List.not_mem_append (a := (1, -1)) (s := Internal.SnakyOpening.opening_negative615_list_43) (t := Internal.SnakyOpening.opening_negative615_list_46)
    Internal.SnakyOpening.opening_negative615_list_43_not_mem Internal.SnakyOpening.opening_negative615_list_46_not_mem
def Internal.SnakyOpening.opening_negative615_list_34 : List Cell := Internal.SnakyOpening.opening_negative615_list_35 ++ Internal.SnakyOpening.opening_negative615_list_42
theorem Internal.SnakyOpening.opening_negative615_list_34_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_34 :=
  List.not_mem_append (a := (1, -1)) (s := Internal.SnakyOpening.opening_negative615_list_35) (t := Internal.SnakyOpening.opening_negative615_list_42)
    Internal.SnakyOpening.opening_negative615_list_35_not_mem Internal.SnakyOpening.opening_negative615_list_42_not_mem
def Internal.SnakyOpening.opening_negative615_list_52 : List Cell := ([(-1, -15), (-1, -14), (-1, -13), (-1, -12), (-1, -11), (-1, -10), (-1, -9), (-1, -8), (-1, -7), (-1, -6)] : List Cell)
theorem Internal.SnakyOpening.opening_negative615_list_52_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_52 := by decide
def Internal.SnakyOpening.opening_negative615_list_53 : List Cell := ([(-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5)] : List Cell)
theorem Internal.SnakyOpening.opening_negative615_list_53_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_53 := by decide
def Internal.SnakyOpening.opening_negative615_list_51 : List Cell := Internal.SnakyOpening.opening_negative615_list_52 ++ Internal.SnakyOpening.opening_negative615_list_53
theorem Internal.SnakyOpening.opening_negative615_list_51_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_51 :=
  List.not_mem_append (a := (1, -1)) (s := Internal.SnakyOpening.opening_negative615_list_52) (t := Internal.SnakyOpening.opening_negative615_list_53)
    Internal.SnakyOpening.opening_negative615_list_52_not_mem Internal.SnakyOpening.opening_negative615_list_53_not_mem
def Internal.SnakyOpening.opening_negative615_list_55 : List Cell := ([(-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (-1, 12), (-1, 13), (-1, 14), (-1, 15), (0, -16)] : List Cell)
theorem Internal.SnakyOpening.opening_negative615_list_55_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_55 := by decide
def Internal.SnakyOpening.opening_negative615_list_56 : List Cell := ([(0, -15), (0, -14), (0, -13), (0, -12), (0, -11), (0, -10), (0, -9), (0, -8), (0, -7), (0, -6), (0, -5)] : List Cell)
theorem Internal.SnakyOpening.opening_negative615_list_56_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_56 := by decide
def Internal.SnakyOpening.opening_negative615_list_54 : List Cell := Internal.SnakyOpening.opening_negative615_list_55 ++ Internal.SnakyOpening.opening_negative615_list_56
theorem Internal.SnakyOpening.opening_negative615_list_54_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_54 :=
  List.not_mem_append (a := (1, -1)) (s := Internal.SnakyOpening.opening_negative615_list_55) (t := Internal.SnakyOpening.opening_negative615_list_56)
    Internal.SnakyOpening.opening_negative615_list_55_not_mem Internal.SnakyOpening.opening_negative615_list_56_not_mem
def Internal.SnakyOpening.opening_negative615_list_50 : List Cell := Internal.SnakyOpening.opening_negative615_list_51 ++ Internal.SnakyOpening.opening_negative615_list_54
theorem Internal.SnakyOpening.opening_negative615_list_50_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_50 :=
  List.not_mem_append (a := (1, -1)) (s := Internal.SnakyOpening.opening_negative615_list_51) (t := Internal.SnakyOpening.opening_negative615_list_54)
    Internal.SnakyOpening.opening_negative615_list_51_not_mem Internal.SnakyOpening.opening_negative615_list_54_not_mem
def Internal.SnakyOpening.opening_negative615_list_59 : List Cell := ([(0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5)] : List Cell)
theorem Internal.SnakyOpening.opening_negative615_list_59_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_59 := by decide
def Internal.SnakyOpening.opening_negative615_list_60 : List Cell := ([(0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (0, 12), (0, 13), (0, 14), (0, 15), (0, 16)] : List Cell)
theorem Internal.SnakyOpening.opening_negative615_list_60_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_60 := by decide
def Internal.SnakyOpening.opening_negative615_list_58 : List Cell := Internal.SnakyOpening.opening_negative615_list_59 ++ Internal.SnakyOpening.opening_negative615_list_60
theorem Internal.SnakyOpening.opening_negative615_list_58_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_58 :=
  List.not_mem_append (a := (1, -1)) (s := Internal.SnakyOpening.opening_negative615_list_59) (t := Internal.SnakyOpening.opening_negative615_list_60)
    Internal.SnakyOpening.opening_negative615_list_59_not_mem Internal.SnakyOpening.opening_negative615_list_60_not_mem
def Internal.SnakyOpening.opening_negative615_list_62 : List Cell := ([(1, -15), (1, -14), (1, -13), (1, -12), (1, -11), (1, -10), (1, -9), (1, -8), (1, -7), (1, -6), (1, -5)] : List Cell)
theorem Internal.SnakyOpening.opening_negative615_list_62_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_62 := by decide
def Internal.SnakyOpening.opening_negative615_list_63 : List Cell := ([(1, -4), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7)] : List Cell)
theorem Internal.SnakyOpening.opening_negative615_list_63_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_63 := by decide
def Internal.SnakyOpening.opening_negative615_list_61 : List Cell := Internal.SnakyOpening.opening_negative615_list_62 ++ Internal.SnakyOpening.opening_negative615_list_63
theorem Internal.SnakyOpening.opening_negative615_list_61_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_61 :=
  List.not_mem_append (a := (1, -1)) (s := Internal.SnakyOpening.opening_negative615_list_62) (t := Internal.SnakyOpening.opening_negative615_list_63)
    Internal.SnakyOpening.opening_negative615_list_62_not_mem Internal.SnakyOpening.opening_negative615_list_63_not_mem
def Internal.SnakyOpening.opening_negative615_list_57 : List Cell := Internal.SnakyOpening.opening_negative615_list_58 ++ Internal.SnakyOpening.opening_negative615_list_61
theorem Internal.SnakyOpening.opening_negative615_list_57_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_57 :=
  List.not_mem_append (a := (1, -1)) (s := Internal.SnakyOpening.opening_negative615_list_58) (t := Internal.SnakyOpening.opening_negative615_list_61)
    Internal.SnakyOpening.opening_negative615_list_58_not_mem Internal.SnakyOpening.opening_negative615_list_61_not_mem
def Internal.SnakyOpening.opening_negative615_list_49 : List Cell := Internal.SnakyOpening.opening_negative615_list_50 ++ Internal.SnakyOpening.opening_negative615_list_57
theorem Internal.SnakyOpening.opening_negative615_list_49_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_49 :=
  List.not_mem_append (a := (1, -1)) (s := Internal.SnakyOpening.opening_negative615_list_50) (t := Internal.SnakyOpening.opening_negative615_list_57)
    Internal.SnakyOpening.opening_negative615_list_50_not_mem Internal.SnakyOpening.opening_negative615_list_57_not_mem
def Internal.SnakyOpening.opening_negative615_list_33 : List Cell := Internal.SnakyOpening.opening_negative615_list_34 ++ Internal.SnakyOpening.opening_negative615_list_49
theorem Internal.SnakyOpening.opening_negative615_list_33_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_33 :=
  List.not_mem_append (a := (1, -1)) (s := Internal.SnakyOpening.opening_negative615_list_34) (t := Internal.SnakyOpening.opening_negative615_list_49)
    Internal.SnakyOpening.opening_negative615_list_34_not_mem Internal.SnakyOpening.opening_negative615_list_49_not_mem
def Internal.SnakyOpening.opening_negative615_list_1 : List Cell := Internal.SnakyOpening.opening_negative615_list_2 ++ Internal.SnakyOpening.opening_negative615_list_33
theorem Internal.SnakyOpening.opening_negative615_list_1_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_1 :=
  List.not_mem_append (a := (1, -1)) (s := Internal.SnakyOpening.opening_negative615_list_2) (t := Internal.SnakyOpening.opening_negative615_list_33)
    Internal.SnakyOpening.opening_negative615_list_2_not_mem Internal.SnakyOpening.opening_negative615_list_33_not_mem
def Internal.SnakyOpening.opening_negative615_list_69 : List Cell := ([(1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (1, 13), (1, 14), (1, 15), (1, 16), (2, -16)] : List Cell)
theorem Internal.SnakyOpening.opening_negative615_list_69_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_69 := by decide
def Internal.SnakyOpening.opening_negative615_list_70 : List Cell := ([(2, -15), (2, -14), (2, -13), (2, -12), (2, -11), (2, -10), (2, -9), (2, -8), (2, -7), (2, -6), (2, -5)] : List Cell)
theorem Internal.SnakyOpening.opening_negative615_list_70_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_70 := by decide
def Internal.SnakyOpening.opening_negative615_list_68 : List Cell := Internal.SnakyOpening.opening_negative615_list_69 ++ Internal.SnakyOpening.opening_negative615_list_70
theorem Internal.SnakyOpening.opening_negative615_list_68_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_68 :=
  List.not_mem_append (a := (1, -1)) (s := Internal.SnakyOpening.opening_negative615_list_69) (t := Internal.SnakyOpening.opening_negative615_list_70)
    Internal.SnakyOpening.opening_negative615_list_69_not_mem Internal.SnakyOpening.opening_negative615_list_70_not_mem
def Internal.SnakyOpening.opening_negative615_list_72 : List Cell := ([(2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5)] : List Cell)
theorem Internal.SnakyOpening.opening_negative615_list_72_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_72 := by decide
def Internal.SnakyOpening.opening_negative615_list_73 : List Cell := ([(2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (2, 13), (2, 14), (2, 15), (2, 16)] : List Cell)
theorem Internal.SnakyOpening.opening_negative615_list_73_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_73 := by decide
def Internal.SnakyOpening.opening_negative615_list_71 : List Cell := Internal.SnakyOpening.opening_negative615_list_72 ++ Internal.SnakyOpening.opening_negative615_list_73
theorem Internal.SnakyOpening.opening_negative615_list_71_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_71 :=
  List.not_mem_append (a := (1, -1)) (s := Internal.SnakyOpening.opening_negative615_list_72) (t := Internal.SnakyOpening.opening_negative615_list_73)
    Internal.SnakyOpening.opening_negative615_list_72_not_mem Internal.SnakyOpening.opening_negative615_list_73_not_mem
def Internal.SnakyOpening.opening_negative615_list_67 : List Cell := Internal.SnakyOpening.opening_negative615_list_68 ++ Internal.SnakyOpening.opening_negative615_list_71
theorem Internal.SnakyOpening.opening_negative615_list_67_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_67 :=
  List.not_mem_append (a := (1, -1)) (s := Internal.SnakyOpening.opening_negative615_list_68) (t := Internal.SnakyOpening.opening_negative615_list_71)
    Internal.SnakyOpening.opening_negative615_list_68_not_mem Internal.SnakyOpening.opening_negative615_list_71_not_mem
def Internal.SnakyOpening.opening_negative615_list_76 : List Cell := ([(3, -14), (3, -13), (3, -12), (3, -11), (3, -10), (3, -9), (3, -8), (3, -7), (3, -6), (3, -5)] : List Cell)
theorem Internal.SnakyOpening.opening_negative615_list_76_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_76 := by decide
def Internal.SnakyOpening.opening_negative615_list_77 : List Cell := ([(3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6)] : List Cell)
theorem Internal.SnakyOpening.opening_negative615_list_77_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_77 := by decide
def Internal.SnakyOpening.opening_negative615_list_75 : List Cell := Internal.SnakyOpening.opening_negative615_list_76 ++ Internal.SnakyOpening.opening_negative615_list_77
theorem Internal.SnakyOpening.opening_negative615_list_75_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_75 :=
  List.not_mem_append (a := (1, -1)) (s := Internal.SnakyOpening.opening_negative615_list_76) (t := Internal.SnakyOpening.opening_negative615_list_77)
    Internal.SnakyOpening.opening_negative615_list_76_not_mem Internal.SnakyOpening.opening_negative615_list_77_not_mem
def Internal.SnakyOpening.opening_negative615_list_79 : List Cell := ([(3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (3, 13), (3, 14), (3, 15), (3, 16), (4, -14)] : List Cell)
theorem Internal.SnakyOpening.opening_negative615_list_79_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_79 := by decide
def Internal.SnakyOpening.opening_negative615_list_80 : List Cell := ([(4, -13), (4, -12), (4, -11), (4, -10), (4, -9), (4, -8), (4, -7), (4, -6), (4, -5), (4, -4), (4, -3)] : List Cell)
theorem Internal.SnakyOpening.opening_negative615_list_80_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_80 := by decide
def Internal.SnakyOpening.opening_negative615_list_78 : List Cell := Internal.SnakyOpening.opening_negative615_list_79 ++ Internal.SnakyOpening.opening_negative615_list_80
theorem Internal.SnakyOpening.opening_negative615_list_78_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_78 :=
  List.not_mem_append (a := (1, -1)) (s := Internal.SnakyOpening.opening_negative615_list_79) (t := Internal.SnakyOpening.opening_negative615_list_80)
    Internal.SnakyOpening.opening_negative615_list_79_not_mem Internal.SnakyOpening.opening_negative615_list_80_not_mem
def Internal.SnakyOpening.opening_negative615_list_74 : List Cell := Internal.SnakyOpening.opening_negative615_list_75 ++ Internal.SnakyOpening.opening_negative615_list_78
theorem Internal.SnakyOpening.opening_negative615_list_74_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_74 :=
  List.not_mem_append (a := (1, -1)) (s := Internal.SnakyOpening.opening_negative615_list_75) (t := Internal.SnakyOpening.opening_negative615_list_78)
    Internal.SnakyOpening.opening_negative615_list_75_not_mem Internal.SnakyOpening.opening_negative615_list_78_not_mem
def Internal.SnakyOpening.opening_negative615_list_66 : List Cell := Internal.SnakyOpening.opening_negative615_list_67 ++ Internal.SnakyOpening.opening_negative615_list_74
theorem Internal.SnakyOpening.opening_negative615_list_66_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_66 :=
  List.not_mem_append (a := (1, -1)) (s := Internal.SnakyOpening.opening_negative615_list_67) (t := Internal.SnakyOpening.opening_negative615_list_74)
    Internal.SnakyOpening.opening_negative615_list_67_not_mem Internal.SnakyOpening.opening_negative615_list_74_not_mem
def Internal.SnakyOpening.opening_negative615_list_84 : List Cell := ([(4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7)] : List Cell)
theorem Internal.SnakyOpening.opening_negative615_list_84_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_84 := by decide
def Internal.SnakyOpening.opening_negative615_list_85 : List Cell := ([(4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (4, 13), (4, 14), (5, -14), (5, -13), (5, -12), (5, -11)] : List Cell)
theorem Internal.SnakyOpening.opening_negative615_list_85_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_85 := by decide
def Internal.SnakyOpening.opening_negative615_list_83 : List Cell := Internal.SnakyOpening.opening_negative615_list_84 ++ Internal.SnakyOpening.opening_negative615_list_85
theorem Internal.SnakyOpening.opening_negative615_list_83_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_83 :=
  List.not_mem_append (a := (1, -1)) (s := Internal.SnakyOpening.opening_negative615_list_84) (t := Internal.SnakyOpening.opening_negative615_list_85)
    Internal.SnakyOpening.opening_negative615_list_84_not_mem Internal.SnakyOpening.opening_negative615_list_85_not_mem
def Internal.SnakyOpening.opening_negative615_list_87 : List Cell := ([(5, -10), (5, -9), (5, -8), (5, -7), (5, -6), (5, -5), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0)] : List Cell)
theorem Internal.SnakyOpening.opening_negative615_list_87_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_87 := by decide
def Internal.SnakyOpening.opening_negative615_list_88 : List Cell := ([(5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11)] : List Cell)
theorem Internal.SnakyOpening.opening_negative615_list_88_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_88 := by decide
def Internal.SnakyOpening.opening_negative615_list_86 : List Cell := Internal.SnakyOpening.opening_negative615_list_87 ++ Internal.SnakyOpening.opening_negative615_list_88
theorem Internal.SnakyOpening.opening_negative615_list_86_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_86 :=
  List.not_mem_append (a := (1, -1)) (s := Internal.SnakyOpening.opening_negative615_list_87) (t := Internal.SnakyOpening.opening_negative615_list_88)
    Internal.SnakyOpening.opening_negative615_list_87_not_mem Internal.SnakyOpening.opening_negative615_list_88_not_mem
def Internal.SnakyOpening.opening_negative615_list_82 : List Cell := Internal.SnakyOpening.opening_negative615_list_83 ++ Internal.SnakyOpening.opening_negative615_list_86
theorem Internal.SnakyOpening.opening_negative615_list_82_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_82 :=
  List.not_mem_append (a := (1, -1)) (s := Internal.SnakyOpening.opening_negative615_list_83) (t := Internal.SnakyOpening.opening_negative615_list_86)
    Internal.SnakyOpening.opening_negative615_list_83_not_mem Internal.SnakyOpening.opening_negative615_list_86_not_mem
def Internal.SnakyOpening.opening_negative615_list_91 : List Cell := ([(5, 12), (5, 13), (5, 14), (6, -14), (6, -13), (6, -12), (6, -11), (6, -10), (6, -9), (6, -8)] : List Cell)
theorem Internal.SnakyOpening.opening_negative615_list_91_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_91 := by decide
def Internal.SnakyOpening.opening_negative615_list_92 : List Cell := ([(6, -7), (6, -6), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3)] : List Cell)
theorem Internal.SnakyOpening.opening_negative615_list_92_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_92 := by decide
def Internal.SnakyOpening.opening_negative615_list_90 : List Cell := Internal.SnakyOpening.opening_negative615_list_91 ++ Internal.SnakyOpening.opening_negative615_list_92
theorem Internal.SnakyOpening.opening_negative615_list_90_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_90 :=
  List.not_mem_append (a := (1, -1)) (s := Internal.SnakyOpening.opening_negative615_list_91) (t := Internal.SnakyOpening.opening_negative615_list_92)
    Internal.SnakyOpening.opening_negative615_list_91_not_mem Internal.SnakyOpening.opening_negative615_list_92_not_mem
def Internal.SnakyOpening.opening_negative615_list_94 : List Cell := ([(6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (6, 12), (6, 13), (6, 14)] : List Cell)
theorem Internal.SnakyOpening.opening_negative615_list_94_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_94 := by decide
def Internal.SnakyOpening.opening_negative615_list_95 : List Cell := ([(7, -12), (7, -11), (7, -10), (7, -9), (7, -8), (7, -7), (7, -6), (7, -5), (7, -4), (7, -3), (7, -2)] : List Cell)
theorem Internal.SnakyOpening.opening_negative615_list_95_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_95 := by decide
def Internal.SnakyOpening.opening_negative615_list_93 : List Cell := Internal.SnakyOpening.opening_negative615_list_94 ++ Internal.SnakyOpening.opening_negative615_list_95
theorem Internal.SnakyOpening.opening_negative615_list_93_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_93 :=
  List.not_mem_append (a := (1, -1)) (s := Internal.SnakyOpening.opening_negative615_list_94) (t := Internal.SnakyOpening.opening_negative615_list_95)
    Internal.SnakyOpening.opening_negative615_list_94_not_mem Internal.SnakyOpening.opening_negative615_list_95_not_mem
def Internal.SnakyOpening.opening_negative615_list_89 : List Cell := Internal.SnakyOpening.opening_negative615_list_90 ++ Internal.SnakyOpening.opening_negative615_list_93
theorem Internal.SnakyOpening.opening_negative615_list_89_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_89 :=
  List.not_mem_append (a := (1, -1)) (s := Internal.SnakyOpening.opening_negative615_list_90) (t := Internal.SnakyOpening.opening_negative615_list_93)
    Internal.SnakyOpening.opening_negative615_list_90_not_mem Internal.SnakyOpening.opening_negative615_list_93_not_mem
def Internal.SnakyOpening.opening_negative615_list_81 : List Cell := Internal.SnakyOpening.opening_negative615_list_82 ++ Internal.SnakyOpening.opening_negative615_list_89
theorem Internal.SnakyOpening.opening_negative615_list_81_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_81 :=
  List.not_mem_append (a := (1, -1)) (s := Internal.SnakyOpening.opening_negative615_list_82) (t := Internal.SnakyOpening.opening_negative615_list_89)
    Internal.SnakyOpening.opening_negative615_list_82_not_mem Internal.SnakyOpening.opening_negative615_list_89_not_mem
def Internal.SnakyOpening.opening_negative615_list_65 : List Cell := Internal.SnakyOpening.opening_negative615_list_66 ++ Internal.SnakyOpening.opening_negative615_list_81
theorem Internal.SnakyOpening.opening_negative615_list_65_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_65 :=
  List.not_mem_append (a := (1, -1)) (s := Internal.SnakyOpening.opening_negative615_list_66) (t := Internal.SnakyOpening.opening_negative615_list_81)
    Internal.SnakyOpening.opening_negative615_list_66_not_mem Internal.SnakyOpening.opening_negative615_list_81_not_mem
def Internal.SnakyOpening.opening_negative615_list_100 : List Cell := ([(7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8)] : List Cell)
theorem Internal.SnakyOpening.opening_negative615_list_100_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_100 := by decide
def Internal.SnakyOpening.opening_negative615_list_101 : List Cell := ([(7, 9), (7, 10), (7, 11), (7, 12), (7, 13), (7, 14), (8, -12), (8, -11), (8, -10), (8, -9), (8, -8)] : List Cell)
theorem Internal.SnakyOpening.opening_negative615_list_101_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_101 := by decide
def Internal.SnakyOpening.opening_negative615_list_99 : List Cell := Internal.SnakyOpening.opening_negative615_list_100 ++ Internal.SnakyOpening.opening_negative615_list_101
theorem Internal.SnakyOpening.opening_negative615_list_99_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_99 :=
  List.not_mem_append (a := (1, -1)) (s := Internal.SnakyOpening.opening_negative615_list_100) (t := Internal.SnakyOpening.opening_negative615_list_101)
    Internal.SnakyOpening.opening_negative615_list_100_not_mem Internal.SnakyOpening.opening_negative615_list_101_not_mem
def Internal.SnakyOpening.opening_negative615_list_103 : List Cell := ([(8, -7), (8, -6), (8, -5), (8, -4), (8, -3), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3)] : List Cell)
theorem Internal.SnakyOpening.opening_negative615_list_103_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_103 := by decide
def Internal.SnakyOpening.opening_negative615_list_104 : List Cell := ([(8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (8, 11), (8, 12), (9, -12), (9, -11)] : List Cell)
theorem Internal.SnakyOpening.opening_negative615_list_104_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_104 := by decide
def Internal.SnakyOpening.opening_negative615_list_102 : List Cell := Internal.SnakyOpening.opening_negative615_list_103 ++ Internal.SnakyOpening.opening_negative615_list_104
theorem Internal.SnakyOpening.opening_negative615_list_102_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_102 :=
  List.not_mem_append (a := (1, -1)) (s := Internal.SnakyOpening.opening_negative615_list_103) (t := Internal.SnakyOpening.opening_negative615_list_104)
    Internal.SnakyOpening.opening_negative615_list_103_not_mem Internal.SnakyOpening.opening_negative615_list_104_not_mem
def Internal.SnakyOpening.opening_negative615_list_98 : List Cell := Internal.SnakyOpening.opening_negative615_list_99 ++ Internal.SnakyOpening.opening_negative615_list_102
theorem Internal.SnakyOpening.opening_negative615_list_98_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_98 :=
  List.not_mem_append (a := (1, -1)) (s := Internal.SnakyOpening.opening_negative615_list_99) (t := Internal.SnakyOpening.opening_negative615_list_102)
    Internal.SnakyOpening.opening_negative615_list_99_not_mem Internal.SnakyOpening.opening_negative615_list_102_not_mem
def Internal.SnakyOpening.opening_negative615_list_107 : List Cell := ([(9, -10), (9, -9), (9, -8), (9, -7), (9, -6), (9, -5), (9, -4), (9, -3), (9, -2), (9, -1)] : List Cell)
theorem Internal.SnakyOpening.opening_negative615_list_107_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_107 := by decide
def Internal.SnakyOpening.opening_negative615_list_108 : List Cell := ([(9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (9, 10)] : List Cell)
theorem Internal.SnakyOpening.opening_negative615_list_108_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_108 := by decide
def Internal.SnakyOpening.opening_negative615_list_106 : List Cell := Internal.SnakyOpening.opening_negative615_list_107 ++ Internal.SnakyOpening.opening_negative615_list_108
theorem Internal.SnakyOpening.opening_negative615_list_106_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_106 :=
  List.not_mem_append (a := (1, -1)) (s := Internal.SnakyOpening.opening_negative615_list_107) (t := Internal.SnakyOpening.opening_negative615_list_108)
    Internal.SnakyOpening.opening_negative615_list_107_not_mem Internal.SnakyOpening.opening_negative615_list_108_not_mem
def Internal.SnakyOpening.opening_negative615_list_110 : List Cell := ([(9, 11), (9, 12), (10, -10), (10, -9), (10, -8), (10, -7), (10, -6), (10, -5), (10, -4), (10, -3), (10, -2)] : List Cell)
theorem Internal.SnakyOpening.opening_negative615_list_110_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_110 := by decide
def Internal.SnakyOpening.opening_negative615_list_111 : List Cell := ([(10, -1), (10, 0), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (10, 9)] : List Cell)
theorem Internal.SnakyOpening.opening_negative615_list_111_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_111 := by decide
def Internal.SnakyOpening.opening_negative615_list_109 : List Cell := Internal.SnakyOpening.opening_negative615_list_110 ++ Internal.SnakyOpening.opening_negative615_list_111
theorem Internal.SnakyOpening.opening_negative615_list_109_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_109 :=
  List.not_mem_append (a := (1, -1)) (s := Internal.SnakyOpening.opening_negative615_list_110) (t := Internal.SnakyOpening.opening_negative615_list_111)
    Internal.SnakyOpening.opening_negative615_list_110_not_mem Internal.SnakyOpening.opening_negative615_list_111_not_mem
def Internal.SnakyOpening.opening_negative615_list_105 : List Cell := Internal.SnakyOpening.opening_negative615_list_106 ++ Internal.SnakyOpening.opening_negative615_list_109
theorem Internal.SnakyOpening.opening_negative615_list_105_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_105 :=
  List.not_mem_append (a := (1, -1)) (s := Internal.SnakyOpening.opening_negative615_list_106) (t := Internal.SnakyOpening.opening_negative615_list_109)
    Internal.SnakyOpening.opening_negative615_list_106_not_mem Internal.SnakyOpening.opening_negative615_list_109_not_mem
def Internal.SnakyOpening.opening_negative615_list_97 : List Cell := Internal.SnakyOpening.opening_negative615_list_98 ++ Internal.SnakyOpening.opening_negative615_list_105
theorem Internal.SnakyOpening.opening_negative615_list_97_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_97 :=
  List.not_mem_append (a := (1, -1)) (s := Internal.SnakyOpening.opening_negative615_list_98) (t := Internal.SnakyOpening.opening_negative615_list_105)
    Internal.SnakyOpening.opening_negative615_list_98_not_mem Internal.SnakyOpening.opening_negative615_list_105_not_mem
def Internal.SnakyOpening.opening_negative615_list_115 : List Cell := ([(10, 10), (10, 11), (10, 12), (11, -9), (11, -8), (11, -7), (11, -6), (11, -5), (11, -4), (11, -3)] : List Cell)
theorem Internal.SnakyOpening.opening_negative615_list_115_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_115 := by decide
def Internal.SnakyOpening.opening_negative615_list_116 : List Cell := ([(11, -2), (11, -1), (11, 0), (11, 1), (11, 2), (11, 3), (11, 4), (11, 5), (11, 6), (11, 7), (11, 8)] : List Cell)
theorem Internal.SnakyOpening.opening_negative615_list_116_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_116 := by decide
def Internal.SnakyOpening.opening_negative615_list_114 : List Cell := Internal.SnakyOpening.opening_negative615_list_115 ++ Internal.SnakyOpening.opening_negative615_list_116
theorem Internal.SnakyOpening.opening_negative615_list_114_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_114 :=
  List.not_mem_append (a := (1, -1)) (s := Internal.SnakyOpening.opening_negative615_list_115) (t := Internal.SnakyOpening.opening_negative615_list_116)
    Internal.SnakyOpening.opening_negative615_list_115_not_mem Internal.SnakyOpening.opening_negative615_list_116_not_mem
def Internal.SnakyOpening.opening_negative615_list_118 : List Cell := ([(11, 9), (11, 10), (12, -9), (12, -8), (12, -7), (12, -6), (12, -5), (12, -4), (12, -3), (12, -2), (12, -1)] : List Cell)
theorem Internal.SnakyOpening.opening_negative615_list_118_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_118 := by decide
def Internal.SnakyOpening.opening_negative615_list_119 : List Cell := ([(12, 0), (12, 1), (12, 2), (12, 3), (12, 4), (12, 5), (12, 6), (12, 7), (12, 8), (12, 9), (13, -6)] : List Cell)
theorem Internal.SnakyOpening.opening_negative615_list_119_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_119 := by decide
def Internal.SnakyOpening.opening_negative615_list_117 : List Cell := Internal.SnakyOpening.opening_negative615_list_118 ++ Internal.SnakyOpening.opening_negative615_list_119
theorem Internal.SnakyOpening.opening_negative615_list_117_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_117 :=
  List.not_mem_append (a := (1, -1)) (s := Internal.SnakyOpening.opening_negative615_list_118) (t := Internal.SnakyOpening.opening_negative615_list_119)
    Internal.SnakyOpening.opening_negative615_list_118_not_mem Internal.SnakyOpening.opening_negative615_list_119_not_mem
def Internal.SnakyOpening.opening_negative615_list_113 : List Cell := Internal.SnakyOpening.opening_negative615_list_114 ++ Internal.SnakyOpening.opening_negative615_list_117
theorem Internal.SnakyOpening.opening_negative615_list_113_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_113 :=
  List.not_mem_append (a := (1, -1)) (s := Internal.SnakyOpening.opening_negative615_list_114) (t := Internal.SnakyOpening.opening_negative615_list_117)
    Internal.SnakyOpening.opening_negative615_list_114_not_mem Internal.SnakyOpening.opening_negative615_list_117_not_mem
def Internal.SnakyOpening.opening_negative615_list_122 : List Cell := ([(13, -5), (13, -4), (13, -3), (13, -2), (13, -1), (13, 0), (13, 1), (13, 2), (13, 3), (13, 4)] : List Cell)
theorem Internal.SnakyOpening.opening_negative615_list_122_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_122 := by decide
def Internal.SnakyOpening.opening_negative615_list_123 : List Cell := ([(13, 5), (13, 6), (13, 7), (13, 8), (13, 9), (14, -6), (14, -5), (14, -4), (14, -3), (14, -2), (14, -1)] : List Cell)
theorem Internal.SnakyOpening.opening_negative615_list_123_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_123 := by decide
def Internal.SnakyOpening.opening_negative615_list_121 : List Cell := Internal.SnakyOpening.opening_negative615_list_122 ++ Internal.SnakyOpening.opening_negative615_list_123
theorem Internal.SnakyOpening.opening_negative615_list_121_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_121 :=
  List.not_mem_append (a := (1, -1)) (s := Internal.SnakyOpening.opening_negative615_list_122) (t := Internal.SnakyOpening.opening_negative615_list_123)
    Internal.SnakyOpening.opening_negative615_list_122_not_mem Internal.SnakyOpening.opening_negative615_list_123_not_mem
def Internal.SnakyOpening.opening_negative615_list_125 : List Cell := ([(14, 0), (14, 1), (14, 2), (14, 3), (14, 4), (14, 5), (14, 6), (15, -2), (15, -1), (15, 0), (15, 1)] : List Cell)
theorem Internal.SnakyOpening.opening_negative615_list_125_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_125 := by decide
def Internal.SnakyOpening.opening_negative615_list_126 : List Cell := ([(15, 2), (15, 3), (15, 4), (15, 5), (15, 6), (16, -2), (16, 0), (16, 1), (16, 2), (17, 0), (17, 2)] : List Cell)
theorem Internal.SnakyOpening.opening_negative615_list_126_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_126 := by decide
def Internal.SnakyOpening.opening_negative615_list_124 : List Cell := Internal.SnakyOpening.opening_negative615_list_125 ++ Internal.SnakyOpening.opening_negative615_list_126
theorem Internal.SnakyOpening.opening_negative615_list_124_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_124 :=
  List.not_mem_append (a := (1, -1)) (s := Internal.SnakyOpening.opening_negative615_list_125) (t := Internal.SnakyOpening.opening_negative615_list_126)
    Internal.SnakyOpening.opening_negative615_list_125_not_mem Internal.SnakyOpening.opening_negative615_list_126_not_mem
def Internal.SnakyOpening.opening_negative615_list_120 : List Cell := Internal.SnakyOpening.opening_negative615_list_121 ++ Internal.SnakyOpening.opening_negative615_list_124
theorem Internal.SnakyOpening.opening_negative615_list_120_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_120 :=
  List.not_mem_append (a := (1, -1)) (s := Internal.SnakyOpening.opening_negative615_list_121) (t := Internal.SnakyOpening.opening_negative615_list_124)
    Internal.SnakyOpening.opening_negative615_list_121_not_mem Internal.SnakyOpening.opening_negative615_list_124_not_mem
def Internal.SnakyOpening.opening_negative615_list_112 : List Cell := Internal.SnakyOpening.opening_negative615_list_113 ++ Internal.SnakyOpening.opening_negative615_list_120
theorem Internal.SnakyOpening.opening_negative615_list_112_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_112 :=
  List.not_mem_append (a := (1, -1)) (s := Internal.SnakyOpening.opening_negative615_list_113) (t := Internal.SnakyOpening.opening_negative615_list_120)
    Internal.SnakyOpening.opening_negative615_list_113_not_mem Internal.SnakyOpening.opening_negative615_list_120_not_mem
def Internal.SnakyOpening.opening_negative615_list_96 : List Cell := Internal.SnakyOpening.opening_negative615_list_97 ++ Internal.SnakyOpening.opening_negative615_list_112
theorem Internal.SnakyOpening.opening_negative615_list_96_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_96 :=
  List.not_mem_append (a := (1, -1)) (s := Internal.SnakyOpening.opening_negative615_list_97) (t := Internal.SnakyOpening.opening_negative615_list_112)
    Internal.SnakyOpening.opening_negative615_list_97_not_mem Internal.SnakyOpening.opening_negative615_list_112_not_mem
def Internal.SnakyOpening.opening_negative615_list_64 : List Cell := Internal.SnakyOpening.opening_negative615_list_65 ++ Internal.SnakyOpening.opening_negative615_list_96
theorem Internal.SnakyOpening.opening_negative615_list_64_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_64 :=
  List.not_mem_append (a := (1, -1)) (s := Internal.SnakyOpening.opening_negative615_list_65) (t := Internal.SnakyOpening.opening_negative615_list_96)
    Internal.SnakyOpening.opening_negative615_list_65_not_mem Internal.SnakyOpening.opening_negative615_list_96_not_mem
def Internal.SnakyOpening.opening_negative615_list_0 : List Cell := Internal.SnakyOpening.opening_negative615_list_1 ++ Internal.SnakyOpening.opening_negative615_list_64
theorem Internal.SnakyOpening.opening_negative615_list_0_not_mem : (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_0 :=
  List.not_mem_append (a := (1, -1)) (s := Internal.SnakyOpening.opening_negative615_list_1) (t := Internal.SnakyOpening.opening_negative615_list_64)
    Internal.SnakyOpening.opening_negative615_list_1_not_mem Internal.SnakyOpening.opening_negative615_list_64_not_mem
theorem Internal.SnakyOpening.opening_breaker_outside_615 : (1, -1) ∉ envelope_615 := by
  change (1, -1) ∉ Internal.SnakyOpening.opening_negative615_list_0
  exact Internal.SnakyOpening.opening_negative615_list_0_not_mem
theorem Internal.SnakyOpening.opening_breaker_disjoint_615 :
    Disjoint ({(1, -1)} : Finset Cell) envelope_615 :=
  Finset.disjoint_singleton_left.mpr Internal.SnakyOpening.opening_breaker_outside_615
theorem row615_pair_after_breaker : ∀ b, b ∉ localPair → b ∉ ({(1, -1)} : Finset Cell) →
    WinsIn HasSnaky 33 localPair (insert b {(1, -1)}) := by
  refine breaker_turn HasSnaky 33 childrenC_615 childrenD_615 children_work_615
    localPair {(1, -1)} envelope_615 (by decide) ?_ child_envelope_sub_615 ?_ Internal.SnakyOpening.opening_breaker_disjoint_615
  · intro j; simpa only [row615_owned] using child_required_sub_615 j
  · intro b hb; simpa only [row615_owned] using common_sub_615 (mem_commonEnvelope childrenD_615 b hb)
theorem near_local_left : WinsIn HasSnaky 34 {(0, 0)} {(1, -1)} := by
  apply WinsIn.move (1, 0) (by decide) (by decide)
  intro b hbM hbB
  have hM : insert (1, 0) ({(0, 0)} : Finset Cell) = localPair := by decide
  rw [hM]
  exact row615_pair_after_breaker b (by simpa only [hM] using hbM) hbB
theorem near_local_right : WinsIn HasSnaky 34 {(1, 0)} {(1, -1)} := by
  apply WinsIn.move (0, 0) (by decide) (by decide)
  intro b hbM hbB
  have hM : insert (0, 0) ({(1, 0)} : Finset Cell) = localPair := by decide
  rw [hM]
  exact row615_pair_after_breaker b (by simpa only [hM] using hbM) hbB
theorem near_works : ∀ i, WinsIn HasSnaky 34 {(0, 0)} {nearPoint i} := by
  intro i
  fin_cases i
  · have h := near_local_left.transport (placementEquiv 4 (0, 0))
      (fun X hx => by simpa only [coe_placementEquiv] using HasSnaky.placed 4 (0, 0) X hx)
    simpa [Finset.image_singleton, placementEquiv_apply, placement, orient, nearPoint] using h
  · have h := near_local_right.transport (placementEquiv 1 (0, -1))
      (fun X hx => by simpa only [coe_placementEquiv] using HasSnaky.placed 1 (0, -1) X hx)
    simpa [Finset.image_singleton, placementEquiv_apply, placement, orient, nearPoint] using h
  · have h := near_local_left.transport (placementEquiv 1 (0, 0))
      (fun X hx => by simpa only [coe_placementEquiv] using HasSnaky.placed 1 (0, 0) X hx)
    simpa [Finset.image_singleton, placementEquiv_apply, placement, orient, nearPoint] using h
  · have h := near_local_right.transport (placementEquiv 0 (-1, 0))
      (fun X hx => by simpa only [coe_placementEquiv] using HasSnaky.placed 0 (-1, 0) X hx)
    simpa [Finset.image_singleton, placementEquiv_apply, placement, orient, nearPoint] using h
  · have h := near_local_right.transport (placementEquiv 2 (-1, 0))
      (fun X hx => by simpa only [coe_placementEquiv] using HasSnaky.placed 2 (-1, 0) X hx)
    simpa [Finset.image_singleton, placementEquiv_apply, placement, orient, nearPoint] using h
  · have h := near_local_left.transport (placementEquiv 0 (0, 0))
      (fun X hx => by simpa only [coe_placementEquiv] using HasSnaky.placed 0 (0, 0) X hx)
    simpa [Finset.image_singleton, placementEquiv_apply, placement, orient, nearPoint] using h
  · have h := near_local_right.transport (placementEquiv 3 (0, -1))
      (fun X hx => by simpa only [coe_placementEquiv] using HasSnaky.placed 3 (0, -1) X hx)
    simpa [Finset.image_singleton, placementEquiv_apply, placement, orient, nearPoint] using h
  · have h := near_local_left.transport (placementEquiv 2 (0, 0))
      (fun X hx => by simpa only [coe_placementEquiv] using HasSnaky.placed 2 (0, 0) X hx)
    simpa [Finset.image_singleton, placementEquiv_apply, placement, orient, nearPoint] using h
theorem all_first_replies (q : Cell) (hqo : q ≠ (0, 0)) :
    WinsIn HasSnaky 34 {(0, 0)} {q} := by
  by_cases hqN : q ∈ nearBlock
  · have hq : q ∈ nearBlock.erase (0, 0) := Finset.mem_erase.mpr ⟨hqo, hqN⟩
    rw [nearPoint_cover] at hq
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hq
    simpa only [hi] using near_works i
  · apply (one_stone_after_distant_reply HasSnaky 27 (0, 0) nearBlock distantEnvelopes
      distant_works (fun b hb => distant_common_sub (mem_commonEnvelope distantEnvelopes b hb))
      q hqo hqN).mono
    decide
theorem empty_board_wins : WinsIn HasSnaky 35 ∅ ∅ :=
  from_first_reply HasSnaky 34 (0, 0) all_first_replies
end SnakyConditional

end OAI
