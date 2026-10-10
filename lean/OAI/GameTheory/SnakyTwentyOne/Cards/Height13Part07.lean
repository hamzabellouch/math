import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part02
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_720_i0 : Finset Cell := ⟨(([(4, 5), (5, 5), (5, 6), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_720_i0 : Finset Cell := ⟨(([(0, 4), (0, 6), (1, 4), (1, 5), (1, 6), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 3), (3, 4), (3, 5), (4, 5), (4, 6), (5, 5), (5, 6), (6, 5), (6, 6), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_720_i0 : Fin 3 → Finset Cell := ![(placed21 7 (6, 6) required_10), (placed21 2 (6, 3) required_180), (placed21 1 (3, 5) required_200)]
def childrenD_720_i0 : Fin 3 → Finset Cell := ![(placed21 7 (6, 6) envelope_10), (placed21 2 (6, 3) envelope_180), (placed21 1 (3, 5) envelope_200)]
theorem common_sub_720_i0 : commonEnvelope childrenD_720_i0 ⊆ insert (3, 5) required_720_i0 := by decide +kernel
theorem child_required_sub_720_i0 : ∀ j, childrenC_720_i0 j ⊆ insert (3, 5) required_720_i0 := by decide +kernel
theorem child_envelope_sub_720_i0 : ∀ j, childrenD_720_i0 j ⊆ envelope_720_i0 := by decide +kernel
theorem pivot_mem_720_i0 : (3, 5) ∈ envelope_720_i0 := by decide +kernel
theorem children_work_720_i0 : ∀ j, Template HasSnaky 6 (childrenC_720_i0 j) (childrenD_720_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_10 7 (6, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_180 2 (6, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_200 1 (3, 5)).mono (by decide +kernel)
theorem row_works_720_i0 : Template HasSnaky 7 required_720_i0 envelope_720_i0 := by
  refine compose HasSnaky 6 childrenC_720_i0 childrenD_720_i0 children_work_720_i0 (3, 5)
    required_720_i0 envelope_720_i0 pivot_mem_720_i0 child_required_sub_720_i0 child_envelope_sub_720_i0 ?_
  intro b hb
  exact common_sub_720_i0 (mem_commonEnvelope childrenD_720_i0 b hb)
def required_720_i4 : Finset Cell := ⟨(([(5, 6), (5, 7), (7, 5), (7, 6), (7, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_720_i4 : Finset Cell := ⟨(([(4, 6), (5, 6), (5, 7), (6, 7), (6, 8), (6, 9), (6, 10), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (8, 6), (8, 7), (9, 6), (9, 7), (9, 8), (10, 6), (10, 7), (10, 8), (11, 6), (11, 7), (11, 8), (12, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_720_i4 : Fin 2 → Finset Cell := ![(placed21 2 (7, 4) required_52), (placed21 1 (4, 6) required_315)]
def childrenD_720_i4 : Fin 2 → Finset Cell := ![(placed21 2 (7, 4) envelope_52), (placed21 1 (4, 6) envelope_315)]
theorem common_sub_720_i4 : commonEnvelope childrenD_720_i4 ⊆ insert (6, 7) required_720_i4 := by decide +kernel
theorem child_required_sub_720_i4 : ∀ j, childrenC_720_i4 j ⊆ insert (6, 7) required_720_i4 := by decide +kernel
theorem child_envelope_sub_720_i4 : ∀ j, childrenD_720_i4 j ⊆ envelope_720_i4 := by decide +kernel
theorem pivot_mem_720_i4 : (6, 7) ∈ envelope_720_i4 := by decide +kernel
theorem children_work_720_i4 : ∀ j, Template HasSnaky 6 (childrenC_720_i4 j) (childrenD_720_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_52 2 (7, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_315 1 (4, 6)).mono (by decide +kernel)
theorem row_works_720_i4 : Template HasSnaky 7 required_720_i4 envelope_720_i4 := by
  refine compose HasSnaky 6 childrenC_720_i4 childrenD_720_i4 children_work_720_i4 (6, 7)
    required_720_i4 envelope_720_i4 pivot_mem_720_i4 child_required_sub_720_i4 child_envelope_sub_720_i4 ?_
  intro b hb
  exact common_sub_720_i4 (mem_commonEnvelope childrenD_720_i4 b hb)
def required_720_i5 : Finset Cell := ⟨(([(5, 6), (5, 7), (7, 5), (7, 6), (7, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_720_i5 : Finset Cell := ⟨(([(4, 6), (5, 6), (5, 7), (6, 1), (6, 2), (6, 3), (6, 7), (6, 8), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_720_i5 : Fin 2 → Finset Cell := ![(placed21 7 (8, 7) required_197), (placed21 5 (8, 4) required_201)]
def childrenD_720_i5 : Fin 2 → Finset Cell := ![(placed21 7 (8, 7) envelope_197), (placed21 5 (8, 4) envelope_201)]
theorem common_sub_720_i5 : commonEnvelope childrenD_720_i5 ⊆ insert (7, 4) required_720_i5 := by decide +kernel
theorem child_required_sub_720_i5 : ∀ j, childrenC_720_i5 j ⊆ insert (7, 4) required_720_i5 := by decide +kernel
theorem child_envelope_sub_720_i5 : ∀ j, childrenD_720_i5 j ⊆ envelope_720_i5 := by decide +kernel
theorem pivot_mem_720_i5 : (7, 4) ∈ envelope_720_i5 := by decide +kernel
theorem children_work_720_i5 : ∀ j, Template HasSnaky 5 (childrenC_720_i5 j) (childrenD_720_i5 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_197 7 (8, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_201 5 (8, 4)).mono (by decide +kernel)
theorem row_works_720_i5 : Template HasSnaky 6 required_720_i5 envelope_720_i5 := by
  refine compose HasSnaky 5 childrenC_720_i5 childrenD_720_i5 children_work_720_i5 (7, 4)
    required_720_i5 envelope_720_i5 pivot_mem_720_i5 child_required_sub_720_i5 child_envelope_sub_720_i5 ?_
  intro b hb
  exact common_sub_720_i5 (mem_commonEnvelope childrenD_720_i5 b hb)
def required_720_i3 : Finset Cell := ⟨(([(5, 6), (5, 7), (7, 5), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_720_i3 : Finset Cell := ⟨(([(4, 6), (5, 6), (5, 7), (6, 1), (6, 2), (6, 3), (6, 7), (6, 8), (6, 9), (6, 10), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (9, 6), (9, 7), (9, 8), (9, 9), (10, 6), (10, 7), (10, 8), (10, 9), (11, 6), (11, 7), (11, 8), (12, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_720_i3 : Fin 6 → Finset Cell := ![(placed21 2 (8, 3) required_12), (placed21 2 (8, 3) required_13), (placed21 6 (8, 10) required_369), (placed21 1 (5, 4) required_474), required_720_i4, required_720_i5]
def childrenD_720_i3 : Fin 6 → Finset Cell := ![(placed21 2 (8, 3) envelope_12), (placed21 2 (8, 3) envelope_13), (placed21 6 (8, 10) envelope_369), (placed21 1 (5, 4) envelope_474), envelope_720_i4, envelope_720_i5]
theorem common_sub_720_i3 : commonEnvelope childrenD_720_i3 ⊆ insert (7, 7) required_720_i3 := by decide +kernel
theorem child_required_sub_720_i3 : ∀ j, childrenC_720_i3 j ⊆ insert (7, 7) required_720_i3 := by decide +kernel
theorem child_envelope_sub_720_i3 : ∀ j, childrenD_720_i3 j ⊆ envelope_720_i3 := by decide +kernel
theorem pivot_mem_720_i3 : (7, 7) ∈ envelope_720_i3 := by decide +kernel
theorem children_work_720_i3 : ∀ j, Template HasSnaky 9 (childrenC_720_i3 j) (childrenD_720_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_12 2 (8, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_13 2 (8, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_369 6 (8, 10)).mono (by decide +kernel)
  · exact (placed21_template row_works_474 1 (5, 4)).mono (by decide +kernel)
  · exact row_works_720_i4.mono (by decide +kernel)
  · exact row_works_720_i5.mono (by decide +kernel)
theorem row_works_720_i3 : Template HasSnaky 10 required_720_i3 envelope_720_i3 := by
  refine compose HasSnaky 9 childrenC_720_i3 childrenD_720_i3 children_work_720_i3 (7, 7)
    required_720_i3 envelope_720_i3 pivot_mem_720_i3 child_required_sub_720_i3 child_envelope_sub_720_i3 ?_
  intro b hb
  exact common_sub_720_i3 (mem_commonEnvelope childrenD_720_i3 b hb)
def required_720_i2 : Finset Cell := ⟨(([(4, 4), (4, 5), (5, 5), (5, 6), (7, 5), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_720_i2 : Finset Cell := ⟨(([(4, 4), (4, 5), (4, 6), (5, 5), (5, 6), (5, 7), (5, 8), (6, 1), (6, 2), (6, 3), (6, 7), (6, 8), (6, 9), (6, 10), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (9, 6), (9, 7), (9, 8), (9, 9), (10, 6), (10, 7), (10, 8), (10, 9), (11, 6), (11, 7), (11, 8), (12, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_720_i2 : Fin 2 → Finset Cell := ![(placed21 7 (5, 8) required_0), required_720_i3]
def childrenD_720_i2 : Fin 2 → Finset Cell := ![(placed21 7 (5, 8) envelope_0), envelope_720_i3]
theorem common_sub_720_i2 : commonEnvelope childrenD_720_i2 ⊆ insert (5, 7) required_720_i2 := by decide +kernel
theorem child_required_sub_720_i2 : ∀ j, childrenC_720_i2 j ⊆ insert (5, 7) required_720_i2 := by decide +kernel
theorem child_envelope_sub_720_i2 : ∀ j, childrenD_720_i2 j ⊆ envelope_720_i2 := by decide +kernel
theorem pivot_mem_720_i2 : (5, 7) ∈ envelope_720_i2 := by decide +kernel
theorem children_work_720_i2 : ∀ j, Template HasSnaky 10 (childrenC_720_i2 j) (childrenD_720_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 7 (5, 8)).mono (by decide +kernel)
  · exact row_works_720_i3.mono (by decide +kernel)
theorem row_works_720_i2 : Template HasSnaky 11 required_720_i2 envelope_720_i2 := by
  refine compose HasSnaky 10 childrenC_720_i2 childrenD_720_i2 children_work_720_i2 (5, 7)
    required_720_i2 envelope_720_i2 pivot_mem_720_i2 child_required_sub_720_i2 child_envelope_sub_720_i2 ?_
  intro b hb
  exact common_sub_720_i2 (mem_commonEnvelope childrenD_720_i2 b hb)
def required_720_i1 : Finset Cell := ⟨(([(4, 4), (4, 5), (5, 5), (5, 6), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_720_i1 : Finset Cell := ⟨(([(3, 4), (4, 4), (4, 5), (4, 6), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 1), (6, 2), (6, 3), (6, 5), (6, 7), (6, 8), (6, 9), (6, 10), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (9, 6), (9, 7), (9, 8), (9, 9), (10, 6), (10, 7), (10, 8), (10, 9), (11, 6), (11, 7), (11, 8), (12, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_720_i1 : Fin 3 → Finset Cell := ![(placed21 1 (3, 4) required_40), (placed21 1 (3, 4) required_310), required_720_i2]
def childrenD_720_i1 : Fin 3 → Finset Cell := ![(placed21 1 (3, 4) envelope_40), (placed21 1 (3, 4) envelope_310), envelope_720_i2]
theorem common_sub_720_i1 : commonEnvelope childrenD_720_i1 ⊆ insert (7, 5) required_720_i1 := by decide +kernel
theorem child_required_sub_720_i1 : ∀ j, childrenC_720_i1 j ⊆ insert (7, 5) required_720_i1 := by decide +kernel
theorem child_envelope_sub_720_i1 : ∀ j, childrenD_720_i1 j ⊆ envelope_720_i1 := by decide +kernel
theorem pivot_mem_720_i1 : (7, 5) ∈ envelope_720_i1 := by decide +kernel
theorem children_work_720_i1 : ∀ j, Template HasSnaky 11 (childrenC_720_i1 j) (childrenD_720_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_40 1 (3, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_310 1 (3, 4)).mono (by decide +kernel)
  · exact row_works_720_i2.mono (by decide +kernel)
theorem row_works_720_i1 : Template HasSnaky 12 required_720_i1 envelope_720_i1 := by
  refine compose HasSnaky 11 childrenC_720_i1 childrenD_720_i1 children_work_720_i1 (7, 5)
    required_720_i1 envelope_720_i1 pivot_mem_720_i1 child_required_sub_720_i1 child_envelope_sub_720_i1 ?_
  intro b hb
  exact common_sub_720_i1 (mem_commonEnvelope childrenD_720_i1 b hb)
def required_720 : Finset Cell := ⟨(([(4, 4), (4, 5), (5, 5), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_720 : Finset Cell := ⟨(([(0, 4), (0, 6), (1, 4), (1, 5), (1, 6), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 3), (3, 4), (3, 5), (4, 4), (4, 5), (4, 6), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 1), (6, 2), (6, 3), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (9, 6), (9, 7), (9, 8), (9, 9), (10, 6), (10, 7), (10, 8), (10, 9), (11, 6), (11, 7), (11, 8), (12, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_720 : Fin 4 → Finset Cell := ![(placed21 7 (8, 6) required_54), (placed21 7 (8, 6) required_64), required_720_i0, required_720_i1]
def childrenD_720 : Fin 4 → Finset Cell := ![(placed21 7 (8, 6) envelope_54), (placed21 7 (8, 6) envelope_64), envelope_720_i0, envelope_720_i1]
theorem common_sub_720 : commonEnvelope childrenD_720 ⊆ insert (7, 6) required_720 := by decide +kernel
theorem child_required_sub_720 : ∀ j, childrenC_720 j ⊆ insert (7, 6) required_720 := by decide +kernel
theorem child_envelope_sub_720 : ∀ j, childrenD_720 j ⊆ envelope_720 := by decide +kernel
theorem pivot_mem_720 : (7, 6) ∈ envelope_720 := by decide +kernel
theorem children_work_720 : ∀ j, Template HasSnaky 12 (childrenC_720 j) (childrenD_720 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_54 7 (8, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_64 7 (8, 6)).mono (by decide +kernel)
  · exact row_works_720_i0.mono (by decide +kernel)
  · exact row_works_720_i1.mono (by decide +kernel)
theorem row_works_720 : Template HasSnaky 13 required_720 envelope_720 := by
  refine compose HasSnaky 12 childrenC_720 childrenD_720 children_work_720 (7, 6)
    required_720 envelope_720 pivot_mem_720 child_required_sub_720 child_envelope_sub_720 ?_
  intro b hb
  exact common_sub_720 (mem_commonEnvelope childrenD_720 b hb)
def height_720_i0 : ℕ := 7
def childrenH_720_i0 : Fin 3 → ℕ := ![height_10, height_180, height_200]
theorem height_exact_720_i0 : height_720_i0 = 1 + Finset.univ.sup childrenH_720_i0 := by decide +kernel
theorem required_origin_720_i0 : ∀ x ∈ required_720_i0,
    (∃ j, x ∈ childrenC_720_i0 j) ∨ ∀ j, x ∈ childrenD_720_i0 j := by decide +kernel
theorem required_exact_720_i0 : required_720_i0 =
    ((Finset.univ.biUnion childrenC_720_i0) ∪ commonEnvelope childrenD_720_i0).erase (3, 5) := by
  exact required_eq_combination childrenC_720_i0 childrenD_720_i0 (3, 5) required_720_i0
    (by decide +kernel) child_required_sub_720_i0 common_sub_720_i0 required_origin_720_i0
theorem envelope_origin_720_i0 : ∀ x ∈ envelope_720_i0,
    x = (3, 5) ∨ ∃ j, x ∈ childrenD_720_i0 j := by decide +kernel
theorem envelope_exact_720_i0 : envelope_720_i0 =
    insert (3, 5) (Finset.univ.biUnion childrenD_720_i0) := by
  exact envelope_eq_combination childrenD_720_i0 (3, 5) envelope_720_i0
    pivot_mem_720_i0 child_envelope_sub_720_i0 envelope_origin_720_i0
def checked_720_i0 : CheckedCard where
  required := required_720_i0
  envelope := envelope_720_i0
  height := height_720_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_720_i0
def height_720_i4 : ℕ := 7
def childrenH_720_i4 : Fin 2 → ℕ := ![height_52, height_315]
theorem height_exact_720_i4 : height_720_i4 = 1 + Finset.univ.sup childrenH_720_i4 := by decide +kernel
theorem required_origin_720_i4 : ∀ x ∈ required_720_i4,
    (∃ j, x ∈ childrenC_720_i4 j) ∨ ∀ j, x ∈ childrenD_720_i4 j := by decide +kernel
theorem required_exact_720_i4 : required_720_i4 =
    ((Finset.univ.biUnion childrenC_720_i4) ∪ commonEnvelope childrenD_720_i4).erase (6, 7) := by
  exact required_eq_combination childrenC_720_i4 childrenD_720_i4 (6, 7) required_720_i4
    (by decide +kernel) child_required_sub_720_i4 common_sub_720_i4 required_origin_720_i4
theorem envelope_origin_720_i4 : ∀ x ∈ envelope_720_i4,
    x = (6, 7) ∨ ∃ j, x ∈ childrenD_720_i4 j := by decide +kernel
theorem envelope_exact_720_i4 : envelope_720_i4 =
    insert (6, 7) (Finset.univ.biUnion childrenD_720_i4) := by
  exact envelope_eq_combination childrenD_720_i4 (6, 7) envelope_720_i4
    pivot_mem_720_i4 child_envelope_sub_720_i4 envelope_origin_720_i4
def checked_720_i4 : CheckedCard where
  required := required_720_i4
  envelope := envelope_720_i4
  height := height_720_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_720_i4
def height_720_i5 : ℕ := 6
def childrenH_720_i5 : Fin 2 → ℕ := ![height_197, height_201]
theorem height_exact_720_i5 : height_720_i5 = 1 + Finset.univ.sup childrenH_720_i5 := by decide +kernel
theorem required_origin_720_i5 : ∀ x ∈ required_720_i5,
    (∃ j, x ∈ childrenC_720_i5 j) ∨ ∀ j, x ∈ childrenD_720_i5 j := by decide +kernel
theorem required_exact_720_i5 : required_720_i5 =
    ((Finset.univ.biUnion childrenC_720_i5) ∪ commonEnvelope childrenD_720_i5).erase (7, 4) := by
  exact required_eq_combination childrenC_720_i5 childrenD_720_i5 (7, 4) required_720_i5
    (by decide +kernel) child_required_sub_720_i5 common_sub_720_i5 required_origin_720_i5
theorem envelope_origin_720_i5 : ∀ x ∈ envelope_720_i5,
    x = (7, 4) ∨ ∃ j, x ∈ childrenD_720_i5 j := by decide +kernel
theorem envelope_exact_720_i5 : envelope_720_i5 =
    insert (7, 4) (Finset.univ.biUnion childrenD_720_i5) := by
  exact envelope_eq_combination childrenD_720_i5 (7, 4) envelope_720_i5
    pivot_mem_720_i5 child_envelope_sub_720_i5 envelope_origin_720_i5
def checked_720_i5 : CheckedCard where
  required := required_720_i5
  envelope := envelope_720_i5
  height := height_720_i5
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_720_i5
def height_720_i3 : ℕ := 10
def childrenH_720_i3 : Fin 6 → ℕ := ![height_12, height_13, height_369, height_474, height_720_i4, height_720_i5]
theorem height_exact_720_i3 : height_720_i3 = 1 + Finset.univ.sup childrenH_720_i3 := by decide +kernel
theorem required_origin_720_i3 : ∀ x ∈ required_720_i3,
    (∃ j, x ∈ childrenC_720_i3 j) ∨ ∀ j, x ∈ childrenD_720_i3 j := by decide +kernel
theorem required_exact_720_i3 : required_720_i3 =
    ((Finset.univ.biUnion childrenC_720_i3) ∪ commonEnvelope childrenD_720_i3).erase (7, 7) := by
  exact required_eq_combination childrenC_720_i3 childrenD_720_i3 (7, 7) required_720_i3
    (by decide +kernel) child_required_sub_720_i3 common_sub_720_i3 required_origin_720_i3
theorem envelope_origin_720_i3 : ∀ x ∈ envelope_720_i3,
    x = (7, 7) ∨ ∃ j, x ∈ childrenD_720_i3 j := by decide +kernel
theorem envelope_exact_720_i3 : envelope_720_i3 =
    insert (7, 7) (Finset.univ.biUnion childrenD_720_i3) := by
  exact envelope_eq_combination childrenD_720_i3 (7, 7) envelope_720_i3
    pivot_mem_720_i3 child_envelope_sub_720_i3 envelope_origin_720_i3
def checked_720_i3 : CheckedCard where
  required := required_720_i3
  envelope := envelope_720_i3
  height := height_720_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_720_i3
def height_720_i2 : ℕ := 11
def childrenH_720_i2 : Fin 2 → ℕ := ![height_0, height_720_i3]
theorem height_exact_720_i2 : height_720_i2 = 1 + Finset.univ.sup childrenH_720_i2 := by decide +kernel
theorem required_origin_720_i2 : ∀ x ∈ required_720_i2,
    (∃ j, x ∈ childrenC_720_i2 j) ∨ ∀ j, x ∈ childrenD_720_i2 j := by decide +kernel
theorem required_exact_720_i2 : required_720_i2 =
    ((Finset.univ.biUnion childrenC_720_i2) ∪ commonEnvelope childrenD_720_i2).erase (5, 7) := by
  exact required_eq_combination childrenC_720_i2 childrenD_720_i2 (5, 7) required_720_i2
    (by decide +kernel) child_required_sub_720_i2 common_sub_720_i2 required_origin_720_i2
theorem envelope_origin_720_i2 : ∀ x ∈ envelope_720_i2,
    x = (5, 7) ∨ ∃ j, x ∈ childrenD_720_i2 j := by decide +kernel
theorem envelope_exact_720_i2 : envelope_720_i2 =
    insert (5, 7) (Finset.univ.biUnion childrenD_720_i2) := by
  exact envelope_eq_combination childrenD_720_i2 (5, 7) envelope_720_i2
    pivot_mem_720_i2 child_envelope_sub_720_i2 envelope_origin_720_i2
def checked_720_i2 : CheckedCard where
  required := required_720_i2
  envelope := envelope_720_i2
  height := height_720_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_720_i2
def height_720_i1 : ℕ := 12
def childrenH_720_i1 : Fin 3 → ℕ := ![height_40, height_310, height_720_i2]
theorem height_exact_720_i1 : height_720_i1 = 1 + Finset.univ.sup childrenH_720_i1 := by decide +kernel
theorem required_origin_720_i1 : ∀ x ∈ required_720_i1,
    (∃ j, x ∈ childrenC_720_i1 j) ∨ ∀ j, x ∈ childrenD_720_i1 j := by decide +kernel
theorem required_exact_720_i1 : required_720_i1 =
    ((Finset.univ.biUnion childrenC_720_i1) ∪ commonEnvelope childrenD_720_i1).erase (7, 5) := by
  exact required_eq_combination childrenC_720_i1 childrenD_720_i1 (7, 5) required_720_i1
    (by decide +kernel) child_required_sub_720_i1 common_sub_720_i1 required_origin_720_i1
theorem envelope_origin_720_i1 : ∀ x ∈ envelope_720_i1,
    x = (7, 5) ∨ ∃ j, x ∈ childrenD_720_i1 j := by decide +kernel
theorem envelope_exact_720_i1 : envelope_720_i1 =
    insert (7, 5) (Finset.univ.biUnion childrenD_720_i1) := by
  exact envelope_eq_combination childrenD_720_i1 (7, 5) envelope_720_i1
    pivot_mem_720_i1 child_envelope_sub_720_i1 envelope_origin_720_i1
def checked_720_i1 : CheckedCard where
  required := required_720_i1
  envelope := envelope_720_i1
  height := height_720_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_720_i1
def height_720 : ℕ := 13
def childrenH_720 : Fin 4 → ℕ := ![height_54, height_64, height_720_i0, height_720_i1]
theorem height_exact_720 : height_720 = 1 + Finset.univ.sup childrenH_720 := by decide +kernel
theorem required_origin_720 : ∀ x ∈ required_720,
    (∃ j, x ∈ childrenC_720 j) ∨ ∀ j, x ∈ childrenD_720 j := by decide +kernel
theorem required_exact_720 : required_720 =
    ((Finset.univ.biUnion childrenC_720) ∪ commonEnvelope childrenD_720).erase (7, 6) := by
  exact required_eq_combination childrenC_720 childrenD_720 (7, 6) required_720
    (by decide +kernel) child_required_sub_720 common_sub_720 required_origin_720
theorem envelope_origin_720 : ∀ x ∈ envelope_720,
    x = (7, 6) ∨ ∃ j, x ∈ childrenD_720 j := by decide +kernel
theorem envelope_exact_720 : envelope_720 =
    insert (7, 6) (Finset.univ.biUnion childrenD_720) := by
  exact envelope_eq_combination childrenD_720 (7, 6) envelope_720
    pivot_mem_720 child_envelope_sub_720 envelope_origin_720
def checked_720 : CheckedCard where
  required := required_720
  envelope := envelope_720
  height := height_720
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_720
end SnakyPrototype.Certificate21

end OAI
