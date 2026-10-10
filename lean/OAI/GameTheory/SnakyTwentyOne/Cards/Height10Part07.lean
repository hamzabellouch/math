import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part01
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_722_i1 : Finset Cell := ⟨(([(2, 4), (4, 3), (4, 4), (4, 5), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_722_i1 : Finset Cell := ⟨(([(1, 4), (2, 4), (3, 4), (3, 5), (3, 7), (3, 8), (3, 9), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 2), (5, 3), (5, 6), (5, 7), (5, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_722_i1 : Fin 2 → Finset Cell := ![(placed21 0 (3, 3) required_17), (placed21 7 (5, 6) required_32)]
def childrenD_722_i1 : Fin 2 → Finset Cell := ![(placed21 0 (3, 3) envelope_17), (placed21 7 (5, 6) envelope_32)]
theorem common_sub_722_i1 : commonEnvelope childrenD_722_i1 ⊆ insert (3, 4) required_722_i1 := by decide +kernel
theorem child_required_sub_722_i1 : ∀ j, childrenC_722_i1 j ⊆ insert (3, 4) required_722_i1 := by decide +kernel
theorem child_envelope_sub_722_i1 : ∀ j, childrenD_722_i1 j ⊆ envelope_722_i1 := by decide +kernel
theorem pivot_mem_722_i1 : (3, 4) ∈ envelope_722_i1 := by decide +kernel
theorem children_work_722_i1 : ∀ j, Template HasSnaky 4 (childrenC_722_i1 j) (childrenD_722_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_17 0 (3, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_32 7 (5, 6)).mono (by decide +kernel)
theorem row_works_722_i1 : Template HasSnaky 5 required_722_i1 envelope_722_i1 := by
  refine compose HasSnaky 4 childrenC_722_i1 childrenD_722_i1 children_work_722_i1 (3, 4)
    required_722_i1 envelope_722_i1 pivot_mem_722_i1 child_required_sub_722_i1 child_envelope_sub_722_i1 ?_
  intro b hb
  exact common_sub_722_i1 (mem_commonEnvelope childrenD_722_i1 b hb)
def required_722_i0 : Finset Cell := ⟨(([(2, 4), (4, 3), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_722_i0 : Finset Cell := ⟨(([(1, 4), (2, 4), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 1), (5, 2), (5, 3), (5, 6), (5, 7), (5, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_722_i0 : Fin 4 → Finset Cell := ![(placed21 5 (5, 3) required_8), (placed21 4 (3, 7) required_9), (placed21 6 (5, 8) required_366), required_722_i1]
def childrenD_722_i0 : Fin 4 → Finset Cell := ![(placed21 5 (5, 3) envelope_8), (placed21 4 (3, 7) envelope_9), (placed21 6 (5, 8) envelope_366), envelope_722_i1]
theorem common_sub_722_i0 : commonEnvelope childrenD_722_i0 ⊆ insert (4, 6) required_722_i0 := by decide +kernel
theorem child_required_sub_722_i0 : ∀ j, childrenC_722_i0 j ⊆ insert (4, 6) required_722_i0 := by decide +kernel
theorem child_envelope_sub_722_i0 : ∀ j, childrenD_722_i0 j ⊆ envelope_722_i0 := by decide +kernel
theorem pivot_mem_722_i0 : (4, 6) ∈ envelope_722_i0 := by decide +kernel
theorem children_work_722_i0 : ∀ j, Template HasSnaky 5 (childrenC_722_i0 j) (childrenD_722_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_8 5 (5, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_9 4 (3, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_366 6 (5, 8)).mono (by decide +kernel)
  · exact row_works_722_i1.mono (by decide +kernel)
theorem row_works_722_i0 : Template HasSnaky 6 required_722_i0 envelope_722_i0 := by
  refine compose HasSnaky 5 childrenC_722_i0 childrenD_722_i0 children_work_722_i0 (4, 6)
    required_722_i0 envelope_722_i0 pivot_mem_722_i0 child_required_sub_722_i0 child_envelope_sub_722_i0 ?_
  intro b hb
  exact common_sub_722_i0 (mem_commonEnvelope childrenD_722_i0 b hb)
def required_722_i2 : Finset Cell := ⟨(([(1, 3), (2, 3), (2, 4), (4, 3), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_722_i2 : Finset Cell := ⟨(([(1, 3), (2, 3), (2, 4), (2, 5), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 2), (5, 3), (5, 4), (5, 6), (5, 7), (5, 8), (6, 4), (6, 5), (6, 6), (6, 7), (7, 5), (7, 6), (7, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_722_i2 : Fin 2 → Finset Cell := ![(placed21 6 (5, 4) required_2), (placed21 1 (2, 2) required_345)]
def childrenD_722_i2 : Fin 2 → Finset Cell := ![(placed21 6 (5, 4) envelope_2), (placed21 1 (2, 2) envelope_345)]
theorem common_sub_722_i2 : commonEnvelope childrenD_722_i2 ⊆ insert (5, 4) required_722_i2 := by decide +kernel
theorem child_required_sub_722_i2 : ∀ j, childrenC_722_i2 j ⊆ insert (5, 4) required_722_i2 := by decide +kernel
theorem child_envelope_sub_722_i2 : ∀ j, childrenD_722_i2 j ⊆ envelope_722_i2 := by decide +kernel
theorem pivot_mem_722_i2 : (5, 4) ∈ envelope_722_i2 := by decide +kernel
theorem children_work_722_i2 : ∀ j, Template HasSnaky 8 (childrenC_722_i2 j) (childrenD_722_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_2 6 (5, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_345 1 (2, 2)).mono (by decide +kernel)
theorem row_works_722_i2 : Template HasSnaky 9 required_722_i2 envelope_722_i2 := by
  refine compose HasSnaky 8 childrenC_722_i2 childrenD_722_i2 children_work_722_i2 (5, 4)
    required_722_i2 envelope_722_i2 pivot_mem_722_i2 child_required_sub_722_i2 child_envelope_sub_722_i2 ?_
  intro b hb
  exact common_sub_722_i2 (mem_commonEnvelope childrenD_722_i2 b hb)
def required_722_i3 : Finset Cell := ⟨(([(1, 3), (2, 3), (2, 4), (4, 3), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_722_i3 : Finset Cell := ⟨(([(0, 4), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4), (3, 5), (3, 6), (3, 7), (4, 2), (4, 3), (4, 4), (4, 5), (5, 3), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_722_i3 : Fin 2 → Finset Cell := ![(placed21 6 (5, 4) required_0), (placed21 2 (5, 2) required_307)]
def childrenD_722_i3 : Fin 2 → Finset Cell := ![(placed21 6 (5, 4) envelope_0), (placed21 2 (5, 2) envelope_307)]
theorem common_sub_722_i3 : commonEnvelope childrenD_722_i3 ⊆ insert (3, 4) required_722_i3 := by decide +kernel
theorem child_required_sub_722_i3 : ∀ j, childrenC_722_i3 j ⊆ insert (3, 4) required_722_i3 := by decide +kernel
theorem child_envelope_sub_722_i3 : ∀ j, childrenD_722_i3 j ⊆ envelope_722_i3 := by decide +kernel
theorem pivot_mem_722_i3 : (3, 4) ∈ envelope_722_i3 := by decide +kernel
theorem children_work_722_i3 : ∀ j, Template HasSnaky 4 (childrenC_722_i3 j) (childrenD_722_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 6 (5, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_307 2 (5, 2)).mono (by decide +kernel)
theorem row_works_722_i3 : Template HasSnaky 5 required_722_i3 envelope_722_i3 := by
  refine compose HasSnaky 4 childrenC_722_i3 childrenD_722_i3 children_work_722_i3 (3, 4)
    required_722_i3 envelope_722_i3 pivot_mem_722_i3 child_required_sub_722_i3 child_envelope_sub_722_i3 ?_
  intro b hb
  exact common_sub_722_i3 (mem_commonEnvelope childrenD_722_i3 b hb)
def required_722_i4 : Finset Cell := ⟨(([(1, 3), (2, 3), (2, 4), (4, 3), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_722_i4 : Finset Cell := ⟨(([(1, 3), (2, 3), (2, 4), (2, 5), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 4), (5, 6), (5, 7), (5, 8), (6, 6), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_722_i4 : Fin 2 → Finset Cell := ![(placed21 6 (5, 4) required_0), (placed21 0 (2, 1) required_267)]
def childrenD_722_i4 : Fin 2 → Finset Cell := ![(placed21 6 (5, 4) envelope_0), (placed21 0 (2, 1) envelope_267)]
theorem common_sub_722_i4 : commonEnvelope childrenD_722_i4 ⊆ insert (3, 4) required_722_i4 := by decide +kernel
theorem child_required_sub_722_i4 : ∀ j, childrenC_722_i4 j ⊆ insert (3, 4) required_722_i4 := by decide +kernel
theorem child_envelope_sub_722_i4 : ∀ j, childrenD_722_i4 j ⊆ envelope_722_i4 := by decide +kernel
theorem pivot_mem_722_i4 : (3, 4) ∈ envelope_722_i4 := by decide +kernel
theorem children_work_722_i4 : ∀ j, Template HasSnaky 6 (childrenC_722_i4 j) (childrenD_722_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 6 (5, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_267 0 (2, 1)).mono (by decide +kernel)
theorem row_works_722_i4 : Template HasSnaky 7 required_722_i4 envelope_722_i4 := by
  refine compose HasSnaky 6 childrenC_722_i4 childrenD_722_i4 children_work_722_i4 (3, 4)
    required_722_i4 envelope_722_i4 pivot_mem_722_i4 child_required_sub_722_i4 child_envelope_sub_722_i4 ?_
  intro b hb
  exact common_sub_722_i4 (mem_commonEnvelope childrenD_722_i4 b hb)
def required_722 : Finset Cell := ⟨(([(1, 3), (2, 3), (2, 4), (4, 3), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_722 : Finset Cell := ⟨(([(0, 4), (1, 3), (1, 4), (2, 3), (2, 4), (2, 5), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 6), (5, 7), (5, 8), (6, 4), (6, 5), (6, 6), (6, 7), (7, 5), (7, 6), (7, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_722 : Fin 6 → Finset Cell := ![(placed21 2 (5, 1) required_13), (placed21 4 (1, 6) required_176), required_722_i0, required_722_i2, required_722_i3, required_722_i4]
def childrenD_722 : Fin 6 → Finset Cell := ![(placed21 2 (5, 1) envelope_13), (placed21 4 (1, 6) envelope_176), envelope_722_i0, envelope_722_i2, envelope_722_i3, envelope_722_i4]
theorem common_sub_722 : commonEnvelope childrenD_722 ⊆ insert (4, 4) required_722 := by decide +kernel
theorem child_required_sub_722 : ∀ j, childrenC_722 j ⊆ insert (4, 4) required_722 := by decide +kernel
theorem child_envelope_sub_722 : ∀ j, childrenD_722 j ⊆ envelope_722 := by decide +kernel
theorem pivot_mem_722 : (4, 4) ∈ envelope_722 := by decide +kernel
theorem children_work_722 : ∀ j, Template HasSnaky 9 (childrenC_722 j) (childrenD_722 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_13 2 (5, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_176 4 (1, 6)).mono (by decide +kernel)
  · exact row_works_722_i0.mono (by decide +kernel)
  · exact row_works_722_i2.mono (by decide +kernel)
  · exact row_works_722_i3.mono (by decide +kernel)
  · exact row_works_722_i4.mono (by decide +kernel)
theorem row_works_722 : Template HasSnaky 10 required_722 envelope_722 := by
  refine compose HasSnaky 9 childrenC_722 childrenD_722 children_work_722 (4, 4)
    required_722 envelope_722 pivot_mem_722 child_required_sub_722 child_envelope_sub_722 ?_
  intro b hb
  exact common_sub_722 (mem_commonEnvelope childrenD_722 b hb)
def height_722_i1 : ℕ := 5
def childrenH_722_i1 : Fin 2 → ℕ := ![height_17, height_32]
theorem height_exact_722_i1 : height_722_i1 = 1 + Finset.univ.sup childrenH_722_i1 := by decide +kernel
theorem required_origin_722_i1 : ∀ x ∈ required_722_i1,
    (∃ j, x ∈ childrenC_722_i1 j) ∨ ∀ j, x ∈ childrenD_722_i1 j := by decide +kernel
theorem required_exact_722_i1 : required_722_i1 =
    ((Finset.univ.biUnion childrenC_722_i1) ∪ commonEnvelope childrenD_722_i1).erase (3, 4) := by
  exact required_eq_combination childrenC_722_i1 childrenD_722_i1 (3, 4) required_722_i1
    (by decide +kernel) child_required_sub_722_i1 common_sub_722_i1 required_origin_722_i1
theorem envelope_origin_722_i1 : ∀ x ∈ envelope_722_i1,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_722_i1 j := by decide +kernel
theorem envelope_exact_722_i1 : envelope_722_i1 =
    insert (3, 4) (Finset.univ.biUnion childrenD_722_i1) := by
  exact envelope_eq_combination childrenD_722_i1 (3, 4) envelope_722_i1
    pivot_mem_722_i1 child_envelope_sub_722_i1 envelope_origin_722_i1
def checked_722_i1 : CheckedCard where
  required := required_722_i1
  envelope := envelope_722_i1
  height := height_722_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_722_i1
def height_722_i0 : ℕ := 6
def childrenH_722_i0 : Fin 4 → ℕ := ![height_8, height_9, height_366, height_722_i1]
theorem height_exact_722_i0 : height_722_i0 = 1 + Finset.univ.sup childrenH_722_i0 := by decide +kernel
theorem required_origin_722_i0 : ∀ x ∈ required_722_i0,
    (∃ j, x ∈ childrenC_722_i0 j) ∨ ∀ j, x ∈ childrenD_722_i0 j := by decide +kernel
theorem required_exact_722_i0 : required_722_i0 =
    ((Finset.univ.biUnion childrenC_722_i0) ∪ commonEnvelope childrenD_722_i0).erase (4, 6) := by
  exact required_eq_combination childrenC_722_i0 childrenD_722_i0 (4, 6) required_722_i0
    (by decide +kernel) child_required_sub_722_i0 common_sub_722_i0 required_origin_722_i0
theorem envelope_origin_722_i0 : ∀ x ∈ envelope_722_i0,
    x = (4, 6) ∨ ∃ j, x ∈ childrenD_722_i0 j := by decide +kernel
theorem envelope_exact_722_i0 : envelope_722_i0 =
    insert (4, 6) (Finset.univ.biUnion childrenD_722_i0) := by
  exact envelope_eq_combination childrenD_722_i0 (4, 6) envelope_722_i0
    pivot_mem_722_i0 child_envelope_sub_722_i0 envelope_origin_722_i0
def checked_722_i0 : CheckedCard where
  required := required_722_i0
  envelope := envelope_722_i0
  height := height_722_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_722_i0
def height_722_i2 : ℕ := 9
def childrenH_722_i2 : Fin 2 → ℕ := ![height_2, height_345]
theorem height_exact_722_i2 : height_722_i2 = 1 + Finset.univ.sup childrenH_722_i2 := by decide +kernel
theorem required_origin_722_i2 : ∀ x ∈ required_722_i2,
    (∃ j, x ∈ childrenC_722_i2 j) ∨ ∀ j, x ∈ childrenD_722_i2 j := by decide +kernel
theorem required_exact_722_i2 : required_722_i2 =
    ((Finset.univ.biUnion childrenC_722_i2) ∪ commonEnvelope childrenD_722_i2).erase (5, 4) := by
  exact required_eq_combination childrenC_722_i2 childrenD_722_i2 (5, 4) required_722_i2
    (by decide +kernel) child_required_sub_722_i2 common_sub_722_i2 required_origin_722_i2
theorem envelope_origin_722_i2 : ∀ x ∈ envelope_722_i2,
    x = (5, 4) ∨ ∃ j, x ∈ childrenD_722_i2 j := by decide +kernel
theorem envelope_exact_722_i2 : envelope_722_i2 =
    insert (5, 4) (Finset.univ.biUnion childrenD_722_i2) := by
  exact envelope_eq_combination childrenD_722_i2 (5, 4) envelope_722_i2
    pivot_mem_722_i2 child_envelope_sub_722_i2 envelope_origin_722_i2
def checked_722_i2 : CheckedCard where
  required := required_722_i2
  envelope := envelope_722_i2
  height := height_722_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_722_i2
def height_722_i3 : ℕ := 5
def childrenH_722_i3 : Fin 2 → ℕ := ![height_0, height_307]
theorem height_exact_722_i3 : height_722_i3 = 1 + Finset.univ.sup childrenH_722_i3 := by decide +kernel
theorem required_origin_722_i3 : ∀ x ∈ required_722_i3,
    (∃ j, x ∈ childrenC_722_i3 j) ∨ ∀ j, x ∈ childrenD_722_i3 j := by decide +kernel
theorem required_exact_722_i3 : required_722_i3 =
    ((Finset.univ.biUnion childrenC_722_i3) ∪ commonEnvelope childrenD_722_i3).erase (3, 4) := by
  exact required_eq_combination childrenC_722_i3 childrenD_722_i3 (3, 4) required_722_i3
    (by decide +kernel) child_required_sub_722_i3 common_sub_722_i3 required_origin_722_i3
theorem envelope_origin_722_i3 : ∀ x ∈ envelope_722_i3,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_722_i3 j := by decide +kernel
theorem envelope_exact_722_i3 : envelope_722_i3 =
    insert (3, 4) (Finset.univ.biUnion childrenD_722_i3) := by
  exact envelope_eq_combination childrenD_722_i3 (3, 4) envelope_722_i3
    pivot_mem_722_i3 child_envelope_sub_722_i3 envelope_origin_722_i3
def checked_722_i3 : CheckedCard where
  required := required_722_i3
  envelope := envelope_722_i3
  height := height_722_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_722_i3
def height_722_i4 : ℕ := 7
def childrenH_722_i4 : Fin 2 → ℕ := ![height_0, height_267]
theorem height_exact_722_i4 : height_722_i4 = 1 + Finset.univ.sup childrenH_722_i4 := by decide +kernel
theorem required_origin_722_i4 : ∀ x ∈ required_722_i4,
    (∃ j, x ∈ childrenC_722_i4 j) ∨ ∀ j, x ∈ childrenD_722_i4 j := by decide +kernel
theorem required_exact_722_i4 : required_722_i4 =
    ((Finset.univ.biUnion childrenC_722_i4) ∪ commonEnvelope childrenD_722_i4).erase (3, 4) := by
  exact required_eq_combination childrenC_722_i4 childrenD_722_i4 (3, 4) required_722_i4
    (by decide +kernel) child_required_sub_722_i4 common_sub_722_i4 required_origin_722_i4
theorem envelope_origin_722_i4 : ∀ x ∈ envelope_722_i4,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_722_i4 j := by decide +kernel
theorem envelope_exact_722_i4 : envelope_722_i4 =
    insert (3, 4) (Finset.univ.biUnion childrenD_722_i4) := by
  exact envelope_eq_combination childrenD_722_i4 (3, 4) envelope_722_i4
    pivot_mem_722_i4 child_envelope_sub_722_i4 envelope_origin_722_i4
def checked_722_i4 : CheckedCard where
  required := required_722_i4
  envelope := envelope_722_i4
  height := height_722_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_722_i4
def height_722 : ℕ := 10
def childrenH_722 : Fin 6 → ℕ := ![height_13, height_176, height_722_i0, height_722_i2, height_722_i3, height_722_i4]
theorem height_exact_722 : height_722 = 1 + Finset.univ.sup childrenH_722 := by decide +kernel
theorem required_origin_722 : ∀ x ∈ required_722,
    (∃ j, x ∈ childrenC_722 j) ∨ ∀ j, x ∈ childrenD_722 j := by decide +kernel
theorem required_exact_722 : required_722 =
    ((Finset.univ.biUnion childrenC_722) ∪ commonEnvelope childrenD_722).erase (4, 4) := by
  exact required_eq_combination childrenC_722 childrenD_722 (4, 4) required_722
    (by decide +kernel) child_required_sub_722 common_sub_722 required_origin_722
theorem envelope_origin_722 : ∀ x ∈ envelope_722,
    x = (4, 4) ∨ ∃ j, x ∈ childrenD_722 j := by decide +kernel
theorem envelope_exact_722 : envelope_722 =
    insert (4, 4) (Finset.univ.biUnion childrenD_722) := by
  exact envelope_eq_combination childrenD_722 (4, 4) envelope_722
    pivot_mem_722 child_envelope_sub_722 envelope_origin_722
def checked_722 : CheckedCard where
  required := required_722
  envelope := envelope_722
  height := height_722
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_722
end SnakyPrototype.Certificate21

end OAI
