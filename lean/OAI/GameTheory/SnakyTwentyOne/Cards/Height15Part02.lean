import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part06
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part07
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part06
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part07
import OAI.GameTheory.SnakyTwentyOne.Cards.Height10Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height10Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height11Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height11Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height12Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height13Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height13Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height13Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height14Part03
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_670_i0 : Finset Cell := ⟨(([(3, 4), (3, 5), (6, 5), (6, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_670_i0 : Finset Cell := ⟨(([(1, 6), (2, 4), (2, 6), (2, 7), (2, 8), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, 1), (5, 2), (5, 3), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 9), (7, 10), (7, 11), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (10, 6), (10, 7), (10, 8), (11, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_670_i0 : Fin 3 → Finset Cell := ![(placed21 7 (7, 6) required_40), (placed21 1 (2, 4) required_125), (placed21 1 (1, 1) required_660)]
def childrenD_670_i0 : Fin 3 → Finset Cell := ![(placed21 7 (7, 6) envelope_40), (placed21 1 (2, 4) envelope_125), (placed21 1 (1, 1) envelope_660)]
theorem common_sub_670_i0 : commonEnvelope childrenD_670_i0 ⊆ insert (5, 5) required_670_i0 := by decide +kernel
theorem child_required_sub_670_i0 : ∀ j, childrenC_670_i0 j ⊆ insert (5, 5) required_670_i0 := by decide +kernel
theorem child_envelope_sub_670_i0 : ∀ j, childrenD_670_i0 j ⊆ envelope_670_i0 := by decide +kernel
theorem pivot_mem_670_i0 : (5, 5) ∈ envelope_670_i0 := by decide +kernel
theorem children_work_670_i0 : ∀ j, Template HasSnaky 11 (childrenC_670_i0 j) (childrenD_670_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_40 7 (7, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_125 1 (2, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_660 1 (1, 1)).mono (by decide +kernel)
theorem row_works_670_i0 : Template HasSnaky 12 required_670_i0 envelope_670_i0 := by
  refine compose HasSnaky 11 childrenC_670_i0 childrenD_670_i0 children_work_670_i0 (5, 5)
    required_670_i0 envelope_670_i0 pivot_mem_670_i0 child_required_sub_670_i0 child_envelope_sub_670_i0 ?_
  intro b hb
  exact common_sub_670_i0 (mem_commonEnvelope childrenD_670_i0 b hb)
def required_670_i1 : Finset Cell := ⟨(([(3, 4), (3, 5), (6, 5), (6, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_670_i1 : Finset Cell := ⟨(([(1, 6), (2, 4), (2, 6), (2, 7), (2, 8), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (9, 5), (9, 6), (9, 7), (9, 8), (10, 6), (10, 7), (10, 8), (11, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_670_i1 : Fin 3 → Finset Cell := ![(placed21 7 (7, 6) required_40), (placed21 1 (2, 4) required_125), (placed21 1 (1, 3) required_663)]
def childrenD_670_i1 : Fin 3 → Finset Cell := ![(placed21 7 (7, 6) envelope_40), (placed21 1 (2, 4) envelope_125), (placed21 1 (1, 3) envelope_663)]
theorem common_sub_670_i1 : commonEnvelope childrenD_670_i1 ⊆ insert (5, 5) required_670_i1 := by decide +kernel
theorem child_required_sub_670_i1 : ∀ j, childrenC_670_i1 j ⊆ insert (5, 5) required_670_i1 := by decide +kernel
theorem child_envelope_sub_670_i1 : ∀ j, childrenD_670_i1 j ⊆ envelope_670_i1 := by decide +kernel
theorem pivot_mem_670_i1 : (5, 5) ∈ envelope_670_i1 := by decide +kernel
theorem children_work_670_i1 : ∀ j, Template HasSnaky 11 (childrenC_670_i1 j) (childrenD_670_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_40 7 (7, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_125 1 (2, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_663 1 (1, 3)).mono (by decide +kernel)
theorem row_works_670_i1 : Template HasSnaky 12 required_670_i1 envelope_670_i1 := by
  refine compose HasSnaky 11 childrenC_670_i1 childrenD_670_i1 children_work_670_i1 (5, 5)
    required_670_i1 envelope_670_i1 pivot_mem_670_i1 child_required_sub_670_i1 child_envelope_sub_670_i1 ?_
  intro b hb
  exact common_sub_670_i1 (mem_commonEnvelope childrenD_670_i1 b hb)
def required_670_i3 : Finset Cell := ⟨(([(3, 5), (5, 6), (6, 5), (6, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_670_i3 : Finset Cell := ⟨(([(3, 5), (3, 6), (3, 7), (4, 5), (4, 6), (4, 7), (5, 6), (5, 7), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (9, 4), (9, 5), (9, 6), (9, 7), (10, 4), (10, 5), (10, 6), (10, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_670_i3 : Fin 3 → Finset Cell := ![(placed21 1 (3, 5) required_106), (placed21 1 (3, 5) required_219), (placed21 4 (5, 9) required_530)]
def childrenD_670_i3 : Fin 3 → Finset Cell := ![(placed21 1 (3, 5) envelope_106), (placed21 1 (3, 5) envelope_219), (placed21 4 (5, 9) envelope_530)]
theorem common_sub_670_i3 : commonEnvelope childrenD_670_i3 ⊆ insert (7, 6) required_670_i3 := by decide +kernel
theorem child_required_sub_670_i3 : ∀ j, childrenC_670_i3 j ⊆ insert (7, 6) required_670_i3 := by decide +kernel
theorem child_envelope_sub_670_i3 : ∀ j, childrenD_670_i3 j ⊆ envelope_670_i3 := by decide +kernel
theorem pivot_mem_670_i3 : (7, 6) ∈ envelope_670_i3 := by decide +kernel
theorem children_work_670_i3 : ∀ j, Template HasSnaky 8 (childrenC_670_i3 j) (childrenD_670_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_106 1 (3, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_219 1 (3, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_530 4 (5, 9)).mono (by decide +kernel)
theorem row_works_670_i3 : Template HasSnaky 9 required_670_i3 envelope_670_i3 := by
  refine compose HasSnaky 8 childrenC_670_i3 childrenD_670_i3 children_work_670_i3 (7, 6)
    required_670_i3 envelope_670_i3 pivot_mem_670_i3 child_required_sub_670_i3 child_envelope_sub_670_i3 ?_
  intro b hb
  exact common_sub_670_i3 (mem_commonEnvelope childrenD_670_i3 b hb)
def required_670_i4 : Finset Cell := ⟨(([(3, 4), (3, 5), (5, 6), (6, 5), (6, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_670_i4 : Finset Cell := ⟨(([(2, 4), (3, 4), (3, 5), (4, 4), (4, 5), (4, 7), (5, 3), (5, 5), (5, 6), (5, 7), (5, 8), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (10, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_670_i4 : Fin 3 → Finset Cell := ![(placed21 7 (7, 6) required_40), (placed21 3 (2, 5) required_98), (placed21 4 (4, 9) required_512)]
def childrenD_670_i4 : Fin 3 → Finset Cell := ![(placed21 7 (7, 6) envelope_40), (placed21 3 (2, 5) envelope_98), (placed21 4 (4, 9) envelope_512)]
theorem common_sub_670_i4 : commonEnvelope childrenD_670_i4 ⊆ insert (5, 5) required_670_i4 := by decide +kernel
theorem child_required_sub_670_i4 : ∀ j, childrenC_670_i4 j ⊆ insert (5, 5) required_670_i4 := by decide +kernel
theorem child_envelope_sub_670_i4 : ∀ j, childrenD_670_i4 j ⊆ envelope_670_i4 := by decide +kernel
theorem pivot_mem_670_i4 : (5, 5) ∈ envelope_670_i4 := by decide +kernel
theorem children_work_670_i4 : ∀ j, Template HasSnaky 9 (childrenC_670_i4 j) (childrenD_670_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_40 7 (7, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_98 3 (2, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_512 4 (4, 9)).mono (by decide +kernel)
theorem row_works_670_i4 : Template HasSnaky 10 required_670_i4 envelope_670_i4 := by
  refine compose HasSnaky 9 childrenC_670_i4 childrenD_670_i4 children_work_670_i4 (5, 5)
    required_670_i4 envelope_670_i4 pivot_mem_670_i4 child_required_sub_670_i4 child_envelope_sub_670_i4 ?_
  intro b hb
  exact common_sub_670_i4 (mem_commonEnvelope childrenD_670_i4 b hb)
def required_670_i2 : Finset Cell := ⟨(([(3, 4), (3, 5), (6, 5), (6, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_670_i2 : Finset Cell := ⟨(([(0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 3), (2, 4), (2, 6), (2, 7), (2, 8), (2, 9), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 3), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (11, 4), (11, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_670_i2 : Fin 5 → Finset Cell := ![(placed21 0 (3, 4) required_270), (placed21 2 (7, 3) required_588), (placed21 4 (4, 9) required_638), required_670_i3, required_670_i4]
def childrenD_670_i2 : Fin 5 → Finset Cell := ![(placed21 0 (3, 4) envelope_270), (placed21 2 (7, 3) envelope_588), (placed21 4 (4, 9) envelope_638), envelope_670_i3, envelope_670_i4]
theorem common_sub_670_i2 : commonEnvelope childrenD_670_i2 ⊆ insert (5, 6) required_670_i2 := by decide +kernel
theorem child_required_sub_670_i2 : ∀ j, childrenC_670_i2 j ⊆ insert (5, 6) required_670_i2 := by decide +kernel
theorem child_envelope_sub_670_i2 : ∀ j, childrenD_670_i2 j ⊆ envelope_670_i2 := by decide +kernel
theorem pivot_mem_670_i2 : (5, 6) ∈ envelope_670_i2 := by decide +kernel
theorem children_work_670_i2 : ∀ j, Template HasSnaky 12 (childrenC_670_i2 j) (childrenD_670_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_270 0 (3, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_588 2 (7, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_638 4 (4, 9)).mono (by decide +kernel)
  · exact row_works_670_i3.mono (by decide +kernel)
  · exact row_works_670_i4.mono (by decide +kernel)
theorem row_works_670_i2 : Template HasSnaky 13 required_670_i2 envelope_670_i2 := by
  refine compose HasSnaky 12 childrenC_670_i2 childrenD_670_i2 children_work_670_i2 (5, 6)
    required_670_i2 envelope_670_i2 pivot_mem_670_i2 child_required_sub_670_i2 child_envelope_sub_670_i2 ?_
  intro b hb
  exact common_sub_670_i2 (mem_commonEnvelope childrenD_670_i2 b hb)
def required_670_i5 : Finset Cell := ⟨(([(3, 4), (3, 5), (6, 5), (6, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_670_i5 : Finset Cell := ⟨(([(2, 4), (2, 6), (2, 7), (3, 4), (3, 5), (3, 6), (3, 7), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 1), (5, 2), (5, 3), (5, 5), (5, 6), (5, 7), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (9, 10), (10, 4), (10, 5), (10, 6), (10, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_670_i5 : Fin 3 → Finset Cell := ![(placed21 7 (7, 6) required_40), (placed21 1 (2, 4) required_125), (placed21 0 (2, 1) required_617)]
def childrenD_670_i5 : Fin 3 → Finset Cell := ![(placed21 7 (7, 6) envelope_40), (placed21 1 (2, 4) envelope_125), (placed21 0 (2, 1) envelope_617)]
theorem common_sub_670_i5 : commonEnvelope childrenD_670_i5 ⊆ insert (5, 5) required_670_i5 := by decide +kernel
theorem child_required_sub_670_i5 : ∀ j, childrenC_670_i5 j ⊆ insert (5, 5) required_670_i5 := by decide +kernel
theorem child_envelope_sub_670_i5 : ∀ j, childrenD_670_i5 j ⊆ envelope_670_i5 := by decide +kernel
theorem pivot_mem_670_i5 : (5, 5) ∈ envelope_670_i5 := by decide +kernel
theorem children_work_670_i5 : ∀ j, Template HasSnaky 11 (childrenC_670_i5 j) (childrenD_670_i5 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_40 7 (7, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_125 1 (2, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_617 0 (2, 1)).mono (by decide +kernel)
theorem row_works_670_i5 : Template HasSnaky 12 required_670_i5 envelope_670_i5 := by
  refine compose HasSnaky 11 childrenC_670_i5 childrenD_670_i5 children_work_670_i5 (5, 5)
    required_670_i5 envelope_670_i5 pivot_mem_670_i5 child_required_sub_670_i5 child_envelope_sub_670_i5 ?_
  intro b hb
  exact common_sub_670_i5 (mem_commonEnvelope childrenD_670_i5 b hb)
def required_670_i6 : Finset Cell := ⟨(([(3, 4), (3, 5), (6, 5), (6, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_670_i6 : Finset Cell := ⟨(([(2, 6), (2, 7), (2, 8), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 1), (5, 2), (5, 3), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, 1), (7, 2), (7, 3), (7, 4), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (8, 6), (8, 7), (9, 6), (9, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_670_i6 : Fin 7 → Finset Cell := ![(placed21 4 (5, 8) required_13), (placed21 4 (5, 8) required_31), (placed21 4 (3, 7) required_355), (placed21 4 (3, 8) required_356), (placed21 0 (2, 3) required_434), (placed21 1 (3, 3) required_435), (placed21 6 (7, 8) required_441)]
def childrenD_670_i6 : Fin 7 → Finset Cell := ![(placed21 4 (5, 8) envelope_13), (placed21 4 (5, 8) envelope_31), (placed21 4 (3, 7) envelope_355), (placed21 4 (3, 8) envelope_356), (placed21 0 (2, 3) envelope_434), (placed21 1 (3, 3) envelope_435), (placed21 6 (7, 8) envelope_441)]
theorem common_sub_670_i6 : commonEnvelope childrenD_670_i6 ⊆ insert (6, 4) required_670_i6 := by decide +kernel
theorem child_required_sub_670_i6 : ∀ j, childrenC_670_i6 j ⊆ insert (6, 4) required_670_i6 := by decide +kernel
theorem child_envelope_sub_670_i6 : ∀ j, childrenD_670_i6 j ⊆ envelope_670_i6 := by decide +kernel
theorem pivot_mem_670_i6 : (6, 4) ∈ envelope_670_i6 := by decide +kernel
theorem children_work_670_i6 : ∀ j, Template HasSnaky 9 (childrenC_670_i6 j) (childrenD_670_i6 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_13 4 (5, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_31 4 (5, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_355 4 (3, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_356 4 (3, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_434 0 (2, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_435 1 (3, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_441 6 (7, 8)).mono (by decide +kernel)
theorem row_works_670_i6 : Template HasSnaky 10 required_670_i6 envelope_670_i6 := by
  refine compose HasSnaky 9 childrenC_670_i6 childrenD_670_i6 children_work_670_i6 (6, 4)
    required_670_i6 envelope_670_i6 pivot_mem_670_i6 child_required_sub_670_i6 child_envelope_sub_670_i6 ?_
  intro b hb
  exact common_sub_670_i6 (mem_commonEnvelope childrenD_670_i6 b hb)
def required_670_i7 : Finset Cell := ⟨(([(3, 4), (3, 5), (6, 5), (6, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_670_i7 : Finset Cell := ⟨(([(2, 4), (2, 6), (3, 4), (3, 5), (3, 6), (4, 4), (4, 5), (4, 6), (4, 8), (5, 1), (5, 2), (5, 3), (5, 5), (5, 6), (5, 8), (5, 9), (5, 10), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (9, 10), (10, 4), (10, 5), (10, 6), (10, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_670_i7 : Fin 3 → Finset Cell := ![(placed21 7 (7, 6) required_40), (placed21 1 (2, 4) required_125), (placed21 4 (4, 10) required_535)]
def childrenD_670_i7 : Fin 3 → Finset Cell := ![(placed21 7 (7, 6) envelope_40), (placed21 1 (2, 4) envelope_125), (placed21 4 (4, 10) envelope_535)]
theorem common_sub_670_i7 : commonEnvelope childrenD_670_i7 ⊆ insert (5, 5) required_670_i7 := by decide +kernel
theorem child_required_sub_670_i7 : ∀ j, childrenC_670_i7 j ⊆ insert (5, 5) required_670_i7 := by decide +kernel
theorem child_envelope_sub_670_i7 : ∀ j, childrenD_670_i7 j ⊆ envelope_670_i7 := by decide +kernel
theorem pivot_mem_670_i7 : (5, 5) ∈ envelope_670_i7 := by decide +kernel
theorem children_work_670_i7 : ∀ j, Template HasSnaky 10 (childrenC_670_i7 j) (childrenD_670_i7 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_40 7 (7, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_125 1 (2, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_535 4 (4, 10)).mono (by decide +kernel)
theorem row_works_670_i7 : Template HasSnaky 11 required_670_i7 envelope_670_i7 := by
  refine compose HasSnaky 10 childrenC_670_i7 childrenD_670_i7 children_work_670_i7 (5, 5)
    required_670_i7 envelope_670_i7 pivot_mem_670_i7 child_required_sub_670_i7 child_envelope_sub_670_i7 ?_
  intro b hb
  exact common_sub_670_i7 (mem_commonEnvelope childrenD_670_i7 b hb)
def required_670_i8 : Finset Cell := ⟨(([(3, 4), (3, 5), (6, 5), (6, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_670_i8 : Finset Cell := ⟨(([(2, 4), (2, 6), (2, 8), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 1), (5, 2), (5, 3), (5, 5), (5, 7), (5, 8), (5, 9), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, 2), (8, 3), (8, 4), (8, 6), (9, 2), (9, 3), (9, 4), (9, 6), (10, 2), (10, 3), (10, 4), (11, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_670_i8 : Fin 6 → Finset Cell := ![(placed21 0 (4, 2) required_188), (placed21 4 (4, 8) required_188), (placed21 6 (7, 8) required_441), (placed21 6 (7, 8) required_442), (placed21 2 (7, 3) required_514), (placed21 4 (3, 7) required_667)]
def childrenD_670_i8 : Fin 6 → Finset Cell := ![(placed21 0 (4, 2) envelope_188), (placed21 4 (4, 8) envelope_188), (placed21 6 (7, 8) envelope_441), (placed21 6 (7, 8) envelope_442), (placed21 2 (7, 3) envelope_514), (placed21 4 (3, 7) envelope_667)]
theorem common_sub_670_i8 : commonEnvelope childrenD_670_i8 ⊆ insert (6, 4) required_670_i8 := by decide +kernel
theorem child_required_sub_670_i8 : ∀ j, childrenC_670_i8 j ⊆ insert (6, 4) required_670_i8 := by decide +kernel
theorem child_envelope_sub_670_i8 : ∀ j, childrenD_670_i8 j ⊆ envelope_670_i8 := by decide +kernel
theorem pivot_mem_670_i8 : (6, 4) ∈ envelope_670_i8 := by decide +kernel
theorem children_work_670_i8 : ∀ j, Template HasSnaky 9 (childrenC_670_i8 j) (childrenD_670_i8 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_188 0 (4, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_188 4 (4, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_441 6 (7, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_442 6 (7, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_514 2 (7, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_667 4 (3, 7)).mono (by decide +kernel)
theorem row_works_670_i8 : Template HasSnaky 10 required_670_i8 envelope_670_i8 := by
  refine compose HasSnaky 9 childrenC_670_i8 childrenD_670_i8 children_work_670_i8 (6, 4)
    required_670_i8 envelope_670_i8 pivot_mem_670_i8 child_required_sub_670_i8 child_envelope_sub_670_i8 ?_
  intro b hb
  exact common_sub_670_i8 (mem_commonEnvelope childrenD_670_i8 b hb)
def required_670_i10 : Finset Cell := ⟨(([(3, 4), (3, 5), (6, 4), (6, 5), (6, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_670_i10 : Finset Cell := ⟨(([(2, 4), (2, 6), (3, 4), (3, 5), (3, 6), (4, 3), (4, 4), (4, 5), (4, 6), (5, 1), (5, 2), (5, 3), (5, 5), (5, 6), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (8, 4), (9, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_670_i10 : Fin 2 → Finset Cell := ![(placed21 1 (2, 4) required_125), (placed21 4 (4, 7) required_136)]
def childrenD_670_i10 : Fin 2 → Finset Cell := ![(placed21 1 (2, 4) envelope_125), (placed21 4 (4, 7) envelope_136)]
theorem common_sub_670_i10 : commonEnvelope childrenD_670_i10 ⊆ insert (5, 5) required_670_i10 := by decide +kernel
theorem child_required_sub_670_i10 : ∀ j, childrenC_670_i10 j ⊆ insert (5, 5) required_670_i10 := by decide +kernel
theorem child_envelope_sub_670_i10 : ∀ j, childrenD_670_i10 j ⊆ envelope_670_i10 := by decide +kernel
theorem pivot_mem_670_i10 : (5, 5) ∈ envelope_670_i10 := by decide +kernel
theorem children_work_670_i10 : ∀ j, Template HasSnaky 6 (childrenC_670_i10 j) (childrenD_670_i10 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_125 1 (2, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_136 4 (4, 7)).mono (by decide +kernel)
theorem row_works_670_i10 : Template HasSnaky 7 required_670_i10 envelope_670_i10 := by
  refine compose HasSnaky 6 childrenC_670_i10 childrenD_670_i10 children_work_670_i10 (5, 5)
    required_670_i10 envelope_670_i10 pivot_mem_670_i10 child_required_sub_670_i10 child_envelope_sub_670_i10 ?_
  intro b hb
  exact common_sub_670_i10 (mem_commonEnvelope childrenD_670_i10 b hb)
def required_670_i9 : Finset Cell := ⟨(([(3, 4), (3, 5), (6, 5), (6, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_670_i9 : Finset Cell := ⟨(([(0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 3), (2, 4), (2, 6), (2, 7), (2, 8), (2, 9), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 1), (5, 2), (5, 3), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 7), (7, 8), (7, 9), (8, 2), (8, 3), (8, 4), (9, 2), (9, 3), (9, 4), (10, 2), (10, 3), (10, 4), (11, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_670_i9 : Fin 5 → Finset Cell := ![(placed21 2 (7, 2) required_13), (placed21 2 (7, 3) required_514), (placed21 2 (7, 3) required_590), (placed21 4 (3, 7) required_668), required_670_i10]
def childrenD_670_i9 : Fin 5 → Finset Cell := ![(placed21 2 (7, 2) envelope_13), (placed21 2 (7, 3) envelope_514), (placed21 2 (7, 3) envelope_590), (placed21 4 (3, 7) envelope_668), envelope_670_i10]
theorem common_sub_670_i9 : commonEnvelope childrenD_670_i9 ⊆ insert (6, 4) required_670_i9 := by decide +kernel
theorem child_required_sub_670_i9 : ∀ j, childrenC_670_i9 j ⊆ insert (6, 4) required_670_i9 := by decide +kernel
theorem child_envelope_sub_670_i9 : ∀ j, childrenD_670_i9 j ⊆ envelope_670_i9 := by decide +kernel
theorem pivot_mem_670_i9 : (6, 4) ∈ envelope_670_i9 := by decide +kernel
theorem children_work_670_i9 : ∀ j, Template HasSnaky 13 (childrenC_670_i9 j) (childrenD_670_i9 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_13 2 (7, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_514 2 (7, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_590 2 (7, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_668 4 (3, 7)).mono (by decide +kernel)
  · exact row_works_670_i10.mono (by decide +kernel)
theorem row_works_670_i9 : Template HasSnaky 14 required_670_i9 envelope_670_i9 := by
  refine compose HasSnaky 13 childrenC_670_i9 childrenD_670_i9 children_work_670_i9 (6, 4)
    required_670_i9 envelope_670_i9 pivot_mem_670_i9 child_required_sub_670_i9 child_envelope_sub_670_i9 ?_
  intro b hb
  exact common_sub_670_i9 (mem_commonEnvelope childrenD_670_i9 b hb)
def required_670 : Finset Cell := ⟨(([(3, 4), (3, 5), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_670 : Finset Cell := ⟨(([(0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, 3), (2, 4), (2, 6), (2, 7), (2, 8), (2, 9), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, 1), (5, 2), (5, 3), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (9, 10), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (10, 9), (11, 4), (11, 5), (11, 6), (11, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_670 : Fin 12 → Finset Cell := ![(placed21 0 (5, 1) required_459), required_670_i0, (placed21 4 (2, 10) required_661), required_670_i1, required_670_i2, required_670_i5, required_670_i6, required_670_i7, (placed21 1 (0, 2) required_665), required_670_i8, required_670_i9, required_669]
def childrenD_670 : Fin 12 → Finset Cell := ![(placed21 0 (5, 1) envelope_459), envelope_670_i0, (placed21 4 (2, 10) envelope_661), envelope_670_i1, envelope_670_i2, envelope_670_i5, envelope_670_i6, envelope_670_i7, (placed21 1 (0, 2) envelope_665), envelope_670_i8, envelope_670_i9, envelope_669]
theorem common_sub_670 : commonEnvelope childrenD_670 ⊆ insert (6, 6) required_670 := by decide +kernel
theorem child_required_sub_670 : ∀ j, childrenC_670 j ⊆ insert (6, 6) required_670 := by decide +kernel
theorem child_envelope_sub_670 : ∀ j, childrenD_670 j ⊆ envelope_670 := by decide +kernel
theorem pivot_mem_670 : (6, 6) ∈ envelope_670 := by decide +kernel
theorem children_work_670 : ∀ j, Template HasSnaky 14 (childrenC_670 j) (childrenD_670 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_459 0 (5, 1)).mono (by decide +kernel)
  · exact row_works_670_i0.mono (by decide +kernel)
  · exact (placed21_template row_works_661 4 (2, 10)).mono (by decide +kernel)
  · exact row_works_670_i1.mono (by decide +kernel)
  · exact row_works_670_i2.mono (by decide +kernel)
  · exact row_works_670_i5.mono (by decide +kernel)
  · exact row_works_670_i6.mono (by decide +kernel)
  · exact row_works_670_i7.mono (by decide +kernel)
  · exact (placed21_template row_works_665 1 (0, 2)).mono (by decide +kernel)
  · exact row_works_670_i8.mono (by decide +kernel)
  · exact row_works_670_i9.mono (by decide +kernel)
  · exact row_works_669.mono (by decide +kernel)
theorem row_works_670 : Template HasSnaky 15 required_670 envelope_670 := by
  refine compose HasSnaky 14 childrenC_670 childrenD_670 children_work_670 (6, 6)
    required_670 envelope_670 pivot_mem_670 child_required_sub_670 child_envelope_sub_670 ?_
  intro b hb
  exact common_sub_670 (mem_commonEnvelope childrenD_670 b hb)
def required_682_i0 : Finset Cell := ⟨(([(3, 5), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_682_i0 : Finset Cell := ⟨(([(1, 3), (2, 3), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, 5), (8, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_682_i0 : Fin 4 → Finset Cell := ![(placed21 2 (4, 2) required_44), (placed21 2 (4, 2) required_52), (placed21 4 (3, 7) required_128), (placed21 1 (1, 2) required_676)]
def childrenD_682_i0 : Fin 4 → Finset Cell := ![(placed21 2 (4, 2) envelope_44), (placed21 2 (4, 2) envelope_52), (placed21 4 (3, 7) envelope_128), (placed21 1 (1, 2) envelope_676)]
theorem common_sub_682_i0 : commonEnvelope childrenD_682_i0 ⊆ insert (4, 3) required_682_i0 := by decide +kernel
theorem child_required_sub_682_i0 : ∀ j, childrenC_682_i0 j ⊆ insert (4, 3) required_682_i0 := by decide +kernel
theorem child_envelope_sub_682_i0 : ∀ j, childrenD_682_i0 j ⊆ envelope_682_i0 := by decide +kernel
theorem pivot_mem_682_i0 : (4, 3) ∈ envelope_682_i0 := by decide +kernel
theorem children_work_682_i0 : ∀ j, Template HasSnaky 11 (childrenC_682_i0 j) (childrenD_682_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_44 2 (4, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_52 2 (4, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_128 4 (3, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_676 1 (1, 2)).mono (by decide +kernel)
theorem row_works_682_i0 : Template HasSnaky 12 required_682_i0 envelope_682_i0 := by
  refine compose HasSnaky 11 childrenC_682_i0 childrenD_682_i0 children_work_682_i0 (4, 3)
    required_682_i0 envelope_682_i0 pivot_mem_682_i0 child_required_sub_682_i0 child_envelope_sub_682_i0 ?_
  intro b hb
  exact common_sub_682_i0 (mem_commonEnvelope childrenD_682_i0 b hb)
def required_682_i5 : Finset Cell := ⟨(([(4, 6), (6, 4), (6, 5), (6, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_682_i5 : Finset Cell := ⟨(([(3, 6), (3, 7), (4, 6), (4, 7), (5, 7), (5, 8), (5, 9), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (8, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_682_i5 : Fin 3 → Finset Cell := ![(placed21 0 (6, 3) required_7), (placed21 2 (7, 3) required_9), (placed21 5 (8, 4) required_386)]
def childrenD_682_i5 : Fin 3 → Finset Cell := ![(placed21 0 (6, 3) envelope_7), (placed21 2 (7, 3) envelope_9), (placed21 5 (8, 4) envelope_386)]
theorem common_sub_682_i5 : commonEnvelope childrenD_682_i5 ⊆ insert (6, 7) required_682_i5 := by decide +kernel
theorem child_required_sub_682_i5 : ∀ j, childrenC_682_i5 j ⊆ insert (6, 7) required_682_i5 := by decide +kernel
theorem child_envelope_sub_682_i5 : ∀ j, childrenD_682_i5 j ⊆ envelope_682_i5 := by decide +kernel
theorem pivot_mem_682_i5 : (6, 7) ∈ envelope_682_i5 := by decide +kernel
theorem children_work_682_i5 : ∀ j, Template HasSnaky 5 (childrenC_682_i5 j) (childrenD_682_i5 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 0 (6, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_9 2 (7, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_386 5 (8, 4)).mono (by decide +kernel)
theorem row_works_682_i5 : Template HasSnaky 6 required_682_i5 envelope_682_i5 := by
  refine compose HasSnaky 5 childrenC_682_i5 childrenD_682_i5 children_work_682_i5 (6, 7)
    required_682_i5 envelope_682_i5 pivot_mem_682_i5 child_required_sub_682_i5 child_envelope_sub_682_i5 ?_
  intro b hb
  exact common_sub_682_i5 (mem_commonEnvelope childrenD_682_i5 b hb)
def required_682_i6 : Finset Cell := ⟨(([(3, 5), (4, 4), (4, 5), (4, 6), (6, 5), (6, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_682_i6 : Finset Cell := ⟨(([(2, 7), (3, 5), (3, 6), (3, 7), (3, 8), (4, 4), (4, 5), (4, 6), (5, 6), (6, 5), (6, 6), (7, 5), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_682_i6 : Fin 2 → Finset Cell := ![(placed21 6 (7, 6) required_0), (placed21 1 (2, 4) required_222)]
def childrenD_682_i6 : Fin 2 → Finset Cell := ![(placed21 6 (7, 6) envelope_0), (placed21 1 (2, 4) envelope_222)]
theorem common_sub_682_i6 : commonEnvelope childrenD_682_i6 ⊆ insert (5, 6) required_682_i6 := by decide +kernel
theorem child_required_sub_682_i6 : ∀ j, childrenC_682_i6 j ⊆ insert (5, 6) required_682_i6 := by decide +kernel
theorem child_envelope_sub_682_i6 : ∀ j, childrenD_682_i6 j ⊆ envelope_682_i6 := by decide +kernel
theorem pivot_mem_682_i6 : (5, 6) ∈ envelope_682_i6 := by decide +kernel
theorem children_work_682_i6 : ∀ j, Template HasSnaky 3 (childrenC_682_i6 j) (childrenD_682_i6 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 6 (7, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_222 1 (2, 4)).mono (by decide +kernel)
theorem row_works_682_i6 : Template HasSnaky 4 required_682_i6 envelope_682_i6 := by
  refine compose HasSnaky 3 childrenC_682_i6 childrenD_682_i6 children_work_682_i6 (5, 6)
    required_682_i6 envelope_682_i6 pivot_mem_682_i6 child_required_sub_682_i6 child_envelope_sub_682_i6 ?_
  intro b hb
  exact common_sub_682_i6 (mem_commonEnvelope childrenD_682_i6 b hb)
def required_682_i4 : Finset Cell := ⟨(([(3, 5), (4, 4), (4, 5), (6, 4), (6, 5), (6, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_682_i4 : Finset Cell := ⟨(([(2, 7), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 6), (5, 7), (5, 8), (5, 9), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (8, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_682_i4 : Fin 4 → Finset Cell := ![(placed21 2 (7, 3) required_377), required_682_i5, (placed21 0 (2, 3) required_426), required_682_i6]
def childrenD_682_i4 : Fin 4 → Finset Cell := ![(placed21 2 (7, 3) envelope_377), envelope_682_i5, (placed21 0 (2, 3) envelope_426), envelope_682_i6]
theorem common_sub_682_i4 : commonEnvelope childrenD_682_i4 ⊆ insert (4, 6) required_682_i4 := by decide +kernel
theorem child_required_sub_682_i4 : ∀ j, childrenC_682_i4 j ⊆ insert (4, 6) required_682_i4 := by decide +kernel
theorem child_envelope_sub_682_i4 : ∀ j, childrenD_682_i4 j ⊆ envelope_682_i4 := by decide +kernel
theorem pivot_mem_682_i4 : (4, 6) ∈ envelope_682_i4 := by decide +kernel
theorem children_work_682_i4 : ∀ j, Template HasSnaky 6 (childrenC_682_i4 j) (childrenD_682_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_377 2 (7, 3)).mono (by decide +kernel)
  · exact row_works_682_i5.mono (by decide +kernel)
  · exact (placed21_template row_works_426 0 (2, 3)).mono (by decide +kernel)
  · exact row_works_682_i6.mono (by decide +kernel)
theorem row_works_682_i4 : Template HasSnaky 7 required_682_i4 envelope_682_i4 := by
  refine compose HasSnaky 6 childrenC_682_i4 childrenD_682_i4 children_work_682_i4 (4, 6)
    required_682_i4 envelope_682_i4 pivot_mem_682_i4 child_required_sub_682_i4 child_envelope_sub_682_i4 ?_
  intro b hb
  exact common_sub_682_i4 (mem_commonEnvelope childrenD_682_i4 b hb)
def required_682_i3 : Finset Cell := ⟨(([(3, 5), (4, 4), (4, 5), (6, 4), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_682_i3 : Finset Cell := ⟨(([(2, 7), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 1), (5, 2), (5, 3), (5, 6), (5, 7), (5, 8), (5, 9), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (8, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_682_i3 : Fin 5 → Finset Cell := ![(placed21 2 (7, 2) required_13), (placed21 6 (7, 8) required_14), (placed21 4 (3, 7) required_79), (placed21 2 (7, 3) required_679), required_682_i4]
def childrenD_682_i3 : Fin 5 → Finset Cell := ![(placed21 2 (7, 2) envelope_13), (placed21 6 (7, 8) envelope_14), (placed21 4 (3, 7) envelope_79), (placed21 2 (7, 3) envelope_679), envelope_682_i4]
theorem common_sub_682_i3 : commonEnvelope childrenD_682_i3 ⊆ insert (6, 6) required_682_i3 := by decide +kernel
theorem child_required_sub_682_i3 : ∀ j, childrenC_682_i3 j ⊆ insert (6, 6) required_682_i3 := by decide +kernel
theorem child_envelope_sub_682_i3 : ∀ j, childrenD_682_i3 j ⊆ envelope_682_i3 := by decide +kernel
theorem pivot_mem_682_i3 : (6, 6) ∈ envelope_682_i3 := by decide +kernel
theorem children_work_682_i3 : ∀ j, Template HasSnaky 7 (childrenC_682_i3 j) (childrenD_682_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_13 2 (7, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_14 6 (7, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_79 4 (3, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_679 2 (7, 3)).mono (by decide +kernel)
  · exact row_works_682_i4.mono (by decide +kernel)
theorem row_works_682_i3 : Template HasSnaky 8 required_682_i3 envelope_682_i3 := by
  refine compose HasSnaky 7 childrenC_682_i3 childrenD_682_i3 children_work_682_i3 (6, 6)
    required_682_i3 envelope_682_i3 pivot_mem_682_i3 child_required_sub_682_i3 child_envelope_sub_682_i3 ?_
  intro b hb
  exact common_sub_682_i3 (mem_commonEnvelope childrenD_682_i3 b hb)
def required_682_i2 : Finset Cell := ⟨(([(3, 5), (4, 4), (4, 5), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_682_i2 : Finset Cell := ⟨(([(2, 4), (2, 7), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 1), (5, 2), (5, 3), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (8, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_682_i2 : Fin 4 → Finset Cell := ![(placed21 4 (3, 8) required_59), (placed21 3 (2, 5) required_105), (placed21 2 (7, 1) required_678), required_682_i3]
def childrenD_682_i2 : Fin 4 → Finset Cell := ![(placed21 4 (3, 8) envelope_59), (placed21 3 (2, 5) envelope_105), (placed21 2 (7, 1) envelope_678), envelope_682_i3]
theorem common_sub_682_i2 : commonEnvelope childrenD_682_i2 ⊆ insert (6, 5) required_682_i2 := by decide +kernel
theorem child_required_sub_682_i2 : ∀ j, childrenC_682_i2 j ⊆ insert (6, 5) required_682_i2 := by decide +kernel
theorem child_envelope_sub_682_i2 : ∀ j, childrenD_682_i2 j ⊆ envelope_682_i2 := by decide +kernel
theorem pivot_mem_682_i2 : (6, 5) ∈ envelope_682_i2 := by decide +kernel
theorem children_work_682_i2 : ∀ j, Template HasSnaky 8 (childrenC_682_i2 j) (childrenD_682_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_59 4 (3, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_105 3 (2, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_678 2 (7, 1)).mono (by decide +kernel)
  · exact row_works_682_i3.mono (by decide +kernel)
theorem row_works_682_i2 : Template HasSnaky 9 required_682_i2 envelope_682_i2 := by
  refine compose HasSnaky 8 childrenC_682_i2 childrenD_682_i2 children_work_682_i2 (6, 5)
    required_682_i2 envelope_682_i2 pivot_mem_682_i2 child_required_sub_682_i2 child_envelope_sub_682_i2 ?_
  intro b hb
  exact common_sub_682_i2 (mem_commonEnvelope childrenD_682_i2 b hb)
def required_682_i8 : Finset Cell := ⟨(([(3, 5), (4, 4), (4, 5), (6, 4), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_682_i8 : Finset Cell := ⟨(([(2, 3), (2, 7), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 4), (4, 5), (4, 6), (4, 7), (5, 1), (5, 2), (5, 3), (5, 4), (5, 6), (5, 7), (5, 8), (5, 9), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (7, 1), (7, 2), (7, 3), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_682_i8 : Fin 4 → Finset Cell := ![(placed21 6 (7, 8) required_13), (placed21 4 (3, 7) required_79), (placed21 2 (7, 2) required_243), (placed21 2 (7, 3) required_679)]
def childrenD_682_i8 : Fin 4 → Finset Cell := ![(placed21 6 (7, 8) envelope_13), (placed21 4 (3, 7) envelope_79), (placed21 2 (7, 2) envelope_243), (placed21 2 (7, 3) envelope_679)]
theorem common_sub_682_i8 : commonEnvelope childrenD_682_i8 ⊆ insert (6, 6) required_682_i8 := by decide +kernel
theorem child_required_sub_682_i8 : ∀ j, childrenC_682_i8 j ⊆ insert (6, 6) required_682_i8 := by decide +kernel
theorem child_envelope_sub_682_i8 : ∀ j, childrenD_682_i8 j ⊆ envelope_682_i8 := by decide +kernel
theorem pivot_mem_682_i8 : (6, 6) ∈ envelope_682_i8 := by decide +kernel
theorem children_work_682_i8 : ∀ j, Template HasSnaky 5 (childrenC_682_i8 j) (childrenD_682_i8 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_13 6 (7, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_79 4 (3, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_243 2 (7, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_679 2 (7, 3)).mono (by decide +kernel)
theorem row_works_682_i8 : Template HasSnaky 6 required_682_i8 envelope_682_i8 := by
  refine compose HasSnaky 5 childrenC_682_i8 childrenD_682_i8 children_work_682_i8 (6, 6)
    required_682_i8 envelope_682_i8 pivot_mem_682_i8 child_required_sub_682_i8 child_envelope_sub_682_i8 ?_
  intro b hb
  exact common_sub_682_i8 (mem_commonEnvelope childrenD_682_i8 b hb)
def required_682_i7 : Finset Cell := ⟨(([(3, 5), (4, 4), (4, 5), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_682_i7 : Finset Cell := ⟨(([(1, 3), (2, 3), (2, 4), (2, 7), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (7, 1), (7, 2), (7, 3), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (8, 6), (9, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_682_i7 : Fin 6 → Finset Cell := ![(placed21 0 (3, 1) required_430), (placed21 0 (2, 2) required_431), (placed21 7 (7, 5) required_592), (placed21 2 (7, 1) required_678), required_682_i8, (placed21 4 (2, 9) required_681)]
def childrenD_682_i7 : Fin 6 → Finset Cell := ![(placed21 0 (3, 1) envelope_430), (placed21 0 (2, 2) envelope_431), (placed21 7 (7, 5) envelope_592), (placed21 2 (7, 1) envelope_678), envelope_682_i8, (placed21 4 (2, 9) envelope_681)]
theorem common_sub_682_i7 : commonEnvelope childrenD_682_i7 ⊆ insert (6, 5) required_682_i7 := by decide +kernel
theorem child_required_sub_682_i7 : ∀ j, childrenC_682_i7 j ⊆ insert (6, 5) required_682_i7 := by decide +kernel
theorem child_envelope_sub_682_i7 : ∀ j, childrenD_682_i7 j ⊆ envelope_682_i7 := by decide +kernel
theorem pivot_mem_682_i7 : (6, 5) ∈ envelope_682_i7 := by decide +kernel
theorem children_work_682_i7 : ∀ j, Template HasSnaky 8 (childrenC_682_i7 j) (childrenD_682_i7 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_430 0 (3, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_431 0 (2, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_592 7 (7, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_678 2 (7, 1)).mono (by decide +kernel)
  · exact row_works_682_i8.mono (by decide +kernel)
  · exact (placed21_template row_works_681 4 (2, 9)).mono (by decide +kernel)
theorem row_works_682_i7 : Template HasSnaky 9 required_682_i7 envelope_682_i7 := by
  refine compose HasSnaky 8 childrenC_682_i7 childrenD_682_i7 children_work_682_i7 (6, 5)
    required_682_i7 envelope_682_i7 pivot_mem_682_i7 child_required_sub_682_i7 child_envelope_sub_682_i7 ?_
  intro b hb
  exact common_sub_682_i7 (mem_commonEnvelope childrenD_682_i7 b hb)
def required_682_i1 : Finset Cell := ⟨(([(3, 5), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_682_i1 : Finset Cell := ⟨(([(1, 3), (2, 3), (2, 4), (2, 7), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_682_i1 : Fin 7 → Finset Cell := ![(placed21 2 (7, 2) required_422), (placed21 4 (2, 8) required_450), (placed21 6 (7, 7) required_503), (placed21 0 (3, 0) required_642), required_682_i2, (placed21 4 (2, 7) required_680), required_682_i7]
def childrenD_682_i1 : Fin 7 → Finset Cell := ![(placed21 2 (7, 2) envelope_422), (placed21 4 (2, 8) envelope_450), (placed21 6 (7, 7) envelope_503), (placed21 0 (3, 0) envelope_642), envelope_682_i2, (placed21 4 (2, 7) envelope_680), envelope_682_i7]
theorem common_sub_682_i1 : commonEnvelope childrenD_682_i1 ⊆ insert (6, 4) required_682_i1 := by decide +kernel
theorem child_required_sub_682_i1 : ∀ j, childrenC_682_i1 j ⊆ insert (6, 4) required_682_i1 := by decide +kernel
theorem child_envelope_sub_682_i1 : ∀ j, childrenD_682_i1 j ⊆ envelope_682_i1 := by decide +kernel
theorem pivot_mem_682_i1 : (6, 4) ∈ envelope_682_i1 := by decide +kernel
theorem children_work_682_i1 : ∀ j, Template HasSnaky 13 (childrenC_682_i1 j) (childrenD_682_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_422 2 (7, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_450 4 (2, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_503 6 (7, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_642 0 (3, 0)).mono (by decide +kernel)
  · exact row_works_682_i2.mono (by decide +kernel)
  · exact (placed21_template row_works_680 4 (2, 7)).mono (by decide +kernel)
  · exact row_works_682_i7.mono (by decide +kernel)
theorem row_works_682_i1 : Template HasSnaky 14 required_682_i1 envelope_682_i1 := by
  refine compose HasSnaky 13 childrenC_682_i1 childrenD_682_i1 children_work_682_i1 (6, 4)
    required_682_i1 envelope_682_i1 pivot_mem_682_i1 child_required_sub_682_i1 child_envelope_sub_682_i1 ?_
  intro b hb
  exact common_sub_682_i1 (mem_commonEnvelope childrenD_682_i1 b hb)
def required_682 : Finset Cell := ⟨(([(3, 5), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_682 : Finset Cell := ⟨(([(0, 2), (0, 3), (0, 4), (1, 1), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 7), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_682 : Fin 9 → Finset Cell := ![(placed21 4 (3, 8) required_408), (placed21 4 (3, 8) required_410), (placed21 6 (6, 8) required_475), (placed21 3 (1, 7) required_509), (placed21 7 (7, 7) required_510), (placed21 4 (2, 8) required_587), (placed21 6 (7, 8) required_646), required_682_i0, required_682_i1]
def childrenD_682 : Fin 9 → Finset Cell := ![(placed21 4 (3, 8) envelope_408), (placed21 4 (3, 8) envelope_410), (placed21 6 (6, 8) envelope_475), (placed21 3 (1, 7) envelope_509), (placed21 7 (7, 7) envelope_510), (placed21 4 (2, 8) envelope_587), (placed21 6 (7, 8) envelope_646), envelope_682_i0, envelope_682_i1]
theorem common_sub_682 : commonEnvelope childrenD_682 ⊆ insert (4, 4) required_682 := by decide +kernel
theorem child_required_sub_682 : ∀ j, childrenC_682 j ⊆ insert (4, 4) required_682 := by decide +kernel
theorem child_envelope_sub_682 : ∀ j, childrenD_682 j ⊆ envelope_682 := by decide +kernel
theorem pivot_mem_682 : (4, 4) ∈ envelope_682 := by decide +kernel
theorem children_work_682 : ∀ j, Template HasSnaky 14 (childrenC_682 j) (childrenD_682 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_408 4 (3, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_410 4 (3, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_475 6 (6, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_509 3 (1, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_510 7 (7, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_587 4 (2, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_646 6 (7, 8)).mono (by decide +kernel)
  · exact row_works_682_i0.mono (by decide +kernel)
  · exact row_works_682_i1.mono (by decide +kernel)
theorem row_works_682 : Template HasSnaky 15 required_682 envelope_682 := by
  refine compose HasSnaky 14 childrenC_682 childrenD_682 children_work_682 (4, 4)
    required_682 envelope_682 pivot_mem_682 child_required_sub_682 child_envelope_sub_682 ?_
  intro b hb
  exact common_sub_682 (mem_commonEnvelope childrenD_682 b hb)
def height_670_i0 : ℕ := 12
def childrenH_670_i0 : Fin 3 → ℕ := ![height_40, height_125, height_660]
theorem height_exact_670_i0 : height_670_i0 = 1 + Finset.univ.sup childrenH_670_i0 := by decide +kernel
theorem required_origin_670_i0 : ∀ x ∈ required_670_i0,
    (∃ j, x ∈ childrenC_670_i0 j) ∨ ∀ j, x ∈ childrenD_670_i0 j := by decide +kernel
theorem required_exact_670_i0 : required_670_i0 =
    ((Finset.univ.biUnion childrenC_670_i0) ∪ commonEnvelope childrenD_670_i0).erase (5, 5) := by
  exact required_eq_combination childrenC_670_i0 childrenD_670_i0 (5, 5) required_670_i0
    (by decide +kernel) child_required_sub_670_i0 common_sub_670_i0 required_origin_670_i0
theorem envelope_origin_670_i0 : ∀ x ∈ envelope_670_i0,
    x = (5, 5) ∨ ∃ j, x ∈ childrenD_670_i0 j := by decide +kernel
theorem envelope_exact_670_i0 : envelope_670_i0 =
    insert (5, 5) (Finset.univ.biUnion childrenD_670_i0) := by
  exact envelope_eq_combination childrenD_670_i0 (5, 5) envelope_670_i0
    pivot_mem_670_i0 child_envelope_sub_670_i0 envelope_origin_670_i0
def checked_670_i0 : CheckedCard where
  required := required_670_i0
  envelope := envelope_670_i0
  height := height_670_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_670_i0
def height_670_i1 : ℕ := 12
def childrenH_670_i1 : Fin 3 → ℕ := ![height_40, height_125, height_663]
theorem height_exact_670_i1 : height_670_i1 = 1 + Finset.univ.sup childrenH_670_i1 := by decide +kernel
theorem required_origin_670_i1 : ∀ x ∈ required_670_i1,
    (∃ j, x ∈ childrenC_670_i1 j) ∨ ∀ j, x ∈ childrenD_670_i1 j := by decide +kernel
theorem required_exact_670_i1 : required_670_i1 =
    ((Finset.univ.biUnion childrenC_670_i1) ∪ commonEnvelope childrenD_670_i1).erase (5, 5) := by
  exact required_eq_combination childrenC_670_i1 childrenD_670_i1 (5, 5) required_670_i1
    (by decide +kernel) child_required_sub_670_i1 common_sub_670_i1 required_origin_670_i1
theorem envelope_origin_670_i1 : ∀ x ∈ envelope_670_i1,
    x = (5, 5) ∨ ∃ j, x ∈ childrenD_670_i1 j := by decide +kernel
theorem envelope_exact_670_i1 : envelope_670_i1 =
    insert (5, 5) (Finset.univ.biUnion childrenD_670_i1) := by
  exact envelope_eq_combination childrenD_670_i1 (5, 5) envelope_670_i1
    pivot_mem_670_i1 child_envelope_sub_670_i1 envelope_origin_670_i1
def checked_670_i1 : CheckedCard where
  required := required_670_i1
  envelope := envelope_670_i1
  height := height_670_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_670_i1
def height_670_i3 : ℕ := 9
def childrenH_670_i3 : Fin 3 → ℕ := ![height_106, height_219, height_530]
theorem height_exact_670_i3 : height_670_i3 = 1 + Finset.univ.sup childrenH_670_i3 := by decide +kernel
theorem required_origin_670_i3 : ∀ x ∈ required_670_i3,
    (∃ j, x ∈ childrenC_670_i3 j) ∨ ∀ j, x ∈ childrenD_670_i3 j := by decide +kernel
theorem required_exact_670_i3 : required_670_i3 =
    ((Finset.univ.biUnion childrenC_670_i3) ∪ commonEnvelope childrenD_670_i3).erase (7, 6) := by
  exact required_eq_combination childrenC_670_i3 childrenD_670_i3 (7, 6) required_670_i3
    (by decide +kernel) child_required_sub_670_i3 common_sub_670_i3 required_origin_670_i3
theorem envelope_origin_670_i3 : ∀ x ∈ envelope_670_i3,
    x = (7, 6) ∨ ∃ j, x ∈ childrenD_670_i3 j := by decide +kernel
theorem envelope_exact_670_i3 : envelope_670_i3 =
    insert (7, 6) (Finset.univ.biUnion childrenD_670_i3) := by
  exact envelope_eq_combination childrenD_670_i3 (7, 6) envelope_670_i3
    pivot_mem_670_i3 child_envelope_sub_670_i3 envelope_origin_670_i3
def checked_670_i3 : CheckedCard where
  required := required_670_i3
  envelope := envelope_670_i3
  height := height_670_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_670_i3
def height_670_i4 : ℕ := 10
def childrenH_670_i4 : Fin 3 → ℕ := ![height_40, height_98, height_512]
theorem height_exact_670_i4 : height_670_i4 = 1 + Finset.univ.sup childrenH_670_i4 := by decide +kernel
theorem required_origin_670_i4 : ∀ x ∈ required_670_i4,
    (∃ j, x ∈ childrenC_670_i4 j) ∨ ∀ j, x ∈ childrenD_670_i4 j := by decide +kernel
theorem required_exact_670_i4 : required_670_i4 =
    ((Finset.univ.biUnion childrenC_670_i4) ∪ commonEnvelope childrenD_670_i4).erase (5, 5) := by
  exact required_eq_combination childrenC_670_i4 childrenD_670_i4 (5, 5) required_670_i4
    (by decide +kernel) child_required_sub_670_i4 common_sub_670_i4 required_origin_670_i4
theorem envelope_origin_670_i4 : ∀ x ∈ envelope_670_i4,
    x = (5, 5) ∨ ∃ j, x ∈ childrenD_670_i4 j := by decide +kernel
theorem envelope_exact_670_i4 : envelope_670_i4 =
    insert (5, 5) (Finset.univ.biUnion childrenD_670_i4) := by
  exact envelope_eq_combination childrenD_670_i4 (5, 5) envelope_670_i4
    pivot_mem_670_i4 child_envelope_sub_670_i4 envelope_origin_670_i4
def checked_670_i4 : CheckedCard where
  required := required_670_i4
  envelope := envelope_670_i4
  height := height_670_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_670_i4
def height_670_i2 : ℕ := 13
def childrenH_670_i2 : Fin 5 → ℕ := ![height_270, height_588, height_638, height_670_i3, height_670_i4]
theorem height_exact_670_i2 : height_670_i2 = 1 + Finset.univ.sup childrenH_670_i2 := by decide +kernel
theorem required_origin_670_i2 : ∀ x ∈ required_670_i2,
    (∃ j, x ∈ childrenC_670_i2 j) ∨ ∀ j, x ∈ childrenD_670_i2 j := by decide +kernel
theorem required_exact_670_i2 : required_670_i2 =
    ((Finset.univ.biUnion childrenC_670_i2) ∪ commonEnvelope childrenD_670_i2).erase (5, 6) := by
  exact required_eq_combination childrenC_670_i2 childrenD_670_i2 (5, 6) required_670_i2
    (by decide +kernel) child_required_sub_670_i2 common_sub_670_i2 required_origin_670_i2
theorem envelope_origin_670_i2 : ∀ x ∈ envelope_670_i2,
    x = (5, 6) ∨ ∃ j, x ∈ childrenD_670_i2 j := by decide +kernel
theorem envelope_exact_670_i2 : envelope_670_i2 =
    insert (5, 6) (Finset.univ.biUnion childrenD_670_i2) := by
  exact envelope_eq_combination childrenD_670_i2 (5, 6) envelope_670_i2
    pivot_mem_670_i2 child_envelope_sub_670_i2 envelope_origin_670_i2
def checked_670_i2 : CheckedCard where
  required := required_670_i2
  envelope := envelope_670_i2
  height := height_670_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_670_i2
def height_670_i5 : ℕ := 12
def childrenH_670_i5 : Fin 3 → ℕ := ![height_40, height_125, height_617]
theorem height_exact_670_i5 : height_670_i5 = 1 + Finset.univ.sup childrenH_670_i5 := by decide +kernel
theorem required_origin_670_i5 : ∀ x ∈ required_670_i5,
    (∃ j, x ∈ childrenC_670_i5 j) ∨ ∀ j, x ∈ childrenD_670_i5 j := by decide +kernel
theorem required_exact_670_i5 : required_670_i5 =
    ((Finset.univ.biUnion childrenC_670_i5) ∪ commonEnvelope childrenD_670_i5).erase (5, 5) := by
  exact required_eq_combination childrenC_670_i5 childrenD_670_i5 (5, 5) required_670_i5
    (by decide +kernel) child_required_sub_670_i5 common_sub_670_i5 required_origin_670_i5
theorem envelope_origin_670_i5 : ∀ x ∈ envelope_670_i5,
    x = (5, 5) ∨ ∃ j, x ∈ childrenD_670_i5 j := by decide +kernel
theorem envelope_exact_670_i5 : envelope_670_i5 =
    insert (5, 5) (Finset.univ.biUnion childrenD_670_i5) := by
  exact envelope_eq_combination childrenD_670_i5 (5, 5) envelope_670_i5
    pivot_mem_670_i5 child_envelope_sub_670_i5 envelope_origin_670_i5
def checked_670_i5 : CheckedCard where
  required := required_670_i5
  envelope := envelope_670_i5
  height := height_670_i5
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_670_i5
def height_670_i6 : ℕ := 10
def childrenH_670_i6 : Fin 7 → ℕ := ![height_13, height_31, height_355, height_356, height_434, height_435, height_441]
theorem height_exact_670_i6 : height_670_i6 = 1 + Finset.univ.sup childrenH_670_i6 := by decide +kernel
theorem required_origin_670_i6 : ∀ x ∈ required_670_i6,
    (∃ j, x ∈ childrenC_670_i6 j) ∨ ∀ j, x ∈ childrenD_670_i6 j := by decide +kernel
theorem required_exact_670_i6 : required_670_i6 =
    ((Finset.univ.biUnion childrenC_670_i6) ∪ commonEnvelope childrenD_670_i6).erase (6, 4) := by
  exact required_eq_combination childrenC_670_i6 childrenD_670_i6 (6, 4) required_670_i6
    (by decide +kernel) child_required_sub_670_i6 common_sub_670_i6 required_origin_670_i6
theorem envelope_origin_670_i6 : ∀ x ∈ envelope_670_i6,
    x = (6, 4) ∨ ∃ j, x ∈ childrenD_670_i6 j := by decide +kernel
theorem envelope_exact_670_i6 : envelope_670_i6 =
    insert (6, 4) (Finset.univ.biUnion childrenD_670_i6) := by
  exact envelope_eq_combination childrenD_670_i6 (6, 4) envelope_670_i6
    pivot_mem_670_i6 child_envelope_sub_670_i6 envelope_origin_670_i6
def checked_670_i6 : CheckedCard where
  required := required_670_i6
  envelope := envelope_670_i6
  height := height_670_i6
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_670_i6
def height_670_i7 : ℕ := 11
def childrenH_670_i7 : Fin 3 → ℕ := ![height_40, height_125, height_535]
theorem height_exact_670_i7 : height_670_i7 = 1 + Finset.univ.sup childrenH_670_i7 := by decide +kernel
theorem required_origin_670_i7 : ∀ x ∈ required_670_i7,
    (∃ j, x ∈ childrenC_670_i7 j) ∨ ∀ j, x ∈ childrenD_670_i7 j := by decide +kernel
theorem required_exact_670_i7 : required_670_i7 =
    ((Finset.univ.biUnion childrenC_670_i7) ∪ commonEnvelope childrenD_670_i7).erase (5, 5) := by
  exact required_eq_combination childrenC_670_i7 childrenD_670_i7 (5, 5) required_670_i7
    (by decide +kernel) child_required_sub_670_i7 common_sub_670_i7 required_origin_670_i7
theorem envelope_origin_670_i7 : ∀ x ∈ envelope_670_i7,
    x = (5, 5) ∨ ∃ j, x ∈ childrenD_670_i7 j := by decide +kernel
theorem envelope_exact_670_i7 : envelope_670_i7 =
    insert (5, 5) (Finset.univ.biUnion childrenD_670_i7) := by
  exact envelope_eq_combination childrenD_670_i7 (5, 5) envelope_670_i7
    pivot_mem_670_i7 child_envelope_sub_670_i7 envelope_origin_670_i7
def checked_670_i7 : CheckedCard where
  required := required_670_i7
  envelope := envelope_670_i7
  height := height_670_i7
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_670_i7
def height_670_i8 : ℕ := 10
def childrenH_670_i8 : Fin 6 → ℕ := ![height_188, height_188, height_441, height_442, height_514, height_667]
theorem height_exact_670_i8 : height_670_i8 = 1 + Finset.univ.sup childrenH_670_i8 := by decide +kernel
theorem required_origin_670_i8 : ∀ x ∈ required_670_i8,
    (∃ j, x ∈ childrenC_670_i8 j) ∨ ∀ j, x ∈ childrenD_670_i8 j := by decide +kernel
theorem required_exact_670_i8 : required_670_i8 =
    ((Finset.univ.biUnion childrenC_670_i8) ∪ commonEnvelope childrenD_670_i8).erase (6, 4) := by
  exact required_eq_combination childrenC_670_i8 childrenD_670_i8 (6, 4) required_670_i8
    (by decide +kernel) child_required_sub_670_i8 common_sub_670_i8 required_origin_670_i8
theorem envelope_origin_670_i8 : ∀ x ∈ envelope_670_i8,
    x = (6, 4) ∨ ∃ j, x ∈ childrenD_670_i8 j := by decide +kernel
theorem envelope_exact_670_i8 : envelope_670_i8 =
    insert (6, 4) (Finset.univ.biUnion childrenD_670_i8) := by
  exact envelope_eq_combination childrenD_670_i8 (6, 4) envelope_670_i8
    pivot_mem_670_i8 child_envelope_sub_670_i8 envelope_origin_670_i8
def checked_670_i8 : CheckedCard where
  required := required_670_i8
  envelope := envelope_670_i8
  height := height_670_i8
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_670_i8
def height_670_i10 : ℕ := 7
def childrenH_670_i10 : Fin 2 → ℕ := ![height_125, height_136]
theorem height_exact_670_i10 : height_670_i10 = 1 + Finset.univ.sup childrenH_670_i10 := by decide +kernel
theorem required_origin_670_i10 : ∀ x ∈ required_670_i10,
    (∃ j, x ∈ childrenC_670_i10 j) ∨ ∀ j, x ∈ childrenD_670_i10 j := by decide +kernel
theorem required_exact_670_i10 : required_670_i10 =
    ((Finset.univ.biUnion childrenC_670_i10) ∪ commonEnvelope childrenD_670_i10).erase (5, 5) := by
  exact required_eq_combination childrenC_670_i10 childrenD_670_i10 (5, 5) required_670_i10
    (by decide +kernel) child_required_sub_670_i10 common_sub_670_i10 required_origin_670_i10
theorem envelope_origin_670_i10 : ∀ x ∈ envelope_670_i10,
    x = (5, 5) ∨ ∃ j, x ∈ childrenD_670_i10 j := by decide +kernel
theorem envelope_exact_670_i10 : envelope_670_i10 =
    insert (5, 5) (Finset.univ.biUnion childrenD_670_i10) := by
  exact envelope_eq_combination childrenD_670_i10 (5, 5) envelope_670_i10
    pivot_mem_670_i10 child_envelope_sub_670_i10 envelope_origin_670_i10
def checked_670_i10 : CheckedCard where
  required := required_670_i10
  envelope := envelope_670_i10
  height := height_670_i10
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_670_i10
def height_670_i9 : ℕ := 14
def childrenH_670_i9 : Fin 5 → ℕ := ![height_13, height_514, height_590, height_668, height_670_i10]
theorem height_exact_670_i9 : height_670_i9 = 1 + Finset.univ.sup childrenH_670_i9 := by decide +kernel
theorem required_origin_670_i9 : ∀ x ∈ required_670_i9,
    (∃ j, x ∈ childrenC_670_i9 j) ∨ ∀ j, x ∈ childrenD_670_i9 j := by decide +kernel
theorem required_exact_670_i9 : required_670_i9 =
    ((Finset.univ.biUnion childrenC_670_i9) ∪ commonEnvelope childrenD_670_i9).erase (6, 4) := by
  exact required_eq_combination childrenC_670_i9 childrenD_670_i9 (6, 4) required_670_i9
    (by decide +kernel) child_required_sub_670_i9 common_sub_670_i9 required_origin_670_i9
theorem envelope_origin_670_i9 : ∀ x ∈ envelope_670_i9,
    x = (6, 4) ∨ ∃ j, x ∈ childrenD_670_i9 j := by decide +kernel
theorem envelope_exact_670_i9 : envelope_670_i9 =
    insert (6, 4) (Finset.univ.biUnion childrenD_670_i9) := by
  exact envelope_eq_combination childrenD_670_i9 (6, 4) envelope_670_i9
    pivot_mem_670_i9 child_envelope_sub_670_i9 envelope_origin_670_i9
def checked_670_i9 : CheckedCard where
  required := required_670_i9
  envelope := envelope_670_i9
  height := height_670_i9
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_670_i9
def height_670 : ℕ := 15
def childrenH_670 : Fin 12 → ℕ := ![height_459, height_670_i0, height_661, height_670_i1, height_670_i2, height_670_i5, height_670_i6, height_670_i7, height_665, height_670_i8, height_670_i9, height_669]
theorem height_exact_670 : height_670 = 1 + Finset.univ.sup childrenH_670 := by decide +kernel
theorem required_origin_670 : ∀ x ∈ required_670,
    (∃ j, x ∈ childrenC_670 j) ∨ ∀ j, x ∈ childrenD_670 j := by decide +kernel
theorem required_exact_670 : required_670 =
    ((Finset.univ.biUnion childrenC_670) ∪ commonEnvelope childrenD_670).erase (6, 6) := by
  exact required_eq_combination childrenC_670 childrenD_670 (6, 6) required_670
    (by decide +kernel) child_required_sub_670 common_sub_670 required_origin_670
theorem envelope_origin_670 : ∀ x ∈ envelope_670,
    x = (6, 6) ∨ ∃ j, x ∈ childrenD_670 j := by decide +kernel
theorem envelope_exact_670 : envelope_670 =
    insert (6, 6) (Finset.univ.biUnion childrenD_670) := by
  exact envelope_eq_combination childrenD_670 (6, 6) envelope_670
    pivot_mem_670 child_envelope_sub_670 envelope_origin_670
def checked_670 : CheckedCard where
  required := required_670
  envelope := envelope_670
  height := height_670
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_670
def height_682_i0 : ℕ := 12
def childrenH_682_i0 : Fin 4 → ℕ := ![height_44, height_52, height_128, height_676]
theorem height_exact_682_i0 : height_682_i0 = 1 + Finset.univ.sup childrenH_682_i0 := by decide +kernel
theorem required_origin_682_i0 : ∀ x ∈ required_682_i0,
    (∃ j, x ∈ childrenC_682_i0 j) ∨ ∀ j, x ∈ childrenD_682_i0 j := by decide +kernel
theorem required_exact_682_i0 : required_682_i0 =
    ((Finset.univ.biUnion childrenC_682_i0) ∪ commonEnvelope childrenD_682_i0).erase (4, 3) := by
  exact required_eq_combination childrenC_682_i0 childrenD_682_i0 (4, 3) required_682_i0
    (by decide +kernel) child_required_sub_682_i0 common_sub_682_i0 required_origin_682_i0
theorem envelope_origin_682_i0 : ∀ x ∈ envelope_682_i0,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_682_i0 j := by decide +kernel
theorem envelope_exact_682_i0 : envelope_682_i0 =
    insert (4, 3) (Finset.univ.biUnion childrenD_682_i0) := by
  exact envelope_eq_combination childrenD_682_i0 (4, 3) envelope_682_i0
    pivot_mem_682_i0 child_envelope_sub_682_i0 envelope_origin_682_i0
def checked_682_i0 : CheckedCard where
  required := required_682_i0
  envelope := envelope_682_i0
  height := height_682_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_682_i0
def height_682_i5 : ℕ := 6
def childrenH_682_i5 : Fin 3 → ℕ := ![height_7, height_9, height_386]
theorem height_exact_682_i5 : height_682_i5 = 1 + Finset.univ.sup childrenH_682_i5 := by decide +kernel
theorem required_origin_682_i5 : ∀ x ∈ required_682_i5,
    (∃ j, x ∈ childrenC_682_i5 j) ∨ ∀ j, x ∈ childrenD_682_i5 j := by decide +kernel
theorem required_exact_682_i5 : required_682_i5 =
    ((Finset.univ.biUnion childrenC_682_i5) ∪ commonEnvelope childrenD_682_i5).erase (6, 7) := by
  exact required_eq_combination childrenC_682_i5 childrenD_682_i5 (6, 7) required_682_i5
    (by decide +kernel) child_required_sub_682_i5 common_sub_682_i5 required_origin_682_i5
theorem envelope_origin_682_i5 : ∀ x ∈ envelope_682_i5,
    x = (6, 7) ∨ ∃ j, x ∈ childrenD_682_i5 j := by decide +kernel
theorem envelope_exact_682_i5 : envelope_682_i5 =
    insert (6, 7) (Finset.univ.biUnion childrenD_682_i5) := by
  exact envelope_eq_combination childrenD_682_i5 (6, 7) envelope_682_i5
    pivot_mem_682_i5 child_envelope_sub_682_i5 envelope_origin_682_i5
def checked_682_i5 : CheckedCard where
  required := required_682_i5
  envelope := envelope_682_i5
  height := height_682_i5
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_682_i5
def height_682_i6 : ℕ := 4
def childrenH_682_i6 : Fin 2 → ℕ := ![height_0, height_222]
theorem height_exact_682_i6 : height_682_i6 = 1 + Finset.univ.sup childrenH_682_i6 := by decide +kernel
theorem required_origin_682_i6 : ∀ x ∈ required_682_i6,
    (∃ j, x ∈ childrenC_682_i6 j) ∨ ∀ j, x ∈ childrenD_682_i6 j := by decide +kernel
theorem required_exact_682_i6 : required_682_i6 =
    ((Finset.univ.biUnion childrenC_682_i6) ∪ commonEnvelope childrenD_682_i6).erase (5, 6) := by
  exact required_eq_combination childrenC_682_i6 childrenD_682_i6 (5, 6) required_682_i6
    (by decide +kernel) child_required_sub_682_i6 common_sub_682_i6 required_origin_682_i6
theorem envelope_origin_682_i6 : ∀ x ∈ envelope_682_i6,
    x = (5, 6) ∨ ∃ j, x ∈ childrenD_682_i6 j := by decide +kernel
theorem envelope_exact_682_i6 : envelope_682_i6 =
    insert (5, 6) (Finset.univ.biUnion childrenD_682_i6) := by
  exact envelope_eq_combination childrenD_682_i6 (5, 6) envelope_682_i6
    pivot_mem_682_i6 child_envelope_sub_682_i6 envelope_origin_682_i6
def checked_682_i6 : CheckedCard where
  required := required_682_i6
  envelope := envelope_682_i6
  height := height_682_i6
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_682_i6
def height_682_i4 : ℕ := 7
def childrenH_682_i4 : Fin 4 → ℕ := ![height_377, height_682_i5, height_426, height_682_i6]
theorem height_exact_682_i4 : height_682_i4 = 1 + Finset.univ.sup childrenH_682_i4 := by decide +kernel
theorem required_origin_682_i4 : ∀ x ∈ required_682_i4,
    (∃ j, x ∈ childrenC_682_i4 j) ∨ ∀ j, x ∈ childrenD_682_i4 j := by decide +kernel
theorem required_exact_682_i4 : required_682_i4 =
    ((Finset.univ.biUnion childrenC_682_i4) ∪ commonEnvelope childrenD_682_i4).erase (4, 6) := by
  exact required_eq_combination childrenC_682_i4 childrenD_682_i4 (4, 6) required_682_i4
    (by decide +kernel) child_required_sub_682_i4 common_sub_682_i4 required_origin_682_i4
theorem envelope_origin_682_i4 : ∀ x ∈ envelope_682_i4,
    x = (4, 6) ∨ ∃ j, x ∈ childrenD_682_i4 j := by decide +kernel
theorem envelope_exact_682_i4 : envelope_682_i4 =
    insert (4, 6) (Finset.univ.biUnion childrenD_682_i4) := by
  exact envelope_eq_combination childrenD_682_i4 (4, 6) envelope_682_i4
    pivot_mem_682_i4 child_envelope_sub_682_i4 envelope_origin_682_i4
def checked_682_i4 : CheckedCard where
  required := required_682_i4
  envelope := envelope_682_i4
  height := height_682_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_682_i4
def height_682_i3 : ℕ := 8
def childrenH_682_i3 : Fin 5 → ℕ := ![height_13, height_14, height_79, height_679, height_682_i4]
theorem height_exact_682_i3 : height_682_i3 = 1 + Finset.univ.sup childrenH_682_i3 := by decide +kernel
theorem required_origin_682_i3 : ∀ x ∈ required_682_i3,
    (∃ j, x ∈ childrenC_682_i3 j) ∨ ∀ j, x ∈ childrenD_682_i3 j := by decide +kernel
theorem required_exact_682_i3 : required_682_i3 =
    ((Finset.univ.biUnion childrenC_682_i3) ∪ commonEnvelope childrenD_682_i3).erase (6, 6) := by
  exact required_eq_combination childrenC_682_i3 childrenD_682_i3 (6, 6) required_682_i3
    (by decide +kernel) child_required_sub_682_i3 common_sub_682_i3 required_origin_682_i3
theorem envelope_origin_682_i3 : ∀ x ∈ envelope_682_i3,
    x = (6, 6) ∨ ∃ j, x ∈ childrenD_682_i3 j := by decide +kernel
theorem envelope_exact_682_i3 : envelope_682_i3 =
    insert (6, 6) (Finset.univ.biUnion childrenD_682_i3) := by
  exact envelope_eq_combination childrenD_682_i3 (6, 6) envelope_682_i3
    pivot_mem_682_i3 child_envelope_sub_682_i3 envelope_origin_682_i3
def checked_682_i3 : CheckedCard where
  required := required_682_i3
  envelope := envelope_682_i3
  height := height_682_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_682_i3
def height_682_i2 : ℕ := 9
def childrenH_682_i2 : Fin 4 → ℕ := ![height_59, height_105, height_678, height_682_i3]
theorem height_exact_682_i2 : height_682_i2 = 1 + Finset.univ.sup childrenH_682_i2 := by decide +kernel
theorem required_origin_682_i2 : ∀ x ∈ required_682_i2,
    (∃ j, x ∈ childrenC_682_i2 j) ∨ ∀ j, x ∈ childrenD_682_i2 j := by decide +kernel
theorem required_exact_682_i2 : required_682_i2 =
    ((Finset.univ.biUnion childrenC_682_i2) ∪ commonEnvelope childrenD_682_i2).erase (6, 5) := by
  exact required_eq_combination childrenC_682_i2 childrenD_682_i2 (6, 5) required_682_i2
    (by decide +kernel) child_required_sub_682_i2 common_sub_682_i2 required_origin_682_i2
theorem envelope_origin_682_i2 : ∀ x ∈ envelope_682_i2,
    x = (6, 5) ∨ ∃ j, x ∈ childrenD_682_i2 j := by decide +kernel
theorem envelope_exact_682_i2 : envelope_682_i2 =
    insert (6, 5) (Finset.univ.biUnion childrenD_682_i2) := by
  exact envelope_eq_combination childrenD_682_i2 (6, 5) envelope_682_i2
    pivot_mem_682_i2 child_envelope_sub_682_i2 envelope_origin_682_i2
def checked_682_i2 : CheckedCard where
  required := required_682_i2
  envelope := envelope_682_i2
  height := height_682_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_682_i2
def height_682_i8 : ℕ := 6
def childrenH_682_i8 : Fin 4 → ℕ := ![height_13, height_79, height_243, height_679]
theorem height_exact_682_i8 : height_682_i8 = 1 + Finset.univ.sup childrenH_682_i8 := by decide +kernel
theorem required_origin_682_i8 : ∀ x ∈ required_682_i8,
    (∃ j, x ∈ childrenC_682_i8 j) ∨ ∀ j, x ∈ childrenD_682_i8 j := by decide +kernel
theorem required_exact_682_i8 : required_682_i8 =
    ((Finset.univ.biUnion childrenC_682_i8) ∪ commonEnvelope childrenD_682_i8).erase (6, 6) := by
  exact required_eq_combination childrenC_682_i8 childrenD_682_i8 (6, 6) required_682_i8
    (by decide +kernel) child_required_sub_682_i8 common_sub_682_i8 required_origin_682_i8
theorem envelope_origin_682_i8 : ∀ x ∈ envelope_682_i8,
    x = (6, 6) ∨ ∃ j, x ∈ childrenD_682_i8 j := by decide +kernel
theorem envelope_exact_682_i8 : envelope_682_i8 =
    insert (6, 6) (Finset.univ.biUnion childrenD_682_i8) := by
  exact envelope_eq_combination childrenD_682_i8 (6, 6) envelope_682_i8
    pivot_mem_682_i8 child_envelope_sub_682_i8 envelope_origin_682_i8
def checked_682_i8 : CheckedCard where
  required := required_682_i8
  envelope := envelope_682_i8
  height := height_682_i8
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_682_i8
def height_682_i7 : ℕ := 9
def childrenH_682_i7 : Fin 6 → ℕ := ![height_430, height_431, height_592, height_678, height_682_i8, height_681]
theorem height_exact_682_i7 : height_682_i7 = 1 + Finset.univ.sup childrenH_682_i7 := by decide +kernel
theorem required_origin_682_i7 : ∀ x ∈ required_682_i7,
    (∃ j, x ∈ childrenC_682_i7 j) ∨ ∀ j, x ∈ childrenD_682_i7 j := by decide +kernel
theorem required_exact_682_i7 : required_682_i7 =
    ((Finset.univ.biUnion childrenC_682_i7) ∪ commonEnvelope childrenD_682_i7).erase (6, 5) := by
  exact required_eq_combination childrenC_682_i7 childrenD_682_i7 (6, 5) required_682_i7
    (by decide +kernel) child_required_sub_682_i7 common_sub_682_i7 required_origin_682_i7
theorem envelope_origin_682_i7 : ∀ x ∈ envelope_682_i7,
    x = (6, 5) ∨ ∃ j, x ∈ childrenD_682_i7 j := by decide +kernel
theorem envelope_exact_682_i7 : envelope_682_i7 =
    insert (6, 5) (Finset.univ.biUnion childrenD_682_i7) := by
  exact envelope_eq_combination childrenD_682_i7 (6, 5) envelope_682_i7
    pivot_mem_682_i7 child_envelope_sub_682_i7 envelope_origin_682_i7
def checked_682_i7 : CheckedCard where
  required := required_682_i7
  envelope := envelope_682_i7
  height := height_682_i7
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_682_i7
def height_682_i1 : ℕ := 14
def childrenH_682_i1 : Fin 7 → ℕ := ![height_422, height_450, height_503, height_642, height_682_i2, height_680, height_682_i7]
theorem height_exact_682_i1 : height_682_i1 = 1 + Finset.univ.sup childrenH_682_i1 := by decide +kernel
theorem required_origin_682_i1 : ∀ x ∈ required_682_i1,
    (∃ j, x ∈ childrenC_682_i1 j) ∨ ∀ j, x ∈ childrenD_682_i1 j := by decide +kernel
theorem required_exact_682_i1 : required_682_i1 =
    ((Finset.univ.biUnion childrenC_682_i1) ∪ commonEnvelope childrenD_682_i1).erase (6, 4) := by
  exact required_eq_combination childrenC_682_i1 childrenD_682_i1 (6, 4) required_682_i1
    (by decide +kernel) child_required_sub_682_i1 common_sub_682_i1 required_origin_682_i1
theorem envelope_origin_682_i1 : ∀ x ∈ envelope_682_i1,
    x = (6, 4) ∨ ∃ j, x ∈ childrenD_682_i1 j := by decide +kernel
theorem envelope_exact_682_i1 : envelope_682_i1 =
    insert (6, 4) (Finset.univ.biUnion childrenD_682_i1) := by
  exact envelope_eq_combination childrenD_682_i1 (6, 4) envelope_682_i1
    pivot_mem_682_i1 child_envelope_sub_682_i1 envelope_origin_682_i1
def checked_682_i1 : CheckedCard where
  required := required_682_i1
  envelope := envelope_682_i1
  height := height_682_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_682_i1
def height_682 : ℕ := 15
def childrenH_682 : Fin 9 → ℕ := ![height_408, height_410, height_475, height_509, height_510, height_587, height_646, height_682_i0, height_682_i1]
theorem height_exact_682 : height_682 = 1 + Finset.univ.sup childrenH_682 := by decide +kernel
theorem required_origin_682 : ∀ x ∈ required_682,
    (∃ j, x ∈ childrenC_682 j) ∨ ∀ j, x ∈ childrenD_682 j := by decide +kernel
theorem required_exact_682 : required_682 =
    ((Finset.univ.biUnion childrenC_682) ∪ commonEnvelope childrenD_682).erase (4, 4) := by
  exact required_eq_combination childrenC_682 childrenD_682 (4, 4) required_682
    (by decide +kernel) child_required_sub_682 common_sub_682 required_origin_682
theorem envelope_origin_682 : ∀ x ∈ envelope_682,
    x = (4, 4) ∨ ∃ j, x ∈ childrenD_682 j := by decide +kernel
theorem envelope_exact_682 : envelope_682 =
    insert (4, 4) (Finset.univ.biUnion childrenD_682) := by
  exact envelope_eq_combination childrenD_682 (4, 4) envelope_682
    pivot_mem_682 child_envelope_sub_682 envelope_origin_682
def checked_682 : CheckedCard where
  required := required_682
  envelope := envelope_682
  height := height_682
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_682
end SnakyPrototype.Certificate21

end OAI
