import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height10Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height11Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height11Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height11Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height12Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height12Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height12Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height13Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height13Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height13Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height13Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height14Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height14Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height15Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height15Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height16Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height17Part01
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_684_i1 : Finset Cell := ⟨(([(6, 7), (7, 7), (7, 10), (8, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_684_i1 : Finset Cell := ⟨(([(4, 3), (4, 5), (5, 3), (5, 4), (5, 5), (5, 6), (5, 8), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (7, 2), (7, 3), (7, 4), (7, 5), (7, 7), (7, 9), (7, 10), (7, 11), (7, 12), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (8, 11), (8, 12), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (9, 10), (9, 11), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (10, 9), (10, 10), (10, 11), (10, 12), (11, 0), (11, 1), (11, 2), (11, 3), (11, 4), (11, 5), (11, 6), (11, 7), (11, 8), (12, 3), (12, 4), (12, 5), (12, 6), (12, 7), (12, 8), (13, 3), (13, 5), (13, 6), (13, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_684_i1 : Fin 6 → Finset Cell := ![(placed21 4 (6, 8) required_8), (placed21 4 (6, 10) required_115), (placed21 1 (5, 6) required_469), (placed21 4 (5, 12) required_470), (placed21 3 (4, 8) required_485), (placed21 4 (4, 12) required_489)]
def childrenD_684_i1 : Fin 6 → Finset Cell := ![(placed21 4 (6, 8) envelope_8), (placed21 4 (6, 10) envelope_115), (placed21 1 (5, 6) envelope_469), (placed21 4 (5, 12) envelope_470), (placed21 3 (4, 8) envelope_485), (placed21 4 (4, 12) envelope_489)]
theorem common_sub_684_i1 : commonEnvelope childrenD_684_i1 ⊆ insert (9, 7) required_684_i1 := by decide +kernel
theorem child_required_sub_684_i1 : ∀ j, childrenC_684_i1 j ⊆ insert (9, 7) required_684_i1 := by decide +kernel
theorem child_envelope_sub_684_i1 : ∀ j, childrenD_684_i1 j ⊆ envelope_684_i1 := by decide +kernel
theorem pivot_mem_684_i1 : (9, 7) ∈ envelope_684_i1 := by decide +kernel
theorem children_work_684_i1 : ∀ j, Template HasSnaky 12 (childrenC_684_i1 j) (childrenD_684_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_8 4 (6, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_115 4 (6, 10)).mono (by decide +kernel)
  · exact (placed21_template row_works_469 1 (5, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_470 4 (5, 12)).mono (by decide +kernel)
  · exact (placed21_template row_works_485 3 (4, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_489 4 (4, 12)).mono (by decide +kernel)
theorem row_works_684_i1 : Template HasSnaky 13 required_684_i1 envelope_684_i1 := by
  refine compose HasSnaky 12 childrenC_684_i1 childrenD_684_i1 children_work_684_i1 (9, 7)
    required_684_i1 envelope_684_i1 pivot_mem_684_i1 child_required_sub_684_i1 child_envelope_sub_684_i1 ?_
  intro b hb
  exact common_sub_684_i1 (mem_commonEnvelope childrenD_684_i1 b hb)
def required_684_i0 : Finset Cell := ⟨(([(6, 7), (7, 7), (7, 10)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_684_i0 : Finset Cell := ⟨(([(3, 8), (3, 10), (4, 3), (4, 5), (4, 6), (4, 8), (4, 9), (4, 10), (5, 3), (5, 4), (5, 5), (5, 6), (5, 8), (5, 9), (5, 10), (5, 11), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (7, 2), (7, 3), (7, 4), (7, 5), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (7, 12), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (8, 11), (8, 12), (8, 13), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (9, 10), (9, 11), (9, 12), (9, 13), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (10, 9), (10, 10), (10, 11), (10, 12), (10, 13), (11, 0), (11, 1), (11, 2), (11, 3), (11, 4), (11, 5), (11, 6), (11, 7), (11, 8), (11, 9), (11, 10), (11, 11), (12, 3), (12, 4), (12, 5), (12, 6), (12, 7), (12, 8), (12, 10), (13, 3), (13, 5), (13, 6), (13, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_684_i0 : Fin 6 → Finset Cell := ![(placed21 4 (5, 10) required_118), (placed21 3 (5, 10) required_355), (placed21 3 (5, 11) required_434), (placed21 1 (3, 6) required_468), required_684_i1, (placed21 7 (9, 11) required_491)]
def childrenD_684_i0 : Fin 6 → Finset Cell := ![(placed21 4 (5, 10) envelope_118), (placed21 3 (5, 10) envelope_355), (placed21 3 (5, 11) envelope_434), (placed21 1 (3, 6) envelope_468), envelope_684_i1, (placed21 7 (9, 11) envelope_491)]
theorem common_sub_684_i0 : commonEnvelope childrenD_684_i0 ⊆ insert (8, 7) required_684_i0 := by decide +kernel
theorem child_required_sub_684_i0 : ∀ j, childrenC_684_i0 j ⊆ insert (8, 7) required_684_i0 := by decide +kernel
theorem child_envelope_sub_684_i0 : ∀ j, childrenD_684_i0 j ⊆ envelope_684_i0 := by decide +kernel
theorem pivot_mem_684_i0 : (8, 7) ∈ envelope_684_i0 := by decide +kernel
theorem children_work_684_i0 : ∀ j, Template HasSnaky 13 (childrenC_684_i0 j) (childrenD_684_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_118 4 (5, 10)).mono (by decide +kernel)
  · exact (placed21_template row_works_355 3 (5, 10)).mono (by decide +kernel)
  · exact (placed21_template row_works_434 3 (5, 11)).mono (by decide +kernel)
  · exact (placed21_template row_works_468 1 (3, 6)).mono (by decide +kernel)
  · exact row_works_684_i1.mono (by decide +kernel)
  · exact (placed21_template row_works_491 7 (9, 11)).mono (by decide +kernel)
theorem row_works_684_i0 : Template HasSnaky 14 required_684_i0 envelope_684_i0 := by
  refine compose HasSnaky 13 childrenC_684_i0 childrenD_684_i0 children_work_684_i0 (8, 7)
    required_684_i0 envelope_684_i0 pivot_mem_684_i0 child_required_sub_684_i0 child_envelope_sub_684_i0 ?_
  intro b hb
  exact common_sub_684_i0 (mem_commonEnvelope childrenD_684_i0 b hb)
def required_684_i2 : Finset Cell := ⟨(([(6, 7), (7, 7), (7, 10)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_684_i2 : Finset Cell := ⟨(([(2, 8), (2, 10), (3, 8), (3, 9), (3, 10), (3, 11), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (4, 13), (4, 14), (5, 8), (5, 9), (5, 10), (5, 11), (5, 12), (5, 13), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (6, 12), (6, 13), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (7, 12), (8, 9), (8, 10), (8, 11), (8, 12), (9, 8), (9, 9), (9, 10), (10, 8), (10, 9), (10, 10), (11, 8), (11, 9), (11, 10), (12, 10)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_684_i2 : Fin 6 → Finset Cell := ![(placed21 0 (6, 6) required_50), (placed21 0 (6, 6) required_97), (placed21 2 (7, 6) required_98), (placed21 6 (8, 11) required_454), (placed21 5 (8, 7) required_455), (placed21 1 (2, 6) required_624)]
def childrenD_684_i2 : Fin 6 → Finset Cell := ![(placed21 0 (6, 6) envelope_50), (placed21 0 (6, 6) envelope_97), (placed21 2 (7, 6) envelope_98), (placed21 6 (8, 11) envelope_454), (placed21 5 (8, 7) envelope_455), (placed21 1 (2, 6) envelope_624)]
theorem common_sub_684_i2 : commonEnvelope childrenD_684_i2 ⊆ insert (7, 9) required_684_i2 := by decide +kernel
theorem child_required_sub_684_i2 : ∀ j, childrenC_684_i2 j ⊆ insert (7, 9) required_684_i2 := by decide +kernel
theorem child_envelope_sub_684_i2 : ∀ j, childrenD_684_i2 j ⊆ envelope_684_i2 := by decide +kernel
theorem pivot_mem_684_i2 : (7, 9) ∈ envelope_684_i2 := by decide +kernel
theorem children_work_684_i2 : ∀ j, Template HasSnaky 11 (childrenC_684_i2 j) (childrenD_684_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_50 0 (6, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_97 0 (6, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_98 2 (7, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_454 6 (8, 11)).mono (by decide +kernel)
  · exact (placed21_template row_works_455 5 (8, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_624 1 (2, 6)).mono (by decide +kernel)
theorem row_works_684_i2 : Template HasSnaky 12 required_684_i2 envelope_684_i2 := by
  refine compose HasSnaky 11 childrenC_684_i2 childrenD_684_i2 children_work_684_i2 (7, 9)
    required_684_i2 envelope_684_i2 pivot_mem_684_i2 child_required_sub_684_i2 child_envelope_sub_684_i2 ?_
  intro b hb
  exact common_sub_684_i2 (mem_commonEnvelope childrenD_684_i2 b hb)
def required_684_i3 : Finset Cell := ⟨(([(7, 10)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_684_i3 : Finset Cell := ⟨(([(3, 10), (3, 11), (3, 12), (3, 13), (4, 9), (4, 10), (4, 11), (4, 12), (4, 13), (4, 14), (5, 9), (5, 10), (5, 11), (5, 12), (5, 13), (5, 14), (5, 15), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (6, 12), (6, 13), (6, 14), (6, 15), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (7, 12), (7, 13), (7, 14), (7, 15), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (8, 11), (8, 12), (8, 13), (8, 14), (8, 15), (9, 6), (9, 7), (9, 8), (9, 9), (9, 10), (9, 11), (9, 12), (9, 13), (9, 14), (9, 15), (10, 6), (10, 7), (10, 8), (10, 9), (10, 10), (10, 11), (10, 12), (10, 13), (10, 14), (10, 15), (11, 7), (11, 8), (11, 9), (11, 10), (11, 11), (11, 12), (11, 13), (11, 14), (12, 7), (12, 8), (12, 9), (12, 10), (12, 11), (12, 12), (12, 13), (12, 14), (13, 10), (13, 11), (13, 12), (13, 14), (14, 10)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_684_i3 : Fin 13 → Finset Cell := ![(placed21 4 (4, 14) required_174), (placed21 0 (5, 7) required_475), (placed21 2 (9, 7) required_475), (placed21 0 (5, 7) required_483), (placed21 1 (4, 8) required_508), (placed21 5 (10, 8) required_508), (placed21 4 (4, 14) required_566), (placed21 0 (5, 7) required_587), (placed21 2 (9, 7) required_587), (placed21 4 (5, 15) required_635), (placed21 4 (3, 15) required_644), (placed21 4 (3, 15) required_645), (placed21 4 (3, 15) required_647)]
def childrenD_684_i3 : Fin 13 → Finset Cell := ![(placed21 4 (4, 14) envelope_174), (placed21 0 (5, 7) envelope_475), (placed21 2 (9, 7) envelope_475), (placed21 0 (5, 7) envelope_483), (placed21 1 (4, 8) envelope_508), (placed21 5 (10, 8) envelope_508), (placed21 4 (4, 14) envelope_566), (placed21 0 (5, 7) envelope_587), (placed21 2 (9, 7) envelope_587), (placed21 4 (5, 15) envelope_635), (placed21 4 (3, 15) envelope_644), (placed21 4 (3, 15) envelope_645), (placed21 4 (3, 15) envelope_647)]
theorem common_sub_684_i3 : commonEnvelope childrenD_684_i3 ⊆ insert (7, 11) required_684_i3 := by decide +kernel
theorem child_required_sub_684_i3 : ∀ j, childrenC_684_i3 j ⊆ insert (7, 11) required_684_i3 := by decide +kernel
theorem child_envelope_sub_684_i3 : ∀ j, childrenD_684_i3 j ⊆ envelope_684_i3 := by decide +kernel
theorem pivot_mem_684_i3 : (7, 11) ∈ envelope_684_i3 := by decide +kernel
theorem children_work_684_i3 : ∀ j, Template HasSnaky 14 (childrenC_684_i3 j) (childrenD_684_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_174 4 (4, 14)).mono (by decide +kernel)
  · exact (placed21_template row_works_475 0 (5, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_475 2 (9, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_483 0 (5, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_508 1 (4, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_508 5 (10, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_566 4 (4, 14)).mono (by decide +kernel)
  · exact (placed21_template row_works_587 0 (5, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_587 2 (9, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_635 4 (5, 15)).mono (by decide +kernel)
  · exact (placed21_template row_works_644 4 (3, 15)).mono (by decide +kernel)
  · exact (placed21_template row_works_645 4 (3, 15)).mono (by decide +kernel)
  · exact (placed21_template row_works_647 4 (3, 15)).mono (by decide +kernel)
theorem row_works_684_i3 : Template HasSnaky 15 required_684_i3 envelope_684_i3 := by
  refine compose HasSnaky 14 childrenC_684_i3 childrenD_684_i3 children_work_684_i3 (7, 11)
    required_684_i3 envelope_684_i3 pivot_mem_684_i3 child_required_sub_684_i3 child_envelope_sub_684_i3 ?_
  intro b hb
  exact common_sub_684_i3 (mem_commonEnvelope childrenD_684_i3 b hb)
def required_684_i5 : Finset Cell := ⟨(([(6, 7), (7, 7), (7, 10), (8, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_684_i5 : Finset Cell := ⟨(([(5, 6), (5, 8), (5, 9), (5, 10), (5, 11), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, 7), (7, 9), (7, 10), (7, 11), (8, 7), (9, 6), (9, 7), (9, 8), (10, 6), (10, 7), (10, 8), (11, 6), (11, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_684_i5 : Fin 2 → Finset Cell := ![(placed21 0 (6, 6) required_8), (placed21 2 (9, 6) required_313)]
def childrenD_684_i5 : Fin 2 → Finset Cell := ![(placed21 0 (6, 6) envelope_8), (placed21 2 (9, 6) envelope_313)]
theorem common_sub_684_i5 : commonEnvelope childrenD_684_i5 ⊆ insert (9, 7) required_684_i5 := by decide +kernel
theorem child_required_sub_684_i5 : ∀ j, childrenC_684_i5 j ⊆ insert (9, 7) required_684_i5 := by decide +kernel
theorem child_envelope_sub_684_i5 : ∀ j, childrenD_684_i5 j ⊆ envelope_684_i5 := by decide +kernel
theorem pivot_mem_684_i5 : (9, 7) ∈ envelope_684_i5 := by decide +kernel
theorem children_work_684_i5 : ∀ j, Template HasSnaky 6 (childrenC_684_i5 j) (childrenD_684_i5 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_8 0 (6, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_313 2 (9, 6)).mono (by decide +kernel)
theorem row_works_684_i5 : Template HasSnaky 7 required_684_i5 envelope_684_i5 := by
  refine compose HasSnaky 6 childrenC_684_i5 childrenD_684_i5 children_work_684_i5 (9, 7)
    required_684_i5 envelope_684_i5 pivot_mem_684_i5 child_required_sub_684_i5 child_envelope_sub_684_i5 ?_
  intro b hb
  exact common_sub_684_i5 (mem_commonEnvelope childrenD_684_i5 b hb)
def required_684_i4 : Finset Cell := ⟨(([(6, 7), (7, 7), (7, 10)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_684_i4 : Finset Cell := ⟨(([(2, 10), (3, 8), (3, 9), (3, 10), (3, 11), (4, 6), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (4, 13), (5, 3), (5, 4), (5, 5), (5, 6), (5, 8), (5, 9), (5, 10), (5, 11), (5, 12), (5, 13), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (6, 12), (6, 13), (7, 3), (7, 4), (7, 5), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (7, 12), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (9, 10), (9, 11), (10, 6), (10, 7), (10, 8), (10, 9), (10, 10), (10, 11), (11, 6), (11, 7), (11, 8), (11, 10), (12, 6), (12, 7), (12, 8), (13, 6), (13, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_684_i4 : Fin 5 → Finset Cell := ![(placed21 0 (5, 4) required_257), required_684_i5, (placed21 3 (5, 11) required_434), (placed21 5 (11, 6) required_468), (placed21 7 (9, 11) required_491)]
def childrenD_684_i4 : Fin 5 → Finset Cell := ![(placed21 0 (5, 4) envelope_257), envelope_684_i5, (placed21 3 (5, 11) envelope_434), (placed21 5 (11, 6) envelope_468), (placed21 7 (9, 11) envelope_491)]
theorem common_sub_684_i4 : commonEnvelope childrenD_684_i4 ⊆ insert (8, 7) required_684_i4 := by decide +kernel
theorem child_required_sub_684_i4 : ∀ j, childrenC_684_i4 j ⊆ insert (8, 7) required_684_i4 := by decide +kernel
theorem child_envelope_sub_684_i4 : ∀ j, childrenD_684_i4 j ⊆ envelope_684_i4 := by decide +kernel
theorem pivot_mem_684_i4 : (8, 7) ∈ envelope_684_i4 := by decide +kernel
theorem children_work_684_i4 : ∀ j, Template HasSnaky 11 (childrenC_684_i4 j) (childrenD_684_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_257 0 (5, 4)).mono (by decide +kernel)
  · exact row_works_684_i5.mono (by decide +kernel)
  · exact (placed21_template row_works_434 3 (5, 11)).mono (by decide +kernel)
  · exact (placed21_template row_works_468 5 (11, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_491 7 (9, 11)).mono (by decide +kernel)
theorem row_works_684_i4 : Template HasSnaky 12 required_684_i4 envelope_684_i4 := by
  refine compose HasSnaky 11 childrenC_684_i4 childrenD_684_i4 children_work_684_i4 (8, 7)
    required_684_i4 envelope_684_i4 pivot_mem_684_i4 child_required_sub_684_i4 child_envelope_sub_684_i4 ?_
  intro b hb
  exact common_sub_684_i4 (mem_commonEnvelope childrenD_684_i4 b hb)
def required_684 : Finset Cell := ⟨(([(6, 7), (7, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_684 : Finset Cell := ⟨(([(0, 9), (0, 11), (0, 13), (1, 9), (1, 10), (1, 11), (1, 12), (1, 13), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (2, 13), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (3, 13), (3, 14), (4, 3), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (4, 13), (4, 14), (4, 15), (5, 3), (5, 4), (5, 5), (5, 6), (5, 8), (5, 9), (5, 10), (5, 11), (5, 12), (5, 13), (5, 14), (5, 15), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (6, 12), (6, 13), (6, 14), (6, 15), (7, 2), (7, 3), (7, 4), (7, 5), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (7, 12), (7, 13), (7, 14), (7, 15), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (8, 11), (8, 12), (8, 13), (8, 14), (8, 15), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (9, 10), (9, 11), (9, 12), (9, 13), (9, 14), (9, 15), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (10, 9), (10, 10), (10, 11), (10, 12), (10, 13), (10, 14), (10, 15), (11, 0), (11, 1), (11, 2), (11, 3), (11, 4), (11, 5), (11, 6), (11, 7), (11, 8), (11, 9), (11, 10), (11, 11), (11, 12), (11, 13), (11, 14), (12, 1), (12, 2), (12, 3), (12, 4), (12, 5), (12, 6), (12, 7), (12, 8), (12, 9), (12, 10), (12, 11), (12, 12), (12, 13), (12, 14), (13, 3), (13, 4), (13, 5), (13, 6), (13, 7), (13, 8), (13, 9), (13, 10), (13, 11), (13, 12), (13, 14), (14, 4), (14, 5), (14, 6), (14, 7), (14, 8), (14, 9), (14, 10), (15, 5), (15, 7), (15, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_684 : Fin 15 → Finset Cell := ![required_684_i0, (placed21 3 (0, 15) required_623), required_684_i2, (placed21 5 (9, 6) required_625), (placed21 3 (0, 14) required_630), (placed21 5 (10, 6) required_632), (placed21 5 (11, 6) required_636), (placed21 1 (3, 6) required_639), required_684_i3, (placed21 1 (1, 5) required_656), (placed21 1 (4, 5) required_657), (placed21 1 (2, 4) required_670), (placed21 5 (12, 3) required_675), (placed21 1 (2, 6) required_683), required_684_i4]
def childrenD_684 : Fin 15 → Finset Cell := ![envelope_684_i0, (placed21 3 (0, 15) envelope_623), envelope_684_i2, (placed21 5 (9, 6) envelope_625), (placed21 3 (0, 14) envelope_630), (placed21 5 (10, 6) envelope_632), (placed21 5 (11, 6) envelope_636), (placed21 1 (3, 6) envelope_639), envelope_684_i3, (placed21 1 (1, 5) envelope_656), (placed21 1 (4, 5) envelope_657), (placed21 1 (2, 4) envelope_670), (placed21 5 (12, 3) envelope_675), (placed21 1 (2, 6) envelope_683), envelope_684_i4]
theorem common_sub_684 : commonEnvelope childrenD_684 ⊆ insert (7, 10) required_684 := by decide +kernel
theorem child_required_sub_684 : ∀ j, childrenC_684 j ⊆ insert (7, 10) required_684 := by decide +kernel
theorem child_envelope_sub_684 : ∀ j, childrenD_684 j ⊆ envelope_684 := by decide +kernel
theorem pivot_mem_684 : (7, 10) ∈ envelope_684 := by decide +kernel
theorem children_work_684 : ∀ j, Template HasSnaky 17 (childrenC_684 j) (childrenD_684 j) := by
  intro j
  fin_cases j
  · exact row_works_684_i0.mono (by decide +kernel)
  · exact (placed21_template row_works_623 3 (0, 15)).mono (by decide +kernel)
  · exact row_works_684_i2.mono (by decide +kernel)
  · exact (placed21_template row_works_625 5 (9, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_630 3 (0, 14)).mono (by decide +kernel)
  · exact (placed21_template row_works_632 5 (10, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_636 5 (11, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_639 1 (3, 6)).mono (by decide +kernel)
  · exact row_works_684_i3.mono (by decide +kernel)
  · exact (placed21_template row_works_656 1 (1, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_657 1 (4, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_670 1 (2, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_675 5 (12, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_683 1 (2, 6)).mono (by decide +kernel)
  · exact row_works_684_i4.mono (by decide +kernel)
theorem row_works_684 : Template HasSnaky 18 required_684 envelope_684 := by
  refine compose HasSnaky 17 childrenC_684 childrenD_684 children_work_684 (7, 10)
    required_684 envelope_684 pivot_mem_684 child_required_sub_684 child_envelope_sub_684 ?_
  intro b hb
  exact common_sub_684 (mem_commonEnvelope childrenD_684 b hb)
def required_691_i0 : Finset Cell := ⟨(([(3, 3), (3, 4), (3, 5), (3, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_691_i0 : Finset Cell := ⟨(([(1, 4), (1, 6), (2, 3), (2, 4), (2, 6), (2, 7), (2, 8), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 0), (4, 1), (4, 2), (4, 4), (4, 5), (4, 6), (5, 5), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_691_i0 : Fin 3 → Finset Cell := ![(placed21 4 (3, 6) required_27), (placed21 3 (1, 7) required_277), (placed21 1 (1, 3) required_278)]
def childrenD_691_i0 : Fin 3 → Finset Cell := ![(placed21 4 (3, 6) envelope_27), (placed21 3 (1, 7) envelope_277), (placed21 1 (1, 3) envelope_278)]
theorem common_sub_691_i0 : commonEnvelope childrenD_691_i0 ⊆ insert (4, 5) required_691_i0 := by decide +kernel
theorem child_required_sub_691_i0 : ∀ j, childrenC_691_i0 j ⊆ insert (4, 5) required_691_i0 := by decide +kernel
theorem child_envelope_sub_691_i0 : ∀ j, childrenD_691_i0 j ⊆ envelope_691_i0 := by decide +kernel
theorem pivot_mem_691_i0 : (4, 5) ∈ envelope_691_i0 := by decide +kernel
theorem children_work_691_i0 : ∀ j, Template HasSnaky 5 (childrenC_691_i0 j) (childrenD_691_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_27 4 (3, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_277 3 (1, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_278 1 (1, 3)).mono (by decide +kernel)
theorem row_works_691_i0 : Template HasSnaky 6 required_691_i0 envelope_691_i0 := by
  refine compose HasSnaky 5 childrenC_691_i0 childrenD_691_i0 children_work_691_i0 (4, 5)
    required_691_i0 envelope_691_i0 pivot_mem_691_i0 child_required_sub_691_i0 child_envelope_sub_691_i0 ?_
  intro b hb
  exact common_sub_691_i0 (mem_commonEnvelope childrenD_691_i0 b hb)
def required_691_i5 : Finset Cell := ⟨(([(3, 5), (4, 5), (4, 6), (6, 5), (6, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_691_i5 : Finset Cell := ⟨(([(3, 5), (3, 6), (4, 5), (4, 6), (5, 2), (5, 3), (5, 4), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, 2), (7, 3), (7, 4), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, 7), (9, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_691_i5 : Fin 2 → Finset Cell := ![(placed21 6 (7, 6) required_0), (placed21 0 (3, 2) required_317)]
def childrenD_691_i5 : Fin 2 → Finset Cell := ![(placed21 6 (7, 6) envelope_0), (placed21 0 (3, 2) envelope_317)]
theorem common_sub_691_i5 : commonEnvelope childrenD_691_i5 ⊆ insert (5, 6) required_691_i5 := by decide +kernel
theorem child_required_sub_691_i5 : ∀ j, childrenC_691_i5 j ⊆ insert (5, 6) required_691_i5 := by decide +kernel
theorem child_envelope_sub_691_i5 : ∀ j, childrenD_691_i5 j ⊆ envelope_691_i5 := by decide +kernel
theorem pivot_mem_691_i5 : (5, 6) ∈ envelope_691_i5 := by decide +kernel
theorem children_work_691_i5 : ∀ j, Template HasSnaky 7 (childrenC_691_i5 j) (childrenD_691_i5 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 6 (7, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_317 0 (3, 2)).mono (by decide +kernel)
theorem row_works_691_i5 : Template HasSnaky 8 required_691_i5 envelope_691_i5 := by
  refine compose HasSnaky 7 childrenC_691_i5 childrenD_691_i5 children_work_691_i5 (5, 6)
    required_691_i5 envelope_691_i5 pivot_mem_691_i5 child_required_sub_691_i5 child_envelope_sub_691_i5 ?_
  intro b hb
  exact common_sub_691_i5 (mem_commonEnvelope childrenD_691_i5 b hb)
def required_691_i4 : Finset Cell := ⟨(([(3, 5), (3, 6), (4, 5), (4, 6), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_691_i4 : Finset Cell := ⟨(([(3, 5), (3, 6), (4, 5), (4, 6), (5, 2), (5, 3), (5, 4), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (10, 3), (10, 4), (10, 5), (10, 7), (10, 9), (11, 3), (11, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_691_i4 : Fin 4 → Finset Cell := ![(placed21 3 (3, 6) required_30), (placed21 4 (3, 9) required_59), (placed21 0 (5, 2) required_462), required_691_i5]
def childrenD_691_i4 : Fin 4 → Finset Cell := ![(placed21 3 (3, 6) envelope_30), (placed21 4 (3, 9) envelope_59), (placed21 0 (5, 2) envelope_462), envelope_691_i5]
theorem common_sub_691_i4 : commonEnvelope childrenD_691_i4 ⊆ insert (6, 6) required_691_i4 := by decide +kernel
theorem child_required_sub_691_i4 : ∀ j, childrenC_691_i4 j ⊆ insert (6, 6) required_691_i4 := by decide +kernel
theorem child_envelope_sub_691_i4 : ∀ j, childrenD_691_i4 j ⊆ envelope_691_i4 := by decide +kernel
theorem pivot_mem_691_i4 : (6, 6) ∈ envelope_691_i4 := by decide +kernel
theorem children_work_691_i4 : ∀ j, Template HasSnaky 13 (childrenC_691_i4 j) (childrenD_691_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_30 3 (3, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_59 4 (3, 9)).mono (by decide +kernel)
  · exact (placed21_template row_works_462 0 (5, 2)).mono (by decide +kernel)
  · exact row_works_691_i5.mono (by decide +kernel)
theorem row_works_691_i4 : Template HasSnaky 14 required_691_i4 envelope_691_i4 := by
  refine compose HasSnaky 13 childrenC_691_i4 childrenD_691_i4 children_work_691_i4 (6, 6)
    required_691_i4 envelope_691_i4 pivot_mem_691_i4 child_required_sub_691_i4 child_envelope_sub_691_i4 ?_
  intro b hb
  exact common_sub_691_i4 (mem_commonEnvelope childrenD_691_i4 b hb)
def required_691_i3 : Finset Cell := ⟨(([(3, 4), (3, 5), (3, 6), (4, 5), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_691_i3 : Finset Cell := ⟨(([(2, 4), (3, 4), (3, 5), (3, 6), (4, 5), (4, 6), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (10, 3), (10, 4), (10, 5), (10, 7), (10, 9), (11, 3), (11, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_691_i3 : Fin 3 → Finset Cell := ![(placed21 3 (2, 6) required_102), (placed21 0 (2, 3) required_400), required_691_i4]
def childrenD_691_i3 : Fin 3 → Finset Cell := ![(placed21 3 (2, 6) envelope_102), (placed21 0 (2, 3) envelope_400), envelope_691_i4]
theorem common_sub_691_i3 : commonEnvelope childrenD_691_i3 ⊆ insert (6, 5) required_691_i3 := by decide +kernel
theorem child_required_sub_691_i3 : ∀ j, childrenC_691_i3 j ⊆ insert (6, 5) required_691_i3 := by decide +kernel
theorem child_envelope_sub_691_i3 : ∀ j, childrenD_691_i3 j ⊆ envelope_691_i3 := by decide +kernel
theorem pivot_mem_691_i3 : (6, 5) ∈ envelope_691_i3 := by decide +kernel
theorem children_work_691_i3 : ∀ j, Template HasSnaky 14 (childrenC_691_i3 j) (childrenD_691_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_102 3 (2, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_400 0 (2, 3)).mono (by decide +kernel)
  · exact row_works_691_i4.mono (by decide +kernel)
theorem row_works_691_i3 : Template HasSnaky 15 required_691_i3 envelope_691_i3 := by
  refine compose HasSnaky 14 childrenC_691_i3 childrenD_691_i3 children_work_691_i3 (6, 5)
    required_691_i3 envelope_691_i3 pivot_mem_691_i3 child_required_sub_691_i3 child_envelope_sub_691_i3 ?_
  intro b hb
  exact common_sub_691_i3 (mem_commonEnvelope childrenD_691_i3 b hb)
def required_691_i2 : Finset Cell := ⟨(([(3, 3), (3, 4), (3, 5), (3, 6), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_691_i2 : Finset Cell := ⟨(([(2, 4), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 5), (4, 6), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (10, 3), (10, 4), (10, 5), (10, 7), (10, 9), (11, 3), (11, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_691_i2 : Fin 2 → Finset Cell := ![(placed21 1 (3, 2) required_0), required_691_i3]
def childrenD_691_i2 : Fin 2 → Finset Cell := ![(placed21 1 (3, 2) envelope_0), envelope_691_i3]
theorem common_sub_691_i2 : commonEnvelope childrenD_691_i2 ⊆ insert (4, 5) required_691_i2 := by decide +kernel
theorem child_required_sub_691_i2 : ∀ j, childrenC_691_i2 j ⊆ insert (4, 5) required_691_i2 := by decide +kernel
theorem child_envelope_sub_691_i2 : ∀ j, childrenD_691_i2 j ⊆ envelope_691_i2 := by decide +kernel
theorem pivot_mem_691_i2 : (4, 5) ∈ envelope_691_i2 := by decide +kernel
theorem children_work_691_i2 : ∀ j, Template HasSnaky 15 (childrenC_691_i2 j) (childrenD_691_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 1 (3, 2)).mono (by decide +kernel)
  · exact row_works_691_i3.mono (by decide +kernel)
theorem row_works_691_i2 : Template HasSnaky 16 required_691_i2 envelope_691_i2 := by
  refine compose HasSnaky 15 childrenC_691_i2 childrenD_691_i2 children_work_691_i2 (4, 5)
    required_691_i2 envelope_691_i2 pivot_mem_691_i2 child_required_sub_691_i2 child_envelope_sub_691_i2 ?_
  intro b hb
  exact common_sub_691_i2 (mem_commonEnvelope childrenD_691_i2 b hb)
def required_691_i1 : Finset Cell := ⟨(([(3, 3), (3, 4), (3, 5), (3, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_691_i1 : Finset Cell := ⟨(([(2, 4), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 5), (4, 6), (4, 7), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (10, 3), (10, 4), (10, 5), (10, 7), (10, 9), (11, 3), (11, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_691_i1 : Fin 2 → Finset Cell := ![(placed21 1 (3, 3) required_5), required_691_i2]
def childrenD_691_i1 : Fin 2 → Finset Cell := ![(placed21 1 (3, 3) envelope_5), envelope_691_i2]
theorem common_sub_691_i1 : commonEnvelope childrenD_691_i1 ⊆ insert (4, 6) required_691_i1 := by decide +kernel
theorem child_required_sub_691_i1 : ∀ j, childrenC_691_i1 j ⊆ insert (4, 6) required_691_i1 := by decide +kernel
theorem child_envelope_sub_691_i1 : ∀ j, childrenD_691_i1 j ⊆ envelope_691_i1 := by decide +kernel
theorem pivot_mem_691_i1 : (4, 6) ∈ envelope_691_i1 := by decide +kernel
theorem children_work_691_i1 : ∀ j, Template HasSnaky 16 (childrenC_691_i1 j) (childrenD_691_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 1 (3, 3)).mono (by decide +kernel)
  · exact row_works_691_i2.mono (by decide +kernel)
theorem row_works_691_i1 : Template HasSnaky 17 required_691_i1 envelope_691_i1 := by
  refine compose HasSnaky 16 childrenC_691_i1 childrenD_691_i1 children_work_691_i1 (4, 6)
    required_691_i1 envelope_691_i1 pivot_mem_691_i1 child_required_sub_691_i1 child_envelope_sub_691_i1 ?_
  intro b hb
  exact common_sub_691_i1 (mem_commonEnvelope childrenD_691_i1 b hb)
def required_691_i10 : Finset Cell := ⟨(([(3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (6, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_691_i10 : Finset Cell := ⟨(([(2, 6), (2, 7), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 7), (4, 8), (5, 7), (6, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_691_i10 : Fin 2 → Finset Cell := ![(placed21 5 (3, 3) required_5), (placed21 1 (2, 4) required_35)]
def childrenD_691_i10 : Fin 2 → Finset Cell := ![(placed21 5 (3, 3) envelope_5), (placed21 1 (2, 4) envelope_35)]
theorem common_sub_691_i10 : commonEnvelope childrenD_691_i10 ⊆ insert (2, 6) required_691_i10 := by decide +kernel
theorem child_required_sub_691_i10 : ∀ j, childrenC_691_i10 j ⊆ insert (2, 6) required_691_i10 := by decide +kernel
theorem child_envelope_sub_691_i10 : ∀ j, childrenD_691_i10 j ⊆ envelope_691_i10 := by decide +kernel
theorem pivot_mem_691_i10 : (2, 6) ∈ envelope_691_i10 := by decide +kernel
theorem children_work_691_i10 : ∀ j, Template HasSnaky 2 (childrenC_691_i10 j) (childrenD_691_i10 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 5 (3, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_35 1 (2, 4)).mono (by decide +kernel)
theorem row_works_691_i10 : Template HasSnaky 3 required_691_i10 envelope_691_i10 := by
  refine compose HasSnaky 2 childrenC_691_i10 childrenD_691_i10 children_work_691_i10 (2, 6)
    required_691_i10 envelope_691_i10 pivot_mem_691_i10 child_required_sub_691_i10 child_envelope_sub_691_i10 ?_
  intro b hb
  exact common_sub_691_i10 (mem_commonEnvelope childrenD_691_i10 b hb)
def required_691_i9 : Finset Cell := ⟨(([(3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_691_i9 : Finset Cell := ⟨(([(2, 6), (2, 7), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 7), (4, 8), (4, 9), (5, 2), (5, 3), (5, 4), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (9, 6), (9, 7), (9, 8), (9, 9), (10, 6), (10, 7), (10, 8), (10, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_691_i9 : Fin 3 → Finset Cell := ![required_691_i10, (placed21 4 (5, 10) required_460), (placed21 0 (2, 2) required_488)]
def childrenD_691_i9 : Fin 3 → Finset Cell := ![envelope_691_i10, (placed21 4 (5, 10) envelope_460), (placed21 0 (2, 2) envelope_488)]
theorem common_sub_691_i9 : commonEnvelope childrenD_691_i9 ⊆ insert (6, 7) required_691_i9 := by decide +kernel
theorem child_required_sub_691_i9 : ∀ j, childrenC_691_i9 j ⊆ insert (6, 7) required_691_i9 := by decide +kernel
theorem child_envelope_sub_691_i9 : ∀ j, childrenD_691_i9 j ⊆ envelope_691_i9 := by decide +kernel
theorem pivot_mem_691_i9 : (6, 7) ∈ envelope_691_i9 := by decide +kernel
theorem children_work_691_i9 : ∀ j, Template HasSnaky 10 (childrenC_691_i9 j) (childrenD_691_i9 j) := by
  intro j
  fin_cases j
  · exact row_works_691_i10.mono (by decide +kernel)
  · exact (placed21_template row_works_460 4 (5, 10)).mono (by decide +kernel)
  · exact (placed21_template row_works_488 0 (2, 2)).mono (by decide +kernel)
theorem row_works_691_i9 : Template HasSnaky 11 required_691_i9 envelope_691_i9 := by
  refine compose HasSnaky 10 childrenC_691_i9 childrenD_691_i9 children_work_691_i9 (6, 7)
    required_691_i9 envelope_691_i9 pivot_mem_691_i9 child_required_sub_691_i9 child_envelope_sub_691_i9 ?_
  intro b hb
  exact common_sub_691_i9 (mem_commonEnvelope childrenD_691_i9 b hb)
def required_691_i8 : Finset Cell := ⟨(([(3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_691_i8 : Finset Cell := ⟨(([(2, 4), (2, 6), (2, 7), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 5), (4, 7), (4, 8), (4, 9), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (9, 6), (9, 7), (9, 8), (9, 9), (10, 6), (10, 7), (10, 8), (10, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_691_i8 : Fin 3 → Finset Cell := ![(placed21 1 (2, 4) required_39), (placed21 1 (2, 4) required_80), required_691_i9]
def childrenD_691_i8 : Fin 3 → Finset Cell := ![(placed21 1 (2, 4) envelope_39), (placed21 1 (2, 4) envelope_80), envelope_691_i9]
theorem common_sub_691_i8 : commonEnvelope childrenD_691_i8 ⊆ insert (6, 5) required_691_i8 := by decide +kernel
theorem child_required_sub_691_i8 : ∀ j, childrenC_691_i8 j ⊆ insert (6, 5) required_691_i8 := by decide +kernel
theorem child_envelope_sub_691_i8 : ∀ j, childrenD_691_i8 j ⊆ envelope_691_i8 := by decide +kernel
theorem pivot_mem_691_i8 : (6, 5) ∈ envelope_691_i8 := by decide +kernel
theorem children_work_691_i8 : ∀ j, Template HasSnaky 11 (childrenC_691_i8 j) (childrenD_691_i8 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_39 1 (2, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_80 1 (2, 4)).mono (by decide +kernel)
  · exact row_works_691_i9.mono (by decide +kernel)
theorem row_works_691_i8 : Template HasSnaky 12 required_691_i8 envelope_691_i8 := by
  refine compose HasSnaky 11 childrenC_691_i8 childrenD_691_i8 children_work_691_i8 (6, 5)
    required_691_i8 envelope_691_i8 pivot_mem_691_i8 child_required_sub_691_i8 child_envelope_sub_691_i8 ?_
  intro b hb
  exact common_sub_691_i8 (mem_commonEnvelope childrenD_691_i8 b hb)
def required_691_i7 : Finset Cell := ⟨(([(3, 3), (3, 4), (3, 5), (3, 6), (3, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_691_i7 : Finset Cell := ⟨(([(0, 4), (1, 4), (2, 3), (2, 4), (2, 6), (2, 7), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 4), (4, 5), (4, 7), (4, 8), (4, 9), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (9, 6), (9, 7), (9, 8), (9, 9), (10, 6), (10, 7), (10, 8), (10, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_691_i7 : Fin 3 → Finset Cell := ![(placed21 0 (3, 4) required_21), (placed21 7 (6, 7) required_56), required_691_i8]
def childrenD_691_i7 : Fin 3 → Finset Cell := ![(placed21 0 (3, 4) envelope_21), (placed21 7 (6, 7) envelope_56), envelope_691_i8]
theorem common_sub_691_i7 : commonEnvelope childrenD_691_i7 ⊆ insert (4, 5) required_691_i7 := by decide +kernel
theorem child_required_sub_691_i7 : ∀ j, childrenC_691_i7 j ⊆ insert (4, 5) required_691_i7 := by decide +kernel
theorem child_envelope_sub_691_i7 : ∀ j, childrenD_691_i7 j ⊆ envelope_691_i7 := by decide +kernel
theorem pivot_mem_691_i7 : (4, 5) ∈ envelope_691_i7 := by decide +kernel
theorem children_work_691_i7 : ∀ j, Template HasSnaky 12 (childrenC_691_i7 j) (childrenD_691_i7 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_21 0 (3, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_56 7 (6, 7)).mono (by decide +kernel)
  · exact row_works_691_i8.mono (by decide +kernel)
theorem row_works_691_i7 : Template HasSnaky 13 required_691_i7 envelope_691_i7 := by
  refine compose HasSnaky 12 childrenC_691_i7 childrenD_691_i7 children_work_691_i7 (4, 5)
    required_691_i7 envelope_691_i7 pivot_mem_691_i7 child_required_sub_691_i7 child_envelope_sub_691_i7 ?_
  intro b hb
  exact common_sub_691_i7 (mem_commonEnvelope childrenD_691_i7 b hb)
def required_691_i6 : Finset Cell := ⟨(([(3, 3), (3, 4), (3, 5), (3, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_691_i6 : Finset Cell := ⟨(([(0, 4), (1, 4), (2, 3), (2, 4), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 4), (4, 5), (4, 7), (4, 8), (4, 9), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (9, 6), (9, 7), (9, 8), (9, 9), (10, 6), (10, 7), (10, 8), (10, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_691_i6 : Fin 4 → Finset Cell := ![(placed21 2 (3, 3) required_6), (placed21 1 (2, 4) required_8), (placed21 1 (0, 2) required_690), required_691_i7]
def childrenD_691_i6 : Fin 4 → Finset Cell := ![(placed21 2 (3, 3) envelope_6), (placed21 1 (2, 4) envelope_8), (placed21 1 (0, 2) envelope_690), envelope_691_i7]
theorem common_sub_691_i6 : commonEnvelope childrenD_691_i6 ⊆ insert (3, 7) required_691_i6 := by decide +kernel
theorem child_required_sub_691_i6 : ∀ j, childrenC_691_i6 j ⊆ insert (3, 7) required_691_i6 := by decide +kernel
theorem child_envelope_sub_691_i6 : ∀ j, childrenD_691_i6 j ⊆ envelope_691_i6 := by decide +kernel
theorem pivot_mem_691_i6 : (3, 7) ∈ envelope_691_i6 := by decide +kernel
theorem children_work_691_i6 : ∀ j, Template HasSnaky 13 (childrenC_691_i6 j) (childrenD_691_i6 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_6 2 (3, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_8 1 (2, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_690 1 (0, 2)).mono (by decide +kernel)
  · exact row_works_691_i7.mono (by decide +kernel)
theorem row_works_691_i6 : Template HasSnaky 14 required_691_i6 envelope_691_i6 := by
  refine compose HasSnaky 13 childrenC_691_i6 childrenD_691_i6 children_work_691_i6 (3, 7)
    required_691_i6 envelope_691_i6 pivot_mem_691_i6 child_required_sub_691_i6 child_envelope_sub_691_i6 ?_
  intro b hb
  exact common_sub_691_i6 (mem_commonEnvelope childrenD_691_i6 b hb)
def required_691 : Finset Cell := ⟨(([(3, 3), (3, 4), (3, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_691 : Finset Cell := ⟨(([(0, 4), (1, 4), (1, 6), (2, 3), (2, 4), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 0), (4, 1), (4, 2), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (10, 9), (11, 3), (11, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_691 : Fin 4 → Finset Cell := ![(placed21 1 (2, 3) required_8), required_691_i0, required_691_i1, required_691_i6]
def childrenD_691 : Fin 4 → Finset Cell := ![(placed21 1 (2, 3) envelope_8), envelope_691_i0, envelope_691_i1, envelope_691_i6]
theorem common_sub_691 : commonEnvelope childrenD_691 ⊆ insert (3, 6) required_691 := by decide +kernel
theorem child_required_sub_691 : ∀ j, childrenC_691 j ⊆ insert (3, 6) required_691 := by decide +kernel
theorem child_envelope_sub_691 : ∀ j, childrenD_691 j ⊆ envelope_691 := by decide +kernel
theorem pivot_mem_691 : (3, 6) ∈ envelope_691 := by decide +kernel
theorem children_work_691 : ∀ j, Template HasSnaky 17 (childrenC_691 j) (childrenD_691 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_8 1 (2, 3)).mono (by decide +kernel)
  · exact row_works_691_i0.mono (by decide +kernel)
  · exact row_works_691_i1.mono (by decide +kernel)
  · exact row_works_691_i6.mono (by decide +kernel)
theorem row_works_691 : Template HasSnaky 18 required_691 envelope_691 := by
  refine compose HasSnaky 17 childrenC_691 childrenD_691 children_work_691 (3, 6)
    required_691 envelope_691 pivot_mem_691 child_required_sub_691 child_envelope_sub_691 ?_
  intro b hb
  exact common_sub_691 (mem_commonEnvelope childrenD_691 b hb)
def height_684_i1 : ℕ := 13
def childrenH_684_i1 : Fin 6 → ℕ := ![height_8, height_115, height_469, height_470, height_485, height_489]
theorem height_exact_684_i1 : height_684_i1 = 1 + Finset.univ.sup childrenH_684_i1 := by decide +kernel
theorem required_origin_684_i1 : ∀ x ∈ required_684_i1,
    (∃ j, x ∈ childrenC_684_i1 j) ∨ ∀ j, x ∈ childrenD_684_i1 j := by decide +kernel
theorem required_exact_684_i1 : required_684_i1 =
    ((Finset.univ.biUnion childrenC_684_i1) ∪ commonEnvelope childrenD_684_i1).erase (9, 7) := by
  exact required_eq_combination childrenC_684_i1 childrenD_684_i1 (9, 7) required_684_i1
    (by decide +kernel) child_required_sub_684_i1 common_sub_684_i1 required_origin_684_i1
theorem envelope_origin_684_i1 : ∀ x ∈ envelope_684_i1,
    x = (9, 7) ∨ ∃ j, x ∈ childrenD_684_i1 j := by decide +kernel
theorem envelope_exact_684_i1 : envelope_684_i1 =
    insert (9, 7) (Finset.univ.biUnion childrenD_684_i1) := by
  exact envelope_eq_combination childrenD_684_i1 (9, 7) envelope_684_i1
    pivot_mem_684_i1 child_envelope_sub_684_i1 envelope_origin_684_i1
def checked_684_i1 : CheckedCard where
  required := required_684_i1
  envelope := envelope_684_i1
  height := height_684_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_684_i1
def height_684_i0 : ℕ := 14
def childrenH_684_i0 : Fin 6 → ℕ := ![height_118, height_355, height_434, height_468, height_684_i1, height_491]
theorem height_exact_684_i0 : height_684_i0 = 1 + Finset.univ.sup childrenH_684_i0 := by decide +kernel
theorem required_origin_684_i0 : ∀ x ∈ required_684_i0,
    (∃ j, x ∈ childrenC_684_i0 j) ∨ ∀ j, x ∈ childrenD_684_i0 j := by decide +kernel
theorem required_exact_684_i0 : required_684_i0 =
    ((Finset.univ.biUnion childrenC_684_i0) ∪ commonEnvelope childrenD_684_i0).erase (8, 7) := by
  exact required_eq_combination childrenC_684_i0 childrenD_684_i0 (8, 7) required_684_i0
    (by decide +kernel) child_required_sub_684_i0 common_sub_684_i0 required_origin_684_i0
theorem envelope_origin_684_i0 : ∀ x ∈ envelope_684_i0,
    x = (8, 7) ∨ ∃ j, x ∈ childrenD_684_i0 j := by decide +kernel
theorem envelope_exact_684_i0 : envelope_684_i0 =
    insert (8, 7) (Finset.univ.biUnion childrenD_684_i0) := by
  exact envelope_eq_combination childrenD_684_i0 (8, 7) envelope_684_i0
    pivot_mem_684_i0 child_envelope_sub_684_i0 envelope_origin_684_i0
def checked_684_i0 : CheckedCard where
  required := required_684_i0
  envelope := envelope_684_i0
  height := height_684_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_684_i0
def height_684_i2 : ℕ := 12
def childrenH_684_i2 : Fin 6 → ℕ := ![height_50, height_97, height_98, height_454, height_455, height_624]
theorem height_exact_684_i2 : height_684_i2 = 1 + Finset.univ.sup childrenH_684_i2 := by decide +kernel
theorem required_origin_684_i2 : ∀ x ∈ required_684_i2,
    (∃ j, x ∈ childrenC_684_i2 j) ∨ ∀ j, x ∈ childrenD_684_i2 j := by decide +kernel
theorem required_exact_684_i2 : required_684_i2 =
    ((Finset.univ.biUnion childrenC_684_i2) ∪ commonEnvelope childrenD_684_i2).erase (7, 9) := by
  exact required_eq_combination childrenC_684_i2 childrenD_684_i2 (7, 9) required_684_i2
    (by decide +kernel) child_required_sub_684_i2 common_sub_684_i2 required_origin_684_i2
theorem envelope_origin_684_i2 : ∀ x ∈ envelope_684_i2,
    x = (7, 9) ∨ ∃ j, x ∈ childrenD_684_i2 j := by decide +kernel
theorem envelope_exact_684_i2 : envelope_684_i2 =
    insert (7, 9) (Finset.univ.biUnion childrenD_684_i2) := by
  exact envelope_eq_combination childrenD_684_i2 (7, 9) envelope_684_i2
    pivot_mem_684_i2 child_envelope_sub_684_i2 envelope_origin_684_i2
def checked_684_i2 : CheckedCard where
  required := required_684_i2
  envelope := envelope_684_i2
  height := height_684_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_684_i2
def height_684_i3 : ℕ := 15
def childrenH_684_i3 : Fin 13 → ℕ := ![height_174, height_475, height_475, height_483, height_508, height_508, height_566, height_587, height_587, height_635, height_644, height_645, height_647]
theorem height_exact_684_i3 : height_684_i3 = 1 + Finset.univ.sup childrenH_684_i3 := by decide +kernel
theorem required_origin_684_i3 : ∀ x ∈ required_684_i3,
    (∃ j, x ∈ childrenC_684_i3 j) ∨ ∀ j, x ∈ childrenD_684_i3 j := by decide +kernel
theorem required_exact_684_i3 : required_684_i3 =
    ((Finset.univ.biUnion childrenC_684_i3) ∪ commonEnvelope childrenD_684_i3).erase (7, 11) := by
  exact required_eq_combination childrenC_684_i3 childrenD_684_i3 (7, 11) required_684_i3
    (by decide +kernel) child_required_sub_684_i3 common_sub_684_i3 required_origin_684_i3
theorem envelope_origin_684_i3 : ∀ x ∈ envelope_684_i3,
    x = (7, 11) ∨ ∃ j, x ∈ childrenD_684_i3 j := by decide +kernel
theorem envelope_exact_684_i3 : envelope_684_i3 =
    insert (7, 11) (Finset.univ.biUnion childrenD_684_i3) := by
  exact envelope_eq_combination childrenD_684_i3 (7, 11) envelope_684_i3
    pivot_mem_684_i3 child_envelope_sub_684_i3 envelope_origin_684_i3
def checked_684_i3 : CheckedCard where
  required := required_684_i3
  envelope := envelope_684_i3
  height := height_684_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_684_i3
def height_684_i5 : ℕ := 7
def childrenH_684_i5 : Fin 2 → ℕ := ![height_8, height_313]
theorem height_exact_684_i5 : height_684_i5 = 1 + Finset.univ.sup childrenH_684_i5 := by decide +kernel
theorem required_origin_684_i5 : ∀ x ∈ required_684_i5,
    (∃ j, x ∈ childrenC_684_i5 j) ∨ ∀ j, x ∈ childrenD_684_i5 j := by decide +kernel
theorem required_exact_684_i5 : required_684_i5 =
    ((Finset.univ.biUnion childrenC_684_i5) ∪ commonEnvelope childrenD_684_i5).erase (9, 7) := by
  exact required_eq_combination childrenC_684_i5 childrenD_684_i5 (9, 7) required_684_i5
    (by decide +kernel) child_required_sub_684_i5 common_sub_684_i5 required_origin_684_i5
theorem envelope_origin_684_i5 : ∀ x ∈ envelope_684_i5,
    x = (9, 7) ∨ ∃ j, x ∈ childrenD_684_i5 j := by decide +kernel
theorem envelope_exact_684_i5 : envelope_684_i5 =
    insert (9, 7) (Finset.univ.biUnion childrenD_684_i5) := by
  exact envelope_eq_combination childrenD_684_i5 (9, 7) envelope_684_i5
    pivot_mem_684_i5 child_envelope_sub_684_i5 envelope_origin_684_i5
def checked_684_i5 : CheckedCard where
  required := required_684_i5
  envelope := envelope_684_i5
  height := height_684_i5
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_684_i5
def height_684_i4 : ℕ := 12
def childrenH_684_i4 : Fin 5 → ℕ := ![height_257, height_684_i5, height_434, height_468, height_491]
theorem height_exact_684_i4 : height_684_i4 = 1 + Finset.univ.sup childrenH_684_i4 := by decide +kernel
theorem required_origin_684_i4 : ∀ x ∈ required_684_i4,
    (∃ j, x ∈ childrenC_684_i4 j) ∨ ∀ j, x ∈ childrenD_684_i4 j := by decide +kernel
theorem required_exact_684_i4 : required_684_i4 =
    ((Finset.univ.biUnion childrenC_684_i4) ∪ commonEnvelope childrenD_684_i4).erase (8, 7) := by
  exact required_eq_combination childrenC_684_i4 childrenD_684_i4 (8, 7) required_684_i4
    (by decide +kernel) child_required_sub_684_i4 common_sub_684_i4 required_origin_684_i4
theorem envelope_origin_684_i4 : ∀ x ∈ envelope_684_i4,
    x = (8, 7) ∨ ∃ j, x ∈ childrenD_684_i4 j := by decide +kernel
theorem envelope_exact_684_i4 : envelope_684_i4 =
    insert (8, 7) (Finset.univ.biUnion childrenD_684_i4) := by
  exact envelope_eq_combination childrenD_684_i4 (8, 7) envelope_684_i4
    pivot_mem_684_i4 child_envelope_sub_684_i4 envelope_origin_684_i4
def checked_684_i4 : CheckedCard where
  required := required_684_i4
  envelope := envelope_684_i4
  height := height_684_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_684_i4
def height_684 : ℕ := 18
def childrenH_684 : Fin 15 → ℕ := ![height_684_i0, height_623, height_684_i2, height_625, height_630, height_632, height_636, height_639, height_684_i3, height_656, height_657, height_670, height_675, height_683, height_684_i4]
theorem height_exact_684 : height_684 = 1 + Finset.univ.sup childrenH_684 := by decide +kernel
theorem required_origin_684 : ∀ x ∈ required_684,
    (∃ j, x ∈ childrenC_684 j) ∨ ∀ j, x ∈ childrenD_684 j := by decide +kernel
theorem required_exact_684 : required_684 =
    ((Finset.univ.biUnion childrenC_684) ∪ commonEnvelope childrenD_684).erase (7, 10) := by
  exact required_eq_combination childrenC_684 childrenD_684 (7, 10) required_684
    (by decide +kernel) child_required_sub_684 common_sub_684 required_origin_684
theorem envelope_origin_684 : ∀ x ∈ envelope_684,
    x = (7, 10) ∨ ∃ j, x ∈ childrenD_684 j := by decide +kernel
theorem envelope_exact_684 : envelope_684 =
    insert (7, 10) (Finset.univ.biUnion childrenD_684) := by
  exact envelope_eq_combination childrenD_684 (7, 10) envelope_684
    pivot_mem_684 child_envelope_sub_684 envelope_origin_684
def checked_684 : CheckedCard where
  required := required_684
  envelope := envelope_684
  height := height_684
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_684
def height_691_i0 : ℕ := 6
def childrenH_691_i0 : Fin 3 → ℕ := ![height_27, height_277, height_278]
theorem height_exact_691_i0 : height_691_i0 = 1 + Finset.univ.sup childrenH_691_i0 := by decide +kernel
theorem required_origin_691_i0 : ∀ x ∈ required_691_i0,
    (∃ j, x ∈ childrenC_691_i0 j) ∨ ∀ j, x ∈ childrenD_691_i0 j := by decide +kernel
theorem required_exact_691_i0 : required_691_i0 =
    ((Finset.univ.biUnion childrenC_691_i0) ∪ commonEnvelope childrenD_691_i0).erase (4, 5) := by
  exact required_eq_combination childrenC_691_i0 childrenD_691_i0 (4, 5) required_691_i0
    (by decide +kernel) child_required_sub_691_i0 common_sub_691_i0 required_origin_691_i0
theorem envelope_origin_691_i0 : ∀ x ∈ envelope_691_i0,
    x = (4, 5) ∨ ∃ j, x ∈ childrenD_691_i0 j := by decide +kernel
theorem envelope_exact_691_i0 : envelope_691_i0 =
    insert (4, 5) (Finset.univ.biUnion childrenD_691_i0) := by
  exact envelope_eq_combination childrenD_691_i0 (4, 5) envelope_691_i0
    pivot_mem_691_i0 child_envelope_sub_691_i0 envelope_origin_691_i0
def checked_691_i0 : CheckedCard where
  required := required_691_i0
  envelope := envelope_691_i0
  height := height_691_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_691_i0
def height_691_i5 : ℕ := 8
def childrenH_691_i5 : Fin 2 → ℕ := ![height_0, height_317]
theorem height_exact_691_i5 : height_691_i5 = 1 + Finset.univ.sup childrenH_691_i5 := by decide +kernel
theorem required_origin_691_i5 : ∀ x ∈ required_691_i5,
    (∃ j, x ∈ childrenC_691_i5 j) ∨ ∀ j, x ∈ childrenD_691_i5 j := by decide +kernel
theorem required_exact_691_i5 : required_691_i5 =
    ((Finset.univ.biUnion childrenC_691_i5) ∪ commonEnvelope childrenD_691_i5).erase (5, 6) := by
  exact required_eq_combination childrenC_691_i5 childrenD_691_i5 (5, 6) required_691_i5
    (by decide +kernel) child_required_sub_691_i5 common_sub_691_i5 required_origin_691_i5
theorem envelope_origin_691_i5 : ∀ x ∈ envelope_691_i5,
    x = (5, 6) ∨ ∃ j, x ∈ childrenD_691_i5 j := by decide +kernel
theorem envelope_exact_691_i5 : envelope_691_i5 =
    insert (5, 6) (Finset.univ.biUnion childrenD_691_i5) := by
  exact envelope_eq_combination childrenD_691_i5 (5, 6) envelope_691_i5
    pivot_mem_691_i5 child_envelope_sub_691_i5 envelope_origin_691_i5
def checked_691_i5 : CheckedCard where
  required := required_691_i5
  envelope := envelope_691_i5
  height := height_691_i5
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_691_i5
def height_691_i4 : ℕ := 14
def childrenH_691_i4 : Fin 4 → ℕ := ![height_30, height_59, height_462, height_691_i5]
theorem height_exact_691_i4 : height_691_i4 = 1 + Finset.univ.sup childrenH_691_i4 := by decide +kernel
theorem required_origin_691_i4 : ∀ x ∈ required_691_i4,
    (∃ j, x ∈ childrenC_691_i4 j) ∨ ∀ j, x ∈ childrenD_691_i4 j := by decide +kernel
theorem required_exact_691_i4 : required_691_i4 =
    ((Finset.univ.biUnion childrenC_691_i4) ∪ commonEnvelope childrenD_691_i4).erase (6, 6) := by
  exact required_eq_combination childrenC_691_i4 childrenD_691_i4 (6, 6) required_691_i4
    (by decide +kernel) child_required_sub_691_i4 common_sub_691_i4 required_origin_691_i4
theorem envelope_origin_691_i4 : ∀ x ∈ envelope_691_i4,
    x = (6, 6) ∨ ∃ j, x ∈ childrenD_691_i4 j := by decide +kernel
theorem envelope_exact_691_i4 : envelope_691_i4 =
    insert (6, 6) (Finset.univ.biUnion childrenD_691_i4) := by
  exact envelope_eq_combination childrenD_691_i4 (6, 6) envelope_691_i4
    pivot_mem_691_i4 child_envelope_sub_691_i4 envelope_origin_691_i4
def checked_691_i4 : CheckedCard where
  required := required_691_i4
  envelope := envelope_691_i4
  height := height_691_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_691_i4
def height_691_i3 : ℕ := 15
def childrenH_691_i3 : Fin 3 → ℕ := ![height_102, height_400, height_691_i4]
theorem height_exact_691_i3 : height_691_i3 = 1 + Finset.univ.sup childrenH_691_i3 := by decide +kernel
theorem required_origin_691_i3 : ∀ x ∈ required_691_i3,
    (∃ j, x ∈ childrenC_691_i3 j) ∨ ∀ j, x ∈ childrenD_691_i3 j := by decide +kernel
theorem required_exact_691_i3 : required_691_i3 =
    ((Finset.univ.biUnion childrenC_691_i3) ∪ commonEnvelope childrenD_691_i3).erase (6, 5) := by
  exact required_eq_combination childrenC_691_i3 childrenD_691_i3 (6, 5) required_691_i3
    (by decide +kernel) child_required_sub_691_i3 common_sub_691_i3 required_origin_691_i3
theorem envelope_origin_691_i3 : ∀ x ∈ envelope_691_i3,
    x = (6, 5) ∨ ∃ j, x ∈ childrenD_691_i3 j := by decide +kernel
theorem envelope_exact_691_i3 : envelope_691_i3 =
    insert (6, 5) (Finset.univ.biUnion childrenD_691_i3) := by
  exact envelope_eq_combination childrenD_691_i3 (6, 5) envelope_691_i3
    pivot_mem_691_i3 child_envelope_sub_691_i3 envelope_origin_691_i3
def checked_691_i3 : CheckedCard where
  required := required_691_i3
  envelope := envelope_691_i3
  height := height_691_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_691_i3
def height_691_i2 : ℕ := 16
def childrenH_691_i2 : Fin 2 → ℕ := ![height_0, height_691_i3]
theorem height_exact_691_i2 : height_691_i2 = 1 + Finset.univ.sup childrenH_691_i2 := by decide +kernel
theorem required_origin_691_i2 : ∀ x ∈ required_691_i2,
    (∃ j, x ∈ childrenC_691_i2 j) ∨ ∀ j, x ∈ childrenD_691_i2 j := by decide +kernel
theorem required_exact_691_i2 : required_691_i2 =
    ((Finset.univ.biUnion childrenC_691_i2) ∪ commonEnvelope childrenD_691_i2).erase (4, 5) := by
  exact required_eq_combination childrenC_691_i2 childrenD_691_i2 (4, 5) required_691_i2
    (by decide +kernel) child_required_sub_691_i2 common_sub_691_i2 required_origin_691_i2
theorem envelope_origin_691_i2 : ∀ x ∈ envelope_691_i2,
    x = (4, 5) ∨ ∃ j, x ∈ childrenD_691_i2 j := by decide +kernel
theorem envelope_exact_691_i2 : envelope_691_i2 =
    insert (4, 5) (Finset.univ.biUnion childrenD_691_i2) := by
  exact envelope_eq_combination childrenD_691_i2 (4, 5) envelope_691_i2
    pivot_mem_691_i2 child_envelope_sub_691_i2 envelope_origin_691_i2
def checked_691_i2 : CheckedCard where
  required := required_691_i2
  envelope := envelope_691_i2
  height := height_691_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_691_i2
def height_691_i1 : ℕ := 17
def childrenH_691_i1 : Fin 2 → ℕ := ![height_5, height_691_i2]
theorem height_exact_691_i1 : height_691_i1 = 1 + Finset.univ.sup childrenH_691_i1 := by decide +kernel
theorem required_origin_691_i1 : ∀ x ∈ required_691_i1,
    (∃ j, x ∈ childrenC_691_i1 j) ∨ ∀ j, x ∈ childrenD_691_i1 j := by decide +kernel
theorem required_exact_691_i1 : required_691_i1 =
    ((Finset.univ.biUnion childrenC_691_i1) ∪ commonEnvelope childrenD_691_i1).erase (4, 6) := by
  exact required_eq_combination childrenC_691_i1 childrenD_691_i1 (4, 6) required_691_i1
    (by decide +kernel) child_required_sub_691_i1 common_sub_691_i1 required_origin_691_i1
theorem envelope_origin_691_i1 : ∀ x ∈ envelope_691_i1,
    x = (4, 6) ∨ ∃ j, x ∈ childrenD_691_i1 j := by decide +kernel
theorem envelope_exact_691_i1 : envelope_691_i1 =
    insert (4, 6) (Finset.univ.biUnion childrenD_691_i1) := by
  exact envelope_eq_combination childrenD_691_i1 (4, 6) envelope_691_i1
    pivot_mem_691_i1 child_envelope_sub_691_i1 envelope_origin_691_i1
def checked_691_i1 : CheckedCard where
  required := required_691_i1
  envelope := envelope_691_i1
  height := height_691_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_691_i1
def height_691_i10 : ℕ := 3
def childrenH_691_i10 : Fin 2 → ℕ := ![height_5, height_35]
theorem height_exact_691_i10 : height_691_i10 = 1 + Finset.univ.sup childrenH_691_i10 := by decide +kernel
theorem required_origin_691_i10 : ∀ x ∈ required_691_i10,
    (∃ j, x ∈ childrenC_691_i10 j) ∨ ∀ j, x ∈ childrenD_691_i10 j := by decide +kernel
theorem required_exact_691_i10 : required_691_i10 =
    ((Finset.univ.biUnion childrenC_691_i10) ∪ commonEnvelope childrenD_691_i10).erase (2, 6) := by
  exact required_eq_combination childrenC_691_i10 childrenD_691_i10 (2, 6) required_691_i10
    (by decide +kernel) child_required_sub_691_i10 common_sub_691_i10 required_origin_691_i10
theorem envelope_origin_691_i10 : ∀ x ∈ envelope_691_i10,
    x = (2, 6) ∨ ∃ j, x ∈ childrenD_691_i10 j := by decide +kernel
theorem envelope_exact_691_i10 : envelope_691_i10 =
    insert (2, 6) (Finset.univ.biUnion childrenD_691_i10) := by
  exact envelope_eq_combination childrenD_691_i10 (2, 6) envelope_691_i10
    pivot_mem_691_i10 child_envelope_sub_691_i10 envelope_origin_691_i10
def checked_691_i10 : CheckedCard where
  required := required_691_i10
  envelope := envelope_691_i10
  height := height_691_i10
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_691_i10
def height_691_i9 : ℕ := 11
def childrenH_691_i9 : Fin 3 → ℕ := ![height_691_i10, height_460, height_488]
theorem height_exact_691_i9 : height_691_i9 = 1 + Finset.univ.sup childrenH_691_i9 := by decide +kernel
theorem required_origin_691_i9 : ∀ x ∈ required_691_i9,
    (∃ j, x ∈ childrenC_691_i9 j) ∨ ∀ j, x ∈ childrenD_691_i9 j := by decide +kernel
theorem required_exact_691_i9 : required_691_i9 =
    ((Finset.univ.biUnion childrenC_691_i9) ∪ commonEnvelope childrenD_691_i9).erase (6, 7) := by
  exact required_eq_combination childrenC_691_i9 childrenD_691_i9 (6, 7) required_691_i9
    (by decide +kernel) child_required_sub_691_i9 common_sub_691_i9 required_origin_691_i9
theorem envelope_origin_691_i9 : ∀ x ∈ envelope_691_i9,
    x = (6, 7) ∨ ∃ j, x ∈ childrenD_691_i9 j := by decide +kernel
theorem envelope_exact_691_i9 : envelope_691_i9 =
    insert (6, 7) (Finset.univ.biUnion childrenD_691_i9) := by
  exact envelope_eq_combination childrenD_691_i9 (6, 7) envelope_691_i9
    pivot_mem_691_i9 child_envelope_sub_691_i9 envelope_origin_691_i9
def checked_691_i9 : CheckedCard where
  required := required_691_i9
  envelope := envelope_691_i9
  height := height_691_i9
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_691_i9
def height_691_i8 : ℕ := 12
def childrenH_691_i8 : Fin 3 → ℕ := ![height_39, height_80, height_691_i9]
theorem height_exact_691_i8 : height_691_i8 = 1 + Finset.univ.sup childrenH_691_i8 := by decide +kernel
theorem required_origin_691_i8 : ∀ x ∈ required_691_i8,
    (∃ j, x ∈ childrenC_691_i8 j) ∨ ∀ j, x ∈ childrenD_691_i8 j := by decide +kernel
theorem required_exact_691_i8 : required_691_i8 =
    ((Finset.univ.biUnion childrenC_691_i8) ∪ commonEnvelope childrenD_691_i8).erase (6, 5) := by
  exact required_eq_combination childrenC_691_i8 childrenD_691_i8 (6, 5) required_691_i8
    (by decide +kernel) child_required_sub_691_i8 common_sub_691_i8 required_origin_691_i8
theorem envelope_origin_691_i8 : ∀ x ∈ envelope_691_i8,
    x = (6, 5) ∨ ∃ j, x ∈ childrenD_691_i8 j := by decide +kernel
theorem envelope_exact_691_i8 : envelope_691_i8 =
    insert (6, 5) (Finset.univ.biUnion childrenD_691_i8) := by
  exact envelope_eq_combination childrenD_691_i8 (6, 5) envelope_691_i8
    pivot_mem_691_i8 child_envelope_sub_691_i8 envelope_origin_691_i8
def checked_691_i8 : CheckedCard where
  required := required_691_i8
  envelope := envelope_691_i8
  height := height_691_i8
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_691_i8
def height_691_i7 : ℕ := 13
def childrenH_691_i7 : Fin 3 → ℕ := ![height_21, height_56, height_691_i8]
theorem height_exact_691_i7 : height_691_i7 = 1 + Finset.univ.sup childrenH_691_i7 := by decide +kernel
theorem required_origin_691_i7 : ∀ x ∈ required_691_i7,
    (∃ j, x ∈ childrenC_691_i7 j) ∨ ∀ j, x ∈ childrenD_691_i7 j := by decide +kernel
theorem required_exact_691_i7 : required_691_i7 =
    ((Finset.univ.biUnion childrenC_691_i7) ∪ commonEnvelope childrenD_691_i7).erase (4, 5) := by
  exact required_eq_combination childrenC_691_i7 childrenD_691_i7 (4, 5) required_691_i7
    (by decide +kernel) child_required_sub_691_i7 common_sub_691_i7 required_origin_691_i7
theorem envelope_origin_691_i7 : ∀ x ∈ envelope_691_i7,
    x = (4, 5) ∨ ∃ j, x ∈ childrenD_691_i7 j := by decide +kernel
theorem envelope_exact_691_i7 : envelope_691_i7 =
    insert (4, 5) (Finset.univ.biUnion childrenD_691_i7) := by
  exact envelope_eq_combination childrenD_691_i7 (4, 5) envelope_691_i7
    pivot_mem_691_i7 child_envelope_sub_691_i7 envelope_origin_691_i7
def checked_691_i7 : CheckedCard where
  required := required_691_i7
  envelope := envelope_691_i7
  height := height_691_i7
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_691_i7
def height_691_i6 : ℕ := 14
def childrenH_691_i6 : Fin 4 → ℕ := ![height_6, height_8, height_690, height_691_i7]
theorem height_exact_691_i6 : height_691_i6 = 1 + Finset.univ.sup childrenH_691_i6 := by decide +kernel
theorem required_origin_691_i6 : ∀ x ∈ required_691_i6,
    (∃ j, x ∈ childrenC_691_i6 j) ∨ ∀ j, x ∈ childrenD_691_i6 j := by decide +kernel
theorem required_exact_691_i6 : required_691_i6 =
    ((Finset.univ.biUnion childrenC_691_i6) ∪ commonEnvelope childrenD_691_i6).erase (3, 7) := by
  exact required_eq_combination childrenC_691_i6 childrenD_691_i6 (3, 7) required_691_i6
    (by decide +kernel) child_required_sub_691_i6 common_sub_691_i6 required_origin_691_i6
theorem envelope_origin_691_i6 : ∀ x ∈ envelope_691_i6,
    x = (3, 7) ∨ ∃ j, x ∈ childrenD_691_i6 j := by decide +kernel
theorem envelope_exact_691_i6 : envelope_691_i6 =
    insert (3, 7) (Finset.univ.biUnion childrenD_691_i6) := by
  exact envelope_eq_combination childrenD_691_i6 (3, 7) envelope_691_i6
    pivot_mem_691_i6 child_envelope_sub_691_i6 envelope_origin_691_i6
def checked_691_i6 : CheckedCard where
  required := required_691_i6
  envelope := envelope_691_i6
  height := height_691_i6
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_691_i6
def height_691 : ℕ := 18
def childrenH_691 : Fin 4 → ℕ := ![height_8, height_691_i0, height_691_i1, height_691_i6]
theorem height_exact_691 : height_691 = 1 + Finset.univ.sup childrenH_691 := by decide +kernel
theorem required_origin_691 : ∀ x ∈ required_691,
    (∃ j, x ∈ childrenC_691 j) ∨ ∀ j, x ∈ childrenD_691 j := by decide +kernel
theorem required_exact_691 : required_691 =
    ((Finset.univ.biUnion childrenC_691) ∪ commonEnvelope childrenD_691).erase (3, 6) := by
  exact required_eq_combination childrenC_691 childrenD_691 (3, 6) required_691
    (by decide +kernel) child_required_sub_691 common_sub_691 required_origin_691
theorem envelope_origin_691 : ∀ x ∈ envelope_691,
    x = (3, 6) ∨ ∃ j, x ∈ childrenD_691 j := by decide +kernel
theorem envelope_exact_691 : envelope_691 =
    insert (3, 6) (Finset.univ.biUnion childrenD_691) := by
  exact envelope_eq_combination childrenD_691 (3, 6) envelope_691
    pivot_mem_691 child_envelope_sub_691 envelope_origin_691
def checked_691 : CheckedCard where
  required := required_691
  envelope := envelope_691
  height := height_691
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_691
end SnakyPrototype.Certificate21

end OAI
