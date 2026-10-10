import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part03
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_452_i0 : Finset Cell := ⟨(([(3, 3), (3, 4), (4, 4), (5, 3), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_452_i0 : Finset Cell := ⟨(([(2, 3), (3, 3), (3, 4), (4, 4), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (6, 4), (6, 5), (6, 6), (6, 7), (7, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_452_i0 : Fin 2 → Finset Cell := ![(placed21 6 (6, 4) required_5), (placed21 0 (3, 1) required_55)]
def childrenD_452_i0 : Fin 2 → Finset Cell := ![(placed21 6 (6, 4) envelope_5), (placed21 0 (3, 1) envelope_55)]
theorem common_sub_452_i0 : commonEnvelope childrenD_452_i0 ⊆ insert (6, 4) required_452_i0 := by decide +kernel
theorem child_required_sub_452_i0 : ∀ j, childrenC_452_i0 j ⊆ insert (6, 4) required_452_i0 := by decide +kernel
theorem child_envelope_sub_452_i0 : ∀ j, childrenD_452_i0 j ⊆ envelope_452_i0 := by decide +kernel
theorem pivot_mem_452_i0 : (6, 4) ∈ envelope_452_i0 := by decide +kernel
theorem children_work_452_i0 : ∀ j, Template HasSnaky 4 (childrenC_452_i0 j) (childrenD_452_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 6 (6, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_55 0 (3, 1)).mono (by decide +kernel)
theorem row_works_452_i0 : Template HasSnaky 5 required_452_i0 envelope_452_i0 := by
  refine compose HasSnaky 4 childrenC_452_i0 childrenD_452_i0 children_work_452_i0 (6, 4)
    required_452_i0 envelope_452_i0 pivot_mem_452_i0 child_required_sub_452_i0 child_envelope_sub_452_i0 ?_
  intro b hb
  exact common_sub_452_i0 (mem_commonEnvelope childrenD_452_i0 b hb)
def required_452 : Finset Cell := ⟨(([(3, 3), (3, 4), (5, 3), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_452 : Finset Cell := ⟨(([(0, 3), (1, 3), (2, 3), (2, 4), (3, 3), (3, 4), (4, 0), (4, 1), (4, 2), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 0), (6, 1), (6, 2), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (7, 5), (8, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_452 : Fin 3 → Finset Cell := ![(placed21 7 (6, 4) required_52), (placed21 0 (2, 0) required_317), required_452_i0]
def childrenD_452 : Fin 3 → Finset Cell := ![(placed21 7 (6, 4) envelope_52), (placed21 0 (2, 0) envelope_317), envelope_452_i0]
theorem common_sub_452 : commonEnvelope childrenD_452 ⊆ insert (4, 4) required_452 := by decide +kernel
theorem child_required_sub_452 : ∀ j, childrenC_452 j ⊆ insert (4, 4) required_452 := by decide +kernel
theorem child_envelope_sub_452 : ∀ j, childrenD_452 j ⊆ envelope_452 := by decide +kernel
theorem pivot_mem_452 : (4, 4) ∈ envelope_452 := by decide +kernel
theorem children_work_452 : ∀ j, Template HasSnaky 7 (childrenC_452 j) (childrenD_452 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_52 7 (6, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_317 0 (2, 0)).mono (by decide +kernel)
  · exact row_works_452_i0.mono (by decide +kernel)
theorem row_works_452 : Template HasSnaky 8 required_452 envelope_452 := by
  refine compose HasSnaky 7 childrenC_452 childrenD_452 children_work_452 (4, 4)
    required_452 envelope_452 pivot_mem_452 child_required_sub_452 child_envelope_sub_452 ?_
  intro b hb
  exact common_sub_452 (mem_commonEnvelope childrenD_452 b hb)
def required_454 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 4), (2, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_454 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (4, 0), (4, 1), (4, 2), (5, 0), (5, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_454 : Fin 2 → Finset Cell := ![(placed21 1 (1, 1) required_5), (placed21 3 (0, 4) required_453)]
def childrenD_454 : Fin 2 → Finset Cell := ![(placed21 1 (1, 1) envelope_5), (placed21 3 (0, 4) envelope_453)]
theorem common_sub_454 : commonEnvelope childrenD_454 ⊆ insert (1, 3) required_454 := by decide +kernel
theorem child_required_sub_454 : ∀ j, childrenC_454 j ⊆ insert (1, 3) required_454 := by decide +kernel
theorem child_envelope_sub_454 : ∀ j, childrenD_454 j ⊆ envelope_454 := by decide +kernel
theorem pivot_mem_454 : (1, 3) ∈ envelope_454 := by decide +kernel
theorem children_work_454 : ∀ j, Template HasSnaky 7 (childrenC_454 j) (childrenD_454 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 1 (1, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_453 3 (0, 4)).mono (by decide +kernel)
theorem row_works_454 : Template HasSnaky 8 required_454 envelope_454 := by
  refine compose HasSnaky 7 childrenC_454 childrenD_454 children_work_454 (1, 3)
    required_454 envelope_454 pivot_mem_454 child_required_sub_454 child_envelope_sub_454 ?_
  intro b hb
  exact common_sub_454 (mem_commonEnvelope childrenD_454 b hb)
def required_455 : Finset Cell := ⟨(([(0, 1), (0, 2), (2, 1), (3, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_455 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 1), (1, 2), (1, 3), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 0), (5, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_455 : Fin 4 → Finset Cell := ![required_8, (placed21 1 (0, 1) required_16), (placed21 4 (0, 2) required_24), required_453]
def childrenD_455 : Fin 4 → Finset Cell := ![envelope_8, (placed21 1 (0, 1) envelope_16), (placed21 4 (0, 2) envelope_24), envelope_453]
theorem common_sub_455 : commonEnvelope childrenD_455 ⊆ insert (1, 1) required_455 := by decide +kernel
theorem child_required_sub_455 : ∀ j, childrenC_455 j ⊆ insert (1, 1) required_455 := by decide +kernel
theorem child_envelope_sub_455 : ∀ j, childrenD_455 j ⊆ envelope_455 := by decide +kernel
theorem pivot_mem_455 : (1, 1) ∈ envelope_455 := by decide +kernel
theorem children_work_455 : ∀ j, Template HasSnaky 7 (childrenC_455 j) (childrenD_455 j) := by
  intro j
  fin_cases j
  · exact row_works_8.mono (by decide +kernel)
  · exact (placed21_template row_works_16 1 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_24 4 (0, 2)).mono (by decide +kernel)
  · exact row_works_453.mono (by decide +kernel)
theorem row_works_455 : Template HasSnaky 8 required_455 envelope_455 := by
  refine compose HasSnaky 7 childrenC_455 childrenD_455 children_work_455 (1, 1)
    required_455 envelope_455 pivot_mem_455 child_required_sub_455 child_envelope_sub_455 ?_
  intro b hb
  exact common_sub_455 (mem_commonEnvelope childrenD_455 b hb)
def required_456 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 3), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_456 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (4, 0), (4, 1), (4, 2), (5, 0), (5, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_456 : Fin 2 → Finset Cell := ![(placed21 1 (1, 1) required_5), (placed21 3 (0, 4) required_453)]
def childrenD_456 : Fin 2 → Finset Cell := ![(placed21 1 (1, 1) envelope_5), (placed21 3 (0, 4) envelope_453)]
theorem common_sub_456 : commonEnvelope childrenD_456 ⊆ insert (2, 4) required_456 := by decide +kernel
theorem child_required_sub_456 : ∀ j, childrenC_456 j ⊆ insert (2, 4) required_456 := by decide +kernel
theorem child_envelope_sub_456 : ∀ j, childrenD_456 j ⊆ envelope_456 := by decide +kernel
theorem pivot_mem_456 : (2, 4) ∈ envelope_456 := by decide +kernel
theorem children_work_456 : ∀ j, Template HasSnaky 7 (childrenC_456 j) (childrenD_456 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 1 (1, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_453 3 (0, 4)).mono (by decide +kernel)
theorem row_works_456 : Template HasSnaky 8 required_456 envelope_456 := by
  refine compose HasSnaky 7 childrenC_456 childrenD_456 children_work_456 (2, 4)
    required_456 envelope_456 pivot_mem_456 child_required_sub_456 child_envelope_sub_456 ?_
  intro b hb
  exact common_sub_456 (mem_commonEnvelope childrenD_456 b hb)
def required_473 : Finset Cell := ⟨(([(1, 2), (2, 2), (3, 2), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_473 : Finset Cell := ⟨(([(0, 1), (0, 3), (0, 4), (0, 5), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 2), (3, 3), (3, 4), (4, 2), (4, 3), (5, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_473 : Fin 2 → Finset Cell := ![(placed21 6 (4, 2) required_5), required_472]
def childrenD_473 : Fin 2 → Finset Cell := ![(placed21 6 (4, 2) envelope_5), envelope_472]
theorem common_sub_473 : commonEnvelope childrenD_473 ⊆ insert (1, 1) required_473 := by decide +kernel
theorem child_required_sub_473 : ∀ j, childrenC_473 j ⊆ insert (1, 1) required_473 := by decide +kernel
theorem child_envelope_sub_473 : ∀ j, childrenD_473 j ⊆ envelope_473 := by decide +kernel
theorem pivot_mem_473 : (1, 1) ∈ envelope_473 := by decide +kernel
theorem children_work_473 : ∀ j, Template HasSnaky 7 (childrenC_473 j) (childrenD_473 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 6 (4, 2)).mono (by decide +kernel)
  · exact row_works_472.mono (by decide +kernel)
theorem row_works_473 : Template HasSnaky 8 required_473 envelope_473 := by
  refine compose HasSnaky 7 childrenC_473 childrenD_473 children_work_473 (1, 1)
    required_473 envelope_473 pivot_mem_473 child_required_sub_473 child_envelope_sub_473 ?_
  intro b hb
  exact common_sub_473 (mem_commonEnvelope childrenD_473 b hb)
def required_478 : Finset Cell := ⟨(([(1, 1), (1, 2), (3, 2), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_478 : Finset Cell := ⟨(([(0, 1), (0, 3), (0, 4), (0, 5), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 2), (3, 3), (3, 4), (4, 2), (4, 3), (5, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_478 : Fin 2 → Finset Cell := ![(placed21 6 (4, 2) required_5), required_472]
def childrenD_478 : Fin 2 → Finset Cell := ![(placed21 6 (4, 2) envelope_5), envelope_472]
theorem common_sub_478 : commonEnvelope childrenD_478 ⊆ insert (2, 2) required_478 := by decide +kernel
theorem child_required_sub_478 : ∀ j, childrenC_478 j ⊆ insert (2, 2) required_478 := by decide +kernel
theorem child_envelope_sub_478 : ∀ j, childrenD_478 j ⊆ envelope_478 := by decide +kernel
theorem pivot_mem_478 : (2, 2) ∈ envelope_478 := by decide +kernel
theorem children_work_478 : ∀ j, Template HasSnaky 7 (childrenC_478 j) (childrenD_478 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 6 (4, 2)).mono (by decide +kernel)
  · exact row_works_472.mono (by decide +kernel)
theorem row_works_478 : Template HasSnaky 8 required_478 envelope_478 := by
  refine compose HasSnaky 7 childrenC_478 childrenD_478 children_work_478 (2, 2)
    required_478 envelope_478 pivot_mem_478 child_required_sub_478 child_envelope_sub_478 ?_
  intro b hb
  exact common_sub_478 (mem_commonEnvelope childrenD_478 b hb)
def required_482 : Finset Cell := ⟨(([(1, 1), (1, 2), (3, 2), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_482 : Finset Cell := ⟨(([(0, 3), (0, 4), (0, 5), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 2), (3, 3), (3, 4), (4, 2), (4, 3), (5, 2), (5, 3), (6, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_482 : Fin 4 → Finset Cell := ![(placed21 1 (0, 2) required_7), (placed21 0 (1, 1) required_24), (placed21 1 (0, 1) required_124), required_472]
def childrenD_482 : Fin 4 → Finset Cell := ![(placed21 1 (0, 2) envelope_7), (placed21 0 (1, 1) envelope_24), (placed21 1 (0, 1) envelope_124), envelope_472]
theorem common_sub_482 : commonEnvelope childrenD_482 ⊆ insert (2, 2) required_482 := by decide +kernel
theorem child_required_sub_482 : ∀ j, childrenC_482 j ⊆ insert (2, 2) required_482 := by decide +kernel
theorem child_envelope_sub_482 : ∀ j, childrenD_482 j ⊆ envelope_482 := by decide +kernel
theorem pivot_mem_482 : (2, 2) ∈ envelope_482 := by decide +kernel
theorem children_work_482 : ∀ j, Template HasSnaky 7 (childrenC_482 j) (childrenD_482 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 1 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_24 0 (1, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_124 1 (0, 1)).mono (by decide +kernel)
  · exact row_works_472.mono (by decide +kernel)
theorem row_works_482 : Template HasSnaky 8 required_482 envelope_482 := by
  refine compose HasSnaky 7 childrenC_482 childrenD_482 children_work_482 (2, 2)
    required_482 envelope_482 pivot_mem_482 child_required_sub_482 child_envelope_sub_482 ?_
  intro b hb
  exact common_sub_482 (mem_commonEnvelope childrenD_482 b hb)
def required_484_i1 : Finset Cell := ⟨(([(1, 2), (1, 3), (1, 4), (1, 5), (3, 2), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_484_i1 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 2), (1, 3), (1, 4), (1, 5), (2, 1), (2, 2), (3, 2), (3, 3), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_484_i1 : Fin 2 → Finset Cell := ![(placed21 3 (1, 5) required_5), (placed21 3 (0, 5) required_96)]
def childrenD_484_i1 : Fin 2 → Finset Cell := ![(placed21 3 (1, 5) envelope_5), (placed21 3 (0, 5) envelope_96)]
theorem common_sub_484_i1 : commonEnvelope childrenD_484_i1 ⊆ insert (2, 2) required_484_i1 := by decide +kernel
theorem child_required_sub_484_i1 : ∀ j, childrenC_484_i1 j ⊆ insert (2, 2) required_484_i1 := by decide +kernel
theorem child_envelope_sub_484_i1 : ∀ j, childrenD_484_i1 j ⊆ envelope_484_i1 := by decide +kernel
theorem pivot_mem_484_i1 : (2, 2) ∈ envelope_484_i1 := by decide +kernel
theorem children_work_484_i1 : ∀ j, Template HasSnaky 2 (childrenC_484_i1 j) (childrenD_484_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 3 (1, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_96 3 (0, 5)).mono (by decide +kernel)
theorem row_works_484_i1 : Template HasSnaky 3 required_484_i1 envelope_484_i1 := by
  refine compose HasSnaky 2 childrenC_484_i1 childrenD_484_i1 children_work_484_i1 (2, 2)
    required_484_i1 envelope_484_i1 pivot_mem_484_i1 child_required_sub_484_i1 child_envelope_sub_484_i1 ?_
  intro b hb
  exact common_sub_484_i1 (mem_commonEnvelope childrenD_484_i1 b hb)
def required_484_i2 : Finset Cell := ⟨(([(3, 2), (4, 3), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_484_i2 : Finset Cell := ⟨(([(3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_484_i2 : Fin 3 → Finset Cell := ![(placed21 0 (3, 2) required_18), (placed21 4 (3, 7) required_33), (placed21 6 (4, 5) required_130)]
def childrenD_484_i2 : Fin 3 → Finset Cell := ![(placed21 0 (3, 2) envelope_18), (placed21 4 (3, 7) envelope_33), (placed21 6 (4, 5) envelope_130)]
theorem common_sub_484_i2 : commonEnvelope childrenD_484_i2 ⊆ insert (4, 4) required_484_i2 := by decide +kernel
theorem child_required_sub_484_i2 : ∀ j, childrenC_484_i2 j ⊆ insert (4, 4) required_484_i2 := by decide +kernel
theorem child_envelope_sub_484_i2 : ∀ j, childrenD_484_i2 j ⊆ envelope_484_i2 := by decide +kernel
theorem pivot_mem_484_i2 : (4, 4) ∈ envelope_484_i2 := by decide +kernel
theorem children_work_484_i2 : ∀ j, Template HasSnaky 4 (childrenC_484_i2 j) (childrenD_484_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_18 0 (3, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_33 4 (3, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_130 6 (4, 5)).mono (by decide +kernel)
theorem row_works_484_i2 : Template HasSnaky 5 required_484_i2 envelope_484_i2 := by
  refine compose HasSnaky 4 childrenC_484_i2 childrenD_484_i2 children_work_484_i2 (4, 4)
    required_484_i2 envelope_484_i2 pivot_mem_484_i2 child_required_sub_484_i2 child_envelope_sub_484_i2 ?_
  intro b hb
  exact common_sub_484_i2 (mem_commonEnvelope childrenD_484_i2 b hb)
def required_484_i4 : Finset Cell := ⟨(([(1, 2), (1, 3), (1, 4), (1, 5), (3, 2), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_484_i4 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 2), (1, 3), (1, 4), (1, 5), (2, 1), (2, 2), (3, 1), (3, 2), (4, 1), (4, 2), (5, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_484_i4 : Fin 2 → Finset Cell := ![(placed21 3 (1, 5) required_5), (placed21 3 (0, 5) required_223)]
def childrenD_484_i4 : Fin 2 → Finset Cell := ![(placed21 3 (1, 5) envelope_5), (placed21 3 (0, 5) envelope_223)]
theorem common_sub_484_i4 : commonEnvelope childrenD_484_i4 ⊆ insert (2, 2) required_484_i4 := by decide +kernel
theorem child_required_sub_484_i4 : ∀ j, childrenC_484_i4 j ⊆ insert (2, 2) required_484_i4 := by decide +kernel
theorem child_envelope_sub_484_i4 : ∀ j, childrenD_484_i4 j ⊆ envelope_484_i4 := by decide +kernel
theorem pivot_mem_484_i4 : (2, 2) ∈ envelope_484_i4 := by decide +kernel
theorem children_work_484_i4 : ∀ j, Template HasSnaky 3 (childrenC_484_i4 j) (childrenD_484_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 3 (1, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_223 3 (0, 5)).mono (by decide +kernel)
theorem row_works_484_i4 : Template HasSnaky 4 required_484_i4 envelope_484_i4 := by
  refine compose HasSnaky 3 childrenC_484_i4 childrenD_484_i4 children_work_484_i4 (2, 2)
    required_484_i4 envelope_484_i4 pivot_mem_484_i4 child_required_sub_484_i4 child_envelope_sub_484_i4 ?_
  intro b hb
  exact common_sub_484_i4 (mem_commonEnvelope childrenD_484_i4 b hb)
def required_484_i3 : Finset Cell := ⟨(([(1, 2), (1, 3), (1, 4), (1, 5), (3, 2), (4, 3), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_484_i3 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 2), (1, 3), (1, 4), (1, 5), (2, 1), (2, 2), (3, 1), (3, 2), (3, 4), (3, 5), (3, 6), (3, 7), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 0), (5, 1), (5, 2), (5, 4), (5, 5), (5, 6), (5, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_484_i3 : Fin 3 → Finset Cell := ![(placed21 0 (3, 1) required_39), (placed21 2 (5, 0) required_268), required_484_i4]
def childrenD_484_i3 : Fin 3 → Finset Cell := ![(placed21 0 (3, 1) envelope_39), (placed21 2 (5, 0) envelope_268), envelope_484_i4]
theorem common_sub_484_i3 : commonEnvelope childrenD_484_i3 ⊆ insert (4, 2) required_484_i3 := by decide +kernel
theorem child_required_sub_484_i3 : ∀ j, childrenC_484_i3 j ⊆ insert (4, 2) required_484_i3 := by decide +kernel
theorem child_envelope_sub_484_i3 : ∀ j, childrenD_484_i3 j ⊆ envelope_484_i3 := by decide +kernel
theorem pivot_mem_484_i3 : (4, 2) ∈ envelope_484_i3 := by decide +kernel
theorem children_work_484_i3 : ∀ j, Template HasSnaky 4 (childrenC_484_i3 j) (childrenD_484_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_39 0 (3, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_268 2 (5, 0)).mono (by decide +kernel)
  · exact row_works_484_i4.mono (by decide +kernel)
theorem row_works_484_i3 : Template HasSnaky 5 required_484_i3 envelope_484_i3 := by
  refine compose HasSnaky 4 childrenC_484_i3 childrenD_484_i3 children_work_484_i3 (4, 2)
    required_484_i3 envelope_484_i3 pivot_mem_484_i3 child_required_sub_484_i3 child_envelope_sub_484_i3 ?_
  intro b hb
  exact common_sub_484_i3 (mem_commonEnvelope childrenD_484_i3 b hb)
def required_484_i0 : Finset Cell := ⟨(([(1, 2), (1, 3), (1, 4), (1, 5), (4, 3), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_484_i0 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 2), (1, 3), (1, 4), (1, 5), (2, 1), (2, 2), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 0), (5, 1), (5, 2), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_484_i0 : Fin 3 → Finset Cell := ![required_484_i1, required_484_i2, required_484_i3]
def childrenD_484_i0 : Fin 3 → Finset Cell := ![envelope_484_i1, envelope_484_i2, envelope_484_i3]
theorem common_sub_484_i0 : commonEnvelope childrenD_484_i0 ⊆ insert (3, 2) required_484_i0 := by decide +kernel
theorem child_required_sub_484_i0 : ∀ j, childrenC_484_i0 j ⊆ insert (3, 2) required_484_i0 := by decide +kernel
theorem child_envelope_sub_484_i0 : ∀ j, childrenD_484_i0 j ⊆ envelope_484_i0 := by decide +kernel
theorem pivot_mem_484_i0 : (3, 2) ∈ envelope_484_i0 := by decide +kernel
theorem children_work_484_i0 : ∀ j, Template HasSnaky 5 (childrenC_484_i0 j) (childrenD_484_i0 j) := by
  intro j
  fin_cases j
  · exact row_works_484_i1.mono (by decide +kernel)
  · exact row_works_484_i2.mono (by decide +kernel)
  · exact row_works_484_i3.mono (by decide +kernel)
theorem row_works_484_i0 : Template HasSnaky 6 required_484_i0 envelope_484_i0 := by
  refine compose HasSnaky 5 childrenC_484_i0 childrenD_484_i0 children_work_484_i0 (3, 2)
    required_484_i0 envelope_484_i0 pivot_mem_484_i0 child_required_sub_484_i0 child_envelope_sub_484_i0 ?_
  intro b hb
  exact common_sub_484_i0 (mem_commonEnvelope childrenD_484_i0 b hb)
def required_484_i6 : Finset Cell := ⟨(([(1, 2), (1, 3), (1, 4), (1, 5), (2, 4), (4, 3), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_484_i6 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 4), (1, 2), (1, 3), (1, 4), (1, 5), (2, 1), (2, 2), (2, 4), (3, 1), (3, 2), (3, 3), (3, 4), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 5), (5, 6), (5, 7), (5, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_484_i6 : Fin 3 → Finset Cell := ![(placed21 0 (1, 2) required_58), (placed21 6 (5, 6) required_168), (placed21 6 (4, 5) required_357)]
def childrenD_484_i6 : Fin 3 → Finset Cell := ![(placed21 0 (1, 2) envelope_58), (placed21 6 (5, 6) envelope_168), (placed21 6 (4, 5) envelope_357)]
theorem common_sub_484_i6 : commonEnvelope childrenD_484_i6 ⊆ insert (4, 4) required_484_i6 := by decide +kernel
theorem child_required_sub_484_i6 : ∀ j, childrenC_484_i6 j ⊆ insert (4, 4) required_484_i6 := by decide +kernel
theorem child_envelope_sub_484_i6 : ∀ j, childrenD_484_i6 j ⊆ envelope_484_i6 := by decide +kernel
theorem pivot_mem_484_i6 : (4, 4) ∈ envelope_484_i6 := by decide +kernel
theorem children_work_484_i6 : ∀ j, Template HasSnaky 5 (childrenC_484_i6 j) (childrenD_484_i6 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_58 0 (1, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_168 6 (5, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_357 6 (4, 5)).mono (by decide +kernel)
theorem row_works_484_i6 : Template HasSnaky 6 required_484_i6 envelope_484_i6 := by
  refine compose HasSnaky 5 childrenC_484_i6 childrenD_484_i6 children_work_484_i6 (4, 4)
    required_484_i6 envelope_484_i6 pivot_mem_484_i6 child_required_sub_484_i6 child_envelope_sub_484_i6 ?_
  intro b hb
  exact common_sub_484_i6 (mem_commonEnvelope childrenD_484_i6 b hb)
def required_484_i5 : Finset Cell := ⟨(([(1, 2), (1, 3), (1, 4), (1, 5), (4, 3), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_484_i5 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 4), (0, 6), (0, 7), (0, 8), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, 1), (2, 2), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, 1), (3, 2), (3, 3), (3, 4), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 5), (5, 6), (5, 7), (5, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_484_i5 : Fin 2 → Finset Cell := ![(placed21 5 (2, 2) required_314), required_484_i6]
def childrenD_484_i5 : Fin 2 → Finset Cell := ![(placed21 5 (2, 2) envelope_314), envelope_484_i6]
theorem common_sub_484_i5 : commonEnvelope childrenD_484_i5 ⊆ insert (2, 4) required_484_i5 := by decide +kernel
theorem child_required_sub_484_i5 : ∀ j, childrenC_484_i5 j ⊆ insert (2, 4) required_484_i5 := by decide +kernel
theorem child_envelope_sub_484_i5 : ∀ j, childrenD_484_i5 j ⊆ envelope_484_i5 := by decide +kernel
theorem pivot_mem_484_i5 : (2, 4) ∈ envelope_484_i5 := by decide +kernel
theorem children_work_484_i5 : ∀ j, Template HasSnaky 6 (childrenC_484_i5 j) (childrenD_484_i5 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_314 5 (2, 2)).mono (by decide +kernel)
  · exact row_works_484_i6.mono (by decide +kernel)
theorem row_works_484_i5 : Template HasSnaky 7 required_484_i5 envelope_484_i5 := by
  refine compose HasSnaky 6 childrenC_484_i5 childrenD_484_i5 children_work_484_i5 (2, 4)
    required_484_i5 envelope_484_i5 pivot_mem_484_i5 child_required_sub_484_i5 child_envelope_sub_484_i5 ?_
  intro b hb
  exact common_sub_484_i5 (mem_commonEnvelope childrenD_484_i5 b hb)
def required_484 : Finset Cell := ⟨(([(1, 2), (1, 3), (1, 4), (1, 5), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_484 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 4), (0, 6), (0, 7), (0, 8), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, 1), (2, 2), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 0), (5, 1), (5, 2), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_484 : Fin 4 → Finset Cell := ![(placed21 1 (0, 2) required_81), (placed21 4 (0, 8) required_204), required_484_i0, required_484_i5]
def childrenD_484 : Fin 4 → Finset Cell := ![(placed21 1 (0, 2) envelope_81), (placed21 4 (0, 8) envelope_204), envelope_484_i0, envelope_484_i5]
theorem common_sub_484 : commonEnvelope childrenD_484 ⊆ insert (4, 5) required_484 := by decide +kernel
theorem child_required_sub_484 : ∀ j, childrenC_484 j ⊆ insert (4, 5) required_484 := by decide +kernel
theorem child_envelope_sub_484 : ∀ j, childrenD_484 j ⊆ envelope_484 := by decide +kernel
theorem pivot_mem_484 : (4, 5) ∈ envelope_484 := by decide +kernel
theorem children_work_484 : ∀ j, Template HasSnaky 7 (childrenC_484 j) (childrenD_484 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_81 1 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_204 4 (0, 8)).mono (by decide +kernel)
  · exact row_works_484_i0.mono (by decide +kernel)
  · exact row_works_484_i5.mono (by decide +kernel)
theorem row_works_484 : Template HasSnaky 8 required_484 envelope_484 := by
  refine compose HasSnaky 7 childrenC_484 childrenD_484 children_work_484 (4, 5)
    required_484 envelope_484 pivot_mem_484 child_required_sub_484 child_envelope_sub_484 ?_
  intro b hb
  exact common_sub_484 (mem_commonEnvelope childrenD_484 b hb)
def required_494 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 4), (3, 1), (3, 2), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_494 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 3), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 3), (2, 4), (2, 6), (2, 7), (2, 8), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 4), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_494 : Fin 4 → Finset Cell := ![(placed21 0 (3, 0) required_7), required_87, required_286, required_492]
def childrenD_494 : Fin 4 → Finset Cell := ![(placed21 0 (3, 0) envelope_7), envelope_87, envelope_286, envelope_492]
theorem common_sub_494 : commonEnvelope childrenD_494 ⊆ insert (3, 3) required_494 := by decide +kernel
theorem child_required_sub_494 : ∀ j, childrenC_494 j ⊆ insert (3, 3) required_494 := by decide +kernel
theorem child_envelope_sub_494 : ∀ j, childrenD_494 j ⊆ envelope_494 := by decide +kernel
theorem pivot_mem_494 : (3, 3) ∈ envelope_494 := by decide +kernel
theorem children_work_494 : ∀ j, Template HasSnaky 7 (childrenC_494 j) (childrenD_494 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 0 (3, 0)).mono (by decide +kernel)
  · exact row_works_87.mono (by decide +kernel)
  · exact row_works_286.mono (by decide +kernel)
  · exact row_works_492.mono (by decide +kernel)
theorem row_works_494 : Template HasSnaky 8 required_494 envelope_494 := by
  refine compose HasSnaky 7 childrenC_494 childrenD_494 children_work_494 (3, 3)
    required_494 envelope_494 pivot_mem_494 child_required_sub_494 child_envelope_sub_494 ?_
  intro b hb
  exact common_sub_494 (mem_commonEnvelope childrenD_494 b hb)
def required_510_i0 : Finset Cell := ⟨(([(2, 3), (2, 4), (3, 3), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_510_i0 : Finset Cell := ⟨(([(0, 4), (1, 3), (1, 4), (2, 3), (2, 4), (3, 3), (3, 4), (4, 3), (5, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_510_i0 : Fin 2 → Finset Cell := ![(placed21 2 (5, 3) required_0), (placed21 5 (4, 3) required_138)]
def childrenD_510_i0 : Fin 2 → Finset Cell := ![(placed21 2 (5, 3) envelope_0), (placed21 5 (4, 3) envelope_138)]
theorem common_sub_510_i0 : commonEnvelope childrenD_510_i0 ⊆ insert (1, 4) required_510_i0 := by decide +kernel
theorem child_required_sub_510_i0 : ∀ j, childrenC_510_i0 j ⊆ insert (1, 4) required_510_i0 := by decide +kernel
theorem child_envelope_sub_510_i0 : ∀ j, childrenD_510_i0 j ⊆ envelope_510_i0 := by decide +kernel
theorem pivot_mem_510_i0 : (1, 4) ∈ envelope_510_i0 := by decide +kernel
theorem children_work_510_i0 : ∀ j, Template HasSnaky 2 (childrenC_510_i0 j) (childrenD_510_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 2 (5, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_138 5 (4, 3)).mono (by decide +kernel)
theorem row_works_510_i0 : Template HasSnaky 3 required_510_i0 envelope_510_i0 := by
  refine compose HasSnaky 2 childrenC_510_i0 childrenD_510_i0 children_work_510_i0 (1, 4)
    required_510_i0 envelope_510_i0 pivot_mem_510_i0 child_required_sub_510_i0 child_envelope_sub_510_i0 ?_
  intro b hb
  exact common_sub_510_i0 (mem_commonEnvelope childrenD_510_i0 b hb)
def required_510 : Finset Cell := ⟨(([(2, 3), (2, 4), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_510 : Finset Cell := ⟨(([(0, 4), (1, 3), (1, 4), (2, 3), (2, 4), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 2), (6, 3), (6, 4), (7, 2), (7, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_510 : Fin 3 → Finset Cell := ![(placed21 3 (1, 4) required_10), required_510_i0, (placed21 0 (1, 0) required_507)]
def childrenD_510 : Fin 3 → Finset Cell := ![(placed21 3 (1, 4) envelope_10), envelope_510_i0, (placed21 0 (1, 0) envelope_507)]
theorem common_sub_510 : commonEnvelope childrenD_510 ⊆ insert (4, 3) required_510 := by decide +kernel
theorem child_required_sub_510 : ∀ j, childrenC_510 j ⊆ insert (4, 3) required_510 := by decide +kernel
theorem child_envelope_sub_510 : ∀ j, childrenD_510 j ⊆ envelope_510 := by decide +kernel
theorem pivot_mem_510 : (4, 3) ∈ envelope_510 := by decide +kernel
theorem children_work_510 : ∀ j, Template HasSnaky 7 (childrenC_510 j) (childrenD_510 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_10 3 (1, 4)).mono (by decide +kernel)
  · exact row_works_510_i0.mono (by decide +kernel)
  · exact (placed21_template row_works_507 0 (1, 0)).mono (by decide +kernel)
theorem row_works_510 : Template HasSnaky 8 required_510 envelope_510 := by
  refine compose HasSnaky 7 childrenC_510 childrenD_510 children_work_510 (4, 3)
    required_510 envelope_510 pivot_mem_510 child_required_sub_510 child_envelope_sub_510 ?_
  intro b hb
  exact common_sub_510 (mem_commonEnvelope childrenD_510 b hb)
def required_513_i0 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 3), (1, 4), (3, 2), (4, 1), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_513_i0 : Finset Cell := ⟨(([(0, 4), (0, 5), (1, 1), (1, 2), (1, 3), (1, 4), (2, 4), (2, 5), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 3), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_513_i0 : Fin 2 → Finset Cell := ![(placed21 5 (1, 1) required_5), (placed21 5 (5, 1) required_439)]
def childrenD_513_i0 : Fin 2 → Finset Cell := ![(placed21 5 (1, 1) envelope_5), (placed21 5 (5, 1) envelope_439)]
theorem common_sub_513_i0 : commonEnvelope childrenD_513_i0 ⊆ insert (0, 4) required_513_i0 := by decide +kernel
theorem child_required_sub_513_i0 : ∀ j, childrenC_513_i0 j ⊆ insert (0, 4) required_513_i0 := by decide +kernel
theorem child_envelope_sub_513_i0 : ∀ j, childrenD_513_i0 j ⊆ envelope_513_i0 := by decide +kernel
theorem pivot_mem_513_i0 : (0, 4) ∈ envelope_513_i0 := by decide +kernel
theorem children_work_513_i0 : ∀ j, Template HasSnaky 6 (childrenC_513_i0 j) (childrenD_513_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 5 (1, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_439 5 (5, 1)).mono (by decide +kernel)
theorem row_works_513_i0 : Template HasSnaky 7 required_513_i0 envelope_513_i0 := by
  refine compose HasSnaky 6 childrenC_513_i0 childrenD_513_i0 children_work_513_i0 (0, 4)
    required_513_i0 envelope_513_i0 pivot_mem_513_i0 child_required_sub_513_i0 child_envelope_sub_513_i0 ?_
  intro b hb
  exact common_sub_513_i0 (mem_commonEnvelope childrenD_513_i0 b hb)
def required_513 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 3), (3, 2), (4, 1), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_513 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 4), (0, 5), (0, 6), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 3), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_513 : Fin 3 → Finset Cell := ![(placed21 2 (1, 0) required_7), required_9, required_513_i0]
def childrenD_513 : Fin 3 → Finset Cell := ![(placed21 2 (1, 0) envelope_7), envelope_9, envelope_513_i0]
theorem common_sub_513 : commonEnvelope childrenD_513 ⊆ insert (1, 4) required_513 := by decide +kernel
theorem child_required_sub_513 : ∀ j, childrenC_513 j ⊆ insert (1, 4) required_513 := by decide +kernel
theorem child_envelope_sub_513 : ∀ j, childrenD_513 j ⊆ envelope_513 := by decide +kernel
theorem pivot_mem_513 : (1, 4) ∈ envelope_513 := by decide +kernel
theorem children_work_513 : ∀ j, Template HasSnaky 7 (childrenC_513 j) (childrenD_513 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 2 (1, 0)).mono (by decide +kernel)
  · exact row_works_9.mono (by decide +kernel)
  · exact row_works_513_i0.mono (by decide +kernel)
theorem row_works_513 : Template HasSnaky 8 required_513 envelope_513 := by
  refine compose HasSnaky 7 childrenC_513 childrenD_513 children_work_513 (1, 4)
    required_513 envelope_513 pivot_mem_513 child_required_sub_513 child_envelope_sub_513 ?_
  intro b hb
  exact common_sub_513 (mem_commonEnvelope childrenD_513 b hb)
def height_452_i0 : ℕ := 5
def childrenH_452_i0 : Fin 2 → ℕ := ![height_5, height_55]
theorem height_exact_452_i0 : height_452_i0 = 1 + Finset.univ.sup childrenH_452_i0 := by decide +kernel
theorem required_origin_452_i0 : ∀ x ∈ required_452_i0,
    (∃ j, x ∈ childrenC_452_i0 j) ∨ ∀ j, x ∈ childrenD_452_i0 j := by decide +kernel
theorem required_exact_452_i0 : required_452_i0 =
    ((Finset.univ.biUnion childrenC_452_i0) ∪ commonEnvelope childrenD_452_i0).erase (6, 4) := by
  exact required_eq_combination childrenC_452_i0 childrenD_452_i0 (6, 4) required_452_i0
    (by decide +kernel) child_required_sub_452_i0 common_sub_452_i0 required_origin_452_i0
theorem envelope_origin_452_i0 : ∀ x ∈ envelope_452_i0,
    x = (6, 4) ∨ ∃ j, x ∈ childrenD_452_i0 j := by decide +kernel
theorem envelope_exact_452_i0 : envelope_452_i0 =
    insert (6, 4) (Finset.univ.biUnion childrenD_452_i0) := by
  exact envelope_eq_combination childrenD_452_i0 (6, 4) envelope_452_i0
    pivot_mem_452_i0 child_envelope_sub_452_i0 envelope_origin_452_i0
def checked_452_i0 : CheckedCard where
  required := required_452_i0
  envelope := envelope_452_i0
  height := height_452_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_452_i0
def height_452 : ℕ := 8
def childrenH_452 : Fin 3 → ℕ := ![height_52, height_317, height_452_i0]
theorem height_exact_452 : height_452 = 1 + Finset.univ.sup childrenH_452 := by decide +kernel
theorem required_origin_452 : ∀ x ∈ required_452,
    (∃ j, x ∈ childrenC_452 j) ∨ ∀ j, x ∈ childrenD_452 j := by decide +kernel
theorem required_exact_452 : required_452 =
    ((Finset.univ.biUnion childrenC_452) ∪ commonEnvelope childrenD_452).erase (4, 4) := by
  exact required_eq_combination childrenC_452 childrenD_452 (4, 4) required_452
    (by decide +kernel) child_required_sub_452 common_sub_452 required_origin_452
theorem envelope_origin_452 : ∀ x ∈ envelope_452,
    x = (4, 4) ∨ ∃ j, x ∈ childrenD_452 j := by decide +kernel
theorem envelope_exact_452 : envelope_452 =
    insert (4, 4) (Finset.univ.biUnion childrenD_452) := by
  exact envelope_eq_combination childrenD_452 (4, 4) envelope_452
    pivot_mem_452 child_envelope_sub_452 envelope_origin_452
def checked_452 : CheckedCard where
  required := required_452
  envelope := envelope_452
  height := height_452
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_452
def height_454 : ℕ := 8
def childrenH_454 : Fin 2 → ℕ := ![height_5, height_453]
theorem height_exact_454 : height_454 = 1 + Finset.univ.sup childrenH_454 := by decide +kernel
theorem required_origin_454 : ∀ x ∈ required_454,
    (∃ j, x ∈ childrenC_454 j) ∨ ∀ j, x ∈ childrenD_454 j := by decide +kernel
theorem required_exact_454 : required_454 =
    ((Finset.univ.biUnion childrenC_454) ∪ commonEnvelope childrenD_454).erase (1, 3) := by
  exact required_eq_combination childrenC_454 childrenD_454 (1, 3) required_454
    (by decide +kernel) child_required_sub_454 common_sub_454 required_origin_454
theorem envelope_origin_454 : ∀ x ∈ envelope_454,
    x = (1, 3) ∨ ∃ j, x ∈ childrenD_454 j := by decide +kernel
theorem envelope_exact_454 : envelope_454 =
    insert (1, 3) (Finset.univ.biUnion childrenD_454) := by
  exact envelope_eq_combination childrenD_454 (1, 3) envelope_454
    pivot_mem_454 child_envelope_sub_454 envelope_origin_454
def checked_454 : CheckedCard where
  required := required_454
  envelope := envelope_454
  height := height_454
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_454
def height_455 : ℕ := 8
def childrenH_455 : Fin 4 → ℕ := ![height_8, height_16, height_24, height_453]
theorem height_exact_455 : height_455 = 1 + Finset.univ.sup childrenH_455 := by decide +kernel
theorem required_origin_455 : ∀ x ∈ required_455,
    (∃ j, x ∈ childrenC_455 j) ∨ ∀ j, x ∈ childrenD_455 j := by decide +kernel
theorem required_exact_455 : required_455 =
    ((Finset.univ.biUnion childrenC_455) ∪ commonEnvelope childrenD_455).erase (1, 1) := by
  exact required_eq_combination childrenC_455 childrenD_455 (1, 1) required_455
    (by decide +kernel) child_required_sub_455 common_sub_455 required_origin_455
theorem envelope_origin_455 : ∀ x ∈ envelope_455,
    x = (1, 1) ∨ ∃ j, x ∈ childrenD_455 j := by decide +kernel
theorem envelope_exact_455 : envelope_455 =
    insert (1, 1) (Finset.univ.biUnion childrenD_455) := by
  exact envelope_eq_combination childrenD_455 (1, 1) envelope_455
    pivot_mem_455 child_envelope_sub_455 envelope_origin_455
def checked_455 : CheckedCard where
  required := required_455
  envelope := envelope_455
  height := height_455
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_455
def height_456 : ℕ := 8
def childrenH_456 : Fin 2 → ℕ := ![height_5, height_453]
theorem height_exact_456 : height_456 = 1 + Finset.univ.sup childrenH_456 := by decide +kernel
theorem required_origin_456 : ∀ x ∈ required_456,
    (∃ j, x ∈ childrenC_456 j) ∨ ∀ j, x ∈ childrenD_456 j := by decide +kernel
theorem required_exact_456 : required_456 =
    ((Finset.univ.biUnion childrenC_456) ∪ commonEnvelope childrenD_456).erase (2, 4) := by
  exact required_eq_combination childrenC_456 childrenD_456 (2, 4) required_456
    (by decide +kernel) child_required_sub_456 common_sub_456 required_origin_456
theorem envelope_origin_456 : ∀ x ∈ envelope_456,
    x = (2, 4) ∨ ∃ j, x ∈ childrenD_456 j := by decide +kernel
theorem envelope_exact_456 : envelope_456 =
    insert (2, 4) (Finset.univ.biUnion childrenD_456) := by
  exact envelope_eq_combination childrenD_456 (2, 4) envelope_456
    pivot_mem_456 child_envelope_sub_456 envelope_origin_456
def checked_456 : CheckedCard where
  required := required_456
  envelope := envelope_456
  height := height_456
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_456
def height_473 : ℕ := 8
def childrenH_473 : Fin 2 → ℕ := ![height_5, height_472]
theorem height_exact_473 : height_473 = 1 + Finset.univ.sup childrenH_473 := by decide +kernel
theorem required_origin_473 : ∀ x ∈ required_473,
    (∃ j, x ∈ childrenC_473 j) ∨ ∀ j, x ∈ childrenD_473 j := by decide +kernel
theorem required_exact_473 : required_473 =
    ((Finset.univ.biUnion childrenC_473) ∪ commonEnvelope childrenD_473).erase (1, 1) := by
  exact required_eq_combination childrenC_473 childrenD_473 (1, 1) required_473
    (by decide +kernel) child_required_sub_473 common_sub_473 required_origin_473
theorem envelope_origin_473 : ∀ x ∈ envelope_473,
    x = (1, 1) ∨ ∃ j, x ∈ childrenD_473 j := by decide +kernel
theorem envelope_exact_473 : envelope_473 =
    insert (1, 1) (Finset.univ.biUnion childrenD_473) := by
  exact envelope_eq_combination childrenD_473 (1, 1) envelope_473
    pivot_mem_473 child_envelope_sub_473 envelope_origin_473
def checked_473 : CheckedCard where
  required := required_473
  envelope := envelope_473
  height := height_473
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_473
def height_478 : ℕ := 8
def childrenH_478 : Fin 2 → ℕ := ![height_5, height_472]
theorem height_exact_478 : height_478 = 1 + Finset.univ.sup childrenH_478 := by decide +kernel
theorem required_origin_478 : ∀ x ∈ required_478,
    (∃ j, x ∈ childrenC_478 j) ∨ ∀ j, x ∈ childrenD_478 j := by decide +kernel
theorem required_exact_478 : required_478 =
    ((Finset.univ.biUnion childrenC_478) ∪ commonEnvelope childrenD_478).erase (2, 2) := by
  exact required_eq_combination childrenC_478 childrenD_478 (2, 2) required_478
    (by decide +kernel) child_required_sub_478 common_sub_478 required_origin_478
theorem envelope_origin_478 : ∀ x ∈ envelope_478,
    x = (2, 2) ∨ ∃ j, x ∈ childrenD_478 j := by decide +kernel
theorem envelope_exact_478 : envelope_478 =
    insert (2, 2) (Finset.univ.biUnion childrenD_478) := by
  exact envelope_eq_combination childrenD_478 (2, 2) envelope_478
    pivot_mem_478 child_envelope_sub_478 envelope_origin_478
def checked_478 : CheckedCard where
  required := required_478
  envelope := envelope_478
  height := height_478
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_478
def height_482 : ℕ := 8
def childrenH_482 : Fin 4 → ℕ := ![height_7, height_24, height_124, height_472]
theorem height_exact_482 : height_482 = 1 + Finset.univ.sup childrenH_482 := by decide +kernel
theorem required_origin_482 : ∀ x ∈ required_482,
    (∃ j, x ∈ childrenC_482 j) ∨ ∀ j, x ∈ childrenD_482 j := by decide +kernel
theorem required_exact_482 : required_482 =
    ((Finset.univ.biUnion childrenC_482) ∪ commonEnvelope childrenD_482).erase (2, 2) := by
  exact required_eq_combination childrenC_482 childrenD_482 (2, 2) required_482
    (by decide +kernel) child_required_sub_482 common_sub_482 required_origin_482
theorem envelope_origin_482 : ∀ x ∈ envelope_482,
    x = (2, 2) ∨ ∃ j, x ∈ childrenD_482 j := by decide +kernel
theorem envelope_exact_482 : envelope_482 =
    insert (2, 2) (Finset.univ.biUnion childrenD_482) := by
  exact envelope_eq_combination childrenD_482 (2, 2) envelope_482
    pivot_mem_482 child_envelope_sub_482 envelope_origin_482
def checked_482 : CheckedCard where
  required := required_482
  envelope := envelope_482
  height := height_482
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_482
def height_484_i1 : ℕ := 3
def childrenH_484_i1 : Fin 2 → ℕ := ![height_5, height_96]
theorem height_exact_484_i1 : height_484_i1 = 1 + Finset.univ.sup childrenH_484_i1 := by decide +kernel
theorem required_origin_484_i1 : ∀ x ∈ required_484_i1,
    (∃ j, x ∈ childrenC_484_i1 j) ∨ ∀ j, x ∈ childrenD_484_i1 j := by decide +kernel
theorem required_exact_484_i1 : required_484_i1 =
    ((Finset.univ.biUnion childrenC_484_i1) ∪ commonEnvelope childrenD_484_i1).erase (2, 2) := by
  exact required_eq_combination childrenC_484_i1 childrenD_484_i1 (2, 2) required_484_i1
    (by decide +kernel) child_required_sub_484_i1 common_sub_484_i1 required_origin_484_i1
theorem envelope_origin_484_i1 : ∀ x ∈ envelope_484_i1,
    x = (2, 2) ∨ ∃ j, x ∈ childrenD_484_i1 j := by decide +kernel
theorem envelope_exact_484_i1 : envelope_484_i1 =
    insert (2, 2) (Finset.univ.biUnion childrenD_484_i1) := by
  exact envelope_eq_combination childrenD_484_i1 (2, 2) envelope_484_i1
    pivot_mem_484_i1 child_envelope_sub_484_i1 envelope_origin_484_i1
def checked_484_i1 : CheckedCard where
  required := required_484_i1
  envelope := envelope_484_i1
  height := height_484_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_484_i1
def height_484_i2 : ℕ := 5
def childrenH_484_i2 : Fin 3 → ℕ := ![height_18, height_33, height_130]
theorem height_exact_484_i2 : height_484_i2 = 1 + Finset.univ.sup childrenH_484_i2 := by decide +kernel
theorem required_origin_484_i2 : ∀ x ∈ required_484_i2,
    (∃ j, x ∈ childrenC_484_i2 j) ∨ ∀ j, x ∈ childrenD_484_i2 j := by decide +kernel
theorem required_exact_484_i2 : required_484_i2 =
    ((Finset.univ.biUnion childrenC_484_i2) ∪ commonEnvelope childrenD_484_i2).erase (4, 4) := by
  exact required_eq_combination childrenC_484_i2 childrenD_484_i2 (4, 4) required_484_i2
    (by decide +kernel) child_required_sub_484_i2 common_sub_484_i2 required_origin_484_i2
theorem envelope_origin_484_i2 : ∀ x ∈ envelope_484_i2,
    x = (4, 4) ∨ ∃ j, x ∈ childrenD_484_i2 j := by decide +kernel
theorem envelope_exact_484_i2 : envelope_484_i2 =
    insert (4, 4) (Finset.univ.biUnion childrenD_484_i2) := by
  exact envelope_eq_combination childrenD_484_i2 (4, 4) envelope_484_i2
    pivot_mem_484_i2 child_envelope_sub_484_i2 envelope_origin_484_i2
def checked_484_i2 : CheckedCard where
  required := required_484_i2
  envelope := envelope_484_i2
  height := height_484_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_484_i2
def height_484_i4 : ℕ := 4
def childrenH_484_i4 : Fin 2 → ℕ := ![height_5, height_223]
theorem height_exact_484_i4 : height_484_i4 = 1 + Finset.univ.sup childrenH_484_i4 := by decide +kernel
theorem required_origin_484_i4 : ∀ x ∈ required_484_i4,
    (∃ j, x ∈ childrenC_484_i4 j) ∨ ∀ j, x ∈ childrenD_484_i4 j := by decide +kernel
theorem required_exact_484_i4 : required_484_i4 =
    ((Finset.univ.biUnion childrenC_484_i4) ∪ commonEnvelope childrenD_484_i4).erase (2, 2) := by
  exact required_eq_combination childrenC_484_i4 childrenD_484_i4 (2, 2) required_484_i4
    (by decide +kernel) child_required_sub_484_i4 common_sub_484_i4 required_origin_484_i4
theorem envelope_origin_484_i4 : ∀ x ∈ envelope_484_i4,
    x = (2, 2) ∨ ∃ j, x ∈ childrenD_484_i4 j := by decide +kernel
theorem envelope_exact_484_i4 : envelope_484_i4 =
    insert (2, 2) (Finset.univ.biUnion childrenD_484_i4) := by
  exact envelope_eq_combination childrenD_484_i4 (2, 2) envelope_484_i4
    pivot_mem_484_i4 child_envelope_sub_484_i4 envelope_origin_484_i4
def checked_484_i4 : CheckedCard where
  required := required_484_i4
  envelope := envelope_484_i4
  height := height_484_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_484_i4
def height_484_i3 : ℕ := 5
def childrenH_484_i3 : Fin 3 → ℕ := ![height_39, height_268, height_484_i4]
theorem height_exact_484_i3 : height_484_i3 = 1 + Finset.univ.sup childrenH_484_i3 := by decide +kernel
theorem required_origin_484_i3 : ∀ x ∈ required_484_i3,
    (∃ j, x ∈ childrenC_484_i3 j) ∨ ∀ j, x ∈ childrenD_484_i3 j := by decide +kernel
theorem required_exact_484_i3 : required_484_i3 =
    ((Finset.univ.biUnion childrenC_484_i3) ∪ commonEnvelope childrenD_484_i3).erase (4, 2) := by
  exact required_eq_combination childrenC_484_i3 childrenD_484_i3 (4, 2) required_484_i3
    (by decide +kernel) child_required_sub_484_i3 common_sub_484_i3 required_origin_484_i3
theorem envelope_origin_484_i3 : ∀ x ∈ envelope_484_i3,
    x = (4, 2) ∨ ∃ j, x ∈ childrenD_484_i3 j := by decide +kernel
theorem envelope_exact_484_i3 : envelope_484_i3 =
    insert (4, 2) (Finset.univ.biUnion childrenD_484_i3) := by
  exact envelope_eq_combination childrenD_484_i3 (4, 2) envelope_484_i3
    pivot_mem_484_i3 child_envelope_sub_484_i3 envelope_origin_484_i3
def checked_484_i3 : CheckedCard where
  required := required_484_i3
  envelope := envelope_484_i3
  height := height_484_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_484_i3
def height_484_i0 : ℕ := 6
def childrenH_484_i0 : Fin 3 → ℕ := ![height_484_i1, height_484_i2, height_484_i3]
theorem height_exact_484_i0 : height_484_i0 = 1 + Finset.univ.sup childrenH_484_i0 := by decide +kernel
theorem required_origin_484_i0 : ∀ x ∈ required_484_i0,
    (∃ j, x ∈ childrenC_484_i0 j) ∨ ∀ j, x ∈ childrenD_484_i0 j := by decide +kernel
theorem required_exact_484_i0 : required_484_i0 =
    ((Finset.univ.biUnion childrenC_484_i0) ∪ commonEnvelope childrenD_484_i0).erase (3, 2) := by
  exact required_eq_combination childrenC_484_i0 childrenD_484_i0 (3, 2) required_484_i0
    (by decide +kernel) child_required_sub_484_i0 common_sub_484_i0 required_origin_484_i0
theorem envelope_origin_484_i0 : ∀ x ∈ envelope_484_i0,
    x = (3, 2) ∨ ∃ j, x ∈ childrenD_484_i0 j := by decide +kernel
theorem envelope_exact_484_i0 : envelope_484_i0 =
    insert (3, 2) (Finset.univ.biUnion childrenD_484_i0) := by
  exact envelope_eq_combination childrenD_484_i0 (3, 2) envelope_484_i0
    pivot_mem_484_i0 child_envelope_sub_484_i0 envelope_origin_484_i0
def checked_484_i0 : CheckedCard where
  required := required_484_i0
  envelope := envelope_484_i0
  height := height_484_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_484_i0
def height_484_i6 : ℕ := 6
def childrenH_484_i6 : Fin 3 → ℕ := ![height_58, height_168, height_357]
theorem height_exact_484_i6 : height_484_i6 = 1 + Finset.univ.sup childrenH_484_i6 := by decide +kernel
theorem required_origin_484_i6 : ∀ x ∈ required_484_i6,
    (∃ j, x ∈ childrenC_484_i6 j) ∨ ∀ j, x ∈ childrenD_484_i6 j := by decide +kernel
theorem required_exact_484_i6 : required_484_i6 =
    ((Finset.univ.biUnion childrenC_484_i6) ∪ commonEnvelope childrenD_484_i6).erase (4, 4) := by
  exact required_eq_combination childrenC_484_i6 childrenD_484_i6 (4, 4) required_484_i6
    (by decide +kernel) child_required_sub_484_i6 common_sub_484_i6 required_origin_484_i6
theorem envelope_origin_484_i6 : ∀ x ∈ envelope_484_i6,
    x = (4, 4) ∨ ∃ j, x ∈ childrenD_484_i6 j := by decide +kernel
theorem envelope_exact_484_i6 : envelope_484_i6 =
    insert (4, 4) (Finset.univ.biUnion childrenD_484_i6) := by
  exact envelope_eq_combination childrenD_484_i6 (4, 4) envelope_484_i6
    pivot_mem_484_i6 child_envelope_sub_484_i6 envelope_origin_484_i6
def checked_484_i6 : CheckedCard where
  required := required_484_i6
  envelope := envelope_484_i6
  height := height_484_i6
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_484_i6
def height_484_i5 : ℕ := 7
def childrenH_484_i5 : Fin 2 → ℕ := ![height_314, height_484_i6]
theorem height_exact_484_i5 : height_484_i5 = 1 + Finset.univ.sup childrenH_484_i5 := by decide +kernel
theorem required_origin_484_i5 : ∀ x ∈ required_484_i5,
    (∃ j, x ∈ childrenC_484_i5 j) ∨ ∀ j, x ∈ childrenD_484_i5 j := by decide +kernel
theorem required_exact_484_i5 : required_484_i5 =
    ((Finset.univ.biUnion childrenC_484_i5) ∪ commonEnvelope childrenD_484_i5).erase (2, 4) := by
  exact required_eq_combination childrenC_484_i5 childrenD_484_i5 (2, 4) required_484_i5
    (by decide +kernel) child_required_sub_484_i5 common_sub_484_i5 required_origin_484_i5
theorem envelope_origin_484_i5 : ∀ x ∈ envelope_484_i5,
    x = (2, 4) ∨ ∃ j, x ∈ childrenD_484_i5 j := by decide +kernel
theorem envelope_exact_484_i5 : envelope_484_i5 =
    insert (2, 4) (Finset.univ.biUnion childrenD_484_i5) := by
  exact envelope_eq_combination childrenD_484_i5 (2, 4) envelope_484_i5
    pivot_mem_484_i5 child_envelope_sub_484_i5 envelope_origin_484_i5
def checked_484_i5 : CheckedCard where
  required := required_484_i5
  envelope := envelope_484_i5
  height := height_484_i5
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_484_i5
def height_484 : ℕ := 8
def childrenH_484 : Fin 4 → ℕ := ![height_81, height_204, height_484_i0, height_484_i5]
theorem height_exact_484 : height_484 = 1 + Finset.univ.sup childrenH_484 := by decide +kernel
theorem required_origin_484 : ∀ x ∈ required_484,
    (∃ j, x ∈ childrenC_484 j) ∨ ∀ j, x ∈ childrenD_484 j := by decide +kernel
theorem required_exact_484 : required_484 =
    ((Finset.univ.biUnion childrenC_484) ∪ commonEnvelope childrenD_484).erase (4, 5) := by
  exact required_eq_combination childrenC_484 childrenD_484 (4, 5) required_484
    (by decide +kernel) child_required_sub_484 common_sub_484 required_origin_484
theorem envelope_origin_484 : ∀ x ∈ envelope_484,
    x = (4, 5) ∨ ∃ j, x ∈ childrenD_484 j := by decide +kernel
theorem envelope_exact_484 : envelope_484 =
    insert (4, 5) (Finset.univ.biUnion childrenD_484) := by
  exact envelope_eq_combination childrenD_484 (4, 5) envelope_484
    pivot_mem_484 child_envelope_sub_484 envelope_origin_484
def checked_484 : CheckedCard where
  required := required_484
  envelope := envelope_484
  height := height_484
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_484
def height_494 : ℕ := 8
def childrenH_494 : Fin 4 → ℕ := ![height_7, height_87, height_286, height_492]
theorem height_exact_494 : height_494 = 1 + Finset.univ.sup childrenH_494 := by decide +kernel
theorem required_origin_494 : ∀ x ∈ required_494,
    (∃ j, x ∈ childrenC_494 j) ∨ ∀ j, x ∈ childrenD_494 j := by decide +kernel
theorem required_exact_494 : required_494 =
    ((Finset.univ.biUnion childrenC_494) ∪ commonEnvelope childrenD_494).erase (3, 3) := by
  exact required_eq_combination childrenC_494 childrenD_494 (3, 3) required_494
    (by decide +kernel) child_required_sub_494 common_sub_494 required_origin_494
theorem envelope_origin_494 : ∀ x ∈ envelope_494,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_494 j := by decide +kernel
theorem envelope_exact_494 : envelope_494 =
    insert (3, 3) (Finset.univ.biUnion childrenD_494) := by
  exact envelope_eq_combination childrenD_494 (3, 3) envelope_494
    pivot_mem_494 child_envelope_sub_494 envelope_origin_494
def checked_494 : CheckedCard where
  required := required_494
  envelope := envelope_494
  height := height_494
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_494
def height_510_i0 : ℕ := 3
def childrenH_510_i0 : Fin 2 → ℕ := ![height_0, height_138]
theorem height_exact_510_i0 : height_510_i0 = 1 + Finset.univ.sup childrenH_510_i0 := by decide +kernel
theorem required_origin_510_i0 : ∀ x ∈ required_510_i0,
    (∃ j, x ∈ childrenC_510_i0 j) ∨ ∀ j, x ∈ childrenD_510_i0 j := by decide +kernel
theorem required_exact_510_i0 : required_510_i0 =
    ((Finset.univ.biUnion childrenC_510_i0) ∪ commonEnvelope childrenD_510_i0).erase (1, 4) := by
  exact required_eq_combination childrenC_510_i0 childrenD_510_i0 (1, 4) required_510_i0
    (by decide +kernel) child_required_sub_510_i0 common_sub_510_i0 required_origin_510_i0
theorem envelope_origin_510_i0 : ∀ x ∈ envelope_510_i0,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_510_i0 j := by decide +kernel
theorem envelope_exact_510_i0 : envelope_510_i0 =
    insert (1, 4) (Finset.univ.biUnion childrenD_510_i0) := by
  exact envelope_eq_combination childrenD_510_i0 (1, 4) envelope_510_i0
    pivot_mem_510_i0 child_envelope_sub_510_i0 envelope_origin_510_i0
def checked_510_i0 : CheckedCard where
  required := required_510_i0
  envelope := envelope_510_i0
  height := height_510_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_510_i0
def height_510 : ℕ := 8
def childrenH_510 : Fin 3 → ℕ := ![height_10, height_510_i0, height_507]
theorem height_exact_510 : height_510 = 1 + Finset.univ.sup childrenH_510 := by decide +kernel
theorem required_origin_510 : ∀ x ∈ required_510,
    (∃ j, x ∈ childrenC_510 j) ∨ ∀ j, x ∈ childrenD_510 j := by decide +kernel
theorem required_exact_510 : required_510 =
    ((Finset.univ.biUnion childrenC_510) ∪ commonEnvelope childrenD_510).erase (4, 3) := by
  exact required_eq_combination childrenC_510 childrenD_510 (4, 3) required_510
    (by decide +kernel) child_required_sub_510 common_sub_510 required_origin_510
theorem envelope_origin_510 : ∀ x ∈ envelope_510,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_510 j := by decide +kernel
theorem envelope_exact_510 : envelope_510 =
    insert (4, 3) (Finset.univ.biUnion childrenD_510) := by
  exact envelope_eq_combination childrenD_510 (4, 3) envelope_510
    pivot_mem_510 child_envelope_sub_510 envelope_origin_510
def checked_510 : CheckedCard where
  required := required_510
  envelope := envelope_510
  height := height_510
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_510
def height_513_i0 : ℕ := 7
def childrenH_513_i0 : Fin 2 → ℕ := ![height_5, height_439]
theorem height_exact_513_i0 : height_513_i0 = 1 + Finset.univ.sup childrenH_513_i0 := by decide +kernel
theorem required_origin_513_i0 : ∀ x ∈ required_513_i0,
    (∃ j, x ∈ childrenC_513_i0 j) ∨ ∀ j, x ∈ childrenD_513_i0 j := by decide +kernel
theorem required_exact_513_i0 : required_513_i0 =
    ((Finset.univ.biUnion childrenC_513_i0) ∪ commonEnvelope childrenD_513_i0).erase (0, 4) := by
  exact required_eq_combination childrenC_513_i0 childrenD_513_i0 (0, 4) required_513_i0
    (by decide +kernel) child_required_sub_513_i0 common_sub_513_i0 required_origin_513_i0
theorem envelope_origin_513_i0 : ∀ x ∈ envelope_513_i0,
    x = (0, 4) ∨ ∃ j, x ∈ childrenD_513_i0 j := by decide +kernel
theorem envelope_exact_513_i0 : envelope_513_i0 =
    insert (0, 4) (Finset.univ.biUnion childrenD_513_i0) := by
  exact envelope_eq_combination childrenD_513_i0 (0, 4) envelope_513_i0
    pivot_mem_513_i0 child_envelope_sub_513_i0 envelope_origin_513_i0
def checked_513_i0 : CheckedCard where
  required := required_513_i0
  envelope := envelope_513_i0
  height := height_513_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_513_i0
def height_513 : ℕ := 8
def childrenH_513 : Fin 3 → ℕ := ![height_7, height_9, height_513_i0]
theorem height_exact_513 : height_513 = 1 + Finset.univ.sup childrenH_513 := by decide +kernel
theorem required_origin_513 : ∀ x ∈ required_513,
    (∃ j, x ∈ childrenC_513 j) ∨ ∀ j, x ∈ childrenD_513 j := by decide +kernel
theorem required_exact_513 : required_513 =
    ((Finset.univ.biUnion childrenC_513) ∪ commonEnvelope childrenD_513).erase (1, 4) := by
  exact required_eq_combination childrenC_513 childrenD_513 (1, 4) required_513
    (by decide +kernel) child_required_sub_513 common_sub_513 required_origin_513
theorem envelope_origin_513 : ∀ x ∈ envelope_513,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_513 j := by decide +kernel
theorem envelope_exact_513 : envelope_513 =
    insert (1, 4) (Finset.univ.biUnion childrenD_513) := by
  exact envelope_eq_combination childrenD_513 (1, 4) envelope_513
    pivot_mem_513 child_envelope_sub_513 envelope_origin_513
def checked_513 : CheckedCard where
  required := required_513
  envelope := envelope_513
  height := height_513
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_513
end SnakyPrototype.Certificate21

end OAI
