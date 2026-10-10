import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part06
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part05
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_447_i0 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 3), (1, 4), (2, 2), (2, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_447_i0 : Finset Cell := ⟨(([(0, 4), (0, 5), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, 2), (2, 3), (2, 4), (3, 3), (3, 4), (3, 5), (3, 6), (4, 3), (4, 4), (4, 5), (5, 3), (5, 4), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_447_i0 : Fin 2 → Finset Cell := ![(placed21 1 (1, 0) required_0), (placed21 1 (0, 1) required_445)]
def childrenD_447_i0 : Fin 2 → Finset Cell := ![(placed21 1 (1, 0) envelope_0), (placed21 1 (0, 1) envelope_445)]
theorem common_sub_447_i0 : commonEnvelope childrenD_447_i0 ⊆ insert (2, 3) required_447_i0 := by decide +kernel
theorem child_required_sub_447_i0 : ∀ j, childrenC_447_i0 j ⊆ insert (2, 3) required_447_i0 := by decide +kernel
theorem child_envelope_sub_447_i0 : ∀ j, childrenD_447_i0 j ⊆ envelope_447_i0 := by decide +kernel
theorem pivot_mem_447_i0 : (2, 3) ∈ envelope_447_i0 := by decide +kernel
theorem children_work_447_i0 : ∀ j, Template HasSnaky 5 (childrenC_447_i0 j) (childrenD_447_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 1 (1, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_445 1 (0, 1)).mono (by decide +kernel)
theorem row_works_447_i0 : Template HasSnaky 6 required_447_i0 envelope_447_i0 := by
  refine compose HasSnaky 5 childrenC_447_i0 childrenD_447_i0 children_work_447_i0 (2, 3)
    required_447_i0 envelope_447_i0 pivot_mem_447_i0 child_required_sub_447_i0 child_envelope_sub_447_i0 ?_
  intro b hb
  exact common_sub_447_i0 (mem_commonEnvelope childrenD_447_i0 b hb)
def required_447 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 3), (1, 4), (2, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_447 : Finset Cell := ⟨(([(0, 4), (0, 5), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, 2), (2, 3), (2, 4), (2, 5), (3, 3), (3, 4), (3, 5), (3, 6), (4, 3), (4, 4), (4, 5), (5, 3), (5, 4), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_447 : Fin 2 → Finset Cell := ![(placed21 1 (1, 1) required_5), required_447_i0]
def childrenD_447 : Fin 2 → Finset Cell := ![(placed21 1 (1, 1) envelope_5), envelope_447_i0]
theorem common_sub_447 : commonEnvelope childrenD_447 ⊆ insert (2, 4) required_447 := by decide +kernel
theorem child_required_sub_447 : ∀ j, childrenC_447 j ⊆ insert (2, 4) required_447 := by decide +kernel
theorem child_envelope_sub_447 : ∀ j, childrenD_447 j ⊆ envelope_447 := by decide +kernel
theorem pivot_mem_447 : (2, 4) ∈ envelope_447 := by decide +kernel
theorem children_work_447 : ∀ j, Template HasSnaky 6 (childrenC_447 j) (childrenD_447 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 1 (1, 1)).mono (by decide +kernel)
  · exact row_works_447_i0.mono (by decide +kernel)
theorem row_works_447 : Template HasSnaky 7 required_447 envelope_447 := by
  refine compose HasSnaky 6 childrenC_447 childrenD_447 children_work_447 (2, 4)
    required_447 envelope_447 pivot_mem_447 child_required_sub_447 child_envelope_sub_447 ?_
  intro b hb
  exact common_sub_447 (mem_commonEnvelope childrenD_447 b hb)
def required_453_i1 : Finset Cell := ⟨(([(0, 2), (2, 1), (3, 0), (3, 1), (3, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_453_i1 : Finset Cell := ⟨(([(0, 2), (1, 2), (1, 3), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 3), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_453_i1 : Fin 3 → Finset Cell := ![(placed21 2 (3, 0) required_21), (placed21 0 (2, 0) required_37), (placed21 5 (4, 0) required_354)]
def childrenD_453_i1 : Fin 3 → Finset Cell := ![(placed21 2 (3, 0) envelope_21), (placed21 0 (2, 0) envelope_37), (placed21 5 (4, 0) envelope_354)]
theorem common_sub_453_i1 : commonEnvelope childrenD_453_i1 ⊆ insert (3, 3) required_453_i1 := by decide +kernel
theorem child_required_sub_453_i1 : ∀ j, childrenC_453_i1 j ⊆ insert (3, 3) required_453_i1 := by decide +kernel
theorem child_envelope_sub_453_i1 : ∀ j, childrenD_453_i1 j ⊆ envelope_453_i1 := by decide +kernel
theorem pivot_mem_453_i1 : (3, 3) ∈ envelope_453_i1 := by decide +kernel
theorem children_work_453_i1 : ∀ j, Template HasSnaky 4 (childrenC_453_i1 j) (childrenD_453_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_21 2 (3, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_37 0 (2, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_354 5 (4, 0)).mono (by decide +kernel)
theorem row_works_453_i1 : Template HasSnaky 5 required_453_i1 envelope_453_i1 := by
  refine compose HasSnaky 4 childrenC_453_i1 childrenD_453_i1 children_work_453_i1 (3, 3)
    required_453_i1 envelope_453_i1 pivot_mem_453_i1 child_required_sub_453_i1 child_envelope_sub_453_i1 ?_
  intro b hb
  exact common_sub_453_i1 (mem_commonEnvelope childrenD_453_i1 b hb)
def required_453_i0 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 1), (2, 1), (3, 1), (3, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_453_i0 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 1), (1, 2), (1, 3), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 0), (4, 3), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_453_i0 : Fin 2 → Finset Cell := ![(placed21 4 (0, 1) required_5), required_453_i1]
def childrenD_453_i0 : Fin 2 → Finset Cell := ![(placed21 4 (0, 1) envelope_5), envelope_453_i1]
theorem common_sub_453_i0 : commonEnvelope childrenD_453_i0 ⊆ insert (3, 0) required_453_i0 := by decide +kernel
theorem child_required_sub_453_i0 : ∀ j, childrenC_453_i0 j ⊆ insert (3, 0) required_453_i0 := by decide +kernel
theorem child_envelope_sub_453_i0 : ∀ j, childrenD_453_i0 j ⊆ envelope_453_i0 := by decide +kernel
theorem pivot_mem_453_i0 : (3, 0) ∈ envelope_453_i0 := by decide +kernel
theorem children_work_453_i0 : ∀ j, Template HasSnaky 5 (childrenC_453_i0 j) (childrenD_453_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 4 (0, 1)).mono (by decide +kernel)
  · exact row_works_453_i1.mono (by decide +kernel)
theorem row_works_453_i0 : Template HasSnaky 6 required_453_i0 envelope_453_i0 := by
  refine compose HasSnaky 5 childrenC_453_i0 childrenD_453_i0 children_work_453_i0 (3, 0)
    required_453_i0 envelope_453_i0 pivot_mem_453_i0 child_required_sub_453_i0 child_envelope_sub_453_i0 ?_
  intro b hb
  exact common_sub_453_i0 (mem_commonEnvelope childrenD_453_i0 b hb)
def required_453 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 1), (2, 1), (3, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_453 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 1), (1, 2), (1, 3), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 0), (4, 2), (4, 3), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_453 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) required_5), required_453_i0]
def childrenD_453 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) envelope_5), envelope_453_i0]
theorem common_sub_453 : commonEnvelope childrenD_453 ⊆ insert (3, 2) required_453 := by decide +kernel
theorem child_required_sub_453 : ∀ j, childrenC_453 j ⊆ insert (3, 2) required_453 := by decide +kernel
theorem child_envelope_sub_453 : ∀ j, childrenD_453 j ⊆ envelope_453 := by decide +kernel
theorem pivot_mem_453 : (3, 2) ∈ envelope_453 := by decide +kernel
theorem children_work_453 : ∀ j, Template HasSnaky 6 (childrenC_453 j) (childrenD_453 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 0 (0, 1)).mono (by decide +kernel)
  · exact row_works_453_i0.mono (by decide +kernel)
theorem row_works_453 : Template HasSnaky 7 required_453 envelope_453 := by
  refine compose HasSnaky 6 childrenC_453 childrenD_453 children_work_453 (3, 2)
    required_453 envelope_453 pivot_mem_453 child_required_sub_453 child_envelope_sub_453 ?_
  intro b hb
  exact common_sub_453 (mem_commonEnvelope childrenD_453 b hb)
def required_466 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 3), (4, 2), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_466 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 4), (0, 5), (0, 6), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 2), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 5), (5, 6), (5, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_466 : Fin 4 → Finset Cell := ![(placed21 2 (1, 0) required_7), (placed21 1 (0, 1) required_8), required_9, required_465]
def childrenD_466 : Fin 4 → Finset Cell := ![(placed21 2 (1, 0) envelope_7), (placed21 1 (0, 1) envelope_8), envelope_9, envelope_465]
theorem common_sub_466 : commonEnvelope childrenD_466 ⊆ insert (1, 4) required_466 := by decide +kernel
theorem child_required_sub_466 : ∀ j, childrenC_466 j ⊆ insert (1, 4) required_466 := by decide +kernel
theorem child_envelope_sub_466 : ∀ j, childrenD_466 j ⊆ envelope_466 := by decide +kernel
theorem pivot_mem_466 : (1, 4) ∈ envelope_466 := by decide +kernel
theorem children_work_466 : ∀ j, Template HasSnaky 6 (childrenC_466 j) (childrenD_466 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 2 (1, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_8 1 (0, 1)).mono (by decide +kernel)
  · exact row_works_9.mono (by decide +kernel)
  · exact row_works_465.mono (by decide +kernel)
theorem row_works_466 : Template HasSnaky 7 required_466 envelope_466 := by
  refine compose HasSnaky 6 childrenC_466 childrenD_466 children_work_466 (1, 4)
    required_466 envelope_466 pivot_mem_466 child_required_sub_466 child_envelope_sub_466 ?_
  intro b hb
  exact common_sub_466 (mem_commonEnvelope childrenD_466 b hb)
def required_469_i0 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 3), (1, 4), (3, 2), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_469_i0 : Finset Cell := ⟨(([(0, 3), (0, 5), (0, 6), (0, 7), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 2), (3, 3), (4, 2), (4, 3), (5, 2), (6, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_469_i0 : Fin 2 → Finset Cell := ![(placed21 3 (0, 3) required_101), (placed21 5 (2, 1) required_314)]
def childrenD_469_i0 : Fin 2 → Finset Cell := ![(placed21 3 (0, 3) envelope_101), (placed21 5 (2, 1) envelope_314)]
theorem common_sub_469_i0 : commonEnvelope childrenD_469_i0 ⊆ insert (2, 3) required_469_i0 := by decide +kernel
theorem child_required_sub_469_i0 : ∀ j, childrenC_469_i0 j ⊆ insert (2, 3) required_469_i0 := by decide +kernel
theorem child_envelope_sub_469_i0 : ∀ j, childrenD_469_i0 j ⊆ envelope_469_i0 := by decide +kernel
theorem pivot_mem_469_i0 : (2, 3) ∈ envelope_469_i0 := by decide +kernel
theorem children_work_469_i0 : ∀ j, Template HasSnaky 5 (childrenC_469_i0 j) (childrenD_469_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_101 3 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_314 5 (2, 1)).mono (by decide +kernel)
theorem row_works_469_i0 : Template HasSnaky 6 required_469_i0 envelope_469_i0 := by
  refine compose HasSnaky 5 childrenC_469_i0 childrenD_469_i0 children_work_469_i0 (2, 3)
    required_469_i0 envelope_469_i0 pivot_mem_469_i0 child_required_sub_469_i0 child_envelope_sub_469_i0 ?_
  intro b hb
  exact common_sub_469_i0 (mem_commonEnvelope childrenD_469_i0 b hb)
def required_469 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 3), (1, 4), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_469 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 3), (0, 5), (0, 6), (0, 7), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 0), (2, 1), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 1), (3, 2), (3, 3), (4, 2), (4, 3), (5, 2), (6, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_469 : Fin 2 → Finset Cell := ![(placed21 3 (0, 4) required_78), required_469_i0]
def childrenD_469 : Fin 2 → Finset Cell := ![(placed21 3 (0, 4) envelope_78), envelope_469_i0]
theorem common_sub_469 : commonEnvelope childrenD_469 ⊆ insert (3, 2) required_469 := by decide +kernel
theorem child_required_sub_469 : ∀ j, childrenC_469 j ⊆ insert (3, 2) required_469 := by decide +kernel
theorem child_envelope_sub_469 : ∀ j, childrenD_469 j ⊆ envelope_469 := by decide +kernel
theorem pivot_mem_469 : (3, 2) ∈ envelope_469 := by decide +kernel
theorem children_work_469 : ∀ j, Template HasSnaky 6 (childrenC_469 j) (childrenD_469 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_78 3 (0, 4)).mono (by decide +kernel)
  · exact row_works_469_i0.mono (by decide +kernel)
theorem row_works_469 : Template HasSnaky 7 required_469 envelope_469 := by
  refine compose HasSnaky 6 childrenC_469 childrenD_469 children_work_469 (3, 2)
    required_469 envelope_469 pivot_mem_469 child_required_sub_469 child_envelope_sub_469 ?_
  intro b hb
  exact common_sub_469 (mem_commonEnvelope childrenD_469 b hb)
def required_472 : Finset Cell := ⟨(([(1, 1), (1, 2), (2, 2), (3, 2), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_472 : Finset Cell := ⟨(([(0, 3), (0, 4), (0, 5), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 2), (3, 3), (3, 4), (4, 2), (4, 3), (5, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_472 : Fin 2 → Finset Cell := ![(placed21 0 (1, 2) required_5), (placed21 2 (4, 0) required_471)]
def childrenD_472 : Fin 2 → Finset Cell := ![(placed21 0 (1, 2) envelope_5), (placed21 2 (4, 0) envelope_471)]
theorem common_sub_472 : commonEnvelope childrenD_472 ⊆ insert (4, 3) required_472 := by decide +kernel
theorem child_required_sub_472 : ∀ j, childrenC_472 j ⊆ insert (4, 3) required_472 := by decide +kernel
theorem child_envelope_sub_472 : ∀ j, childrenD_472 j ⊆ envelope_472 := by decide +kernel
theorem pivot_mem_472 : (4, 3) ∈ envelope_472 := by decide +kernel
theorem children_work_472 : ∀ j, Template HasSnaky 6 (childrenC_472 j) (childrenD_472 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 0 (1, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_471 2 (4, 0)).mono (by decide +kernel)
theorem row_works_472 : Template HasSnaky 7 required_472 envelope_472 := by
  refine compose HasSnaky 6 childrenC_472 childrenD_472 children_work_472 (4, 3)
    required_472 envelope_472 pivot_mem_472 child_required_sub_472 child_envelope_sub_472 ?_
  intro b hb
  exact common_sub_472 (mem_commonEnvelope childrenD_472 b hb)
def required_487 : Finset Cell := ⟨(([(0, 1), (1, 3), (3, 0), (3, 1), (3, 2), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_487 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 4), (1, 1), (1, 2), (1, 3), (1, 4), (2, 2), (2, 3), (2, 4), (3, 0), (3, 1), (3, 2), (3, 3), (4, 2), (4, 3), (5, 2), (5, 3), (5, 4), (6, 2), (6, 3), (6, 4), (7, 2), (7, 3), (7, 4), (8, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_487 : Fin 2 → Finset Cell := ![(placed21 5 (3, 0) required_5), required_486]
def childrenD_487 : Fin 2 → Finset Cell := ![(placed21 5 (3, 0) envelope_5), envelope_486]
theorem common_sub_487 : commonEnvelope childrenD_487 ⊆ insert (2, 3) required_487 := by decide +kernel
theorem child_required_sub_487 : ∀ j, childrenC_487 j ⊆ insert (2, 3) required_487 := by decide +kernel
theorem child_envelope_sub_487 : ∀ j, childrenD_487 j ⊆ envelope_487 := by decide +kernel
theorem pivot_mem_487 : (2, 3) ∈ envelope_487 := by decide +kernel
theorem children_work_487 : ∀ j, Template HasSnaky 6 (childrenC_487 j) (childrenD_487 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 5 (3, 0)).mono (by decide +kernel)
  · exact row_works_486.mono (by decide +kernel)
theorem row_works_487 : Template HasSnaky 7 required_487 envelope_487 := by
  refine compose HasSnaky 6 childrenC_487 childrenD_487 children_work_487 (2, 3)
    required_487 envelope_487 pivot_mem_487 child_required_sub_487 child_envelope_sub_487 ?_
  intro b hb
  exact common_sub_487 (mem_commonEnvelope childrenD_487 b hb)
def required_488_i1 : Finset Cell := ⟨(([(1, 3), (1, 4), (1, 5), (2, 6), (4, 5), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_488_i1 : Finset Cell := ⟨(([(0, 5), (1, 3), (1, 4), (1, 5), (1, 6), (2, 6), (2, 7), (3, 6), (4, 5), (4, 6), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_488_i1 : Fin 2 → Finset Cell := ![(placed21 1 (1, 3) required_5), (placed21 3 (0, 6) required_34)]
def childrenD_488_i1 : Fin 2 → Finset Cell := ![(placed21 1 (1, 3) envelope_5), (placed21 3 (0, 6) envelope_34)]
theorem common_sub_488_i1 : commonEnvelope childrenD_488_i1 ⊆ insert (1, 6) required_488_i1 := by decide +kernel
theorem child_required_sub_488_i1 : ∀ j, childrenC_488_i1 j ⊆ insert (1, 6) required_488_i1 := by decide +kernel
theorem child_envelope_sub_488_i1 : ∀ j, childrenD_488_i1 j ⊆ envelope_488_i1 := by decide +kernel
theorem pivot_mem_488_i1 : (1, 6) ∈ envelope_488_i1 := by decide +kernel
theorem children_work_488_i1 : ∀ j, Template HasSnaky 2 (childrenC_488_i1 j) (childrenD_488_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 1 (1, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_34 3 (0, 6)).mono (by decide +kernel)
theorem row_works_488_i1 : Template HasSnaky 3 required_488_i1 envelope_488_i1 := by
  refine compose HasSnaky 2 childrenC_488_i1 childrenD_488_i1 children_work_488_i1 (1, 6)
    required_488_i1 envelope_488_i1 pivot_mem_488_i1 child_required_sub_488_i1 child_envelope_sub_488_i1 ?_
  intro b hb
  exact common_sub_488_i1 (mem_commonEnvelope childrenD_488_i1 b hb)
def required_488_i0 : Finset Cell := ⟨(([(1, 2), (1, 3), (1, 4), (1, 5), (4, 5), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_488_i0 : Finset Cell := ⟨(([(0, 5), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 5), (2, 6), (2, 7), (3, 6), (4, 5), (4, 6), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_488_i0 : Fin 2 → Finset Cell := ![(placed21 1 (1, 2) required_4), required_488_i1]
def childrenD_488_i0 : Fin 2 → Finset Cell := ![(placed21 1 (1, 2) envelope_4), envelope_488_i1]
theorem common_sub_488_i0 : commonEnvelope childrenD_488_i0 ⊆ insert (2, 6) required_488_i0 := by decide +kernel
theorem child_required_sub_488_i0 : ∀ j, childrenC_488_i0 j ⊆ insert (2, 6) required_488_i0 := by decide +kernel
theorem child_envelope_sub_488_i0 : ∀ j, childrenD_488_i0 j ⊆ envelope_488_i0 := by decide +kernel
theorem pivot_mem_488_i0 : (2, 6) ∈ envelope_488_i0 := by decide +kernel
theorem children_work_488_i0 : ∀ j, Template HasSnaky 3 (childrenC_488_i0 j) (childrenD_488_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_4 1 (1, 2)).mono (by decide +kernel)
  · exact row_works_488_i1.mono (by decide +kernel)
theorem row_works_488_i0 : Template HasSnaky 4 required_488_i0 envelope_488_i0 := by
  refine compose HasSnaky 3 childrenC_488_i0 childrenD_488_i0 children_work_488_i0 (2, 6)
    required_488_i0 envelope_488_i0 pivot_mem_488_i0 child_required_sub_488_i0 child_envelope_sub_488_i0 ?_
  intro b hb
  exact common_sub_488_i0 (mem_commonEnvelope childrenD_488_i0 b hb)
def required_488_i2 : Finset Cell := ⟨(([(1, 3), (1, 4), (1, 5), (4, 3), (4, 5), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_488_i2 : Finset Cell := ⟨(([(1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 5), (2, 6), (2, 7), (3, 6), (3, 7), (3, 8), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 2), (5, 3), (5, 4), (5, 6), (5, 7), (5, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_488_i2 : Fin 3 → Finset Cell := ![(placed21 0 (4, 2) required_7), (placed21 2 (5, 2) required_9), (placed21 0 (1, 3) required_357)]
def childrenD_488_i2 : Fin 3 → Finset Cell := ![(placed21 0 (4, 2) envelope_7), (placed21 2 (5, 2) envelope_9), (placed21 0 (1, 3) envelope_357)]
theorem common_sub_488_i2 : commonEnvelope childrenD_488_i2 ⊆ insert (4, 4) required_488_i2 := by decide +kernel
theorem child_required_sub_488_i2 : ∀ j, childrenC_488_i2 j ⊆ insert (4, 4) required_488_i2 := by decide +kernel
theorem child_envelope_sub_488_i2 : ∀ j, childrenD_488_i2 j ⊆ envelope_488_i2 := by decide +kernel
theorem pivot_mem_488_i2 : (4, 4) ∈ envelope_488_i2 := by decide +kernel
theorem children_work_488_i2 : ∀ j, Template HasSnaky 5 (childrenC_488_i2 j) (childrenD_488_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 0 (4, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_9 2 (5, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_357 0 (1, 3)).mono (by decide +kernel)
theorem row_works_488_i2 : Template HasSnaky 6 required_488_i2 envelope_488_i2 := by
  refine compose HasSnaky 5 childrenC_488_i2 childrenD_488_i2 children_work_488_i2 (4, 4)
    required_488_i2 envelope_488_i2 pivot_mem_488_i2 child_required_sub_488_i2 child_envelope_sub_488_i2 ?_
  intro b hb
  exact common_sub_488_i2 (mem_commonEnvelope childrenD_488_i2 b hb)
def required_488 : Finset Cell := ⟨(([(1, 2), (1, 3), (1, 4), (1, 5), (4, 3), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_488 : Finset Cell := ⟨(([(0, 5), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 5), (2, 6), (2, 7), (3, 0), (3, 1), (3, 2), (3, 6), (3, 7), (3, 8), (3, 9), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_488 : Fin 3 → Finset Cell := ![(placed21 6 (5, 9) required_95), required_488_i0, required_488_i2]
def childrenD_488 : Fin 3 → Finset Cell := ![(placed21 6 (5, 9) envelope_95), envelope_488_i0, envelope_488_i2]
theorem common_sub_488 : commonEnvelope childrenD_488 ⊆ insert (4, 6) required_488 := by decide +kernel
theorem child_required_sub_488 : ∀ j, childrenC_488 j ⊆ insert (4, 6) required_488 := by decide +kernel
theorem child_envelope_sub_488 : ∀ j, childrenD_488 j ⊆ envelope_488 := by decide +kernel
theorem pivot_mem_488 : (4, 6) ∈ envelope_488 := by decide +kernel
theorem children_work_488 : ∀ j, Template HasSnaky 6 (childrenC_488 j) (childrenD_488 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_95 6 (5, 9)).mono (by decide +kernel)
  · exact row_works_488_i0.mono (by decide +kernel)
  · exact row_works_488_i2.mono (by decide +kernel)
theorem row_works_488 : Template HasSnaky 7 required_488 envelope_488 := by
  refine compose HasSnaky 6 childrenC_488 childrenD_488 children_work_488 (4, 6)
    required_488 envelope_488 pivot_mem_488 child_required_sub_488 child_envelope_sub_488 ?_
  intro b hb
  exact common_sub_488 (mem_commonEnvelope childrenD_488 b hb)
def required_499_i0 : Finset Cell := ⟨(([(0, 2), (1, 2), (1, 3), (2, 1), (2, 2), (2, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_499_i0 : Finset Cell := ⟨(([(0, 2), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 3), (3, 4), (3, 5), (3, 6), (4, 3), (4, 4), (5, 3), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_499_i0 : Fin 2 → Finset Cell := ![(placed21 6 (4, 3) required_1), (placed21 0 (1, 1) required_347)]
def childrenD_499_i0 : Fin 2 → Finset Cell := ![(placed21 6 (4, 3) envelope_1), (placed21 0 (1, 1) envelope_347)]
theorem common_sub_499_i0 : commonEnvelope childrenD_499_i0 ⊆ insert (4, 3) required_499_i0 := by decide +kernel
theorem child_required_sub_499_i0 : ∀ j, childrenC_499_i0 j ⊆ insert (4, 3) required_499_i0 := by decide +kernel
theorem child_envelope_sub_499_i0 : ∀ j, childrenD_499_i0 j ⊆ envelope_499_i0 := by decide +kernel
theorem pivot_mem_499_i0 : (4, 3) ∈ envelope_499_i0 := by decide +kernel
theorem children_work_499_i0 : ∀ j, Template HasSnaky 5 (childrenC_499_i0 j) (childrenD_499_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_1 6 (4, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_347 0 (1, 1)).mono (by decide +kernel)
theorem row_works_499_i0 : Template HasSnaky 6 required_499_i0 envelope_499_i0 := by
  refine compose HasSnaky 5 childrenC_499_i0 childrenD_499_i0 children_work_499_i0 (4, 3)
    required_499_i0 envelope_499_i0 pivot_mem_499_i0 child_required_sub_499_i0 child_envelope_sub_499_i0 ?_
  intro b hb
  exact common_sub_499_i0 (mem_commonEnvelope childrenD_499_i0 b hb)
def required_499_i1 : Finset Cell := ⟨(([(0, 2), (1, 2), (2, 1), (2, 2), (2, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_499_i1 : Finset Cell := ⟨(([(0, 2), (1, 2), (1, 3), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, 3), (3, 4), (3, 5), (3, 6), (4, 3), (5, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_499_i1 : Fin 2 → Finset Cell := ![(placed21 1 (0, 2) required_43), (placed21 0 (2, 0) required_52)]
def childrenD_499_i1 : Fin 2 → Finset Cell := ![(placed21 1 (0, 2) envelope_43), (placed21 0 (2, 0) envelope_52)]
theorem common_sub_499_i1 : commonEnvelope childrenD_499_i1 ⊆ insert (3, 3) required_499_i1 := by decide +kernel
theorem child_required_sub_499_i1 : ∀ j, childrenC_499_i1 j ⊆ insert (3, 3) required_499_i1 := by decide +kernel
theorem child_envelope_sub_499_i1 : ∀ j, childrenD_499_i1 j ⊆ envelope_499_i1 := by decide +kernel
theorem pivot_mem_499_i1 : (3, 3) ∈ envelope_499_i1 := by decide +kernel
theorem children_work_499_i1 : ∀ j, Template HasSnaky 3 (childrenC_499_i1 j) (childrenD_499_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_43 1 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_52 0 (2, 0)).mono (by decide +kernel)
theorem row_works_499_i1 : Template HasSnaky 4 required_499_i1 envelope_499_i1 := by
  refine compose HasSnaky 3 childrenC_499_i1 childrenD_499_i1 children_work_499_i1 (3, 3)
    required_499_i1 envelope_499_i1 pivot_mem_499_i1 child_required_sub_499_i1 child_envelope_sub_499_i1 ?_
  intro b hb
  exact common_sub_499_i1 (mem_commonEnvelope childrenD_499_i1 b hb)
def required_499 : Finset Cell := ⟨(([(0, 2), (1, 2), (1, 3), (2, 2), (2, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_499 : Finset Cell := ⟨(([(0, 2), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 3), (3, 4), (3, 5), (3, 6), (4, 3), (4, 4), (5, 3), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_499 : Fin 3 → Finset Cell := ![(placed21 2 (2, 0) required_15), required_499_i0, required_499_i1]
def childrenD_499 : Fin 3 → Finset Cell := ![(placed21 2 (2, 0) envelope_15), envelope_499_i0, envelope_499_i1]
theorem common_sub_499 : commonEnvelope childrenD_499 ⊆ insert (2, 1) required_499 := by decide +kernel
theorem child_required_sub_499 : ∀ j, childrenC_499 j ⊆ insert (2, 1) required_499 := by decide +kernel
theorem child_envelope_sub_499 : ∀ j, childrenD_499 j ⊆ envelope_499 := by decide +kernel
theorem pivot_mem_499 : (2, 1) ∈ envelope_499 := by decide +kernel
theorem children_work_499 : ∀ j, Template HasSnaky 6 (childrenC_499 j) (childrenD_499 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_15 2 (2, 0)).mono (by decide +kernel)
  · exact row_works_499_i0.mono (by decide +kernel)
  · exact row_works_499_i1.mono (by decide +kernel)
theorem row_works_499 : Template HasSnaky 7 required_499 envelope_499 := by
  refine compose HasSnaky 6 childrenC_499 childrenD_499 children_work_499 (2, 1)
    required_499 envelope_499 pivot_mem_499 child_required_sub_499 child_envelope_sub_499 ?_
  intro b hb
  exact common_sub_499 (mem_commonEnvelope childrenD_499 b hb)
def required_504_i1 : Finset Cell := ⟨(([(2, 2), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_504_i1 : Finset Cell := ⟨(([(0, 3), (1, 3), (2, 2), (2, 3), (2, 4), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 4), (4, 5), (5, 4), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_504_i1 : Fin 2 → Finset Cell := ![(placed21 7 (3, 6) required_0), (placed21 1 (0, 1) required_56)]
def childrenD_504_i1 : Fin 2 → Finset Cell := ![(placed21 7 (3, 6) envelope_0), (placed21 1 (0, 1) envelope_56)]
theorem common_sub_504_i1 : commonEnvelope childrenD_504_i1 ⊆ insert (2, 3) required_504_i1 := by decide +kernel
theorem child_required_sub_504_i1 : ∀ j, childrenC_504_i1 j ⊆ insert (2, 3) required_504_i1 := by decide +kernel
theorem child_envelope_sub_504_i1 : ∀ j, childrenD_504_i1 j ⊆ envelope_504_i1 := by decide +kernel
theorem pivot_mem_504_i1 : (2, 3) ∈ envelope_504_i1 := by decide +kernel
theorem children_work_504_i1 : ∀ j, Template HasSnaky 4 (childrenC_504_i1 j) (childrenD_504_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 7 (3, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_56 1 (0, 1)).mono (by decide +kernel)
theorem row_works_504_i1 : Template HasSnaky 5 required_504_i1 envelope_504_i1 := by
  refine compose HasSnaky 4 childrenC_504_i1 childrenD_504_i1 children_work_504_i1 (2, 3)
    required_504_i1 envelope_504_i1 pivot_mem_504_i1 child_required_sub_504_i1 child_envelope_sub_504_i1 ?_
  intro b hb
  exact common_sub_504_i1 (mem_commonEnvelope childrenD_504_i1 b hb)
def required_504_i0 : Finset Cell := ⟨(([(2, 2), (3, 1), (3, 2), (3, 3), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_504_i0 : Finset Cell := ⟨(([(0, 3), (1, 3), (2, 2), (2, 3), (2, 4), (2, 6), (2, 7), (2, 8), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 4), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_504_i0 : Fin 3 → Finset Cell := ![(placed21 0 (3, 1) required_6), (placed21 0 (2, 2) required_18), required_504_i1]
def childrenD_504_i0 : Fin 3 → Finset Cell := ![(placed21 0 (3, 1) envelope_6), (placed21 0 (2, 2) envelope_18), envelope_504_i1]
theorem common_sub_504_i0 : commonEnvelope childrenD_504_i0 ⊆ insert (3, 5) required_504_i0 := by decide +kernel
theorem child_required_sub_504_i0 : ∀ j, childrenC_504_i0 j ⊆ insert (3, 5) required_504_i0 := by decide +kernel
theorem child_envelope_sub_504_i0 : ∀ j, childrenD_504_i0 j ⊆ envelope_504_i0 := by decide +kernel
theorem pivot_mem_504_i0 : (3, 5) ∈ envelope_504_i0 := by decide +kernel
theorem children_work_504_i0 : ∀ j, Template HasSnaky 5 (childrenC_504_i0 j) (childrenD_504_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_6 0 (3, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_18 0 (2, 2)).mono (by decide +kernel)
  · exact row_works_504_i1.mono (by decide +kernel)
theorem row_works_504_i0 : Template HasSnaky 6 required_504_i0 envelope_504_i0 := by
  refine compose HasSnaky 5 childrenC_504_i0 childrenD_504_i0 children_work_504_i0 (3, 5)
    required_504_i0 envelope_504_i0 pivot_mem_504_i0 child_required_sub_504_i0 child_envelope_sub_504_i0 ?_
  intro b hb
  exact common_sub_504_i0 (mem_commonEnvelope childrenD_504_i0 b hb)
def required_504 : Finset Cell := ⟨(([(1, 2), (2, 2), (3, 2), (3, 3), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_504 : Finset Cell := ⟨(([(0, 2), (0, 3), (1, 2), (1, 3), (2, 2), (2, 3), (2, 4), (2, 6), (2, 7), (2, 8), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 0), (4, 1), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 4), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_504 : Fin 2 → Finset Cell := ![(placed21 7 (4, 4) required_32), required_504_i0]
def childrenD_504 : Fin 2 → Finset Cell := ![(placed21 7 (4, 4) envelope_32), envelope_504_i0]
theorem common_sub_504 : commonEnvelope childrenD_504 ⊆ insert (3, 1) required_504 := by decide +kernel
theorem child_required_sub_504 : ∀ j, childrenC_504 j ⊆ insert (3, 1) required_504 := by decide +kernel
theorem child_envelope_sub_504 : ∀ j, childrenD_504 j ⊆ envelope_504 := by decide +kernel
theorem pivot_mem_504 : (3, 1) ∈ envelope_504 := by decide +kernel
theorem children_work_504 : ∀ j, Template HasSnaky 6 (childrenC_504 j) (childrenD_504 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_32 7 (4, 4)).mono (by decide +kernel)
  · exact row_works_504_i0.mono (by decide +kernel)
theorem row_works_504 : Template HasSnaky 7 required_504 envelope_504 := by
  refine compose HasSnaky 6 childrenC_504 childrenD_504 children_work_504 (3, 1)
    required_504 envelope_504 pivot_mem_504 child_required_sub_504 child_envelope_sub_504 ?_
  intro b hb
  exact common_sub_504 (mem_commonEnvelope childrenD_504 b hb)
def required_507_i0 : Finset Cell := ⟨(([(2, 3), (3, 3), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_507_i0 : Finset Cell := ⟨(([(1, 3), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 0), (4, 1), (4, 2), (4, 4), (4, 5), (4, 6), (4, 7), (5, 2), (6, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_507_i0 : Fin 3 → Finset Cell := ![(placed21 6 (4, 7) required_33), (placed21 6 (3, 6) required_44), (placed21 3 (1, 6) required_47)]
def childrenD_507_i0 : Fin 3 → Finset Cell := ![(placed21 6 (4, 7) envelope_33), (placed21 6 (3, 6) envelope_44), (placed21 3 (1, 6) envelope_47)]
theorem common_sub_507_i0 : commonEnvelope childrenD_507_i0 ⊆ insert (3, 5) required_507_i0 := by decide +kernel
theorem child_required_sub_507_i0 : ∀ j, childrenC_507_i0 j ⊆ insert (3, 5) required_507_i0 := by decide +kernel
theorem child_envelope_sub_507_i0 : ∀ j, childrenD_507_i0 j ⊆ envelope_507_i0 := by decide +kernel
theorem pivot_mem_507_i0 : (3, 5) ∈ envelope_507_i0 := by decide +kernel
theorem children_work_507_i0 : ∀ j, Template HasSnaky 5 (childrenC_507_i0 j) (childrenD_507_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_33 6 (4, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_44 6 (3, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_47 3 (1, 6)).mono (by decide +kernel)
theorem row_works_507_i0 : Template HasSnaky 6 required_507_i0 envelope_507_i0 := by
  refine compose HasSnaky 5 childrenC_507_i0 childrenD_507_i0 children_work_507_i0 (3, 5)
    required_507_i0 envelope_507_i0 pivot_mem_507_i0 child_required_sub_507_i0 child_envelope_sub_507_i0 ?_
  intro b hb
  exact common_sub_507_i0 (mem_commonEnvelope childrenD_507_i0 b hb)
def required_507 : Finset Cell := ⟨(([(1, 3), (2, 3), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_507 : Finset Cell := ⟨(([(0, 3), (1, 3), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 0), (4, 1), (4, 2), (4, 4), (4, 5), (4, 6), (4, 7), (5, 2), (5, 4), (6, 2), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_507 : Fin 4 → Finset Cell := ![(placed21 1 (0, 3) required_44), required_274, (placed21 2 (4, 0) required_506), required_507_i0]
def childrenD_507 : Fin 4 → Finset Cell := ![(placed21 1 (0, 3) envelope_44), envelope_274, (placed21 2 (4, 0) envelope_506), envelope_507_i0]
theorem common_sub_507 : commonEnvelope childrenD_507 ⊆ insert (3, 4) required_507 := by decide +kernel
theorem child_required_sub_507 : ∀ j, childrenC_507 j ⊆ insert (3, 4) required_507 := by decide +kernel
theorem child_envelope_sub_507 : ∀ j, childrenD_507 j ⊆ envelope_507 := by decide +kernel
theorem pivot_mem_507 : (3, 4) ∈ envelope_507 := by decide +kernel
theorem children_work_507 : ∀ j, Template HasSnaky 6 (childrenC_507 j) (childrenD_507 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_44 1 (0, 3)).mono (by decide +kernel)
  · exact row_works_274.mono (by decide +kernel)
  · exact (placed21_template row_works_506 2 (4, 0)).mono (by decide +kernel)
  · exact row_works_507_i0.mono (by decide +kernel)
theorem row_works_507 : Template HasSnaky 7 required_507 envelope_507 := by
  refine compose HasSnaky 6 childrenC_507 childrenD_507 children_work_507 (3, 4)
    required_507 envelope_507 pivot_mem_507 child_required_sub_507 child_envelope_sub_507 ?_
  intro b hb
  exact common_sub_507 (mem_commonEnvelope childrenD_507 b hb)
def height_447_i0 : ℕ := 6
def childrenH_447_i0 : Fin 2 → ℕ := ![height_0, height_445]
theorem height_exact_447_i0 : height_447_i0 = 1 + Finset.univ.sup childrenH_447_i0 := by decide +kernel
theorem required_origin_447_i0 : ∀ x ∈ required_447_i0,
    (∃ j, x ∈ childrenC_447_i0 j) ∨ ∀ j, x ∈ childrenD_447_i0 j := by decide +kernel
theorem required_exact_447_i0 : required_447_i0 =
    ((Finset.univ.biUnion childrenC_447_i0) ∪ commonEnvelope childrenD_447_i0).erase (2, 3) := by
  exact required_eq_combination childrenC_447_i0 childrenD_447_i0 (2, 3) required_447_i0
    (by decide +kernel) child_required_sub_447_i0 common_sub_447_i0 required_origin_447_i0
theorem envelope_origin_447_i0 : ∀ x ∈ envelope_447_i0,
    x = (2, 3) ∨ ∃ j, x ∈ childrenD_447_i0 j := by decide +kernel
theorem envelope_exact_447_i0 : envelope_447_i0 =
    insert (2, 3) (Finset.univ.biUnion childrenD_447_i0) := by
  exact envelope_eq_combination childrenD_447_i0 (2, 3) envelope_447_i0
    pivot_mem_447_i0 child_envelope_sub_447_i0 envelope_origin_447_i0
def checked_447_i0 : CheckedCard where
  required := required_447_i0
  envelope := envelope_447_i0
  height := height_447_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_447_i0
def height_447 : ℕ := 7
def childrenH_447 : Fin 2 → ℕ := ![height_5, height_447_i0]
theorem height_exact_447 : height_447 = 1 + Finset.univ.sup childrenH_447 := by decide +kernel
theorem required_origin_447 : ∀ x ∈ required_447,
    (∃ j, x ∈ childrenC_447 j) ∨ ∀ j, x ∈ childrenD_447 j := by decide +kernel
theorem required_exact_447 : required_447 =
    ((Finset.univ.biUnion childrenC_447) ∪ commonEnvelope childrenD_447).erase (2, 4) := by
  exact required_eq_combination childrenC_447 childrenD_447 (2, 4) required_447
    (by decide +kernel) child_required_sub_447 common_sub_447 required_origin_447
theorem envelope_origin_447 : ∀ x ∈ envelope_447,
    x = (2, 4) ∨ ∃ j, x ∈ childrenD_447 j := by decide +kernel
theorem envelope_exact_447 : envelope_447 =
    insert (2, 4) (Finset.univ.biUnion childrenD_447) := by
  exact envelope_eq_combination childrenD_447 (2, 4) envelope_447
    pivot_mem_447 child_envelope_sub_447 envelope_origin_447
def checked_447 : CheckedCard where
  required := required_447
  envelope := envelope_447
  height := height_447
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_447
def height_453_i1 : ℕ := 5
def childrenH_453_i1 : Fin 3 → ℕ := ![height_21, height_37, height_354]
theorem height_exact_453_i1 : height_453_i1 = 1 + Finset.univ.sup childrenH_453_i1 := by decide +kernel
theorem required_origin_453_i1 : ∀ x ∈ required_453_i1,
    (∃ j, x ∈ childrenC_453_i1 j) ∨ ∀ j, x ∈ childrenD_453_i1 j := by decide +kernel
theorem required_exact_453_i1 : required_453_i1 =
    ((Finset.univ.biUnion childrenC_453_i1) ∪ commonEnvelope childrenD_453_i1).erase (3, 3) := by
  exact required_eq_combination childrenC_453_i1 childrenD_453_i1 (3, 3) required_453_i1
    (by decide +kernel) child_required_sub_453_i1 common_sub_453_i1 required_origin_453_i1
theorem envelope_origin_453_i1 : ∀ x ∈ envelope_453_i1,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_453_i1 j := by decide +kernel
theorem envelope_exact_453_i1 : envelope_453_i1 =
    insert (3, 3) (Finset.univ.biUnion childrenD_453_i1) := by
  exact envelope_eq_combination childrenD_453_i1 (3, 3) envelope_453_i1
    pivot_mem_453_i1 child_envelope_sub_453_i1 envelope_origin_453_i1
def checked_453_i1 : CheckedCard where
  required := required_453_i1
  envelope := envelope_453_i1
  height := height_453_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_453_i1
def height_453_i0 : ℕ := 6
def childrenH_453_i0 : Fin 2 → ℕ := ![height_5, height_453_i1]
theorem height_exact_453_i0 : height_453_i0 = 1 + Finset.univ.sup childrenH_453_i0 := by decide +kernel
theorem required_origin_453_i0 : ∀ x ∈ required_453_i0,
    (∃ j, x ∈ childrenC_453_i0 j) ∨ ∀ j, x ∈ childrenD_453_i0 j := by decide +kernel
theorem required_exact_453_i0 : required_453_i0 =
    ((Finset.univ.biUnion childrenC_453_i0) ∪ commonEnvelope childrenD_453_i0).erase (3, 0) := by
  exact required_eq_combination childrenC_453_i0 childrenD_453_i0 (3, 0) required_453_i0
    (by decide +kernel) child_required_sub_453_i0 common_sub_453_i0 required_origin_453_i0
theorem envelope_origin_453_i0 : ∀ x ∈ envelope_453_i0,
    x = (3, 0) ∨ ∃ j, x ∈ childrenD_453_i0 j := by decide +kernel
theorem envelope_exact_453_i0 : envelope_453_i0 =
    insert (3, 0) (Finset.univ.biUnion childrenD_453_i0) := by
  exact envelope_eq_combination childrenD_453_i0 (3, 0) envelope_453_i0
    pivot_mem_453_i0 child_envelope_sub_453_i0 envelope_origin_453_i0
def checked_453_i0 : CheckedCard where
  required := required_453_i0
  envelope := envelope_453_i0
  height := height_453_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_453_i0
def height_453 : ℕ := 7
def childrenH_453 : Fin 2 → ℕ := ![height_5, height_453_i0]
theorem height_exact_453 : height_453 = 1 + Finset.univ.sup childrenH_453 := by decide +kernel
theorem required_origin_453 : ∀ x ∈ required_453,
    (∃ j, x ∈ childrenC_453 j) ∨ ∀ j, x ∈ childrenD_453 j := by decide +kernel
theorem required_exact_453 : required_453 =
    ((Finset.univ.biUnion childrenC_453) ∪ commonEnvelope childrenD_453).erase (3, 2) := by
  exact required_eq_combination childrenC_453 childrenD_453 (3, 2) required_453
    (by decide +kernel) child_required_sub_453 common_sub_453 required_origin_453
theorem envelope_origin_453 : ∀ x ∈ envelope_453,
    x = (3, 2) ∨ ∃ j, x ∈ childrenD_453 j := by decide +kernel
theorem envelope_exact_453 : envelope_453 =
    insert (3, 2) (Finset.univ.biUnion childrenD_453) := by
  exact envelope_eq_combination childrenD_453 (3, 2) envelope_453
    pivot_mem_453 child_envelope_sub_453 envelope_origin_453
def checked_453 : CheckedCard where
  required := required_453
  envelope := envelope_453
  height := height_453
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_453
def height_466 : ℕ := 7
def childrenH_466 : Fin 4 → ℕ := ![height_7, height_8, height_9, height_465]
theorem height_exact_466 : height_466 = 1 + Finset.univ.sup childrenH_466 := by decide +kernel
theorem required_origin_466 : ∀ x ∈ required_466,
    (∃ j, x ∈ childrenC_466 j) ∨ ∀ j, x ∈ childrenD_466 j := by decide +kernel
theorem required_exact_466 : required_466 =
    ((Finset.univ.biUnion childrenC_466) ∪ commonEnvelope childrenD_466).erase (1, 4) := by
  exact required_eq_combination childrenC_466 childrenD_466 (1, 4) required_466
    (by decide +kernel) child_required_sub_466 common_sub_466 required_origin_466
theorem envelope_origin_466 : ∀ x ∈ envelope_466,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_466 j := by decide +kernel
theorem envelope_exact_466 : envelope_466 =
    insert (1, 4) (Finset.univ.biUnion childrenD_466) := by
  exact envelope_eq_combination childrenD_466 (1, 4) envelope_466
    pivot_mem_466 child_envelope_sub_466 envelope_origin_466
def checked_466 : CheckedCard where
  required := required_466
  envelope := envelope_466
  height := height_466
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_466
def height_469_i0 : ℕ := 6
def childrenH_469_i0 : Fin 2 → ℕ := ![height_101, height_314]
theorem height_exact_469_i0 : height_469_i0 = 1 + Finset.univ.sup childrenH_469_i0 := by decide +kernel
theorem required_origin_469_i0 : ∀ x ∈ required_469_i0,
    (∃ j, x ∈ childrenC_469_i0 j) ∨ ∀ j, x ∈ childrenD_469_i0 j := by decide +kernel
theorem required_exact_469_i0 : required_469_i0 =
    ((Finset.univ.biUnion childrenC_469_i0) ∪ commonEnvelope childrenD_469_i0).erase (2, 3) := by
  exact required_eq_combination childrenC_469_i0 childrenD_469_i0 (2, 3) required_469_i0
    (by decide +kernel) child_required_sub_469_i0 common_sub_469_i0 required_origin_469_i0
theorem envelope_origin_469_i0 : ∀ x ∈ envelope_469_i0,
    x = (2, 3) ∨ ∃ j, x ∈ childrenD_469_i0 j := by decide +kernel
theorem envelope_exact_469_i0 : envelope_469_i0 =
    insert (2, 3) (Finset.univ.biUnion childrenD_469_i0) := by
  exact envelope_eq_combination childrenD_469_i0 (2, 3) envelope_469_i0
    pivot_mem_469_i0 child_envelope_sub_469_i0 envelope_origin_469_i0
def checked_469_i0 : CheckedCard where
  required := required_469_i0
  envelope := envelope_469_i0
  height := height_469_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_469_i0
def height_469 : ℕ := 7
def childrenH_469 : Fin 2 → ℕ := ![height_78, height_469_i0]
theorem height_exact_469 : height_469 = 1 + Finset.univ.sup childrenH_469 := by decide +kernel
theorem required_origin_469 : ∀ x ∈ required_469,
    (∃ j, x ∈ childrenC_469 j) ∨ ∀ j, x ∈ childrenD_469 j := by decide +kernel
theorem required_exact_469 : required_469 =
    ((Finset.univ.biUnion childrenC_469) ∪ commonEnvelope childrenD_469).erase (3, 2) := by
  exact required_eq_combination childrenC_469 childrenD_469 (3, 2) required_469
    (by decide +kernel) child_required_sub_469 common_sub_469 required_origin_469
theorem envelope_origin_469 : ∀ x ∈ envelope_469,
    x = (3, 2) ∨ ∃ j, x ∈ childrenD_469 j := by decide +kernel
theorem envelope_exact_469 : envelope_469 =
    insert (3, 2) (Finset.univ.biUnion childrenD_469) := by
  exact envelope_eq_combination childrenD_469 (3, 2) envelope_469
    pivot_mem_469 child_envelope_sub_469 envelope_origin_469
def checked_469 : CheckedCard where
  required := required_469
  envelope := envelope_469
  height := height_469
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_469
def height_472 : ℕ := 7
def childrenH_472 : Fin 2 → ℕ := ![height_5, height_471]
theorem height_exact_472 : height_472 = 1 + Finset.univ.sup childrenH_472 := by decide +kernel
theorem required_origin_472 : ∀ x ∈ required_472,
    (∃ j, x ∈ childrenC_472 j) ∨ ∀ j, x ∈ childrenD_472 j := by decide +kernel
theorem required_exact_472 : required_472 =
    ((Finset.univ.biUnion childrenC_472) ∪ commonEnvelope childrenD_472).erase (4, 3) := by
  exact required_eq_combination childrenC_472 childrenD_472 (4, 3) required_472
    (by decide +kernel) child_required_sub_472 common_sub_472 required_origin_472
theorem envelope_origin_472 : ∀ x ∈ envelope_472,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_472 j := by decide +kernel
theorem envelope_exact_472 : envelope_472 =
    insert (4, 3) (Finset.univ.biUnion childrenD_472) := by
  exact envelope_eq_combination childrenD_472 (4, 3) envelope_472
    pivot_mem_472 child_envelope_sub_472 envelope_origin_472
def checked_472 : CheckedCard where
  required := required_472
  envelope := envelope_472
  height := height_472
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_472
def height_487 : ℕ := 7
def childrenH_487 : Fin 2 → ℕ := ![height_5, height_486]
theorem height_exact_487 : height_487 = 1 + Finset.univ.sup childrenH_487 := by decide +kernel
theorem required_origin_487 : ∀ x ∈ required_487,
    (∃ j, x ∈ childrenC_487 j) ∨ ∀ j, x ∈ childrenD_487 j := by decide +kernel
theorem required_exact_487 : required_487 =
    ((Finset.univ.biUnion childrenC_487) ∪ commonEnvelope childrenD_487).erase (2, 3) := by
  exact required_eq_combination childrenC_487 childrenD_487 (2, 3) required_487
    (by decide +kernel) child_required_sub_487 common_sub_487 required_origin_487
theorem envelope_origin_487 : ∀ x ∈ envelope_487,
    x = (2, 3) ∨ ∃ j, x ∈ childrenD_487 j := by decide +kernel
theorem envelope_exact_487 : envelope_487 =
    insert (2, 3) (Finset.univ.biUnion childrenD_487) := by
  exact envelope_eq_combination childrenD_487 (2, 3) envelope_487
    pivot_mem_487 child_envelope_sub_487 envelope_origin_487
def checked_487 : CheckedCard where
  required := required_487
  envelope := envelope_487
  height := height_487
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_487
def height_488_i1 : ℕ := 3
def childrenH_488_i1 : Fin 2 → ℕ := ![height_5, height_34]
theorem height_exact_488_i1 : height_488_i1 = 1 + Finset.univ.sup childrenH_488_i1 := by decide +kernel
theorem required_origin_488_i1 : ∀ x ∈ required_488_i1,
    (∃ j, x ∈ childrenC_488_i1 j) ∨ ∀ j, x ∈ childrenD_488_i1 j := by decide +kernel
theorem required_exact_488_i1 : required_488_i1 =
    ((Finset.univ.biUnion childrenC_488_i1) ∪ commonEnvelope childrenD_488_i1).erase (1, 6) := by
  exact required_eq_combination childrenC_488_i1 childrenD_488_i1 (1, 6) required_488_i1
    (by decide +kernel) child_required_sub_488_i1 common_sub_488_i1 required_origin_488_i1
theorem envelope_origin_488_i1 : ∀ x ∈ envelope_488_i1,
    x = (1, 6) ∨ ∃ j, x ∈ childrenD_488_i1 j := by decide +kernel
theorem envelope_exact_488_i1 : envelope_488_i1 =
    insert (1, 6) (Finset.univ.biUnion childrenD_488_i1) := by
  exact envelope_eq_combination childrenD_488_i1 (1, 6) envelope_488_i1
    pivot_mem_488_i1 child_envelope_sub_488_i1 envelope_origin_488_i1
def checked_488_i1 : CheckedCard where
  required := required_488_i1
  envelope := envelope_488_i1
  height := height_488_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_488_i1
def height_488_i0 : ℕ := 4
def childrenH_488_i0 : Fin 2 → ℕ := ![height_4, height_488_i1]
theorem height_exact_488_i0 : height_488_i0 = 1 + Finset.univ.sup childrenH_488_i0 := by decide +kernel
theorem required_origin_488_i0 : ∀ x ∈ required_488_i0,
    (∃ j, x ∈ childrenC_488_i0 j) ∨ ∀ j, x ∈ childrenD_488_i0 j := by decide +kernel
theorem required_exact_488_i0 : required_488_i0 =
    ((Finset.univ.biUnion childrenC_488_i0) ∪ commonEnvelope childrenD_488_i0).erase (2, 6) := by
  exact required_eq_combination childrenC_488_i0 childrenD_488_i0 (2, 6) required_488_i0
    (by decide +kernel) child_required_sub_488_i0 common_sub_488_i0 required_origin_488_i0
theorem envelope_origin_488_i0 : ∀ x ∈ envelope_488_i0,
    x = (2, 6) ∨ ∃ j, x ∈ childrenD_488_i0 j := by decide +kernel
theorem envelope_exact_488_i0 : envelope_488_i0 =
    insert (2, 6) (Finset.univ.biUnion childrenD_488_i0) := by
  exact envelope_eq_combination childrenD_488_i0 (2, 6) envelope_488_i0
    pivot_mem_488_i0 child_envelope_sub_488_i0 envelope_origin_488_i0
def checked_488_i0 : CheckedCard where
  required := required_488_i0
  envelope := envelope_488_i0
  height := height_488_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_488_i0
def height_488_i2 : ℕ := 6
def childrenH_488_i2 : Fin 3 → ℕ := ![height_7, height_9, height_357]
theorem height_exact_488_i2 : height_488_i2 = 1 + Finset.univ.sup childrenH_488_i2 := by decide +kernel
theorem required_origin_488_i2 : ∀ x ∈ required_488_i2,
    (∃ j, x ∈ childrenC_488_i2 j) ∨ ∀ j, x ∈ childrenD_488_i2 j := by decide +kernel
theorem required_exact_488_i2 : required_488_i2 =
    ((Finset.univ.biUnion childrenC_488_i2) ∪ commonEnvelope childrenD_488_i2).erase (4, 4) := by
  exact required_eq_combination childrenC_488_i2 childrenD_488_i2 (4, 4) required_488_i2
    (by decide +kernel) child_required_sub_488_i2 common_sub_488_i2 required_origin_488_i2
theorem envelope_origin_488_i2 : ∀ x ∈ envelope_488_i2,
    x = (4, 4) ∨ ∃ j, x ∈ childrenD_488_i2 j := by decide +kernel
theorem envelope_exact_488_i2 : envelope_488_i2 =
    insert (4, 4) (Finset.univ.biUnion childrenD_488_i2) := by
  exact envelope_eq_combination childrenD_488_i2 (4, 4) envelope_488_i2
    pivot_mem_488_i2 child_envelope_sub_488_i2 envelope_origin_488_i2
def checked_488_i2 : CheckedCard where
  required := required_488_i2
  envelope := envelope_488_i2
  height := height_488_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_488_i2
def height_488 : ℕ := 7
def childrenH_488 : Fin 3 → ℕ := ![height_95, height_488_i0, height_488_i2]
theorem height_exact_488 : height_488 = 1 + Finset.univ.sup childrenH_488 := by decide +kernel
theorem required_origin_488 : ∀ x ∈ required_488,
    (∃ j, x ∈ childrenC_488 j) ∨ ∀ j, x ∈ childrenD_488 j := by decide +kernel
theorem required_exact_488 : required_488 =
    ((Finset.univ.biUnion childrenC_488) ∪ commonEnvelope childrenD_488).erase (4, 6) := by
  exact required_eq_combination childrenC_488 childrenD_488 (4, 6) required_488
    (by decide +kernel) child_required_sub_488 common_sub_488 required_origin_488
theorem envelope_origin_488 : ∀ x ∈ envelope_488,
    x = (4, 6) ∨ ∃ j, x ∈ childrenD_488 j := by decide +kernel
theorem envelope_exact_488 : envelope_488 =
    insert (4, 6) (Finset.univ.biUnion childrenD_488) := by
  exact envelope_eq_combination childrenD_488 (4, 6) envelope_488
    pivot_mem_488 child_envelope_sub_488 envelope_origin_488
def checked_488 : CheckedCard where
  required := required_488
  envelope := envelope_488
  height := height_488
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_488
def height_499_i0 : ℕ := 6
def childrenH_499_i0 : Fin 2 → ℕ := ![height_1, height_347]
theorem height_exact_499_i0 : height_499_i0 = 1 + Finset.univ.sup childrenH_499_i0 := by decide +kernel
theorem required_origin_499_i0 : ∀ x ∈ required_499_i0,
    (∃ j, x ∈ childrenC_499_i0 j) ∨ ∀ j, x ∈ childrenD_499_i0 j := by decide +kernel
theorem required_exact_499_i0 : required_499_i0 =
    ((Finset.univ.biUnion childrenC_499_i0) ∪ commonEnvelope childrenD_499_i0).erase (4, 3) := by
  exact required_eq_combination childrenC_499_i0 childrenD_499_i0 (4, 3) required_499_i0
    (by decide +kernel) child_required_sub_499_i0 common_sub_499_i0 required_origin_499_i0
theorem envelope_origin_499_i0 : ∀ x ∈ envelope_499_i0,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_499_i0 j := by decide +kernel
theorem envelope_exact_499_i0 : envelope_499_i0 =
    insert (4, 3) (Finset.univ.biUnion childrenD_499_i0) := by
  exact envelope_eq_combination childrenD_499_i0 (4, 3) envelope_499_i0
    pivot_mem_499_i0 child_envelope_sub_499_i0 envelope_origin_499_i0
def checked_499_i0 : CheckedCard where
  required := required_499_i0
  envelope := envelope_499_i0
  height := height_499_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_499_i0
def height_499_i1 : ℕ := 4
def childrenH_499_i1 : Fin 2 → ℕ := ![height_43, height_52]
theorem height_exact_499_i1 : height_499_i1 = 1 + Finset.univ.sup childrenH_499_i1 := by decide +kernel
theorem required_origin_499_i1 : ∀ x ∈ required_499_i1,
    (∃ j, x ∈ childrenC_499_i1 j) ∨ ∀ j, x ∈ childrenD_499_i1 j := by decide +kernel
theorem required_exact_499_i1 : required_499_i1 =
    ((Finset.univ.biUnion childrenC_499_i1) ∪ commonEnvelope childrenD_499_i1).erase (3, 3) := by
  exact required_eq_combination childrenC_499_i1 childrenD_499_i1 (3, 3) required_499_i1
    (by decide +kernel) child_required_sub_499_i1 common_sub_499_i1 required_origin_499_i1
theorem envelope_origin_499_i1 : ∀ x ∈ envelope_499_i1,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_499_i1 j := by decide +kernel
theorem envelope_exact_499_i1 : envelope_499_i1 =
    insert (3, 3) (Finset.univ.biUnion childrenD_499_i1) := by
  exact envelope_eq_combination childrenD_499_i1 (3, 3) envelope_499_i1
    pivot_mem_499_i1 child_envelope_sub_499_i1 envelope_origin_499_i1
def checked_499_i1 : CheckedCard where
  required := required_499_i1
  envelope := envelope_499_i1
  height := height_499_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_499_i1
def height_499 : ℕ := 7
def childrenH_499 : Fin 3 → ℕ := ![height_15, height_499_i0, height_499_i1]
theorem height_exact_499 : height_499 = 1 + Finset.univ.sup childrenH_499 := by decide +kernel
theorem required_origin_499 : ∀ x ∈ required_499,
    (∃ j, x ∈ childrenC_499 j) ∨ ∀ j, x ∈ childrenD_499 j := by decide +kernel
theorem required_exact_499 : required_499 =
    ((Finset.univ.biUnion childrenC_499) ∪ commonEnvelope childrenD_499).erase (2, 1) := by
  exact required_eq_combination childrenC_499 childrenD_499 (2, 1) required_499
    (by decide +kernel) child_required_sub_499 common_sub_499 required_origin_499
theorem envelope_origin_499 : ∀ x ∈ envelope_499,
    x = (2, 1) ∨ ∃ j, x ∈ childrenD_499 j := by decide +kernel
theorem envelope_exact_499 : envelope_499 =
    insert (2, 1) (Finset.univ.biUnion childrenD_499) := by
  exact envelope_eq_combination childrenD_499 (2, 1) envelope_499
    pivot_mem_499 child_envelope_sub_499 envelope_origin_499
def checked_499 : CheckedCard where
  required := required_499
  envelope := envelope_499
  height := height_499
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_499
def height_504_i1 : ℕ := 5
def childrenH_504_i1 : Fin 2 → ℕ := ![height_0, height_56]
theorem height_exact_504_i1 : height_504_i1 = 1 + Finset.univ.sup childrenH_504_i1 := by decide +kernel
theorem required_origin_504_i1 : ∀ x ∈ required_504_i1,
    (∃ j, x ∈ childrenC_504_i1 j) ∨ ∀ j, x ∈ childrenD_504_i1 j := by decide +kernel
theorem required_exact_504_i1 : required_504_i1 =
    ((Finset.univ.biUnion childrenC_504_i1) ∪ commonEnvelope childrenD_504_i1).erase (2, 3) := by
  exact required_eq_combination childrenC_504_i1 childrenD_504_i1 (2, 3) required_504_i1
    (by decide +kernel) child_required_sub_504_i1 common_sub_504_i1 required_origin_504_i1
theorem envelope_origin_504_i1 : ∀ x ∈ envelope_504_i1,
    x = (2, 3) ∨ ∃ j, x ∈ childrenD_504_i1 j := by decide +kernel
theorem envelope_exact_504_i1 : envelope_504_i1 =
    insert (2, 3) (Finset.univ.biUnion childrenD_504_i1) := by
  exact envelope_eq_combination childrenD_504_i1 (2, 3) envelope_504_i1
    pivot_mem_504_i1 child_envelope_sub_504_i1 envelope_origin_504_i1
def checked_504_i1 : CheckedCard where
  required := required_504_i1
  envelope := envelope_504_i1
  height := height_504_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_504_i1
def height_504_i0 : ℕ := 6
def childrenH_504_i0 : Fin 3 → ℕ := ![height_6, height_18, height_504_i1]
theorem height_exact_504_i0 : height_504_i0 = 1 + Finset.univ.sup childrenH_504_i0 := by decide +kernel
theorem required_origin_504_i0 : ∀ x ∈ required_504_i0,
    (∃ j, x ∈ childrenC_504_i0 j) ∨ ∀ j, x ∈ childrenD_504_i0 j := by decide +kernel
theorem required_exact_504_i0 : required_504_i0 =
    ((Finset.univ.biUnion childrenC_504_i0) ∪ commonEnvelope childrenD_504_i0).erase (3, 5) := by
  exact required_eq_combination childrenC_504_i0 childrenD_504_i0 (3, 5) required_504_i0
    (by decide +kernel) child_required_sub_504_i0 common_sub_504_i0 required_origin_504_i0
theorem envelope_origin_504_i0 : ∀ x ∈ envelope_504_i0,
    x = (3, 5) ∨ ∃ j, x ∈ childrenD_504_i0 j := by decide +kernel
theorem envelope_exact_504_i0 : envelope_504_i0 =
    insert (3, 5) (Finset.univ.biUnion childrenD_504_i0) := by
  exact envelope_eq_combination childrenD_504_i0 (3, 5) envelope_504_i0
    pivot_mem_504_i0 child_envelope_sub_504_i0 envelope_origin_504_i0
def checked_504_i0 : CheckedCard where
  required := required_504_i0
  envelope := envelope_504_i0
  height := height_504_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_504_i0
def height_504 : ℕ := 7
def childrenH_504 : Fin 2 → ℕ := ![height_32, height_504_i0]
theorem height_exact_504 : height_504 = 1 + Finset.univ.sup childrenH_504 := by decide +kernel
theorem required_origin_504 : ∀ x ∈ required_504,
    (∃ j, x ∈ childrenC_504 j) ∨ ∀ j, x ∈ childrenD_504 j := by decide +kernel
theorem required_exact_504 : required_504 =
    ((Finset.univ.biUnion childrenC_504) ∪ commonEnvelope childrenD_504).erase (3, 1) := by
  exact required_eq_combination childrenC_504 childrenD_504 (3, 1) required_504
    (by decide +kernel) child_required_sub_504 common_sub_504 required_origin_504
theorem envelope_origin_504 : ∀ x ∈ envelope_504,
    x = (3, 1) ∨ ∃ j, x ∈ childrenD_504 j := by decide +kernel
theorem envelope_exact_504 : envelope_504 =
    insert (3, 1) (Finset.univ.biUnion childrenD_504) := by
  exact envelope_eq_combination childrenD_504 (3, 1) envelope_504
    pivot_mem_504 child_envelope_sub_504 envelope_origin_504
def checked_504 : CheckedCard where
  required := required_504
  envelope := envelope_504
  height := height_504
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_504
def height_507_i0 : ℕ := 6
def childrenH_507_i0 : Fin 3 → ℕ := ![height_33, height_44, height_47]
theorem height_exact_507_i0 : height_507_i0 = 1 + Finset.univ.sup childrenH_507_i0 := by decide +kernel
theorem required_origin_507_i0 : ∀ x ∈ required_507_i0,
    (∃ j, x ∈ childrenC_507_i0 j) ∨ ∀ j, x ∈ childrenD_507_i0 j := by decide +kernel
theorem required_exact_507_i0 : required_507_i0 =
    ((Finset.univ.biUnion childrenC_507_i0) ∪ commonEnvelope childrenD_507_i0).erase (3, 5) := by
  exact required_eq_combination childrenC_507_i0 childrenD_507_i0 (3, 5) required_507_i0
    (by decide +kernel) child_required_sub_507_i0 common_sub_507_i0 required_origin_507_i0
theorem envelope_origin_507_i0 : ∀ x ∈ envelope_507_i0,
    x = (3, 5) ∨ ∃ j, x ∈ childrenD_507_i0 j := by decide +kernel
theorem envelope_exact_507_i0 : envelope_507_i0 =
    insert (3, 5) (Finset.univ.biUnion childrenD_507_i0) := by
  exact envelope_eq_combination childrenD_507_i0 (3, 5) envelope_507_i0
    pivot_mem_507_i0 child_envelope_sub_507_i0 envelope_origin_507_i0
def checked_507_i0 : CheckedCard where
  required := required_507_i0
  envelope := envelope_507_i0
  height := height_507_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_507_i0
def height_507 : ℕ := 7
def childrenH_507 : Fin 4 → ℕ := ![height_44, height_274, height_506, height_507_i0]
theorem height_exact_507 : height_507 = 1 + Finset.univ.sup childrenH_507 := by decide +kernel
theorem required_origin_507 : ∀ x ∈ required_507,
    (∃ j, x ∈ childrenC_507 j) ∨ ∀ j, x ∈ childrenD_507 j := by decide +kernel
theorem required_exact_507 : required_507 =
    ((Finset.univ.biUnion childrenC_507) ∪ commonEnvelope childrenD_507).erase (3, 4) := by
  exact required_eq_combination childrenC_507 childrenD_507 (3, 4) required_507
    (by decide +kernel) child_required_sub_507 common_sub_507 required_origin_507
theorem envelope_origin_507 : ∀ x ∈ envelope_507,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_507 j := by decide +kernel
theorem envelope_exact_507 : envelope_507 =
    insert (3, 4) (Finset.univ.biUnion childrenD_507) := by
  exact envelope_eq_combination childrenD_507 (3, 4) envelope_507
    pivot_mem_507 child_envelope_sub_507 envelope_origin_507
def checked_507 : CheckedCard where
  required := required_507
  envelope := envelope_507
  height := height_507
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_507
end SnakyPrototype.Certificate21

end OAI
