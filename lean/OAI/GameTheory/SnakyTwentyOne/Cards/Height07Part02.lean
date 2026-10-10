import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part04
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_361 : Finset Cell := ⟨(([(2, 2), (2, 3), (3, 2), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_361 : Finset Cell := ⟨(([(0, 2), (1, 2), (1, 4), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 3), (4, 4), (4, 5), (4, 6), (5, 3), (5, 4), (6, 3), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_361 : Fin 3 → Finset Cell := ![(placed21 2 (3, 0) required_15), (placed21 1 (0, 0) required_57), (placed21 1 (1, 1) required_360)]
def childrenD_361 : Fin 3 → Finset Cell := ![(placed21 2 (3, 0) envelope_15), (placed21 1 (0, 0) envelope_57), (placed21 1 (1, 1) envelope_360)]
theorem common_sub_361 : commonEnvelope childrenD_361 ⊆ insert (3, 1) required_361 := by decide +kernel
theorem child_required_sub_361 : ∀ j, childrenC_361 j ⊆ insert (3, 1) required_361 := by decide +kernel
theorem child_envelope_sub_361 : ∀ j, childrenD_361 j ⊆ envelope_361 := by decide +kernel
theorem pivot_mem_361 : (3, 1) ∈ envelope_361 := by decide +kernel
theorem children_work_361 : ∀ j, Template HasSnaky 6 (childrenC_361 j) (childrenD_361 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_15 2 (3, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_57 1 (0, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_360 1 (1, 1)).mono (by decide +kernel)
theorem row_works_361 : Template HasSnaky 7 required_361 envelope_361 := by
  refine compose HasSnaky 6 childrenC_361 childrenD_361 children_work_361 (3, 1)
    required_361 envelope_361 pivot_mem_361 child_required_sub_361 child_envelope_sub_361 ?_
  intro b hb
  exact common_sub_361 (mem_commonEnvelope childrenD_361 b hb)
def required_372_i0 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 3), (1, 4), (2, 1), (3, 1), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_372_i0 : Finset Cell := ⟨(([(0, 3), (1, 1), (1, 2), (1, 3), (1, 4), (2, 1), (2, 3), (2, 4), (2, 5), (3, 1), (3, 4), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 0), (5, 1), (5, 2), (5, 4), (5, 5), (6, 0), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_372_i0 : Fin 2 → Finset Cell := ![(placed21 1 (0, 1) required_81), (placed21 0 (1, 0) required_351)]
def childrenD_372_i0 : Fin 2 → Finset Cell := ![(placed21 1 (0, 1) envelope_81), (placed21 0 (1, 0) envelope_351)]
theorem common_sub_372_i0 : commonEnvelope childrenD_372_i0 ⊆ insert (4, 4) required_372_i0 := by decide +kernel
theorem child_required_sub_372_i0 : ∀ j, childrenC_372_i0 j ⊆ insert (4, 4) required_372_i0 := by decide +kernel
theorem child_envelope_sub_372_i0 : ∀ j, childrenD_372_i0 j ⊆ envelope_372_i0 := by decide +kernel
theorem pivot_mem_372_i0 : (4, 4) ∈ envelope_372_i0 := by decide +kernel
theorem children_work_372_i0 : ∀ j, Template HasSnaky 5 (childrenC_372_i0 j) (childrenD_372_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_81 1 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_351 0 (1, 0)).mono (by decide +kernel)
theorem row_works_372_i0 : Template HasSnaky 6 required_372_i0 envelope_372_i0 := by
  refine compose HasSnaky 5 childrenC_372_i0 childrenD_372_i0 children_work_372_i0 (4, 4)
    required_372_i0 envelope_372_i0 pivot_mem_372_i0 child_required_sub_372_i0 child_envelope_sub_372_i0 ?_
  intro b hb
  exact common_sub_372_i0 (mem_commonEnvelope childrenD_372_i0 b hb)
def required_372 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 3), (1, 4), (2, 1), (3, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_372 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 3), (1, 1), (1, 2), (1, 3), (1, 4), (2, 1), (2, 3), (2, 4), (2, 5), (3, 1), (3, 2), (3, 4), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 0), (5, 1), (5, 2), (5, 4), (5, 5), (6, 0), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_372 : Fin 2 → Finset Cell := ![(placed21 3 (0, 4) required_96), required_372_i0]
def childrenD_372 : Fin 2 → Finset Cell := ![(placed21 3 (0, 4) envelope_96), envelope_372_i0]
theorem common_sub_372 : commonEnvelope childrenD_372 ⊆ insert (4, 2) required_372 := by decide +kernel
theorem child_required_sub_372 : ∀ j, childrenC_372 j ⊆ insert (4, 2) required_372 := by decide +kernel
theorem child_envelope_sub_372 : ∀ j, childrenD_372 j ⊆ envelope_372 := by decide +kernel
theorem pivot_mem_372 : (4, 2) ∈ envelope_372 := by decide +kernel
theorem children_work_372 : ∀ j, Template HasSnaky 6 (childrenC_372 j) (childrenD_372 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_96 3 (0, 4)).mono (by decide +kernel)
  · exact row_works_372_i0.mono (by decide +kernel)
theorem row_works_372 : Template HasSnaky 7 required_372 envelope_372 := by
  refine compose HasSnaky 6 childrenC_372 childrenD_372 children_work_372 (4, 2)
    required_372 envelope_372 pivot_mem_372 child_required_sub_372 child_envelope_sub_372 ?_
  intro b hb
  exact common_sub_372 (mem_commonEnvelope childrenD_372 b hb)
def required_379 : Finset Cell := ⟨(([(0, 2), (1, 1), (1, 2), (2, 0), (2, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_379 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 1), (5, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_379 : Fin 3 → Finset Cell := ![(placed21 3 (0, 2) required_21), (placed21 1 (0, 1) required_37), required_378]
def childrenD_379 : Fin 3 → Finset Cell := ![(placed21 3 (0, 2) envelope_21), (placed21 1 (0, 1) envelope_37), envelope_378]
theorem common_sub_379 : commonEnvelope childrenD_379 ⊆ insert (3, 2) required_379 := by decide +kernel
theorem child_required_sub_379 : ∀ j, childrenC_379 j ⊆ insert (3, 2) required_379 := by decide +kernel
theorem child_envelope_sub_379 : ∀ j, childrenD_379 j ⊆ envelope_379 := by decide +kernel
theorem pivot_mem_379 : (3, 2) ∈ envelope_379 := by decide +kernel
theorem children_work_379 : ∀ j, Template HasSnaky 6 (childrenC_379 j) (childrenD_379 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_21 3 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_37 1 (0, 1)).mono (by decide +kernel)
  · exact row_works_378.mono (by decide +kernel)
theorem row_works_379 : Template HasSnaky 7 required_379 envelope_379 := by
  refine compose HasSnaky 6 childrenC_379 childrenD_379 children_work_379 (3, 2)
    required_379 envelope_379 pivot_mem_379 child_required_sub_379 child_envelope_sub_379 ?_
  intro b hb
  exact common_sub_379 (mem_commonEnvelope childrenD_379 b hb)
def required_385 : Finset Cell := ⟨(([(0, 2), (3, 1), (3, 2), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_385 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 3), (1, 1), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1), (2, 3), (2, 4), (2, 5), (3, 1), (3, 2), (3, 3), (3, 4), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 2), (5, 3), (5, 4), (5, 5), (6, 3), (6, 4), (6, 5), (7, 3), (7, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_385 : Fin 2 → Finset Cell := ![(placed21 1 (0, 1) required_115), (placed21 7 (5, 4) required_383)]
def childrenD_385 : Fin 2 → Finset Cell := ![(placed21 1 (0, 1) envelope_115), (placed21 7 (5, 4) envelope_383)]
theorem common_sub_385 : commonEnvelope childrenD_385 ⊆ insert (3, 3) required_385 := by decide +kernel
theorem child_required_sub_385 : ∀ j, childrenC_385 j ⊆ insert (3, 3) required_385 := by decide +kernel
theorem child_envelope_sub_385 : ∀ j, childrenD_385 j ⊆ envelope_385 := by decide +kernel
theorem pivot_mem_385 : (3, 3) ∈ envelope_385 := by decide +kernel
theorem children_work_385 : ∀ j, Template HasSnaky 6 (childrenC_385 j) (childrenD_385 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_115 1 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_383 7 (5, 4)).mono (by decide +kernel)
theorem row_works_385 : Template HasSnaky 7 required_385 envelope_385 := by
  refine compose HasSnaky 6 childrenC_385 childrenD_385 children_work_385 (3, 3)
    required_385 envelope_385 pivot_mem_385 child_required_sub_385 child_envelope_sub_385 ?_
  intro b hb
  exact common_sub_385 (mem_commonEnvelope childrenD_385 b hb)
def required_388 : Finset Cell := ⟨(([(0, 2), (1, 2), (2, 1), (2, 2), (2, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_388 : Finset Cell := ⟨(([(0, 2), (0, 3), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 2), (3, 3), (3, 4), (3, 5), (4, 3), (4, 4), (5, 3), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_388 : Fin 2 → Finset Cell := ![(placed21 2 (2, 0) required_11), (placed21 0 (0, 1) required_387)]
def childrenD_388 : Fin 2 → Finset Cell := ![(placed21 2 (2, 0) envelope_11), (placed21 0 (0, 1) envelope_387)]
theorem common_sub_388 : commonEnvelope childrenD_388 ⊆ insert (2, 4) required_388 := by decide +kernel
theorem child_required_sub_388 : ∀ j, childrenC_388 j ⊆ insert (2, 4) required_388 := by decide +kernel
theorem child_envelope_sub_388 : ∀ j, childrenD_388 j ⊆ envelope_388 := by decide +kernel
theorem pivot_mem_388 : (2, 4) ∈ envelope_388 := by decide +kernel
theorem children_work_388 : ∀ j, Template HasSnaky 6 (childrenC_388 j) (childrenD_388 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_11 2 (2, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_387 0 (0, 1)).mono (by decide +kernel)
theorem row_works_388 : Template HasSnaky 7 required_388 envelope_388 := by
  refine compose HasSnaky 6 childrenC_388 childrenD_388 children_work_388 (2, 4)
    required_388 envelope_388 pivot_mem_388 child_required_sub_388 child_envelope_sub_388 ?_
  intro b hb
  exact common_sub_388 (mem_commonEnvelope childrenD_388 b hb)
def required_394 : Finset Cell := ⟨(([(0, 2), (1, 1), (1, 2), (1, 3), (2, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_394 : Finset Cell := ⟨(([(0, 2), (0, 3), (0, 5), (0, 6), (0, 7), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 0), (3, 1), (3, 2), (3, 3), (4, 1), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_394 : Fin 3 → Finset Cell := ![(placed21 0 (0, 1) required_17), required_241, required_392]
def childrenD_394 : Fin 3 → Finset Cell := ![(placed21 0 (0, 1) envelope_17), envelope_241, envelope_392]
theorem common_sub_394 : commonEnvelope childrenD_394 ⊆ insert (1, 4) required_394 := by decide +kernel
theorem child_required_sub_394 : ∀ j, childrenC_394 j ⊆ insert (1, 4) required_394 := by decide +kernel
theorem child_envelope_sub_394 : ∀ j, childrenD_394 j ⊆ envelope_394 := by decide +kernel
theorem pivot_mem_394 : (1, 4) ∈ envelope_394 := by decide +kernel
theorem children_work_394 : ∀ j, Template HasSnaky 6 (childrenC_394 j) (childrenD_394 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_17 0 (0, 1)).mono (by decide +kernel)
  · exact row_works_241.mono (by decide +kernel)
  · exact row_works_392.mono (by decide +kernel)
theorem row_works_394 : Template HasSnaky 7 required_394 envelope_394 := by
  refine compose HasSnaky 6 childrenC_394 childrenD_394 children_work_394 (1, 4)
    required_394 envelope_394 pivot_mem_394 child_required_sub_394 child_envelope_sub_394 ?_
  intro b hb
  exact common_sub_394 (mem_commonEnvelope childrenD_394 b hb)
def required_404_i1 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 1), (1, 2), (2, 1), (2, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_404_i1 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 1), (1, 2), (2, 1), (2, 2), (2, 3), (2, 4), (3, 0), (3, 1), (3, 2), (3, 3), (4, 0), (4, 1), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_404_i1 : Fin 2 → Finset Cell := ![(placed21 2 (4, 1) required_0), required_354]
def childrenD_404_i1 : Fin 2 → Finset Cell := ![(placed21 2 (4, 1) envelope_0), envelope_354]
theorem common_sub_404_i1 : commonEnvelope childrenD_404_i1 ⊆ insert (3, 1) required_404_i1 := by decide +kernel
theorem child_required_sub_404_i1 : ∀ j, childrenC_404_i1 j ⊆ insert (3, 1) required_404_i1 := by decide +kernel
theorem child_envelope_sub_404_i1 : ∀ j, childrenD_404_i1 j ⊆ envelope_404_i1 := by decide +kernel
theorem pivot_mem_404_i1 : (3, 1) ∈ envelope_404_i1 := by decide +kernel
theorem children_work_404_i1 : ∀ j, Template HasSnaky 4 (childrenC_404_i1 j) (childrenD_404_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 2 (4, 1)).mono (by decide +kernel)
  · exact row_works_354.mono (by decide +kernel)
theorem row_works_404_i1 : Template HasSnaky 5 required_404_i1 envelope_404_i1 := by
  refine compose HasSnaky 4 childrenC_404_i1 childrenD_404_i1 children_work_404_i1 (3, 1)
    required_404_i1 envelope_404_i1 pivot_mem_404_i1 child_required_sub_404_i1 child_envelope_sub_404_i1 ?_
  intro b hb
  exact common_sub_404_i1 (mem_commonEnvelope childrenD_404_i1 b hb)
def required_404_i0 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 1), (1, 2), (1, 3), (1, 4), (2, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_404_i0 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 1), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, 0), (3, 1), (3, 2), (3, 3), (4, 0), (4, 1), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_404_i0 : Fin 2 → Finset Cell := ![(placed21 3 (1, 4) required_5), required_404_i1]
def childrenD_404_i0 : Fin 2 → Finset Cell := ![(placed21 3 (1, 4) envelope_5), envelope_404_i1]
theorem common_sub_404_i0 : commonEnvelope childrenD_404_i0 ⊆ insert (2, 1) required_404_i0 := by decide +kernel
theorem child_required_sub_404_i0 : ∀ j, childrenC_404_i0 j ⊆ insert (2, 1) required_404_i0 := by decide +kernel
theorem child_envelope_sub_404_i0 : ∀ j, childrenD_404_i0 j ⊆ envelope_404_i0 := by decide +kernel
theorem pivot_mem_404_i0 : (2, 1) ∈ envelope_404_i0 := by decide +kernel
theorem children_work_404_i0 : ∀ j, Template HasSnaky 5 (childrenC_404_i0 j) (childrenD_404_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 3 (1, 4)).mono (by decide +kernel)
  · exact row_works_404_i1.mono (by decide +kernel)
theorem row_works_404_i0 : Template HasSnaky 6 required_404_i0 envelope_404_i0 := by
  refine compose HasSnaky 5 childrenC_404_i0 childrenD_404_i0 children_work_404_i0 (2, 1)
    required_404_i0 envelope_404_i0 pivot_mem_404_i0 child_required_sub_404_i0 child_envelope_sub_404_i0 ?_
  intro b hb
  exact common_sub_404_i0 (mem_commonEnvelope childrenD_404_i0 b hb)
def required_404 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 1), (1, 2), (1, 3), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_404 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 1), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (4, 0), (4, 1), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_404 : Fin 2 → Finset Cell := ![(placed21 1 (1, 1) required_5), required_404_i0]
def childrenD_404 : Fin 2 → Finset Cell := ![(placed21 1 (1, 1) envelope_5), envelope_404_i0]
theorem common_sub_404 : commonEnvelope childrenD_404 ⊆ insert (2, 4) required_404 := by decide +kernel
theorem child_required_sub_404 : ∀ j, childrenC_404 j ⊆ insert (2, 4) required_404 := by decide +kernel
theorem child_envelope_sub_404 : ∀ j, childrenD_404 j ⊆ envelope_404 := by decide +kernel
theorem pivot_mem_404 : (2, 4) ∈ envelope_404 := by decide +kernel
theorem children_work_404 : ∀ j, Template HasSnaky 6 (childrenC_404 j) (childrenD_404 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 1 (1, 1)).mono (by decide +kernel)
  · exact row_works_404_i0.mono (by decide +kernel)
theorem row_works_404 : Template HasSnaky 7 required_404 envelope_404 := by
  refine compose HasSnaky 6 childrenC_404 childrenD_404 children_work_404 (2, 4)
    required_404 envelope_404 pivot_mem_404 child_required_sub_404 child_envelope_sub_404 ?_
  intro b hb
  exact common_sub_404 (mem_commonEnvelope childrenD_404 b hb)
def required_415 : Finset Cell := ⟨(([(0, 2), (1, 2), (3, 1), (4, 1), (4, 2), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_415 : Finset Cell := ⟨(([(0, 2), (0, 4), (1, 2), (1, 4), (2, 2), (2, 4), (2, 5), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_415 : Fin 2 → Finset Cell := ![(placed21 4 (0, 2) required_2), (placed21 2 (5, 0) required_414)]
def childrenD_415 : Fin 2 → Finset Cell := ![(placed21 4 (0, 2) envelope_2), (placed21 2 (5, 0) envelope_414)]
theorem common_sub_415 : commonEnvelope childrenD_415 ⊆ insert (3, 2) required_415 := by decide +kernel
theorem child_required_sub_415 : ∀ j, childrenC_415 j ⊆ insert (3, 2) required_415 := by decide +kernel
theorem child_envelope_sub_415 : ∀ j, childrenD_415 j ⊆ envelope_415 := by decide +kernel
theorem pivot_mem_415 : (3, 2) ∈ envelope_415 := by decide +kernel
theorem children_work_415 : ∀ j, Template HasSnaky 6 (childrenC_415 j) (childrenD_415 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_2 4 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_414 2 (5, 0)).mono (by decide +kernel)
theorem row_works_415 : Template HasSnaky 7 required_415 envelope_415 := by
  refine compose HasSnaky 6 childrenC_415 childrenD_415 children_work_415 (3, 2)
    required_415 envelope_415 pivot_mem_415 child_required_sub_415 child_envelope_sub_415 ?_
  intro b hb
  exact common_sub_415 (mem_commonEnvelope childrenD_415 b hb)
def required_418_i2 : Finset Cell := ⟨(([(0, 2), (1, 2), (2, 1), (3, 0), (3, 1), (3, 2), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_418_i2 : Finset Cell := ⟨(([(0, 2), (1, 2), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_418_i2 : Fin 2 → Finset Cell := ![(placed21 0 (0, 2) required_5), (placed21 2 (3, 0) required_29)]
def childrenD_418_i2 : Fin 2 → Finset Cell := ![(placed21 0 (0, 2) envelope_5), (placed21 2 (3, 0) envelope_29)]
theorem common_sub_418_i2 : commonEnvelope childrenD_418_i2 ⊆ insert (2, 2) required_418_i2 := by decide +kernel
theorem child_required_sub_418_i2 : ∀ j, childrenC_418_i2 j ⊆ insert (2, 2) required_418_i2 := by decide +kernel
theorem child_envelope_sub_418_i2 : ∀ j, childrenD_418_i2 j ⊆ envelope_418_i2 := by decide +kernel
theorem pivot_mem_418_i2 : (2, 2) ∈ envelope_418_i2 := by decide +kernel
theorem children_work_418_i2 : ∀ j, Template HasSnaky 3 (childrenC_418_i2 j) (childrenD_418_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 0 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_29 2 (3, 0)).mono (by decide +kernel)
theorem row_works_418_i2 : Template HasSnaky 4 required_418_i2 envelope_418_i2 := by
  refine compose HasSnaky 3 childrenC_418_i2 childrenD_418_i2 children_work_418_i2 (2, 2)
    required_418_i2 envelope_418_i2 pivot_mem_418_i2 child_required_sub_418_i2 child_envelope_sub_418_i2 ?_
  intro b hb
  exact common_sub_418_i2 (mem_commonEnvelope childrenD_418_i2 b hb)
def required_418_i1 : Finset Cell := ⟨(([(0, 2), (1, 2), (2, 1), (3, 0), (3, 1), (3, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_418_i1 : Finset Cell := ⟨(([(0, 2), (1, 2), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 3), (4, 4), (4, 5), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_418_i1 : Fin 4 → Finset Cell := ![(placed21 1 (2, 0) required_8), (placed21 5 (4, 0) required_25), (placed21 0 (2, 0) required_41), required_418_i2]
def childrenD_418_i1 : Fin 4 → Finset Cell := ![(placed21 1 (2, 0) envelope_8), (placed21 5 (4, 0) envelope_25), (placed21 0 (2, 0) envelope_41), envelope_418_i2]
theorem common_sub_418_i1 : commonEnvelope childrenD_418_i1 ⊆ insert (3, 3) required_418_i1 := by decide +kernel
theorem child_required_sub_418_i1 : ∀ j, childrenC_418_i1 j ⊆ insert (3, 3) required_418_i1 := by decide +kernel
theorem child_envelope_sub_418_i1 : ∀ j, childrenD_418_i1 j ⊆ envelope_418_i1 := by decide +kernel
theorem pivot_mem_418_i1 : (3, 3) ∈ envelope_418_i1 := by decide +kernel
theorem children_work_418_i1 : ∀ j, Template HasSnaky 4 (childrenC_418_i1 j) (childrenD_418_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_8 1 (2, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_25 5 (4, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_41 0 (2, 0)).mono (by decide +kernel)
  · exact row_works_418_i2.mono (by decide +kernel)
theorem row_works_418_i1 : Template HasSnaky 5 required_418_i1 envelope_418_i1 := by
  refine compose HasSnaky 4 childrenC_418_i1 childrenD_418_i1 children_work_418_i1 (3, 3)
    required_418_i1 envelope_418_i1 pivot_mem_418_i1 child_required_sub_418_i1 child_envelope_sub_418_i1 ?_
  intro b hb
  exact common_sub_418_i1 (mem_commonEnvelope childrenD_418_i1 b hb)
def required_418_i0 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 1), (1, 2), (2, 1), (3, 0), (3, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_418_i0 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 1), (1, 2), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_418_i0 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) required_5), required_418_i1]
def childrenD_418_i0 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) envelope_5), envelope_418_i1]
theorem common_sub_418_i0 : commonEnvelope childrenD_418_i0 ⊆ insert (3, 2) required_418_i0 := by decide +kernel
theorem child_required_sub_418_i0 : ∀ j, childrenC_418_i0 j ⊆ insert (3, 2) required_418_i0 := by decide +kernel
theorem child_envelope_sub_418_i0 : ∀ j, childrenD_418_i0 j ⊆ envelope_418_i0 := by decide +kernel
theorem pivot_mem_418_i0 : (3, 2) ∈ envelope_418_i0 := by decide +kernel
theorem children_work_418_i0 : ∀ j, Template HasSnaky 5 (childrenC_418_i0 j) (childrenD_418_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 0 (0, 1)).mono (by decide +kernel)
  · exact row_works_418_i1.mono (by decide +kernel)
theorem row_works_418_i0 : Template HasSnaky 6 required_418_i0 envelope_418_i0 := by
  refine compose HasSnaky 5 childrenC_418_i0 childrenD_418_i0 children_work_418_i0 (3, 2)
    required_418_i0 envelope_418_i0 pivot_mem_418_i0 child_required_sub_418_i0 child_envelope_sub_418_i0 ?_
  intro b hb
  exact common_sub_418_i0 (mem_commonEnvelope childrenD_418_i0 b hb)
def required_418 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 1), (1, 2), (2, 1), (3, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_418 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 1), (1, 2), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 0), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_418 : Fin 2 → Finset Cell := ![(placed21 4 (0, 1) required_5), required_418_i0]
def childrenD_418 : Fin 2 → Finset Cell := ![(placed21 4 (0, 1) envelope_5), envelope_418_i0]
theorem common_sub_418 : commonEnvelope childrenD_418 ⊆ insert (3, 0) required_418 := by decide +kernel
theorem child_required_sub_418 : ∀ j, childrenC_418 j ⊆ insert (3, 0) required_418 := by decide +kernel
theorem child_envelope_sub_418 : ∀ j, childrenD_418 j ⊆ envelope_418 := by decide +kernel
theorem pivot_mem_418 : (3, 0) ∈ envelope_418 := by decide +kernel
theorem children_work_418 : ∀ j, Template HasSnaky 6 (childrenC_418 j) (childrenD_418 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 4 (0, 1)).mono (by decide +kernel)
  · exact row_works_418_i0.mono (by decide +kernel)
theorem row_works_418 : Template HasSnaky 7 required_418 envelope_418 := by
  refine compose HasSnaky 6 childrenC_418 childrenD_418 children_work_418 (3, 0)
    required_418 envelope_418 pivot_mem_418 child_required_sub_418 child_envelope_sub_418 ?_
  intro b hb
  exact common_sub_418 (mem_commonEnvelope childrenD_418 b hb)
def required_422_i0 : Finset Cell := ⟨(([(1, 2), (2, 2), (3, 2), (3, 3), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_422_i0 : Finset Cell := ⟨(([(0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 1), (2, 2), (2, 3), (3, 2), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 2), (4, 3), (5, 1), (5, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_422_i0 : Fin 2 → Finset Cell := ![(placed21 0 (1, 0) required_69), (placed21 5 (5, 1) required_413)]
def childrenD_422_i0 : Fin 2 → Finset Cell := ![(placed21 0 (1, 0) envelope_69), (placed21 5 (5, 1) envelope_413)]
theorem common_sub_422_i0 : commonEnvelope childrenD_422_i0 ⊆ insert (4, 2) required_422_i0 := by decide +kernel
theorem child_required_sub_422_i0 : ∀ j, childrenC_422_i0 j ⊆ insert (4, 2) required_422_i0 := by decide +kernel
theorem child_envelope_sub_422_i0 : ∀ j, childrenD_422_i0 j ⊆ envelope_422_i0 := by decide +kernel
theorem pivot_mem_422_i0 : (4, 2) ∈ envelope_422_i0 := by decide +kernel
theorem children_work_422_i0 : ∀ j, Template HasSnaky 5 (childrenC_422_i0 j) (childrenD_422_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_69 0 (1, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_413 5 (5, 1)).mono (by decide +kernel)
theorem row_works_422_i0 : Template HasSnaky 6 required_422_i0 envelope_422_i0 := by
  refine compose HasSnaky 5 childrenC_422_i0 childrenD_422_i0 children_work_422_i0 (4, 2)
    required_422_i0 envelope_422_i0 pivot_mem_422_i0 child_required_sub_422_i0 child_envelope_sub_422_i0 ?_
  intro b hb
  exact common_sub_422_i0 (mem_commonEnvelope childrenD_422_i0 b hb)
def required_422 : Finset Cell := ⟨(([(1, 2), (3, 2), (3, 3), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_422 : Finset Cell := ⟨(([(0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 1), (2, 2), (2, 3), (3, 2), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 2), (4, 3), (5, 1), (5, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_422 : Fin 2 → Finset Cell := ![(placed21 0 (0, 2) required_0), required_422_i0]
def childrenD_422 : Fin 2 → Finset Cell := ![(placed21 0 (0, 2) envelope_0), envelope_422_i0]
theorem common_sub_422 : commonEnvelope childrenD_422 ⊆ insert (2, 2) required_422 := by decide +kernel
theorem child_required_sub_422 : ∀ j, childrenC_422 j ⊆ insert (2, 2) required_422 := by decide +kernel
theorem child_envelope_sub_422 : ∀ j, childrenD_422 j ⊆ envelope_422 := by decide +kernel
theorem pivot_mem_422 : (2, 2) ∈ envelope_422 := by decide +kernel
theorem children_work_422 : ∀ j, Template HasSnaky 6 (childrenC_422 j) (childrenD_422 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 0 (0, 2)).mono (by decide +kernel)
  · exact row_works_422_i0.mono (by decide +kernel)
theorem row_works_422 : Template HasSnaky 7 required_422 envelope_422 := by
  refine compose HasSnaky 6 childrenC_422 childrenD_422 children_work_422 (2, 2)
    required_422 envelope_422 pivot_mem_422 child_required_sub_422 child_envelope_sub_422 ?_
  intro b hb
  exact common_sub_422 (mem_commonEnvelope childrenD_422 b hb)
def required_430 : Finset Cell := ⟨(([(0, 4), (1, 4), (3, 3), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_430 : Finset Cell := ⟨(([(0, 4), (0, 6), (1, 4), (1, 6), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 0), (4, 1), (4, 2), (4, 5), (4, 6), (4, 7), (4, 8), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_430 : Fin 5 → Finset Cell := ![(placed21 4 (2, 7) required_14), (placed21 4 (2, 7) required_31), (placed21 0 (0, 2) required_58), (placed21 4 (0, 6) required_100), (placed21 0 (0, 2) required_429)]
def childrenD_430 : Fin 5 → Finset Cell := ![(placed21 4 (2, 7) envelope_14), (placed21 4 (2, 7) envelope_31), (placed21 0 (0, 2) envelope_58), (placed21 4 (0, 6) envelope_100), (placed21 0 (0, 2) envelope_429)]
theorem common_sub_430 : commonEnvelope childrenD_430 ⊆ insert (3, 5) required_430 := by decide +kernel
theorem child_required_sub_430 : ∀ j, childrenC_430 j ⊆ insert (3, 5) required_430 := by decide +kernel
theorem child_envelope_sub_430 : ∀ j, childrenD_430 j ⊆ envelope_430 := by decide +kernel
theorem pivot_mem_430 : (3, 5) ∈ envelope_430 := by decide +kernel
theorem children_work_430 : ∀ j, Template HasSnaky 6 (childrenC_430 j) (childrenD_430 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_14 4 (2, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_31 4 (2, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_58 0 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_100 4 (0, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_429 0 (0, 2)).mono (by decide +kernel)
theorem row_works_430 : Template HasSnaky 7 required_430 envelope_430 := by
  refine compose HasSnaky 6 childrenC_430 childrenD_430 children_work_430 (3, 5)
    required_430 envelope_430 pivot_mem_430 child_required_sub_430 child_envelope_sub_430 ?_
  intro b hb
  exact common_sub_430 (mem_commonEnvelope childrenD_430 b hb)
def required_431 : Finset Cell := ⟨(([(1, 3), (2, 2), (2, 3), (4, 2), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_431 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (1, 3), (1, 5), (2, 2), (2, 3), (2, 4), (2, 5), (3, 1), (3, 2), (3, 3), (3, 5), (3, 6), (3, 7), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_431 : Fin 3 → Finset Cell := ![(placed21 7 (5, 4) required_160), (placed21 2 (5, 0) required_243), (placed21 0 (1, 1) required_429)]
def childrenD_431 : Fin 3 → Finset Cell := ![(placed21 7 (5, 4) envelope_160), (placed21 2 (5, 0) envelope_243), (placed21 0 (1, 1) envelope_429)]
theorem common_sub_431 : commonEnvelope childrenD_431 ⊆ insert (4, 4) required_431 := by decide +kernel
theorem child_required_sub_431 : ∀ j, childrenC_431 j ⊆ insert (4, 4) required_431 := by decide +kernel
theorem child_envelope_sub_431 : ∀ j, childrenD_431 j ⊆ envelope_431 := by decide +kernel
theorem pivot_mem_431 : (4, 4) ∈ envelope_431 := by decide +kernel
theorem children_work_431 : ∀ j, Template HasSnaky 6 (childrenC_431 j) (childrenD_431 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_160 7 (5, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_243 2 (5, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_429 0 (1, 1)).mono (by decide +kernel)
theorem row_works_431 : Template HasSnaky 7 required_431 envelope_431 := by
  refine compose HasSnaky 6 childrenC_431 childrenD_431 children_work_431 (4, 4)
    required_431 envelope_431 pivot_mem_431 child_required_sub_431 child_envelope_sub_431 ?_
  intro b hb
  exact common_sub_431 (mem_commonEnvelope childrenD_431 b hb)
def required_436 : Finset Cell := ⟨(([(2, 3), (3, 3), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_436 : Finset Cell := ⟨(([(0, 5), (1, 3), (1, 5), (2, 0), (2, 1), (2, 2), (2, 3), (2, 5), (2, 6), (2, 7), (2, 8), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 0), (4, 1), (4, 2), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 2), (5, 4), (5, 6), (6, 2), (6, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_436 : Fin 4 → Finset Cell := ![(placed21 0 (2, 2) required_10), (placed21 3 (1, 6) required_47), (placed21 6 (3, 6) required_52), (placed21 5 (6, 2) required_435)]
def childrenD_436 : Fin 4 → Finset Cell := ![(placed21 0 (2, 2) envelope_10), (placed21 3 (1, 6) envelope_47), (placed21 6 (3, 6) envelope_52), (placed21 5 (6, 2) envelope_435)]
theorem common_sub_436 : commonEnvelope childrenD_436 ⊆ insert (3, 5) required_436 := by decide +kernel
theorem child_required_sub_436 : ∀ j, childrenC_436 j ⊆ insert (3, 5) required_436 := by decide +kernel
theorem child_envelope_sub_436 : ∀ j, childrenD_436 j ⊆ envelope_436 := by decide +kernel
theorem pivot_mem_436 : (3, 5) ∈ envelope_436 := by decide +kernel
theorem children_work_436 : ∀ j, Template HasSnaky 6 (childrenC_436 j) (childrenD_436 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_10 0 (2, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_47 3 (1, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_52 6 (3, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_435 5 (6, 2)).mono (by decide +kernel)
theorem row_works_436 : Template HasSnaky 7 required_436 envelope_436 := by
  refine compose HasSnaky 6 childrenC_436 childrenD_436 children_work_436 (3, 5)
    required_436 envelope_436 pivot_mem_436 child_required_sub_436 child_envelope_sub_436 ?_
  intro b hb
  exact common_sub_436 (mem_commonEnvelope childrenD_436 b hb)
def required_437 : Finset Cell := ⟨(([(2, 3), (3, 3), (3, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_437 : Finset Cell := ⟨(([(0, 5), (1, 3), (1, 5), (2, 0), (2, 1), (2, 2), (2, 3), (2, 5), (2, 6), (2, 7), (2, 8), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 0), (4, 1), (4, 2), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 2), (5, 4), (5, 6), (6, 2), (6, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_437 : Fin 4 → Finset Cell := ![(placed21 0 (2, 2) required_10), (placed21 3 (1, 6) required_47), (placed21 6 (3, 6) required_52), (placed21 5 (6, 2) required_435)]
def childrenD_437 : Fin 4 → Finset Cell := ![(placed21 0 (2, 2) envelope_10), (placed21 3 (1, 6) envelope_47), (placed21 6 (3, 6) envelope_52), (placed21 5 (6, 2) envelope_435)]
theorem common_sub_437 : commonEnvelope childrenD_437 ⊆ insert (3, 4) required_437 := by decide +kernel
theorem child_required_sub_437 : ∀ j, childrenC_437 j ⊆ insert (3, 4) required_437 := by decide +kernel
theorem child_envelope_sub_437 : ∀ j, childrenD_437 j ⊆ envelope_437 := by decide +kernel
theorem pivot_mem_437 : (3, 4) ∈ envelope_437 := by decide +kernel
theorem children_work_437 : ∀ j, Template HasSnaky 6 (childrenC_437 j) (childrenD_437 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_10 0 (2, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_47 3 (1, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_52 6 (3, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_435 5 (6, 2)).mono (by decide +kernel)
theorem row_works_437 : Template HasSnaky 7 required_437 envelope_437 := by
  refine compose HasSnaky 6 childrenC_437 childrenD_437 children_work_437 (3, 4)
    required_437 envelope_437 pivot_mem_437 child_required_sub_437 child_envelope_sub_437 ?_
  intro b hb
  exact common_sub_437 (mem_commonEnvelope childrenD_437 b hb)
def required_446_i0 : Finset Cell := ⟨(([(0, 3), (1, 3), (1, 4), (1, 5), (1, 6), (2, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_446_i0 : Finset Cell := ⟨(([(0, 3), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 2), (4, 3), (4, 4), (5, 2), (5, 3), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_446_i0 : Fin 2 → Finset Cell := ![(placed21 3 (1, 7) required_0), (placed21 4 (0, 5) required_72)]
def childrenD_446_i0 : Fin 2 → Finset Cell := ![(placed21 3 (1, 7) envelope_0), (placed21 4 (0, 5) envelope_72)]
theorem common_sub_446_i0 : commonEnvelope childrenD_446_i0 ⊆ insert (2, 4) required_446_i0 := by decide +kernel
theorem child_required_sub_446_i0 : ∀ j, childrenC_446_i0 j ⊆ insert (2, 4) required_446_i0 := by decide +kernel
theorem child_envelope_sub_446_i0 : ∀ j, childrenD_446_i0 j ⊆ envelope_446_i0 := by decide +kernel
theorem pivot_mem_446_i0 : (2, 4) ∈ envelope_446_i0 := by decide +kernel
theorem children_work_446_i0 : ∀ j, Template HasSnaky 5 (childrenC_446_i0 j) (childrenD_446_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 3 (1, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_72 4 (0, 5)).mono (by decide +kernel)
theorem row_works_446_i0 : Template HasSnaky 6 required_446_i0 envelope_446_i0 := by
  refine compose HasSnaky 5 childrenC_446_i0 childrenD_446_i0 children_work_446_i0 (2, 4)
    required_446_i0 envelope_446_i0 pivot_mem_446_i0 child_required_sub_446_i0 child_envelope_sub_446_i0 ?_
  intro b hb
  exact common_sub_446_i0 (mem_commonEnvelope childrenD_446_i0 b hb)
def required_446 : Finset Cell := ⟨(([(0, 3), (1, 3), (1, 4), (1, 5), (1, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_446 : Finset Cell := ⟨(([(0, 3), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 2), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 2), (4, 3), (4, 4), (5, 2), (5, 3), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_446 : Fin 2 → Finset Cell := ![(placed21 3 (1, 6) required_5), required_446_i0]
def childrenD_446 : Fin 2 → Finset Cell := ![(placed21 3 (1, 6) envelope_5), envelope_446_i0]
theorem common_sub_446 : commonEnvelope childrenD_446 ⊆ insert (2, 3) required_446 := by decide +kernel
theorem child_required_sub_446 : ∀ j, childrenC_446 j ⊆ insert (2, 3) required_446 := by decide +kernel
theorem child_envelope_sub_446 : ∀ j, childrenD_446 j ⊆ envelope_446 := by decide +kernel
theorem pivot_mem_446 : (2, 3) ∈ envelope_446 := by decide +kernel
theorem children_work_446 : ∀ j, Template HasSnaky 6 (childrenC_446 j) (childrenD_446 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 3 (1, 6)).mono (by decide +kernel)
  · exact row_works_446_i0.mono (by decide +kernel)
theorem row_works_446 : Template HasSnaky 7 required_446 envelope_446 := by
  refine compose HasSnaky 6 childrenC_446 childrenD_446 children_work_446 (2, 3)
    required_446 envelope_446 pivot_mem_446 child_required_sub_446 child_envelope_sub_446 ?_
  intro b hb
  exact common_sub_446 (mem_commonEnvelope childrenD_446 b hb)
def height_361 : ℕ := 7
def childrenH_361 : Fin 3 → ℕ := ![height_15, height_57, height_360]
theorem height_exact_361 : height_361 = 1 + Finset.univ.sup childrenH_361 := by decide +kernel
theorem required_origin_361 : ∀ x ∈ required_361,
    (∃ j, x ∈ childrenC_361 j) ∨ ∀ j, x ∈ childrenD_361 j := by decide +kernel
theorem required_exact_361 : required_361 =
    ((Finset.univ.biUnion childrenC_361) ∪ commonEnvelope childrenD_361).erase (3, 1) := by
  exact required_eq_combination childrenC_361 childrenD_361 (3, 1) required_361
    (by decide +kernel) child_required_sub_361 common_sub_361 required_origin_361
theorem envelope_origin_361 : ∀ x ∈ envelope_361,
    x = (3, 1) ∨ ∃ j, x ∈ childrenD_361 j := by decide +kernel
theorem envelope_exact_361 : envelope_361 =
    insert (3, 1) (Finset.univ.biUnion childrenD_361) := by
  exact envelope_eq_combination childrenD_361 (3, 1) envelope_361
    pivot_mem_361 child_envelope_sub_361 envelope_origin_361
def checked_361 : CheckedCard where
  required := required_361
  envelope := envelope_361
  height := height_361
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_361
def height_372_i0 : ℕ := 6
def childrenH_372_i0 : Fin 2 → ℕ := ![height_81, height_351]
theorem height_exact_372_i0 : height_372_i0 = 1 + Finset.univ.sup childrenH_372_i0 := by decide +kernel
theorem required_origin_372_i0 : ∀ x ∈ required_372_i0,
    (∃ j, x ∈ childrenC_372_i0 j) ∨ ∀ j, x ∈ childrenD_372_i0 j := by decide +kernel
theorem required_exact_372_i0 : required_372_i0 =
    ((Finset.univ.biUnion childrenC_372_i0) ∪ commonEnvelope childrenD_372_i0).erase (4, 4) := by
  exact required_eq_combination childrenC_372_i0 childrenD_372_i0 (4, 4) required_372_i0
    (by decide +kernel) child_required_sub_372_i0 common_sub_372_i0 required_origin_372_i0
theorem envelope_origin_372_i0 : ∀ x ∈ envelope_372_i0,
    x = (4, 4) ∨ ∃ j, x ∈ childrenD_372_i0 j := by decide +kernel
theorem envelope_exact_372_i0 : envelope_372_i0 =
    insert (4, 4) (Finset.univ.biUnion childrenD_372_i0) := by
  exact envelope_eq_combination childrenD_372_i0 (4, 4) envelope_372_i0
    pivot_mem_372_i0 child_envelope_sub_372_i0 envelope_origin_372_i0
def checked_372_i0 : CheckedCard where
  required := required_372_i0
  envelope := envelope_372_i0
  height := height_372_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_372_i0
def height_372 : ℕ := 7
def childrenH_372 : Fin 2 → ℕ := ![height_96, height_372_i0]
theorem height_exact_372 : height_372 = 1 + Finset.univ.sup childrenH_372 := by decide +kernel
theorem required_origin_372 : ∀ x ∈ required_372,
    (∃ j, x ∈ childrenC_372 j) ∨ ∀ j, x ∈ childrenD_372 j := by decide +kernel
theorem required_exact_372 : required_372 =
    ((Finset.univ.biUnion childrenC_372) ∪ commonEnvelope childrenD_372).erase (4, 2) := by
  exact required_eq_combination childrenC_372 childrenD_372 (4, 2) required_372
    (by decide +kernel) child_required_sub_372 common_sub_372 required_origin_372
theorem envelope_origin_372 : ∀ x ∈ envelope_372,
    x = (4, 2) ∨ ∃ j, x ∈ childrenD_372 j := by decide +kernel
theorem envelope_exact_372 : envelope_372 =
    insert (4, 2) (Finset.univ.biUnion childrenD_372) := by
  exact envelope_eq_combination childrenD_372 (4, 2) envelope_372
    pivot_mem_372 child_envelope_sub_372 envelope_origin_372
def checked_372 : CheckedCard where
  required := required_372
  envelope := envelope_372
  height := height_372
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_372
def height_379 : ℕ := 7
def childrenH_379 : Fin 3 → ℕ := ![height_21, height_37, height_378]
theorem height_exact_379 : height_379 = 1 + Finset.univ.sup childrenH_379 := by decide +kernel
theorem required_origin_379 : ∀ x ∈ required_379,
    (∃ j, x ∈ childrenC_379 j) ∨ ∀ j, x ∈ childrenD_379 j := by decide +kernel
theorem required_exact_379 : required_379 =
    ((Finset.univ.biUnion childrenC_379) ∪ commonEnvelope childrenD_379).erase (3, 2) := by
  exact required_eq_combination childrenC_379 childrenD_379 (3, 2) required_379
    (by decide +kernel) child_required_sub_379 common_sub_379 required_origin_379
theorem envelope_origin_379 : ∀ x ∈ envelope_379,
    x = (3, 2) ∨ ∃ j, x ∈ childrenD_379 j := by decide +kernel
theorem envelope_exact_379 : envelope_379 =
    insert (3, 2) (Finset.univ.biUnion childrenD_379) := by
  exact envelope_eq_combination childrenD_379 (3, 2) envelope_379
    pivot_mem_379 child_envelope_sub_379 envelope_origin_379
def checked_379 : CheckedCard where
  required := required_379
  envelope := envelope_379
  height := height_379
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_379
def height_385 : ℕ := 7
def childrenH_385 : Fin 2 → ℕ := ![height_115, height_383]
theorem height_exact_385 : height_385 = 1 + Finset.univ.sup childrenH_385 := by decide +kernel
theorem required_origin_385 : ∀ x ∈ required_385,
    (∃ j, x ∈ childrenC_385 j) ∨ ∀ j, x ∈ childrenD_385 j := by decide +kernel
theorem required_exact_385 : required_385 =
    ((Finset.univ.biUnion childrenC_385) ∪ commonEnvelope childrenD_385).erase (3, 3) := by
  exact required_eq_combination childrenC_385 childrenD_385 (3, 3) required_385
    (by decide +kernel) child_required_sub_385 common_sub_385 required_origin_385
theorem envelope_origin_385 : ∀ x ∈ envelope_385,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_385 j := by decide +kernel
theorem envelope_exact_385 : envelope_385 =
    insert (3, 3) (Finset.univ.biUnion childrenD_385) := by
  exact envelope_eq_combination childrenD_385 (3, 3) envelope_385
    pivot_mem_385 child_envelope_sub_385 envelope_origin_385
def checked_385 : CheckedCard where
  required := required_385
  envelope := envelope_385
  height := height_385
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_385
def height_388 : ℕ := 7
def childrenH_388 : Fin 2 → ℕ := ![height_11, height_387]
theorem height_exact_388 : height_388 = 1 + Finset.univ.sup childrenH_388 := by decide +kernel
theorem required_origin_388 : ∀ x ∈ required_388,
    (∃ j, x ∈ childrenC_388 j) ∨ ∀ j, x ∈ childrenD_388 j := by decide +kernel
theorem required_exact_388 : required_388 =
    ((Finset.univ.biUnion childrenC_388) ∪ commonEnvelope childrenD_388).erase (2, 4) := by
  exact required_eq_combination childrenC_388 childrenD_388 (2, 4) required_388
    (by decide +kernel) child_required_sub_388 common_sub_388 required_origin_388
theorem envelope_origin_388 : ∀ x ∈ envelope_388,
    x = (2, 4) ∨ ∃ j, x ∈ childrenD_388 j := by decide +kernel
theorem envelope_exact_388 : envelope_388 =
    insert (2, 4) (Finset.univ.biUnion childrenD_388) := by
  exact envelope_eq_combination childrenD_388 (2, 4) envelope_388
    pivot_mem_388 child_envelope_sub_388 envelope_origin_388
def checked_388 : CheckedCard where
  required := required_388
  envelope := envelope_388
  height := height_388
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_388
def height_394 : ℕ := 7
def childrenH_394 : Fin 3 → ℕ := ![height_17, height_241, height_392]
theorem height_exact_394 : height_394 = 1 + Finset.univ.sup childrenH_394 := by decide +kernel
theorem required_origin_394 : ∀ x ∈ required_394,
    (∃ j, x ∈ childrenC_394 j) ∨ ∀ j, x ∈ childrenD_394 j := by decide +kernel
theorem required_exact_394 : required_394 =
    ((Finset.univ.biUnion childrenC_394) ∪ commonEnvelope childrenD_394).erase (1, 4) := by
  exact required_eq_combination childrenC_394 childrenD_394 (1, 4) required_394
    (by decide +kernel) child_required_sub_394 common_sub_394 required_origin_394
theorem envelope_origin_394 : ∀ x ∈ envelope_394,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_394 j := by decide +kernel
theorem envelope_exact_394 : envelope_394 =
    insert (1, 4) (Finset.univ.biUnion childrenD_394) := by
  exact envelope_eq_combination childrenD_394 (1, 4) envelope_394
    pivot_mem_394 child_envelope_sub_394 envelope_origin_394
def checked_394 : CheckedCard where
  required := required_394
  envelope := envelope_394
  height := height_394
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_394
def height_404_i1 : ℕ := 5
def childrenH_404_i1 : Fin 2 → ℕ := ![height_0, height_354]
theorem height_exact_404_i1 : height_404_i1 = 1 + Finset.univ.sup childrenH_404_i1 := by decide +kernel
theorem required_origin_404_i1 : ∀ x ∈ required_404_i1,
    (∃ j, x ∈ childrenC_404_i1 j) ∨ ∀ j, x ∈ childrenD_404_i1 j := by decide +kernel
theorem required_exact_404_i1 : required_404_i1 =
    ((Finset.univ.biUnion childrenC_404_i1) ∪ commonEnvelope childrenD_404_i1).erase (3, 1) := by
  exact required_eq_combination childrenC_404_i1 childrenD_404_i1 (3, 1) required_404_i1
    (by decide +kernel) child_required_sub_404_i1 common_sub_404_i1 required_origin_404_i1
theorem envelope_origin_404_i1 : ∀ x ∈ envelope_404_i1,
    x = (3, 1) ∨ ∃ j, x ∈ childrenD_404_i1 j := by decide +kernel
theorem envelope_exact_404_i1 : envelope_404_i1 =
    insert (3, 1) (Finset.univ.biUnion childrenD_404_i1) := by
  exact envelope_eq_combination childrenD_404_i1 (3, 1) envelope_404_i1
    pivot_mem_404_i1 child_envelope_sub_404_i1 envelope_origin_404_i1
def checked_404_i1 : CheckedCard where
  required := required_404_i1
  envelope := envelope_404_i1
  height := height_404_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_404_i1
def height_404_i0 : ℕ := 6
def childrenH_404_i0 : Fin 2 → ℕ := ![height_5, height_404_i1]
theorem height_exact_404_i0 : height_404_i0 = 1 + Finset.univ.sup childrenH_404_i0 := by decide +kernel
theorem required_origin_404_i0 : ∀ x ∈ required_404_i0,
    (∃ j, x ∈ childrenC_404_i0 j) ∨ ∀ j, x ∈ childrenD_404_i0 j := by decide +kernel
theorem required_exact_404_i0 : required_404_i0 =
    ((Finset.univ.biUnion childrenC_404_i0) ∪ commonEnvelope childrenD_404_i0).erase (2, 1) := by
  exact required_eq_combination childrenC_404_i0 childrenD_404_i0 (2, 1) required_404_i0
    (by decide +kernel) child_required_sub_404_i0 common_sub_404_i0 required_origin_404_i0
theorem envelope_origin_404_i0 : ∀ x ∈ envelope_404_i0,
    x = (2, 1) ∨ ∃ j, x ∈ childrenD_404_i0 j := by decide +kernel
theorem envelope_exact_404_i0 : envelope_404_i0 =
    insert (2, 1) (Finset.univ.biUnion childrenD_404_i0) := by
  exact envelope_eq_combination childrenD_404_i0 (2, 1) envelope_404_i0
    pivot_mem_404_i0 child_envelope_sub_404_i0 envelope_origin_404_i0
def checked_404_i0 : CheckedCard where
  required := required_404_i0
  envelope := envelope_404_i0
  height := height_404_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_404_i0
def height_404 : ℕ := 7
def childrenH_404 : Fin 2 → ℕ := ![height_5, height_404_i0]
theorem height_exact_404 : height_404 = 1 + Finset.univ.sup childrenH_404 := by decide +kernel
theorem required_origin_404 : ∀ x ∈ required_404,
    (∃ j, x ∈ childrenC_404 j) ∨ ∀ j, x ∈ childrenD_404 j := by decide +kernel
theorem required_exact_404 : required_404 =
    ((Finset.univ.biUnion childrenC_404) ∪ commonEnvelope childrenD_404).erase (2, 4) := by
  exact required_eq_combination childrenC_404 childrenD_404 (2, 4) required_404
    (by decide +kernel) child_required_sub_404 common_sub_404 required_origin_404
theorem envelope_origin_404 : ∀ x ∈ envelope_404,
    x = (2, 4) ∨ ∃ j, x ∈ childrenD_404 j := by decide +kernel
theorem envelope_exact_404 : envelope_404 =
    insert (2, 4) (Finset.univ.biUnion childrenD_404) := by
  exact envelope_eq_combination childrenD_404 (2, 4) envelope_404
    pivot_mem_404 child_envelope_sub_404 envelope_origin_404
def checked_404 : CheckedCard where
  required := required_404
  envelope := envelope_404
  height := height_404
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_404
def height_415 : ℕ := 7
def childrenH_415 : Fin 2 → ℕ := ![height_2, height_414]
theorem height_exact_415 : height_415 = 1 + Finset.univ.sup childrenH_415 := by decide +kernel
theorem required_origin_415 : ∀ x ∈ required_415,
    (∃ j, x ∈ childrenC_415 j) ∨ ∀ j, x ∈ childrenD_415 j := by decide +kernel
theorem required_exact_415 : required_415 =
    ((Finset.univ.biUnion childrenC_415) ∪ commonEnvelope childrenD_415).erase (3, 2) := by
  exact required_eq_combination childrenC_415 childrenD_415 (3, 2) required_415
    (by decide +kernel) child_required_sub_415 common_sub_415 required_origin_415
theorem envelope_origin_415 : ∀ x ∈ envelope_415,
    x = (3, 2) ∨ ∃ j, x ∈ childrenD_415 j := by decide +kernel
theorem envelope_exact_415 : envelope_415 =
    insert (3, 2) (Finset.univ.biUnion childrenD_415) := by
  exact envelope_eq_combination childrenD_415 (3, 2) envelope_415
    pivot_mem_415 child_envelope_sub_415 envelope_origin_415
def checked_415 : CheckedCard where
  required := required_415
  envelope := envelope_415
  height := height_415
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_415
def height_418_i2 : ℕ := 4
def childrenH_418_i2 : Fin 2 → ℕ := ![height_5, height_29]
theorem height_exact_418_i2 : height_418_i2 = 1 + Finset.univ.sup childrenH_418_i2 := by decide +kernel
theorem required_origin_418_i2 : ∀ x ∈ required_418_i2,
    (∃ j, x ∈ childrenC_418_i2 j) ∨ ∀ j, x ∈ childrenD_418_i2 j := by decide +kernel
theorem required_exact_418_i2 : required_418_i2 =
    ((Finset.univ.biUnion childrenC_418_i2) ∪ commonEnvelope childrenD_418_i2).erase (2, 2) := by
  exact required_eq_combination childrenC_418_i2 childrenD_418_i2 (2, 2) required_418_i2
    (by decide +kernel) child_required_sub_418_i2 common_sub_418_i2 required_origin_418_i2
theorem envelope_origin_418_i2 : ∀ x ∈ envelope_418_i2,
    x = (2, 2) ∨ ∃ j, x ∈ childrenD_418_i2 j := by decide +kernel
theorem envelope_exact_418_i2 : envelope_418_i2 =
    insert (2, 2) (Finset.univ.biUnion childrenD_418_i2) := by
  exact envelope_eq_combination childrenD_418_i2 (2, 2) envelope_418_i2
    pivot_mem_418_i2 child_envelope_sub_418_i2 envelope_origin_418_i2
def checked_418_i2 : CheckedCard where
  required := required_418_i2
  envelope := envelope_418_i2
  height := height_418_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_418_i2
def height_418_i1 : ℕ := 5
def childrenH_418_i1 : Fin 4 → ℕ := ![height_8, height_25, height_41, height_418_i2]
theorem height_exact_418_i1 : height_418_i1 = 1 + Finset.univ.sup childrenH_418_i1 := by decide +kernel
theorem required_origin_418_i1 : ∀ x ∈ required_418_i1,
    (∃ j, x ∈ childrenC_418_i1 j) ∨ ∀ j, x ∈ childrenD_418_i1 j := by decide +kernel
theorem required_exact_418_i1 : required_418_i1 =
    ((Finset.univ.biUnion childrenC_418_i1) ∪ commonEnvelope childrenD_418_i1).erase (3, 3) := by
  exact required_eq_combination childrenC_418_i1 childrenD_418_i1 (3, 3) required_418_i1
    (by decide +kernel) child_required_sub_418_i1 common_sub_418_i1 required_origin_418_i1
theorem envelope_origin_418_i1 : ∀ x ∈ envelope_418_i1,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_418_i1 j := by decide +kernel
theorem envelope_exact_418_i1 : envelope_418_i1 =
    insert (3, 3) (Finset.univ.biUnion childrenD_418_i1) := by
  exact envelope_eq_combination childrenD_418_i1 (3, 3) envelope_418_i1
    pivot_mem_418_i1 child_envelope_sub_418_i1 envelope_origin_418_i1
def checked_418_i1 : CheckedCard where
  required := required_418_i1
  envelope := envelope_418_i1
  height := height_418_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_418_i1
def height_418_i0 : ℕ := 6
def childrenH_418_i0 : Fin 2 → ℕ := ![height_5, height_418_i1]
theorem height_exact_418_i0 : height_418_i0 = 1 + Finset.univ.sup childrenH_418_i0 := by decide +kernel
theorem required_origin_418_i0 : ∀ x ∈ required_418_i0,
    (∃ j, x ∈ childrenC_418_i0 j) ∨ ∀ j, x ∈ childrenD_418_i0 j := by decide +kernel
theorem required_exact_418_i0 : required_418_i0 =
    ((Finset.univ.biUnion childrenC_418_i0) ∪ commonEnvelope childrenD_418_i0).erase (3, 2) := by
  exact required_eq_combination childrenC_418_i0 childrenD_418_i0 (3, 2) required_418_i0
    (by decide +kernel) child_required_sub_418_i0 common_sub_418_i0 required_origin_418_i0
theorem envelope_origin_418_i0 : ∀ x ∈ envelope_418_i0,
    x = (3, 2) ∨ ∃ j, x ∈ childrenD_418_i0 j := by decide +kernel
theorem envelope_exact_418_i0 : envelope_418_i0 =
    insert (3, 2) (Finset.univ.biUnion childrenD_418_i0) := by
  exact envelope_eq_combination childrenD_418_i0 (3, 2) envelope_418_i0
    pivot_mem_418_i0 child_envelope_sub_418_i0 envelope_origin_418_i0
def checked_418_i0 : CheckedCard where
  required := required_418_i0
  envelope := envelope_418_i0
  height := height_418_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_418_i0
def height_418 : ℕ := 7
def childrenH_418 : Fin 2 → ℕ := ![height_5, height_418_i0]
theorem height_exact_418 : height_418 = 1 + Finset.univ.sup childrenH_418 := by decide +kernel
theorem required_origin_418 : ∀ x ∈ required_418,
    (∃ j, x ∈ childrenC_418 j) ∨ ∀ j, x ∈ childrenD_418 j := by decide +kernel
theorem required_exact_418 : required_418 =
    ((Finset.univ.biUnion childrenC_418) ∪ commonEnvelope childrenD_418).erase (3, 0) := by
  exact required_eq_combination childrenC_418 childrenD_418 (3, 0) required_418
    (by decide +kernel) child_required_sub_418 common_sub_418 required_origin_418
theorem envelope_origin_418 : ∀ x ∈ envelope_418,
    x = (3, 0) ∨ ∃ j, x ∈ childrenD_418 j := by decide +kernel
theorem envelope_exact_418 : envelope_418 =
    insert (3, 0) (Finset.univ.biUnion childrenD_418) := by
  exact envelope_eq_combination childrenD_418 (3, 0) envelope_418
    pivot_mem_418 child_envelope_sub_418 envelope_origin_418
def checked_418 : CheckedCard where
  required := required_418
  envelope := envelope_418
  height := height_418
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_418
def height_422_i0 : ℕ := 6
def childrenH_422_i0 : Fin 2 → ℕ := ![height_69, height_413]
theorem height_exact_422_i0 : height_422_i0 = 1 + Finset.univ.sup childrenH_422_i0 := by decide +kernel
theorem required_origin_422_i0 : ∀ x ∈ required_422_i0,
    (∃ j, x ∈ childrenC_422_i0 j) ∨ ∀ j, x ∈ childrenD_422_i0 j := by decide +kernel
theorem required_exact_422_i0 : required_422_i0 =
    ((Finset.univ.biUnion childrenC_422_i0) ∪ commonEnvelope childrenD_422_i0).erase (4, 2) := by
  exact required_eq_combination childrenC_422_i0 childrenD_422_i0 (4, 2) required_422_i0
    (by decide +kernel) child_required_sub_422_i0 common_sub_422_i0 required_origin_422_i0
theorem envelope_origin_422_i0 : ∀ x ∈ envelope_422_i0,
    x = (4, 2) ∨ ∃ j, x ∈ childrenD_422_i0 j := by decide +kernel
theorem envelope_exact_422_i0 : envelope_422_i0 =
    insert (4, 2) (Finset.univ.biUnion childrenD_422_i0) := by
  exact envelope_eq_combination childrenD_422_i0 (4, 2) envelope_422_i0
    pivot_mem_422_i0 child_envelope_sub_422_i0 envelope_origin_422_i0
def checked_422_i0 : CheckedCard where
  required := required_422_i0
  envelope := envelope_422_i0
  height := height_422_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_422_i0
def height_422 : ℕ := 7
def childrenH_422 : Fin 2 → ℕ := ![height_0, height_422_i0]
theorem height_exact_422 : height_422 = 1 + Finset.univ.sup childrenH_422 := by decide +kernel
theorem required_origin_422 : ∀ x ∈ required_422,
    (∃ j, x ∈ childrenC_422 j) ∨ ∀ j, x ∈ childrenD_422 j := by decide +kernel
theorem required_exact_422 : required_422 =
    ((Finset.univ.biUnion childrenC_422) ∪ commonEnvelope childrenD_422).erase (2, 2) := by
  exact required_eq_combination childrenC_422 childrenD_422 (2, 2) required_422
    (by decide +kernel) child_required_sub_422 common_sub_422 required_origin_422
theorem envelope_origin_422 : ∀ x ∈ envelope_422,
    x = (2, 2) ∨ ∃ j, x ∈ childrenD_422 j := by decide +kernel
theorem envelope_exact_422 : envelope_422 =
    insert (2, 2) (Finset.univ.biUnion childrenD_422) := by
  exact envelope_eq_combination childrenD_422 (2, 2) envelope_422
    pivot_mem_422 child_envelope_sub_422 envelope_origin_422
def checked_422 : CheckedCard where
  required := required_422
  envelope := envelope_422
  height := height_422
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_422
def height_430 : ℕ := 7
def childrenH_430 : Fin 5 → ℕ := ![height_14, height_31, height_58, height_100, height_429]
theorem height_exact_430 : height_430 = 1 + Finset.univ.sup childrenH_430 := by decide +kernel
theorem required_origin_430 : ∀ x ∈ required_430,
    (∃ j, x ∈ childrenC_430 j) ∨ ∀ j, x ∈ childrenD_430 j := by decide +kernel
theorem required_exact_430 : required_430 =
    ((Finset.univ.biUnion childrenC_430) ∪ commonEnvelope childrenD_430).erase (3, 5) := by
  exact required_eq_combination childrenC_430 childrenD_430 (3, 5) required_430
    (by decide +kernel) child_required_sub_430 common_sub_430 required_origin_430
theorem envelope_origin_430 : ∀ x ∈ envelope_430,
    x = (3, 5) ∨ ∃ j, x ∈ childrenD_430 j := by decide +kernel
theorem envelope_exact_430 : envelope_430 =
    insert (3, 5) (Finset.univ.biUnion childrenD_430) := by
  exact envelope_eq_combination childrenD_430 (3, 5) envelope_430
    pivot_mem_430 child_envelope_sub_430 envelope_origin_430
def checked_430 : CheckedCard where
  required := required_430
  envelope := envelope_430
  height := height_430
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_430
def height_431 : ℕ := 7
def childrenH_431 : Fin 3 → ℕ := ![height_160, height_243, height_429]
theorem height_exact_431 : height_431 = 1 + Finset.univ.sup childrenH_431 := by decide +kernel
theorem required_origin_431 : ∀ x ∈ required_431,
    (∃ j, x ∈ childrenC_431 j) ∨ ∀ j, x ∈ childrenD_431 j := by decide +kernel
theorem required_exact_431 : required_431 =
    ((Finset.univ.biUnion childrenC_431) ∪ commonEnvelope childrenD_431).erase (4, 4) := by
  exact required_eq_combination childrenC_431 childrenD_431 (4, 4) required_431
    (by decide +kernel) child_required_sub_431 common_sub_431 required_origin_431
theorem envelope_origin_431 : ∀ x ∈ envelope_431,
    x = (4, 4) ∨ ∃ j, x ∈ childrenD_431 j := by decide +kernel
theorem envelope_exact_431 : envelope_431 =
    insert (4, 4) (Finset.univ.biUnion childrenD_431) := by
  exact envelope_eq_combination childrenD_431 (4, 4) envelope_431
    pivot_mem_431 child_envelope_sub_431 envelope_origin_431
def checked_431 : CheckedCard where
  required := required_431
  envelope := envelope_431
  height := height_431
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_431
def height_436 : ℕ := 7
def childrenH_436 : Fin 4 → ℕ := ![height_10, height_47, height_52, height_435]
theorem height_exact_436 : height_436 = 1 + Finset.univ.sup childrenH_436 := by decide +kernel
theorem required_origin_436 : ∀ x ∈ required_436,
    (∃ j, x ∈ childrenC_436 j) ∨ ∀ j, x ∈ childrenD_436 j := by decide +kernel
theorem required_exact_436 : required_436 =
    ((Finset.univ.biUnion childrenC_436) ∪ commonEnvelope childrenD_436).erase (3, 5) := by
  exact required_eq_combination childrenC_436 childrenD_436 (3, 5) required_436
    (by decide +kernel) child_required_sub_436 common_sub_436 required_origin_436
theorem envelope_origin_436 : ∀ x ∈ envelope_436,
    x = (3, 5) ∨ ∃ j, x ∈ childrenD_436 j := by decide +kernel
theorem envelope_exact_436 : envelope_436 =
    insert (3, 5) (Finset.univ.biUnion childrenD_436) := by
  exact envelope_eq_combination childrenD_436 (3, 5) envelope_436
    pivot_mem_436 child_envelope_sub_436 envelope_origin_436
def checked_436 : CheckedCard where
  required := required_436
  envelope := envelope_436
  height := height_436
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_436
def height_437 : ℕ := 7
def childrenH_437 : Fin 4 → ℕ := ![height_10, height_47, height_52, height_435]
theorem height_exact_437 : height_437 = 1 + Finset.univ.sup childrenH_437 := by decide +kernel
theorem required_origin_437 : ∀ x ∈ required_437,
    (∃ j, x ∈ childrenC_437 j) ∨ ∀ j, x ∈ childrenD_437 j := by decide +kernel
theorem required_exact_437 : required_437 =
    ((Finset.univ.biUnion childrenC_437) ∪ commonEnvelope childrenD_437).erase (3, 4) := by
  exact required_eq_combination childrenC_437 childrenD_437 (3, 4) required_437
    (by decide +kernel) child_required_sub_437 common_sub_437 required_origin_437
theorem envelope_origin_437 : ∀ x ∈ envelope_437,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_437 j := by decide +kernel
theorem envelope_exact_437 : envelope_437 =
    insert (3, 4) (Finset.univ.biUnion childrenD_437) := by
  exact envelope_eq_combination childrenD_437 (3, 4) envelope_437
    pivot_mem_437 child_envelope_sub_437 envelope_origin_437
def checked_437 : CheckedCard where
  required := required_437
  envelope := envelope_437
  height := height_437
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_437
def height_446_i0 : ℕ := 6
def childrenH_446_i0 : Fin 2 → ℕ := ![height_0, height_72]
theorem height_exact_446_i0 : height_446_i0 = 1 + Finset.univ.sup childrenH_446_i0 := by decide +kernel
theorem required_origin_446_i0 : ∀ x ∈ required_446_i0,
    (∃ j, x ∈ childrenC_446_i0 j) ∨ ∀ j, x ∈ childrenD_446_i0 j := by decide +kernel
theorem required_exact_446_i0 : required_446_i0 =
    ((Finset.univ.biUnion childrenC_446_i0) ∪ commonEnvelope childrenD_446_i0).erase (2, 4) := by
  exact required_eq_combination childrenC_446_i0 childrenD_446_i0 (2, 4) required_446_i0
    (by decide +kernel) child_required_sub_446_i0 common_sub_446_i0 required_origin_446_i0
theorem envelope_origin_446_i0 : ∀ x ∈ envelope_446_i0,
    x = (2, 4) ∨ ∃ j, x ∈ childrenD_446_i0 j := by decide +kernel
theorem envelope_exact_446_i0 : envelope_446_i0 =
    insert (2, 4) (Finset.univ.biUnion childrenD_446_i0) := by
  exact envelope_eq_combination childrenD_446_i0 (2, 4) envelope_446_i0
    pivot_mem_446_i0 child_envelope_sub_446_i0 envelope_origin_446_i0
def checked_446_i0 : CheckedCard where
  required := required_446_i0
  envelope := envelope_446_i0
  height := height_446_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_446_i0
def height_446 : ℕ := 7
def childrenH_446 : Fin 2 → ℕ := ![height_5, height_446_i0]
theorem height_exact_446 : height_446 = 1 + Finset.univ.sup childrenH_446 := by decide +kernel
theorem required_origin_446 : ∀ x ∈ required_446,
    (∃ j, x ∈ childrenC_446 j) ∨ ∀ j, x ∈ childrenD_446 j := by decide +kernel
theorem required_exact_446 : required_446 =
    ((Finset.univ.biUnion childrenC_446) ∪ commonEnvelope childrenD_446).erase (2, 3) := by
  exact required_eq_combination childrenC_446 childrenD_446 (2, 3) required_446
    (by decide +kernel) child_required_sub_446 common_sub_446 required_origin_446
theorem envelope_origin_446 : ∀ x ∈ envelope_446,
    x = (2, 3) ∨ ∃ j, x ∈ childrenD_446 j := by decide +kernel
theorem envelope_exact_446 : envelope_446 =
    insert (2, 3) (Finset.univ.biUnion childrenD_446) := by
  exact envelope_eq_combination childrenD_446 (2, 3) envelope_446
    pivot_mem_446 child_envelope_sub_446 envelope_origin_446
def checked_446 : CheckedCard where
  required := required_446
  envelope := envelope_446
  height := height_446
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_446
end SnakyPrototype.Certificate21

end OAI
