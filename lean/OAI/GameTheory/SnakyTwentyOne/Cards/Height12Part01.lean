import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height10Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height10Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height11Part01
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_428 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_428 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 4), (0, 5), (0, 6), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 3), (5, 4), (5, 5), (6, 3), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_428 : Fin 4 → Finset Cell := ![(placed21 0 (1, 0) required_7), (placed21 1 (0, 1) required_8), (placed21 2 (2, 0) required_9), (placed21 4 (0, 5) required_427)]
def childrenD_428 : Fin 4 → Finset Cell := ![(placed21 0 (1, 0) envelope_7), (placed21 1 (0, 1) envelope_8), (placed21 2 (2, 0) envelope_9), (placed21 4 (0, 5) envelope_427)]
theorem common_sub_428 : commonEnvelope childrenD_428 ⊆ insert (1, 4) required_428 := by decide +kernel
theorem child_required_sub_428 : ∀ j, childrenC_428 j ⊆ insert (1, 4) required_428 := by decide +kernel
theorem child_envelope_sub_428 : ∀ j, childrenD_428 j ⊆ envelope_428 := by decide +kernel
theorem pivot_mem_428 : (1, 4) ∈ envelope_428 := by decide +kernel
theorem children_work_428 : ∀ j, Template HasSnaky 11 (childrenC_428 j) (childrenD_428 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 0 (1, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_8 1 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_9 2 (2, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_427 4 (0, 5)).mono (by decide +kernel)
theorem row_works_428 : Template HasSnaky 12 required_428 envelope_428 := by
  refine compose HasSnaky 11 childrenC_428 childrenD_428 children_work_428 (1, 4)
    required_428 envelope_428 pivot_mem_428 child_required_sub_428 child_envelope_sub_428 ?_
  intro b hb
  exact common_sub_428 (mem_commonEnvelope childrenD_428 b hb)
def required_485_i0 : Finset Cell := ⟨(([(1, 2), (1, 3), (1, 4), (1, 5), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_485_i0 : Finset Cell := ⟨(([(0, 4), (0, 6), (0, 7), (0, 8), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 0), (3, 1), (3, 2), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, 4), (7, 5), (7, 6), (7, 7), (8, 5), (8, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_485_i0 : Fin 4 → Finset Cell := ![(placed21 1 (0, 2) required_81), (placed21 4 (0, 8) required_204), required_353, (placed21 4 (2, 8) required_481)]
def childrenD_485_i0 : Fin 4 → Finset Cell := ![(placed21 1 (0, 2) envelope_81), (placed21 4 (0, 8) envelope_204), envelope_353, (placed21 4 (2, 8) envelope_481)]
theorem common_sub_485_i0 : commonEnvelope childrenD_485_i0 ⊆ insert (4, 5) required_485_i0 := by decide +kernel
theorem child_required_sub_485_i0 : ∀ j, childrenC_485_i0 j ⊆ insert (4, 5) required_485_i0 := by decide +kernel
theorem child_envelope_sub_485_i0 : ∀ j, childrenD_485_i0 j ⊆ envelope_485_i0 := by decide +kernel
theorem pivot_mem_485_i0 : (4, 5) ∈ envelope_485_i0 := by decide +kernel
theorem children_work_485_i0 : ∀ j, Template HasSnaky 10 (childrenC_485_i0 j) (childrenD_485_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_81 1 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_204 4 (0, 8)).mono (by decide +kernel)
  · exact row_works_353.mono (by decide +kernel)
  · exact (placed21_template row_works_481 4 (2, 8)).mono (by decide +kernel)
theorem row_works_485_i0 : Template HasSnaky 11 required_485_i0 envelope_485_i0 := by
  refine compose HasSnaky 10 childrenC_485_i0 childrenD_485_i0 children_work_485_i0 (4, 5)
    required_485_i0 envelope_485_i0 pivot_mem_485_i0 child_required_sub_485_i0 child_envelope_sub_485_i0 ?_
  intro b hb
  exact common_sub_485_i0 (mem_commonEnvelope childrenD_485_i0 b hb)
def required_485_i2 : Finset Cell := ⟨(([(4, 3), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_485_i2 : Finset Cell := ⟨(([(2, 4), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, 4), (7, 5), (7, 6), (7, 7), (8, 5), (8, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_485_i2 : Fin 6 → Finset Cell := ![(placed21 2 (5, 1) required_14), (placed21 0 (3, 1) required_189), (placed21 2 (5, 1) required_192), (placed21 2 (5, 1) required_193), (placed21 0 (3, 2) required_457), (placed21 3 (2, 6) required_477)]
def childrenD_485_i2 : Fin 6 → Finset Cell := ![(placed21 2 (5, 1) envelope_14), (placed21 0 (3, 1) envelope_189), (placed21 2 (5, 1) envelope_192), (placed21 2 (5, 1) envelope_193), (placed21 0 (3, 2) envelope_457), (placed21 3 (2, 6) envelope_477)]
theorem common_sub_485_i2 : commonEnvelope childrenD_485_i2 ⊆ insert (4, 4) required_485_i2 := by decide +kernel
theorem child_required_sub_485_i2 : ∀ j, childrenC_485_i2 j ⊆ insert (4, 4) required_485_i2 := by decide +kernel
theorem child_envelope_sub_485_i2 : ∀ j, childrenD_485_i2 j ⊆ envelope_485_i2 := by decide +kernel
theorem pivot_mem_485_i2 : (4, 4) ∈ envelope_485_i2 := by decide +kernel
theorem children_work_485_i2 : ∀ j, Template HasSnaky 9 (childrenC_485_i2 j) (childrenD_485_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_14 2 (5, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_189 0 (3, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_192 2 (5, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_193 2 (5, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_457 0 (3, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_477 3 (2, 6)).mono (by decide +kernel)
theorem row_works_485_i2 : Template HasSnaky 10 required_485_i2 envelope_485_i2 := by
  refine compose HasSnaky 9 childrenC_485_i2 childrenD_485_i2 children_work_485_i2 (4, 4)
    required_485_i2 envelope_485_i2 pivot_mem_485_i2 child_required_sub_485_i2 child_envelope_sub_485_i2 ?_
  intro b hb
  exact common_sub_485_i2 (mem_commonEnvelope childrenD_485_i2 b hb)
def required_485_i3 : Finset Cell := ⟨(([(1, 2), (1, 3), (1, 4), (1, 5), (4, 3), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_485_i3 : Finset Cell := ⟨(([(0, 6), (0, 7), (0, 8), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, 4), (3, 6), (3, 7), (3, 8), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_485_i3 : Fin 2 → Finset Cell := ![(placed21 0 (1, 1) required_166), (placed21 5 (2, 2) required_314)]
def childrenD_485_i3 : Fin 2 → Finset Cell := ![(placed21 0 (1, 1) envelope_166), (placed21 5 (2, 2) envelope_314)]
theorem common_sub_485_i3 : commonEnvelope childrenD_485_i3 ⊆ insert (2, 4) required_485_i3 := by decide +kernel
theorem child_required_sub_485_i3 : ∀ j, childrenC_485_i3 j ⊆ insert (2, 4) required_485_i3 := by decide +kernel
theorem child_envelope_sub_485_i3 : ∀ j, childrenD_485_i3 j ⊆ envelope_485_i3 := by decide +kernel
theorem pivot_mem_485_i3 : (2, 4) ∈ envelope_485_i3 := by decide +kernel
theorem children_work_485_i3 : ∀ j, Template HasSnaky 6 (childrenC_485_i3 j) (childrenD_485_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_166 0 (1, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_314 5 (2, 2)).mono (by decide +kernel)
theorem row_works_485_i3 : Template HasSnaky 7 required_485_i3 envelope_485_i3 := by
  refine compose HasSnaky 6 childrenC_485_i3 childrenD_485_i3 children_work_485_i3 (2, 4)
    required_485_i3 envelope_485_i3 pivot_mem_485_i3 child_required_sub_485_i3 child_envelope_sub_485_i3 ?_
  intro b hb
  exact common_sub_485_i3 (mem_commonEnvelope childrenD_485_i3 b hb)
def required_485_i1 : Finset Cell := ⟨(([(1, 2), (1, 3), (1, 4), (1, 5), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_485_i1 : Finset Cell := ⟨(([(0, 4), (0, 6), (0, 7), (0, 8), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, 4), (7, 5), (7, 6), (7, 7), (8, 5), (8, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_485_i1 : Fin 4 → Finset Cell := ![(placed21 1 (0, 2) required_81), (placed21 1 (0, 2) required_167), required_485_i2, required_485_i3]
def childrenD_485_i1 : Fin 4 → Finset Cell := ![(placed21 1 (0, 2) envelope_81), (placed21 1 (0, 2) envelope_167), envelope_485_i2, envelope_485_i3]
theorem common_sub_485_i1 : commonEnvelope childrenD_485_i1 ⊆ insert (4, 5) required_485_i1 := by decide +kernel
theorem child_required_sub_485_i1 : ∀ j, childrenC_485_i1 j ⊆ insert (4, 5) required_485_i1 := by decide +kernel
theorem child_envelope_sub_485_i1 : ∀ j, childrenD_485_i1 j ⊆ envelope_485_i1 := by decide +kernel
theorem pivot_mem_485_i1 : (4, 5) ∈ envelope_485_i1 := by decide +kernel
theorem children_work_485_i1 : ∀ j, Template HasSnaky 10 (childrenC_485_i1 j) (childrenD_485_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_81 1 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_167 1 (0, 2)).mono (by decide +kernel)
  · exact row_works_485_i2.mono (by decide +kernel)
  · exact row_works_485_i3.mono (by decide +kernel)
theorem row_works_485_i1 : Template HasSnaky 11 required_485_i1 envelope_485_i1 := by
  refine compose HasSnaky 10 childrenC_485_i1 childrenD_485_i1 children_work_485_i1 (4, 5)
    required_485_i1 envelope_485_i1 pivot_mem_485_i1 child_required_sub_485_i1 child_envelope_sub_485_i1 ?_
  intro b hb
  exact common_sub_485_i1 (mem_commonEnvelope childrenD_485_i1 b hb)
def required_485 : Finset Cell := ⟨(([(1, 2), (1, 3), (1, 4), (1, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_485 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 4), (0, 6), (0, 7), (0, 8), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, 1), (2, 2), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, 4), (7, 5), (7, 6), (7, 7), (8, 5), (8, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_485 : Fin 5 → Finset Cell := ![(placed21 3 (0, 5) required_313), (placed21 0 (0, 1) required_469), required_485_i0, required_485_i1, required_484]
def childrenD_485 : Fin 5 → Finset Cell := ![(placed21 3 (0, 5) envelope_313), (placed21 0 (0, 1) envelope_469), envelope_485_i0, envelope_485_i1, envelope_484]
theorem common_sub_485 : commonEnvelope childrenD_485 ⊆ insert (4, 3) required_485 := by decide +kernel
theorem child_required_sub_485 : ∀ j, childrenC_485 j ⊆ insert (4, 3) required_485 := by decide +kernel
theorem child_envelope_sub_485 : ∀ j, childrenD_485 j ⊆ envelope_485 := by decide +kernel
theorem pivot_mem_485 : (4, 3) ∈ envelope_485 := by decide +kernel
theorem children_work_485 : ∀ j, Template HasSnaky 11 (childrenC_485 j) (childrenD_485 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_313 3 (0, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_469 0 (0, 1)).mono (by decide +kernel)
  · exact row_works_485_i0.mono (by decide +kernel)
  · exact row_works_485_i1.mono (by decide +kernel)
  · exact row_works_484.mono (by decide +kernel)
theorem row_works_485 : Template HasSnaky 12 required_485 envelope_485 := by
  refine compose HasSnaky 11 childrenC_485 childrenD_485 children_work_485 (4, 3)
    required_485 envelope_485 pivot_mem_485 child_required_sub_485 child_envelope_sub_485 ?_
  intro b hb
  exact common_sub_485 (mem_commonEnvelope childrenD_485 b hb)
def required_489_i1 : Finset Cell := ⟨(([(3, 8), (4, 5), (5, 5), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_489_i1 : Finset Cell := ⟨(([(2, 8), (3, 7), (3, 8), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 1), (6, 2), (6, 3), (6, 7), (6, 8), (6, 9), (6, 10)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_489_i1 : Fin 4 → Finset Cell := ![(placed21 0 (4, 4) required_10), (placed21 6 (5, 8) required_44), (placed21 0 (4, 4) required_63), (placed21 3 (2, 8) required_486)]
def childrenD_489_i1 : Fin 4 → Finset Cell := ![(placed21 0 (4, 4) envelope_10), (placed21 6 (5, 8) envelope_44), (placed21 0 (4, 4) envelope_63), (placed21 3 (2, 8) envelope_486)]
theorem common_sub_489_i1 : commonEnvelope childrenD_489_i1 ⊆ insert (5, 7) required_489_i1 := by decide +kernel
theorem child_required_sub_489_i1 : ∀ j, childrenC_489_i1 j ⊆ insert (5, 7) required_489_i1 := by decide +kernel
theorem child_envelope_sub_489_i1 : ∀ j, childrenD_489_i1 j ⊆ envelope_489_i1 := by decide +kernel
theorem pivot_mem_489_i1 : (5, 7) ∈ envelope_489_i1 := by decide +kernel
theorem children_work_489_i1 : ∀ j, Template HasSnaky 6 (childrenC_489_i1 j) (childrenD_489_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_10 0 (4, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_44 6 (5, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_63 0 (4, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_486 3 (2, 8)).mono (by decide +kernel)
theorem row_works_489_i1 : Template HasSnaky 7 required_489_i1 envelope_489_i1 := by
  refine compose HasSnaky 6 childrenC_489_i1 childrenD_489_i1 children_work_489_i1 (5, 7)
    required_489_i1 envelope_489_i1 pivot_mem_489_i1 child_required_sub_489_i1 child_envelope_sub_489_i1 ?_
  intro b hb
  exact common_sub_489_i1 (mem_commonEnvelope childrenD_489_i1 b hb)
def required_489_i0 : Finset Cell := ⟨(([(2, 5), (3, 5), (3, 8), (4, 5), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_489_i0 : Finset Cell := ⟨(([(2, 5), (2, 8), (3, 5), (3, 7), (3, 8), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 1), (6, 2), (6, 3), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_489_i0 : Fin 2 → Finset Cell := ![(placed21 0 (2, 5) required_5), required_489_i1]
def childrenD_489_i0 : Fin 2 → Finset Cell := ![(placed21 0 (2, 5) envelope_5), envelope_489_i1]
theorem common_sub_489_i0 : commonEnvelope childrenD_489_i0 ⊆ insert (5, 6) required_489_i0 := by decide +kernel
theorem child_required_sub_489_i0 : ∀ j, childrenC_489_i0 j ⊆ insert (5, 6) required_489_i0 := by decide +kernel
theorem child_envelope_sub_489_i0 : ∀ j, childrenD_489_i0 j ⊆ envelope_489_i0 := by decide +kernel
theorem pivot_mem_489_i0 : (5, 6) ∈ envelope_489_i0 := by decide +kernel
theorem children_work_489_i0 : ∀ j, Template HasSnaky 7 (childrenC_489_i0 j) (childrenD_489_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 0 (2, 5)).mono (by decide +kernel)
  · exact row_works_489_i1.mono (by decide +kernel)
theorem row_works_489_i0 : Template HasSnaky 8 required_489_i0 envelope_489_i0 := by
  refine compose HasSnaky 7 childrenC_489_i0 childrenD_489_i0 children_work_489_i0 (5, 6)
    required_489_i0 envelope_489_i0 pivot_mem_489_i0 child_required_sub_489_i0 child_envelope_sub_489_i0 ?_
  intro b hb
  exact common_sub_489_i0 (mem_commonEnvelope childrenD_489_i0 b hb)
def required_489_i2 : Finset Cell := ⟨(([(2, 5), (3, 5), (3, 8), (4, 5), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_489_i2 : Finset Cell := ⟨(([(0, 7), (0, 9), (1, 7), (1, 8), (1, 9), (2, 5), (2, 7), (2, 8), (2, 9), (3, 5), (3, 8), (3, 9), (3, 10), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (5, 12), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (7, 12), (8, 7), (8, 8), (8, 9), (9, 7), (9, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_489_i2 : Fin 4 → Finset Cell := ![(placed21 0 (2, 4) required_81), (placed21 0 (2, 4) required_167), (placed21 5 (8, 6) required_481), (placed21 1 (0, 4) required_488)]
def childrenD_489_i2 : Fin 4 → Finset Cell := ![(placed21 0 (2, 4) envelope_81), (placed21 0 (2, 4) envelope_167), (placed21 5 (8, 6) envelope_481), (placed21 1 (0, 4) envelope_488)]
theorem common_sub_489_i2 : commonEnvelope childrenD_489_i2 ⊆ insert (5, 8) required_489_i2 := by decide +kernel
theorem child_required_sub_489_i2 : ∀ j, childrenC_489_i2 j ⊆ insert (5, 8) required_489_i2 := by decide +kernel
theorem child_envelope_sub_489_i2 : ∀ j, childrenD_489_i2 j ⊆ envelope_489_i2 := by decide +kernel
theorem pivot_mem_489_i2 : (5, 8) ∈ envelope_489_i2 := by decide +kernel
theorem children_work_489_i2 : ∀ j, Template HasSnaky 10 (childrenC_489_i2 j) (childrenD_489_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_81 0 (2, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_167 0 (2, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_481 5 (8, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_488 1 (0, 4)).mono (by decide +kernel)
theorem row_works_489_i2 : Template HasSnaky 11 required_489_i2 envelope_489_i2 := by
  refine compose HasSnaky 10 childrenC_489_i2 childrenD_489_i2 children_work_489_i2 (5, 8)
    required_489_i2 envelope_489_i2 pivot_mem_489_i2 child_required_sub_489_i2 child_envelope_sub_489_i2 ?_
  intro b hb
  exact common_sub_489_i2 (mem_commonEnvelope childrenD_489_i2 b hb)
def required_489 : Finset Cell := ⟨(([(2, 5), (3, 5), (4, 5), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_489 : Finset Cell := ⟨(([(0, 7), (0, 9), (1, 4), (1, 6), (1, 7), (1, 8), (1, 9), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, 5), (3, 7), (3, 8), (3, 9), (3, 10), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (5, 12), (6, 1), (6, 2), (6, 3), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (7, 12), (8, 6), (8, 7), (8, 8), (8, 9), (9, 7), (9, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_489 : Fin 4 → Finset Cell := ![(placed21 2 (5, 4) required_313), (placed21 4 (1, 10) required_470), required_489_i0, required_489_i2]
def childrenD_489 : Fin 4 → Finset Cell := ![(placed21 2 (5, 4) envelope_313), (placed21 4 (1, 10) envelope_470), envelope_489_i0, envelope_489_i2]
theorem common_sub_489 : commonEnvelope childrenD_489 ⊆ insert (3, 8) required_489 := by decide +kernel
theorem child_required_sub_489 : ∀ j, childrenC_489 j ⊆ insert (3, 8) required_489 := by decide +kernel
theorem child_envelope_sub_489 : ∀ j, childrenD_489 j ⊆ envelope_489 := by decide +kernel
theorem pivot_mem_489 : (3, 8) ∈ envelope_489 := by decide +kernel
theorem children_work_489 : ∀ j, Template HasSnaky 11 (childrenC_489 j) (childrenD_489 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_313 2 (5, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_470 4 (1, 10)).mono (by decide +kernel)
  · exact row_works_489_i0.mono (by decide +kernel)
  · exact row_works_489_i2.mono (by decide +kernel)
theorem row_works_489 : Template HasSnaky 12 required_489 envelope_489 := by
  refine compose HasSnaky 11 childrenC_489 childrenD_489 children_work_489 (3, 8)
    required_489 envelope_489 pivot_mem_489 child_required_sub_489 child_envelope_sub_489 ?_
  intro b hb
  exact common_sub_489 (mem_commonEnvelope childrenD_489 b hb)
def required_543_i1 : Finset Cell := ⟨(([(2, 6), (2, 7), (2, 8), (2, 9), (4, 3), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_543_i1 : Finset Cell := ⟨(([(1, 6), (1, 7), (1, 9), (1, 10), (1, 11), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, 7), (3, 8), (3, 10), (3, 11), (3, 12), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_543_i1 : Fin 2 → Finset Cell := ![(placed21 0 (4, 3) required_261), (placed21 1 (1, 6) required_370)]
def childrenD_543_i1 : Fin 2 → Finset Cell := ![(placed21 0 (4, 3) envelope_261), (placed21 1 (1, 6) envelope_370)]
theorem common_sub_543_i1 : commonEnvelope childrenD_543_i1 ⊆ insert (5, 7) required_543_i1 := by decide +kernel
theorem child_required_sub_543_i1 : ∀ j, childrenC_543_i1 j ⊆ insert (5, 7) required_543_i1 := by decide +kernel
theorem child_envelope_sub_543_i1 : ∀ j, childrenD_543_i1 j ⊆ envelope_543_i1 := by decide +kernel
theorem pivot_mem_543_i1 : (5, 7) ∈ envelope_543_i1 := by decide +kernel
theorem children_work_543_i1 : ∀ j, Template HasSnaky 5 (childrenC_543_i1 j) (childrenD_543_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_261 0 (4, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_370 1 (1, 6)).mono (by decide +kernel)
theorem row_works_543_i1 : Template HasSnaky 6 required_543_i1 envelope_543_i1 := by
  refine compose HasSnaky 5 childrenC_543_i1 childrenD_543_i1 children_work_543_i1 (5, 7)
    required_543_i1 envelope_543_i1 pivot_mem_543_i1 child_required_sub_543_i1 child_envelope_sub_543_i1 ?_
  intro b hb
  exact common_sub_543_i1 (mem_commonEnvelope childrenD_543_i1 b hb)
def required_543_i6 : Finset Cell := ⟨(([(1, 3), (1, 4), (1, 6), (2, 6), (2, 7), (4, 3), (4, 4), (4, 5), (5, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_543_i6 : Finset Cell := ⟨(([(1, 3), (1, 4), (1, 6), (2, 4), (2, 5), (2, 6), (2, 7), (3, 5), (4, 3), (4, 4), (4, 5), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_543_i6 : Fin 2 → Finset Cell := ![(placed21 0 (4, 3) required_154), (placed21 0 (1, 3) required_170)]
def childrenD_543_i6 : Fin 2 → Finset Cell := ![(placed21 0 (4, 3) envelope_154), (placed21 0 (1, 3) envelope_170)]
theorem common_sub_543_i6 : commonEnvelope childrenD_543_i6 ⊆ insert (5, 5) required_543_i6 := by decide +kernel
theorem child_required_sub_543_i6 : ∀ j, childrenC_543_i6 j ⊆ insert (5, 5) required_543_i6 := by decide +kernel
theorem child_envelope_sub_543_i6 : ∀ j, childrenD_543_i6 j ⊆ envelope_543_i6 := by decide +kernel
theorem pivot_mem_543_i6 : (5, 5) ∈ envelope_543_i6 := by decide +kernel
theorem children_work_543_i6 : ∀ j, Template HasSnaky 2 (childrenC_543_i6 j) (childrenD_543_i6 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_154 0 (4, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_170 0 (1, 3)).mono (by decide +kernel)
theorem row_works_543_i6 : Template HasSnaky 3 required_543_i6 envelope_543_i6 := by
  refine compose HasSnaky 2 childrenC_543_i6 childrenD_543_i6 children_work_543_i6 (5, 5)
    required_543_i6 envelope_543_i6 pivot_mem_543_i6 child_required_sub_543_i6 child_envelope_sub_543_i6 ?_
  intro b hb
  exact common_sub_543_i6 (mem_commonEnvelope childrenD_543_i6 b hb)
def required_543_i5 : Finset Cell := ⟨(([(1, 3), (1, 4), (1, 6), (2, 6), (2, 7), (3, 7), (4, 3), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_543_i5 : Finset Cell := ⟨(([(1, 3), (1, 4), (1, 6), (2, 4), (2, 5), (2, 6), (2, 7), (3, 5), (3, 7), (4, 3), (4, 4), (4, 5), (4, 7), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_543_i5 : Fin 2 → Finset Cell := ![(placed21 6 (5, 7) required_1), required_543_i6]
def childrenD_543_i5 : Fin 2 → Finset Cell := ![(placed21 6 (5, 7) envelope_1), envelope_543_i6]
theorem common_sub_543_i5 : commonEnvelope childrenD_543_i5 ⊆ insert (5, 7) required_543_i5 := by decide +kernel
theorem child_required_sub_543_i5 : ∀ j, childrenC_543_i5 j ⊆ insert (5, 7) required_543_i5 := by decide +kernel
theorem child_envelope_sub_543_i5 : ∀ j, childrenD_543_i5 j ⊆ envelope_543_i5 := by decide +kernel
theorem pivot_mem_543_i5 : (5, 7) ∈ envelope_543_i5 := by decide +kernel
theorem children_work_543_i5 : ∀ j, Template HasSnaky 3 (childrenC_543_i5 j) (childrenD_543_i5 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_1 6 (5, 7)).mono (by decide +kernel)
  · exact row_works_543_i6.mono (by decide +kernel)
theorem row_works_543_i5 : Template HasSnaky 4 required_543_i5 envelope_543_i5 := by
  refine compose HasSnaky 3 childrenC_543_i5 childrenD_543_i5 children_work_543_i5 (5, 7)
    required_543_i5 envelope_543_i5 pivot_mem_543_i5 child_required_sub_543_i5 child_envelope_sub_543_i5 ?_
  intro b hb
  exact common_sub_543_i5 (mem_commonEnvelope childrenD_543_i5 b hb)
def required_543_i4 : Finset Cell := ⟨(([(1, 3), (1, 4), (1, 6), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (4, 3), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_543_i4 : Finset Cell := ⟨(([(1, 3), (1, 4), (1, 6), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, 5), (3, 7), (3, 8), (3, 10), (3, 11), (3, 12), (4, 3), (4, 4), (4, 5), (4, 7), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_543_i4 : Fin 2 → Finset Cell := ![(placed21 0 (2, 7) required_16), required_543_i5]
def childrenD_543_i4 : Fin 2 → Finset Cell := ![(placed21 0 (2, 7) envelope_16), envelope_543_i5]
theorem common_sub_543_i4 : commonEnvelope childrenD_543_i4 ⊆ insert (3, 7) required_543_i4 := by decide +kernel
theorem child_required_sub_543_i4 : ∀ j, childrenC_543_i4 j ⊆ insert (3, 7) required_543_i4 := by decide +kernel
theorem child_envelope_sub_543_i4 : ∀ j, childrenD_543_i4 j ⊆ envelope_543_i4 := by decide +kernel
theorem pivot_mem_543_i4 : (3, 7) ∈ envelope_543_i4 := by decide +kernel
theorem children_work_543_i4 : ∀ j, Template HasSnaky 4 (childrenC_543_i4 j) (childrenD_543_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_16 0 (2, 7)).mono (by decide +kernel)
  · exact row_works_543_i5.mono (by decide +kernel)
theorem row_works_543_i4 : Template HasSnaky 5 required_543_i4 envelope_543_i4 := by
  refine compose HasSnaky 4 childrenC_543_i4 childrenD_543_i4 children_work_543_i4 (3, 7)
    required_543_i4 envelope_543_i4 pivot_mem_543_i4 child_required_sub_543_i4 child_envelope_sub_543_i4 ?_
  intro b hb
  exact common_sub_543_i4 (mem_commonEnvelope childrenD_543_i4 b hb)
def required_543_i3 : Finset Cell := ⟨(([(1, 3), (1, 4), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (4, 3), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_543_i3 : Finset Cell := ⟨(([(1, 3), (1, 4), (1, 6), (1, 7), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, 5), (3, 7), (3, 8), (3, 10), (3, 11), (3, 12), (4, 3), (4, 4), (4, 5), (4, 7), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_543_i3 : Fin 2 → Finset Cell := ![(placed21 7 (2, 10) required_4), required_543_i4]
def childrenD_543_i3 : Fin 2 → Finset Cell := ![(placed21 7 (2, 10) envelope_4), envelope_543_i4]
theorem common_sub_543_i3 : commonEnvelope childrenD_543_i3 ⊆ insert (1, 6) required_543_i3 := by decide +kernel
theorem child_required_sub_543_i3 : ∀ j, childrenC_543_i3 j ⊆ insert (1, 6) required_543_i3 := by decide +kernel
theorem child_envelope_sub_543_i3 : ∀ j, childrenD_543_i3 j ⊆ envelope_543_i3 := by decide +kernel
theorem pivot_mem_543_i3 : (1, 6) ∈ envelope_543_i3 := by decide +kernel
theorem children_work_543_i3 : ∀ j, Template HasSnaky 5 (childrenC_543_i3 j) (childrenD_543_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_4 7 (2, 10)).mono (by decide +kernel)
  · exact row_works_543_i4.mono (by decide +kernel)
theorem row_works_543_i3 : Template HasSnaky 6 required_543_i3 envelope_543_i3 := by
  refine compose HasSnaky 5 childrenC_543_i3 childrenD_543_i3 children_work_543_i3 (1, 6)
    required_543_i3 envelope_543_i3 pivot_mem_543_i3 child_required_sub_543_i3 child_envelope_sub_543_i3 ?_
  intro b hb
  exact common_sub_543_i3 (mem_commonEnvelope childrenD_543_i3 b hb)
def required_543_i2 : Finset Cell := ⟨(([(1, 3), (1, 4), (2, 6), (2, 7), (2, 8), (2, 9), (4, 3), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_543_i2 : Finset Cell := ⟨(([(1, 3), (1, 4), (1, 6), (1, 7), (1, 9), (1, 10), (1, 11), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, 5), (3, 7), (3, 8), (3, 10), (3, 11), (3, 12), (4, 3), (4, 4), (4, 5), (4, 7), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_543_i2 : Fin 2 → Finset Cell := ![(placed21 2 (2, 6) required_6), required_543_i3]
def childrenD_543_i2 : Fin 2 → Finset Cell := ![(placed21 2 (2, 6) envelope_6), envelope_543_i3]
theorem common_sub_543_i2 : commonEnvelope childrenD_543_i2 ⊆ insert (2, 10) required_543_i2 := by decide +kernel
theorem child_required_sub_543_i2 : ∀ j, childrenC_543_i2 j ⊆ insert (2, 10) required_543_i2 := by decide +kernel
theorem child_envelope_sub_543_i2 : ∀ j, childrenD_543_i2 j ⊆ envelope_543_i2 := by decide +kernel
theorem pivot_mem_543_i2 : (2, 10) ∈ envelope_543_i2 := by decide +kernel
theorem children_work_543_i2 : ∀ j, Template HasSnaky 6 (childrenC_543_i2 j) (childrenD_543_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_6 2 (2, 6)).mono (by decide +kernel)
  · exact row_works_543_i3.mono (by decide +kernel)
theorem row_works_543_i2 : Template HasSnaky 7 required_543_i2 envelope_543_i2 := by
  refine compose HasSnaky 6 childrenC_543_i2 childrenD_543_i2 children_work_543_i2 (2, 10)
    required_543_i2 envelope_543_i2 pivot_mem_543_i2 child_required_sub_543_i2 child_envelope_sub_543_i2 ?_
  intro b hb
  exact common_sub_543_i2 (mem_commonEnvelope childrenD_543_i2 b hb)
def required_543_i7 : Finset Cell := ⟨(([(1, 3), (1, 4), (2, 6), (2, 7), (2, 8), (2, 9), (4, 3), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_543_i7 : Finset Cell := ⟨(([(1, 3), (1, 4), (1, 6), (1, 7), (1, 9), (1, 10), (1, 11), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, 2), (3, 3), (3, 7), (3, 8), (3, 10), (3, 11), (3, 12), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_543_i7 : Fin 2 → Finset Cell := ![(placed21 2 (2, 6) required_6), (placed21 0 (1, 2) required_539)]
def childrenD_543_i7 : Fin 2 → Finset Cell := ![(placed21 2 (2, 6) envelope_6), (placed21 0 (1, 2) envelope_539)]
theorem common_sub_543_i7 : commonEnvelope childrenD_543_i7 ⊆ insert (2, 10) required_543_i7 := by decide +kernel
theorem child_required_sub_543_i7 : ∀ j, childrenC_543_i7 j ⊆ insert (2, 10) required_543_i7 := by decide +kernel
theorem child_envelope_sub_543_i7 : ∀ j, childrenD_543_i7 j ⊆ envelope_543_i7 := by decide +kernel
theorem pivot_mem_543_i7 : (2, 10) ∈ envelope_543_i7 := by decide +kernel
theorem children_work_543_i7 : ∀ j, Template HasSnaky 9 (childrenC_543_i7 j) (childrenD_543_i7 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_6 2 (2, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_539 0 (1, 2)).mono (by decide +kernel)
theorem row_works_543_i7 : Template HasSnaky 10 required_543_i7 envelope_543_i7 := by
  refine compose HasSnaky 9 childrenC_543_i7 childrenD_543_i7 children_work_543_i7 (2, 10)
    required_543_i7 envelope_543_i7 pivot_mem_543_i7 child_required_sub_543_i7 child_envelope_sub_543_i7 ?_
  intro b hb
  exact common_sub_543_i7 (mem_commonEnvelope childrenD_543_i7 b hb)
def required_543_i8 : Finset Cell := ⟨(([(1, 3), (1, 4), (2, 6), (2, 7), (4, 3), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_543_i8 : Finset Cell := ⟨(([(1, 3), (1, 4), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 2), (3, 3), (3, 5), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 4), (7, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_543_i8 : Fin 3 → Finset Cell := ![(placed21 0 (4, 2) required_7), (placed21 0 (1, 2) required_86), (placed21 0 (1, 2) required_542)]
def childrenD_543_i8 : Fin 3 → Finset Cell := ![(placed21 0 (4, 2) envelope_7), (placed21 0 (1, 2) envelope_86), (placed21 0 (1, 2) envelope_542)]
theorem common_sub_543_i8 : commonEnvelope childrenD_543_i8 ⊆ insert (4, 6) required_543_i8 := by decide +kernel
theorem child_required_sub_543_i8 : ∀ j, childrenC_543_i8 j ⊆ insert (4, 6) required_543_i8 := by decide +kernel
theorem child_envelope_sub_543_i8 : ∀ j, childrenD_543_i8 j ⊆ envelope_543_i8 := by decide +kernel
theorem pivot_mem_543_i8 : (4, 6) ∈ envelope_543_i8 := by decide +kernel
theorem children_work_543_i8 : ∀ j, Template HasSnaky 7 (childrenC_543_i8 j) (childrenD_543_i8 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 0 (4, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_86 0 (1, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_542 0 (1, 2)).mono (by decide +kernel)
theorem row_works_543_i8 : Template HasSnaky 8 required_543_i8 envelope_543_i8 := by
  refine compose HasSnaky 7 childrenC_543_i8 childrenD_543_i8 children_work_543_i8 (4, 6)
    required_543_i8 envelope_543_i8 pivot_mem_543_i8 child_required_sub_543_i8 child_envelope_sub_543_i8 ?_
  intro b hb
  exact common_sub_543_i8 (mem_commonEnvelope childrenD_543_i8 b hb)
def required_543_i0 : Finset Cell := ⟨(([(1, 3), (1, 4), (2, 6), (2, 7), (2, 8), (2, 9), (4, 3), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_543_i0 : Finset Cell := ⟨(([(1, 3), (1, 4), (1, 6), (1, 7), (1, 9), (1, 10), (1, 11), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, 2), (3, 3), (3, 5), (3, 7), (3, 8), (3, 10), (3, 11), (3, 12), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, 2), (7, 3), (7, 4), (8, 2), (8, 3), (8, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_543_i0 : Fin 7 → Finset Cell := ![(placed21 0 (1, 2) required_433), required_543_i1, required_543_i2, required_543_i7, (placed21 0 (1, 0) required_540), (placed21 0 (1, 2) required_541), required_543_i8]
def childrenD_543_i0 : Fin 7 → Finset Cell := ![(placed21 0 (1, 2) envelope_433), envelope_543_i1, envelope_543_i2, envelope_543_i7, (placed21 0 (1, 0) envelope_540), (placed21 0 (1, 2) envelope_541), envelope_543_i8]
theorem common_sub_543_i0 : commonEnvelope childrenD_543_i0 ⊆ insert (4, 5) required_543_i0 := by decide +kernel
theorem child_required_sub_543_i0 : ∀ j, childrenC_543_i0 j ⊆ insert (4, 5) required_543_i0 := by decide +kernel
theorem child_envelope_sub_543_i0 : ∀ j, childrenD_543_i0 j ⊆ envelope_543_i0 := by decide +kernel
theorem pivot_mem_543_i0 : (4, 5) ∈ envelope_543_i0 := by decide +kernel
theorem children_work_543_i0 : ∀ j, Template HasSnaky 10 (childrenC_543_i0 j) (childrenD_543_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_433 0 (1, 2)).mono (by decide +kernel)
  · exact row_works_543_i1.mono (by decide +kernel)
  · exact row_works_543_i2.mono (by decide +kernel)
  · exact row_works_543_i7.mono (by decide +kernel)
  · exact (placed21_template row_works_540 0 (1, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_541 0 (1, 2)).mono (by decide +kernel)
  · exact row_works_543_i8.mono (by decide +kernel)
theorem row_works_543_i0 : Template HasSnaky 11 required_543_i0 envelope_543_i0 := by
  refine compose HasSnaky 10 childrenC_543_i0 childrenD_543_i0 children_work_543_i0 (4, 5)
    required_543_i0 envelope_543_i0 pivot_mem_543_i0 child_required_sub_543_i0 child_envelope_sub_543_i0 ?_
  intro b hb
  exact common_sub_543_i0 (mem_commonEnvelope childrenD_543_i0 b hb)
def required_543_i10 : Finset Cell := ⟨(([(1, 3), (1, 4), (2, 6), (2, 7), (2, 8), (3, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_543_i10 : Finset Cell := ⟨(([(1, 3), (1, 4), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 8), (3, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_543_i10 : Fin 2 → Finset Cell := ![(placed21 7 (2, 7) required_3), (placed21 1 (2, 5) required_5)]
def childrenD_543_i10 : Fin 2 → Finset Cell := ![(placed21 7 (2, 7) envelope_3), (placed21 1 (2, 5) envelope_5)]
theorem common_sub_543_i10 : commonEnvelope childrenD_543_i10 ⊆ insert (2, 5) required_543_i10 := by decide +kernel
theorem child_required_sub_543_i10 : ∀ j, childrenC_543_i10 j ⊆ insert (2, 5) required_543_i10 := by decide +kernel
theorem child_envelope_sub_543_i10 : ∀ j, childrenD_543_i10 j ⊆ envelope_543_i10 := by decide +kernel
theorem pivot_mem_543_i10 : (2, 5) ∈ envelope_543_i10 := by decide +kernel
theorem children_work_543_i10 : ∀ j, Template HasSnaky 1 (childrenC_543_i10 j) (childrenD_543_i10 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_3 7 (2, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_5 1 (2, 5)).mono (by decide +kernel)
theorem row_works_543_i10 : Template HasSnaky 2 required_543_i10 envelope_543_i10 := by
  refine compose HasSnaky 1 childrenC_543_i10 childrenD_543_i10 children_work_543_i10 (2, 5)
    required_543_i10 envelope_543_i10 pivot_mem_543_i10 child_required_sub_543_i10 child_envelope_sub_543_i10 ?_
  intro b hb
  exact common_sub_543_i10 (mem_commonEnvelope childrenD_543_i10 b hb)
def required_543_i9 : Finset Cell := ⟨(([(1, 3), (1, 4), (2, 6), (2, 7), (2, 8), (2, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_543_i9 : Finset Cell := ⟨(([(0, 7), (1, 3), (1, 4), (1, 6), (1, 7), (1, 9), (1, 10), (1, 11), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, 7), (3, 8), (3, 9), (4, 8), (5, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_543_i9 : Fin 2 → Finset Cell := ![(placed21 1 (0, 6) required_278), required_543_i10]
def childrenD_543_i9 : Fin 2 → Finset Cell := ![(placed21 1 (0, 6) envelope_278), envelope_543_i10]
theorem common_sub_543_i9 : commonEnvelope childrenD_543_i9 ⊆ insert (3, 8) required_543_i9 := by decide +kernel
theorem child_required_sub_543_i9 : ∀ j, childrenC_543_i9 j ⊆ insert (3, 8) required_543_i9 := by decide +kernel
theorem child_envelope_sub_543_i9 : ∀ j, childrenD_543_i9 j ⊆ envelope_543_i9 := by decide +kernel
theorem pivot_mem_543_i9 : (3, 8) ∈ envelope_543_i9 := by decide +kernel
theorem children_work_543_i9 : ∀ j, Template HasSnaky 5 (childrenC_543_i9 j) (childrenD_543_i9 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_278 1 (0, 6)).mono (by decide +kernel)
  · exact row_works_543_i10.mono (by decide +kernel)
theorem row_works_543_i9 : Template HasSnaky 6 required_543_i9 envelope_543_i9 := by
  refine compose HasSnaky 5 childrenC_543_i9 childrenD_543_i9 children_work_543_i9 (3, 8)
    required_543_i9 envelope_543_i9 pivot_mem_543_i9 child_required_sub_543_i9 child_envelope_sub_543_i9 ?_
  intro b hb
  exact common_sub_543_i9 (mem_commonEnvelope childrenD_543_i9 b hb)
def required_543 : Finset Cell := ⟨(([(1, 3), (1, 4), (2, 6), (2, 7), (2, 8), (4, 3), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_543 : Finset Cell := ⟨(([(0, 7), (1, 3), (1, 4), (1, 6), (1, 7), (1, 9), (1, 10), (1, 11), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, 2), (3, 3), (3, 5), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, 2), (7, 3), (7, 4), (8, 2), (8, 3), (8, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_543 : Fin 4 → Finset Cell := ![(placed21 1 (1, 6) required_8), (placed21 0 (1, 3) required_280), required_543_i0, required_543_i9]
def childrenD_543 : Fin 4 → Finset Cell := ![(placed21 1 (1, 6) envelope_8), (placed21 0 (1, 3) envelope_280), envelope_543_i0, envelope_543_i9]
theorem common_sub_543 : commonEnvelope childrenD_543 ⊆ insert (2, 9) required_543 := by decide +kernel
theorem child_required_sub_543 : ∀ j, childrenC_543 j ⊆ insert (2, 9) required_543 := by decide +kernel
theorem child_envelope_sub_543 : ∀ j, childrenD_543 j ⊆ envelope_543 := by decide +kernel
theorem pivot_mem_543 : (2, 9) ∈ envelope_543 := by decide +kernel
theorem children_work_543 : ∀ j, Template HasSnaky 11 (childrenC_543 j) (childrenD_543 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_8 1 (1, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_280 0 (1, 3)).mono (by decide +kernel)
  · exact row_works_543_i0.mono (by decide +kernel)
  · exact row_works_543_i9.mono (by decide +kernel)
theorem row_works_543 : Template HasSnaky 12 required_543 envelope_543 := by
  refine compose HasSnaky 11 childrenC_543 childrenD_543 children_work_543 (2, 9)
    required_543 envelope_543 pivot_mem_543 child_required_sub_543 child_envelope_sub_543 ?_
  intro b hb
  exact common_sub_543 (mem_commonEnvelope childrenD_543 b hb)
def height_428 : ℕ := 12
def childrenH_428 : Fin 4 → ℕ := ![height_7, height_8, height_9, height_427]
theorem height_exact_428 : height_428 = 1 + Finset.univ.sup childrenH_428 := by decide +kernel
theorem required_origin_428 : ∀ x ∈ required_428,
    (∃ j, x ∈ childrenC_428 j) ∨ ∀ j, x ∈ childrenD_428 j := by decide +kernel
theorem required_exact_428 : required_428 =
    ((Finset.univ.biUnion childrenC_428) ∪ commonEnvelope childrenD_428).erase (1, 4) := by
  exact required_eq_combination childrenC_428 childrenD_428 (1, 4) required_428
    (by decide +kernel) child_required_sub_428 common_sub_428 required_origin_428
theorem envelope_origin_428 : ∀ x ∈ envelope_428,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_428 j := by decide +kernel
theorem envelope_exact_428 : envelope_428 =
    insert (1, 4) (Finset.univ.biUnion childrenD_428) := by
  exact envelope_eq_combination childrenD_428 (1, 4) envelope_428
    pivot_mem_428 child_envelope_sub_428 envelope_origin_428
def checked_428 : CheckedCard where
  required := required_428
  envelope := envelope_428
  height := height_428
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_428
def height_485_i0 : ℕ := 11
def childrenH_485_i0 : Fin 4 → ℕ := ![height_81, height_204, height_353, height_481]
theorem height_exact_485_i0 : height_485_i0 = 1 + Finset.univ.sup childrenH_485_i0 := by decide +kernel
theorem required_origin_485_i0 : ∀ x ∈ required_485_i0,
    (∃ j, x ∈ childrenC_485_i0 j) ∨ ∀ j, x ∈ childrenD_485_i0 j := by decide +kernel
theorem required_exact_485_i0 : required_485_i0 =
    ((Finset.univ.biUnion childrenC_485_i0) ∪ commonEnvelope childrenD_485_i0).erase (4, 5) := by
  exact required_eq_combination childrenC_485_i0 childrenD_485_i0 (4, 5) required_485_i0
    (by decide +kernel) child_required_sub_485_i0 common_sub_485_i0 required_origin_485_i0
theorem envelope_origin_485_i0 : ∀ x ∈ envelope_485_i0,
    x = (4, 5) ∨ ∃ j, x ∈ childrenD_485_i0 j := by decide +kernel
theorem envelope_exact_485_i0 : envelope_485_i0 =
    insert (4, 5) (Finset.univ.biUnion childrenD_485_i0) := by
  exact envelope_eq_combination childrenD_485_i0 (4, 5) envelope_485_i0
    pivot_mem_485_i0 child_envelope_sub_485_i0 envelope_origin_485_i0
def checked_485_i0 : CheckedCard where
  required := required_485_i0
  envelope := envelope_485_i0
  height := height_485_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_485_i0
def height_485_i2 : ℕ := 10
def childrenH_485_i2 : Fin 6 → ℕ := ![height_14, height_189, height_192, height_193, height_457, height_477]
theorem height_exact_485_i2 : height_485_i2 = 1 + Finset.univ.sup childrenH_485_i2 := by decide +kernel
theorem required_origin_485_i2 : ∀ x ∈ required_485_i2,
    (∃ j, x ∈ childrenC_485_i2 j) ∨ ∀ j, x ∈ childrenD_485_i2 j := by decide +kernel
theorem required_exact_485_i2 : required_485_i2 =
    ((Finset.univ.biUnion childrenC_485_i2) ∪ commonEnvelope childrenD_485_i2).erase (4, 4) := by
  exact required_eq_combination childrenC_485_i2 childrenD_485_i2 (4, 4) required_485_i2
    (by decide +kernel) child_required_sub_485_i2 common_sub_485_i2 required_origin_485_i2
theorem envelope_origin_485_i2 : ∀ x ∈ envelope_485_i2,
    x = (4, 4) ∨ ∃ j, x ∈ childrenD_485_i2 j := by decide +kernel
theorem envelope_exact_485_i2 : envelope_485_i2 =
    insert (4, 4) (Finset.univ.biUnion childrenD_485_i2) := by
  exact envelope_eq_combination childrenD_485_i2 (4, 4) envelope_485_i2
    pivot_mem_485_i2 child_envelope_sub_485_i2 envelope_origin_485_i2
def checked_485_i2 : CheckedCard where
  required := required_485_i2
  envelope := envelope_485_i2
  height := height_485_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_485_i2
def height_485_i3 : ℕ := 7
def childrenH_485_i3 : Fin 2 → ℕ := ![height_166, height_314]
theorem height_exact_485_i3 : height_485_i3 = 1 + Finset.univ.sup childrenH_485_i3 := by decide +kernel
theorem required_origin_485_i3 : ∀ x ∈ required_485_i3,
    (∃ j, x ∈ childrenC_485_i3 j) ∨ ∀ j, x ∈ childrenD_485_i3 j := by decide +kernel
theorem required_exact_485_i3 : required_485_i3 =
    ((Finset.univ.biUnion childrenC_485_i3) ∪ commonEnvelope childrenD_485_i3).erase (2, 4) := by
  exact required_eq_combination childrenC_485_i3 childrenD_485_i3 (2, 4) required_485_i3
    (by decide +kernel) child_required_sub_485_i3 common_sub_485_i3 required_origin_485_i3
theorem envelope_origin_485_i3 : ∀ x ∈ envelope_485_i3,
    x = (2, 4) ∨ ∃ j, x ∈ childrenD_485_i3 j := by decide +kernel
theorem envelope_exact_485_i3 : envelope_485_i3 =
    insert (2, 4) (Finset.univ.biUnion childrenD_485_i3) := by
  exact envelope_eq_combination childrenD_485_i3 (2, 4) envelope_485_i3
    pivot_mem_485_i3 child_envelope_sub_485_i3 envelope_origin_485_i3
def checked_485_i3 : CheckedCard where
  required := required_485_i3
  envelope := envelope_485_i3
  height := height_485_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_485_i3
def height_485_i1 : ℕ := 11
def childrenH_485_i1 : Fin 4 → ℕ := ![height_81, height_167, height_485_i2, height_485_i3]
theorem height_exact_485_i1 : height_485_i1 = 1 + Finset.univ.sup childrenH_485_i1 := by decide +kernel
theorem required_origin_485_i1 : ∀ x ∈ required_485_i1,
    (∃ j, x ∈ childrenC_485_i1 j) ∨ ∀ j, x ∈ childrenD_485_i1 j := by decide +kernel
theorem required_exact_485_i1 : required_485_i1 =
    ((Finset.univ.biUnion childrenC_485_i1) ∪ commonEnvelope childrenD_485_i1).erase (4, 5) := by
  exact required_eq_combination childrenC_485_i1 childrenD_485_i1 (4, 5) required_485_i1
    (by decide +kernel) child_required_sub_485_i1 common_sub_485_i1 required_origin_485_i1
theorem envelope_origin_485_i1 : ∀ x ∈ envelope_485_i1,
    x = (4, 5) ∨ ∃ j, x ∈ childrenD_485_i1 j := by decide +kernel
theorem envelope_exact_485_i1 : envelope_485_i1 =
    insert (4, 5) (Finset.univ.biUnion childrenD_485_i1) := by
  exact envelope_eq_combination childrenD_485_i1 (4, 5) envelope_485_i1
    pivot_mem_485_i1 child_envelope_sub_485_i1 envelope_origin_485_i1
def checked_485_i1 : CheckedCard where
  required := required_485_i1
  envelope := envelope_485_i1
  height := height_485_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_485_i1
def height_485 : ℕ := 12
def childrenH_485 : Fin 5 → ℕ := ![height_313, height_469, height_485_i0, height_485_i1, height_484]
theorem height_exact_485 : height_485 = 1 + Finset.univ.sup childrenH_485 := by decide +kernel
theorem required_origin_485 : ∀ x ∈ required_485,
    (∃ j, x ∈ childrenC_485 j) ∨ ∀ j, x ∈ childrenD_485 j := by decide +kernel
theorem required_exact_485 : required_485 =
    ((Finset.univ.biUnion childrenC_485) ∪ commonEnvelope childrenD_485).erase (4, 3) := by
  exact required_eq_combination childrenC_485 childrenD_485 (4, 3) required_485
    (by decide +kernel) child_required_sub_485 common_sub_485 required_origin_485
theorem envelope_origin_485 : ∀ x ∈ envelope_485,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_485 j := by decide +kernel
theorem envelope_exact_485 : envelope_485 =
    insert (4, 3) (Finset.univ.biUnion childrenD_485) := by
  exact envelope_eq_combination childrenD_485 (4, 3) envelope_485
    pivot_mem_485 child_envelope_sub_485 envelope_origin_485
def checked_485 : CheckedCard where
  required := required_485
  envelope := envelope_485
  height := height_485
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_485
def height_489_i1 : ℕ := 7
def childrenH_489_i1 : Fin 4 → ℕ := ![height_10, height_44, height_63, height_486]
theorem height_exact_489_i1 : height_489_i1 = 1 + Finset.univ.sup childrenH_489_i1 := by decide +kernel
theorem required_origin_489_i1 : ∀ x ∈ required_489_i1,
    (∃ j, x ∈ childrenC_489_i1 j) ∨ ∀ j, x ∈ childrenD_489_i1 j := by decide +kernel
theorem required_exact_489_i1 : required_489_i1 =
    ((Finset.univ.biUnion childrenC_489_i1) ∪ commonEnvelope childrenD_489_i1).erase (5, 7) := by
  exact required_eq_combination childrenC_489_i1 childrenD_489_i1 (5, 7) required_489_i1
    (by decide +kernel) child_required_sub_489_i1 common_sub_489_i1 required_origin_489_i1
theorem envelope_origin_489_i1 : ∀ x ∈ envelope_489_i1,
    x = (5, 7) ∨ ∃ j, x ∈ childrenD_489_i1 j := by decide +kernel
theorem envelope_exact_489_i1 : envelope_489_i1 =
    insert (5, 7) (Finset.univ.biUnion childrenD_489_i1) := by
  exact envelope_eq_combination childrenD_489_i1 (5, 7) envelope_489_i1
    pivot_mem_489_i1 child_envelope_sub_489_i1 envelope_origin_489_i1
def checked_489_i1 : CheckedCard where
  required := required_489_i1
  envelope := envelope_489_i1
  height := height_489_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_489_i1
def height_489_i0 : ℕ := 8
def childrenH_489_i0 : Fin 2 → ℕ := ![height_5, height_489_i1]
theorem height_exact_489_i0 : height_489_i0 = 1 + Finset.univ.sup childrenH_489_i0 := by decide +kernel
theorem required_origin_489_i0 : ∀ x ∈ required_489_i0,
    (∃ j, x ∈ childrenC_489_i0 j) ∨ ∀ j, x ∈ childrenD_489_i0 j := by decide +kernel
theorem required_exact_489_i0 : required_489_i0 =
    ((Finset.univ.biUnion childrenC_489_i0) ∪ commonEnvelope childrenD_489_i0).erase (5, 6) := by
  exact required_eq_combination childrenC_489_i0 childrenD_489_i0 (5, 6) required_489_i0
    (by decide +kernel) child_required_sub_489_i0 common_sub_489_i0 required_origin_489_i0
theorem envelope_origin_489_i0 : ∀ x ∈ envelope_489_i0,
    x = (5, 6) ∨ ∃ j, x ∈ childrenD_489_i0 j := by decide +kernel
theorem envelope_exact_489_i0 : envelope_489_i0 =
    insert (5, 6) (Finset.univ.biUnion childrenD_489_i0) := by
  exact envelope_eq_combination childrenD_489_i0 (5, 6) envelope_489_i0
    pivot_mem_489_i0 child_envelope_sub_489_i0 envelope_origin_489_i0
def checked_489_i0 : CheckedCard where
  required := required_489_i0
  envelope := envelope_489_i0
  height := height_489_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_489_i0
def height_489_i2 : ℕ := 11
def childrenH_489_i2 : Fin 4 → ℕ := ![height_81, height_167, height_481, height_488]
theorem height_exact_489_i2 : height_489_i2 = 1 + Finset.univ.sup childrenH_489_i2 := by decide +kernel
theorem required_origin_489_i2 : ∀ x ∈ required_489_i2,
    (∃ j, x ∈ childrenC_489_i2 j) ∨ ∀ j, x ∈ childrenD_489_i2 j := by decide +kernel
theorem required_exact_489_i2 : required_489_i2 =
    ((Finset.univ.biUnion childrenC_489_i2) ∪ commonEnvelope childrenD_489_i2).erase (5, 8) := by
  exact required_eq_combination childrenC_489_i2 childrenD_489_i2 (5, 8) required_489_i2
    (by decide +kernel) child_required_sub_489_i2 common_sub_489_i2 required_origin_489_i2
theorem envelope_origin_489_i2 : ∀ x ∈ envelope_489_i2,
    x = (5, 8) ∨ ∃ j, x ∈ childrenD_489_i2 j := by decide +kernel
theorem envelope_exact_489_i2 : envelope_489_i2 =
    insert (5, 8) (Finset.univ.biUnion childrenD_489_i2) := by
  exact envelope_eq_combination childrenD_489_i2 (5, 8) envelope_489_i2
    pivot_mem_489_i2 child_envelope_sub_489_i2 envelope_origin_489_i2
def checked_489_i2 : CheckedCard where
  required := required_489_i2
  envelope := envelope_489_i2
  height := height_489_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_489_i2
def height_489 : ℕ := 12
def childrenH_489 : Fin 4 → ℕ := ![height_313, height_470, height_489_i0, height_489_i2]
theorem height_exact_489 : height_489 = 1 + Finset.univ.sup childrenH_489 := by decide +kernel
theorem required_origin_489 : ∀ x ∈ required_489,
    (∃ j, x ∈ childrenC_489 j) ∨ ∀ j, x ∈ childrenD_489 j := by decide +kernel
theorem required_exact_489 : required_489 =
    ((Finset.univ.biUnion childrenC_489) ∪ commonEnvelope childrenD_489).erase (3, 8) := by
  exact required_eq_combination childrenC_489 childrenD_489 (3, 8) required_489
    (by decide +kernel) child_required_sub_489 common_sub_489 required_origin_489
theorem envelope_origin_489 : ∀ x ∈ envelope_489,
    x = (3, 8) ∨ ∃ j, x ∈ childrenD_489 j := by decide +kernel
theorem envelope_exact_489 : envelope_489 =
    insert (3, 8) (Finset.univ.biUnion childrenD_489) := by
  exact envelope_eq_combination childrenD_489 (3, 8) envelope_489
    pivot_mem_489 child_envelope_sub_489 envelope_origin_489
def checked_489 : CheckedCard where
  required := required_489
  envelope := envelope_489
  height := height_489
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_489
def height_543_i1 : ℕ := 6
def childrenH_543_i1 : Fin 2 → ℕ := ![height_261, height_370]
theorem height_exact_543_i1 : height_543_i1 = 1 + Finset.univ.sup childrenH_543_i1 := by decide +kernel
theorem required_origin_543_i1 : ∀ x ∈ required_543_i1,
    (∃ j, x ∈ childrenC_543_i1 j) ∨ ∀ j, x ∈ childrenD_543_i1 j := by decide +kernel
theorem required_exact_543_i1 : required_543_i1 =
    ((Finset.univ.biUnion childrenC_543_i1) ∪ commonEnvelope childrenD_543_i1).erase (5, 7) := by
  exact required_eq_combination childrenC_543_i1 childrenD_543_i1 (5, 7) required_543_i1
    (by decide +kernel) child_required_sub_543_i1 common_sub_543_i1 required_origin_543_i1
theorem envelope_origin_543_i1 : ∀ x ∈ envelope_543_i1,
    x = (5, 7) ∨ ∃ j, x ∈ childrenD_543_i1 j := by decide +kernel
theorem envelope_exact_543_i1 : envelope_543_i1 =
    insert (5, 7) (Finset.univ.biUnion childrenD_543_i1) := by
  exact envelope_eq_combination childrenD_543_i1 (5, 7) envelope_543_i1
    pivot_mem_543_i1 child_envelope_sub_543_i1 envelope_origin_543_i1
def checked_543_i1 : CheckedCard where
  required := required_543_i1
  envelope := envelope_543_i1
  height := height_543_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_543_i1
def height_543_i6 : ℕ := 3
def childrenH_543_i6 : Fin 2 → ℕ := ![height_154, height_170]
theorem height_exact_543_i6 : height_543_i6 = 1 + Finset.univ.sup childrenH_543_i6 := by decide +kernel
theorem required_origin_543_i6 : ∀ x ∈ required_543_i6,
    (∃ j, x ∈ childrenC_543_i6 j) ∨ ∀ j, x ∈ childrenD_543_i6 j := by decide +kernel
theorem required_exact_543_i6 : required_543_i6 =
    ((Finset.univ.biUnion childrenC_543_i6) ∪ commonEnvelope childrenD_543_i6).erase (5, 5) := by
  exact required_eq_combination childrenC_543_i6 childrenD_543_i6 (5, 5) required_543_i6
    (by decide +kernel) child_required_sub_543_i6 common_sub_543_i6 required_origin_543_i6
theorem envelope_origin_543_i6 : ∀ x ∈ envelope_543_i6,
    x = (5, 5) ∨ ∃ j, x ∈ childrenD_543_i6 j := by decide +kernel
theorem envelope_exact_543_i6 : envelope_543_i6 =
    insert (5, 5) (Finset.univ.biUnion childrenD_543_i6) := by
  exact envelope_eq_combination childrenD_543_i6 (5, 5) envelope_543_i6
    pivot_mem_543_i6 child_envelope_sub_543_i6 envelope_origin_543_i6
def checked_543_i6 : CheckedCard where
  required := required_543_i6
  envelope := envelope_543_i6
  height := height_543_i6
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_543_i6
def height_543_i5 : ℕ := 4
def childrenH_543_i5 : Fin 2 → ℕ := ![height_1, height_543_i6]
theorem height_exact_543_i5 : height_543_i5 = 1 + Finset.univ.sup childrenH_543_i5 := by decide +kernel
theorem required_origin_543_i5 : ∀ x ∈ required_543_i5,
    (∃ j, x ∈ childrenC_543_i5 j) ∨ ∀ j, x ∈ childrenD_543_i5 j := by decide +kernel
theorem required_exact_543_i5 : required_543_i5 =
    ((Finset.univ.biUnion childrenC_543_i5) ∪ commonEnvelope childrenD_543_i5).erase (5, 7) := by
  exact required_eq_combination childrenC_543_i5 childrenD_543_i5 (5, 7) required_543_i5
    (by decide +kernel) child_required_sub_543_i5 common_sub_543_i5 required_origin_543_i5
theorem envelope_origin_543_i5 : ∀ x ∈ envelope_543_i5,
    x = (5, 7) ∨ ∃ j, x ∈ childrenD_543_i5 j := by decide +kernel
theorem envelope_exact_543_i5 : envelope_543_i5 =
    insert (5, 7) (Finset.univ.biUnion childrenD_543_i5) := by
  exact envelope_eq_combination childrenD_543_i5 (5, 7) envelope_543_i5
    pivot_mem_543_i5 child_envelope_sub_543_i5 envelope_origin_543_i5
def checked_543_i5 : CheckedCard where
  required := required_543_i5
  envelope := envelope_543_i5
  height := height_543_i5
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_543_i5
def height_543_i4 : ℕ := 5
def childrenH_543_i4 : Fin 2 → ℕ := ![height_16, height_543_i5]
theorem height_exact_543_i4 : height_543_i4 = 1 + Finset.univ.sup childrenH_543_i4 := by decide +kernel
theorem required_origin_543_i4 : ∀ x ∈ required_543_i4,
    (∃ j, x ∈ childrenC_543_i4 j) ∨ ∀ j, x ∈ childrenD_543_i4 j := by decide +kernel
theorem required_exact_543_i4 : required_543_i4 =
    ((Finset.univ.biUnion childrenC_543_i4) ∪ commonEnvelope childrenD_543_i4).erase (3, 7) := by
  exact required_eq_combination childrenC_543_i4 childrenD_543_i4 (3, 7) required_543_i4
    (by decide +kernel) child_required_sub_543_i4 common_sub_543_i4 required_origin_543_i4
theorem envelope_origin_543_i4 : ∀ x ∈ envelope_543_i4,
    x = (3, 7) ∨ ∃ j, x ∈ childrenD_543_i4 j := by decide +kernel
theorem envelope_exact_543_i4 : envelope_543_i4 =
    insert (3, 7) (Finset.univ.biUnion childrenD_543_i4) := by
  exact envelope_eq_combination childrenD_543_i4 (3, 7) envelope_543_i4
    pivot_mem_543_i4 child_envelope_sub_543_i4 envelope_origin_543_i4
def checked_543_i4 : CheckedCard where
  required := required_543_i4
  envelope := envelope_543_i4
  height := height_543_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_543_i4
def height_543_i3 : ℕ := 6
def childrenH_543_i3 : Fin 2 → ℕ := ![height_4, height_543_i4]
theorem height_exact_543_i3 : height_543_i3 = 1 + Finset.univ.sup childrenH_543_i3 := by decide +kernel
theorem required_origin_543_i3 : ∀ x ∈ required_543_i3,
    (∃ j, x ∈ childrenC_543_i3 j) ∨ ∀ j, x ∈ childrenD_543_i3 j := by decide +kernel
theorem required_exact_543_i3 : required_543_i3 =
    ((Finset.univ.biUnion childrenC_543_i3) ∪ commonEnvelope childrenD_543_i3).erase (1, 6) := by
  exact required_eq_combination childrenC_543_i3 childrenD_543_i3 (1, 6) required_543_i3
    (by decide +kernel) child_required_sub_543_i3 common_sub_543_i3 required_origin_543_i3
theorem envelope_origin_543_i3 : ∀ x ∈ envelope_543_i3,
    x = (1, 6) ∨ ∃ j, x ∈ childrenD_543_i3 j := by decide +kernel
theorem envelope_exact_543_i3 : envelope_543_i3 =
    insert (1, 6) (Finset.univ.biUnion childrenD_543_i3) := by
  exact envelope_eq_combination childrenD_543_i3 (1, 6) envelope_543_i3
    pivot_mem_543_i3 child_envelope_sub_543_i3 envelope_origin_543_i3
def checked_543_i3 : CheckedCard where
  required := required_543_i3
  envelope := envelope_543_i3
  height := height_543_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_543_i3
def height_543_i2 : ℕ := 7
def childrenH_543_i2 : Fin 2 → ℕ := ![height_6, height_543_i3]
theorem height_exact_543_i2 : height_543_i2 = 1 + Finset.univ.sup childrenH_543_i2 := by decide +kernel
theorem required_origin_543_i2 : ∀ x ∈ required_543_i2,
    (∃ j, x ∈ childrenC_543_i2 j) ∨ ∀ j, x ∈ childrenD_543_i2 j := by decide +kernel
theorem required_exact_543_i2 : required_543_i2 =
    ((Finset.univ.biUnion childrenC_543_i2) ∪ commonEnvelope childrenD_543_i2).erase (2, 10) := by
  exact required_eq_combination childrenC_543_i2 childrenD_543_i2 (2, 10) required_543_i2
    (by decide +kernel) child_required_sub_543_i2 common_sub_543_i2 required_origin_543_i2
theorem envelope_origin_543_i2 : ∀ x ∈ envelope_543_i2,
    x = (2, 10) ∨ ∃ j, x ∈ childrenD_543_i2 j := by decide +kernel
theorem envelope_exact_543_i2 : envelope_543_i2 =
    insert (2, 10) (Finset.univ.biUnion childrenD_543_i2) := by
  exact envelope_eq_combination childrenD_543_i2 (2, 10) envelope_543_i2
    pivot_mem_543_i2 child_envelope_sub_543_i2 envelope_origin_543_i2
def checked_543_i2 : CheckedCard where
  required := required_543_i2
  envelope := envelope_543_i2
  height := height_543_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_543_i2
def height_543_i7 : ℕ := 10
def childrenH_543_i7 : Fin 2 → ℕ := ![height_6, height_539]
theorem height_exact_543_i7 : height_543_i7 = 1 + Finset.univ.sup childrenH_543_i7 := by decide +kernel
theorem required_origin_543_i7 : ∀ x ∈ required_543_i7,
    (∃ j, x ∈ childrenC_543_i7 j) ∨ ∀ j, x ∈ childrenD_543_i7 j := by decide +kernel
theorem required_exact_543_i7 : required_543_i7 =
    ((Finset.univ.biUnion childrenC_543_i7) ∪ commonEnvelope childrenD_543_i7).erase (2, 10) := by
  exact required_eq_combination childrenC_543_i7 childrenD_543_i7 (2, 10) required_543_i7
    (by decide +kernel) child_required_sub_543_i7 common_sub_543_i7 required_origin_543_i7
theorem envelope_origin_543_i7 : ∀ x ∈ envelope_543_i7,
    x = (2, 10) ∨ ∃ j, x ∈ childrenD_543_i7 j := by decide +kernel
theorem envelope_exact_543_i7 : envelope_543_i7 =
    insert (2, 10) (Finset.univ.biUnion childrenD_543_i7) := by
  exact envelope_eq_combination childrenD_543_i7 (2, 10) envelope_543_i7
    pivot_mem_543_i7 child_envelope_sub_543_i7 envelope_origin_543_i7
def checked_543_i7 : CheckedCard where
  required := required_543_i7
  envelope := envelope_543_i7
  height := height_543_i7
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_543_i7
def height_543_i8 : ℕ := 8
def childrenH_543_i8 : Fin 3 → ℕ := ![height_7, height_86, height_542]
theorem height_exact_543_i8 : height_543_i8 = 1 + Finset.univ.sup childrenH_543_i8 := by decide +kernel
theorem required_origin_543_i8 : ∀ x ∈ required_543_i8,
    (∃ j, x ∈ childrenC_543_i8 j) ∨ ∀ j, x ∈ childrenD_543_i8 j := by decide +kernel
theorem required_exact_543_i8 : required_543_i8 =
    ((Finset.univ.biUnion childrenC_543_i8) ∪ commonEnvelope childrenD_543_i8).erase (4, 6) := by
  exact required_eq_combination childrenC_543_i8 childrenD_543_i8 (4, 6) required_543_i8
    (by decide +kernel) child_required_sub_543_i8 common_sub_543_i8 required_origin_543_i8
theorem envelope_origin_543_i8 : ∀ x ∈ envelope_543_i8,
    x = (4, 6) ∨ ∃ j, x ∈ childrenD_543_i8 j := by decide +kernel
theorem envelope_exact_543_i8 : envelope_543_i8 =
    insert (4, 6) (Finset.univ.biUnion childrenD_543_i8) := by
  exact envelope_eq_combination childrenD_543_i8 (4, 6) envelope_543_i8
    pivot_mem_543_i8 child_envelope_sub_543_i8 envelope_origin_543_i8
def checked_543_i8 : CheckedCard where
  required := required_543_i8
  envelope := envelope_543_i8
  height := height_543_i8
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_543_i8
def height_543_i0 : ℕ := 11
def childrenH_543_i0 : Fin 7 → ℕ := ![height_433, height_543_i1, height_543_i2, height_543_i7, height_540, height_541, height_543_i8]
theorem height_exact_543_i0 : height_543_i0 = 1 + Finset.univ.sup childrenH_543_i0 := by decide +kernel
theorem required_origin_543_i0 : ∀ x ∈ required_543_i0,
    (∃ j, x ∈ childrenC_543_i0 j) ∨ ∀ j, x ∈ childrenD_543_i0 j := by decide +kernel
theorem required_exact_543_i0 : required_543_i0 =
    ((Finset.univ.biUnion childrenC_543_i0) ∪ commonEnvelope childrenD_543_i0).erase (4, 5) := by
  exact required_eq_combination childrenC_543_i0 childrenD_543_i0 (4, 5) required_543_i0
    (by decide +kernel) child_required_sub_543_i0 common_sub_543_i0 required_origin_543_i0
theorem envelope_origin_543_i0 : ∀ x ∈ envelope_543_i0,
    x = (4, 5) ∨ ∃ j, x ∈ childrenD_543_i0 j := by decide +kernel
theorem envelope_exact_543_i0 : envelope_543_i0 =
    insert (4, 5) (Finset.univ.biUnion childrenD_543_i0) := by
  exact envelope_eq_combination childrenD_543_i0 (4, 5) envelope_543_i0
    pivot_mem_543_i0 child_envelope_sub_543_i0 envelope_origin_543_i0
def checked_543_i0 : CheckedCard where
  required := required_543_i0
  envelope := envelope_543_i0
  height := height_543_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_543_i0
def height_543_i10 : ℕ := 2
def childrenH_543_i10 : Fin 2 → ℕ := ![height_3, height_5]
theorem height_exact_543_i10 : height_543_i10 = 1 + Finset.univ.sup childrenH_543_i10 := by decide +kernel
theorem required_origin_543_i10 : ∀ x ∈ required_543_i10,
    (∃ j, x ∈ childrenC_543_i10 j) ∨ ∀ j, x ∈ childrenD_543_i10 j := by decide +kernel
theorem required_exact_543_i10 : required_543_i10 =
    ((Finset.univ.biUnion childrenC_543_i10) ∪ commonEnvelope childrenD_543_i10).erase (2, 5) := by
  exact required_eq_combination childrenC_543_i10 childrenD_543_i10 (2, 5) required_543_i10
    (by decide +kernel) child_required_sub_543_i10 common_sub_543_i10 required_origin_543_i10
theorem envelope_origin_543_i10 : ∀ x ∈ envelope_543_i10,
    x = (2, 5) ∨ ∃ j, x ∈ childrenD_543_i10 j := by decide +kernel
theorem envelope_exact_543_i10 : envelope_543_i10 =
    insert (2, 5) (Finset.univ.biUnion childrenD_543_i10) := by
  exact envelope_eq_combination childrenD_543_i10 (2, 5) envelope_543_i10
    pivot_mem_543_i10 child_envelope_sub_543_i10 envelope_origin_543_i10
def checked_543_i10 : CheckedCard where
  required := required_543_i10
  envelope := envelope_543_i10
  height := height_543_i10
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_543_i10
def height_543_i9 : ℕ := 6
def childrenH_543_i9 : Fin 2 → ℕ := ![height_278, height_543_i10]
theorem height_exact_543_i9 : height_543_i9 = 1 + Finset.univ.sup childrenH_543_i9 := by decide +kernel
theorem required_origin_543_i9 : ∀ x ∈ required_543_i9,
    (∃ j, x ∈ childrenC_543_i9 j) ∨ ∀ j, x ∈ childrenD_543_i9 j := by decide +kernel
theorem required_exact_543_i9 : required_543_i9 =
    ((Finset.univ.biUnion childrenC_543_i9) ∪ commonEnvelope childrenD_543_i9).erase (3, 8) := by
  exact required_eq_combination childrenC_543_i9 childrenD_543_i9 (3, 8) required_543_i9
    (by decide +kernel) child_required_sub_543_i9 common_sub_543_i9 required_origin_543_i9
theorem envelope_origin_543_i9 : ∀ x ∈ envelope_543_i9,
    x = (3, 8) ∨ ∃ j, x ∈ childrenD_543_i9 j := by decide +kernel
theorem envelope_exact_543_i9 : envelope_543_i9 =
    insert (3, 8) (Finset.univ.biUnion childrenD_543_i9) := by
  exact envelope_eq_combination childrenD_543_i9 (3, 8) envelope_543_i9
    pivot_mem_543_i9 child_envelope_sub_543_i9 envelope_origin_543_i9
def checked_543_i9 : CheckedCard where
  required := required_543_i9
  envelope := envelope_543_i9
  height := height_543_i9
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_543_i9
def height_543 : ℕ := 12
def childrenH_543 : Fin 4 → ℕ := ![height_8, height_280, height_543_i0, height_543_i9]
theorem height_exact_543 : height_543 = 1 + Finset.univ.sup childrenH_543 := by decide +kernel
theorem required_origin_543 : ∀ x ∈ required_543,
    (∃ j, x ∈ childrenC_543 j) ∨ ∀ j, x ∈ childrenD_543 j := by decide +kernel
theorem required_exact_543 : required_543 =
    ((Finset.univ.biUnion childrenC_543) ∪ commonEnvelope childrenD_543).erase (2, 9) := by
  exact required_eq_combination childrenC_543 childrenD_543 (2, 9) required_543
    (by decide +kernel) child_required_sub_543 common_sub_543 required_origin_543
theorem envelope_origin_543 : ∀ x ∈ envelope_543,
    x = (2, 9) ∨ ∃ j, x ∈ childrenD_543 j := by decide +kernel
theorem envelope_exact_543 : envelope_543 =
    insert (2, 9) (Finset.univ.biUnion childrenD_543) := by
  exact envelope_eq_combination childrenD_543 (2, 9) envelope_543
    pivot_mem_543 child_envelope_sub_543 envelope_origin_543
def checked_543 : CheckedCard where
  required := required_543
  envelope := envelope_543
  height := height_543
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_543
end SnakyPrototype.Certificate21

end OAI
