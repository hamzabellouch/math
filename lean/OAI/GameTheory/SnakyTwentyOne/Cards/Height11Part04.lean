import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part06
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part06
import OAI.GameTheory.SnakyTwentyOne.Cards.Height10Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height10Part05
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_615_i5 : Finset Cell := ⟨(([(3, 4), (3, 5), (4, 4), (4, 5), (4, 6), (5, 5), (6, 4), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_615_i5 : Finset Cell := ⟨(([(3, 4), (3, 5), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 1), (5, 2), (5, 3), (5, 5), (5, 6), (5, 7), (6, 2), (6, 3), (6, 4), (6, 5), (7, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_615_i5 : Fin 3 → Finset Cell := ![(placed21 4 (4, 7) required_11), (placed21 4 (3, 6) required_20), (placed21 0 (3, 2) required_402)]
def childrenD_615_i5 : Fin 3 → Finset Cell := ![(placed21 4 (4, 7) envelope_11), (placed21 4 (3, 6) envelope_20), (placed21 0 (3, 2) envelope_402)]
theorem common_sub_615_i5 : commonEnvelope childrenD_615_i5 ⊆ insert (4, 3) required_615_i5 := by decide +kernel
theorem child_required_sub_615_i5 : ∀ j, childrenC_615_i5 j ⊆ insert (4, 3) required_615_i5 := by decide +kernel
theorem child_envelope_sub_615_i5 : ∀ j, childrenD_615_i5 j ⊆ envelope_615_i5 := by decide +kernel
theorem pivot_mem_615_i5 : (4, 3) ∈ envelope_615_i5 := by decide +kernel
theorem children_work_615_i5 : ∀ j, Template HasSnaky 3 (childrenC_615_i5 j) (childrenD_615_i5 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_11 4 (4, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_20 4 (3, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_402 0 (3, 2)).mono (by decide +kernel)
theorem row_works_615_i5 : Template HasSnaky 4 required_615_i5 envelope_615_i5 := by
  refine compose HasSnaky 3 childrenC_615_i5 childrenD_615_i5 children_work_615_i5 (4, 3)
    required_615_i5 envelope_615_i5 pivot_mem_615_i5 child_required_sub_615_i5 child_envelope_sub_615_i5 ?_
  intro b hb
  exact common_sub_615_i5 (mem_commonEnvelope childrenD_615_i5 b hb)
def required_615_i4 : Finset Cell := ⟨(([(3, 4), (3, 5), (4, 5), (4, 6), (5, 5), (6, 4), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_615_i4 : Finset Cell := ⟨(([(3, 4), (3, 5), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 1), (5, 2), (5, 3), (5, 5), (5, 6), (5, 7), (6, 2), (6, 3), (6, 4), (6, 5), (7, 3), (7, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_615_i4 : Fin 2 → Finset Cell := ![(placed21 6 (7, 5) required_0), required_615_i5]
def childrenD_615_i4 : Fin 2 → Finset Cell := ![(placed21 6 (7, 5) envelope_0), envelope_615_i5]
theorem common_sub_615_i4 : commonEnvelope childrenD_615_i4 ⊆ insert (4, 4) required_615_i4 := by decide +kernel
theorem child_required_sub_615_i4 : ∀ j, childrenC_615_i4 j ⊆ insert (4, 4) required_615_i4 := by decide +kernel
theorem child_envelope_sub_615_i4 : ∀ j, childrenD_615_i4 j ⊆ envelope_615_i4 := by decide +kernel
theorem pivot_mem_615_i4 : (4, 4) ∈ envelope_615_i4 := by decide +kernel
theorem children_work_615_i4 : ∀ j, Template HasSnaky 4 (childrenC_615_i4 j) (childrenD_615_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 6 (7, 5)).mono (by decide +kernel)
  · exact row_works_615_i5.mono (by decide +kernel)
theorem row_works_615_i4 : Template HasSnaky 5 required_615_i4 envelope_615_i4 := by
  refine compose HasSnaky 4 childrenC_615_i4 childrenD_615_i4 children_work_615_i4 (4, 4)
    required_615_i4 envelope_615_i4 pivot_mem_615_i4 child_required_sub_615_i4 child_envelope_sub_615_i4 ?_
  intro b hb
  exact common_sub_615_i4 (mem_commonEnvelope childrenD_615_i4 b hb)
def required_615_i3 : Finset Cell := ⟨(([(3, 4), (3, 5), (4, 5), (4, 6), (5, 5), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_615_i3 : Finset Cell := ⟨(([(3, 4), (3, 5), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 1), (5, 2), (5, 3), (5, 5), (5, 6), (5, 7), (6, 2), (6, 3), (6, 4), (6, 5), (7, 3), (7, 4), (7, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_615_i3 : Fin 2 → Finset Cell := ![(placed21 4 (3, 5) required_5), required_615_i4]
def childrenD_615_i3 : Fin 2 → Finset Cell := ![(placed21 4 (3, 5) envelope_5), envelope_615_i4]
theorem common_sub_615_i3 : commonEnvelope childrenD_615_i3 ⊆ insert (6, 5) required_615_i3 := by decide +kernel
theorem child_required_sub_615_i3 : ∀ j, childrenC_615_i3 j ⊆ insert (6, 5) required_615_i3 := by decide +kernel
theorem child_envelope_sub_615_i3 : ∀ j, childrenD_615_i3 j ⊆ envelope_615_i3 := by decide +kernel
theorem pivot_mem_615_i3 : (6, 5) ∈ envelope_615_i3 := by decide +kernel
theorem children_work_615_i3 : ∀ j, Template HasSnaky 5 (childrenC_615_i3 j) (childrenD_615_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 4 (3, 5)).mono (by decide +kernel)
  · exact row_works_615_i4.mono (by decide +kernel)
theorem row_works_615_i3 : Template HasSnaky 6 required_615_i3 envelope_615_i3 := by
  refine compose HasSnaky 5 childrenC_615_i3 childrenD_615_i3 children_work_615_i3 (6, 5)
    required_615_i3 envelope_615_i3 pivot_mem_615_i3 child_required_sub_615_i3 child_envelope_sub_615_i3 ?_
  intro b hb
  exact common_sub_615_i3 (mem_commonEnvelope childrenD_615_i3 b hb)
def required_615_i2 : Finset Cell := ⟨(([(3, 4), (3, 5), (4, 5), (4, 6), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_615_i2 : Finset Cell := ⟨(([(0, 6), (1, 5), (1, 6), (2, 5), (2, 6), (3, 4), (3, 5), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 2), (6, 3), (6, 4), (6, 5), (7, 3), (7, 4), (7, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_615_i2 : Fin 3 → Finset Cell := ![(placed21 3 (2, 5) required_139), (placed21 5 (6, 4) required_148), required_615_i3]
def childrenD_615_i2 : Fin 3 → Finset Cell := ![(placed21 3 (2, 5) envelope_139), (placed21 5 (6, 4) envelope_148), envelope_615_i3]
theorem common_sub_615_i2 : commonEnvelope childrenD_615_i2 ⊆ insert (6, 4) required_615_i2 := by decide +kernel
theorem child_required_sub_615_i2 : ∀ j, childrenC_615_i2 j ⊆ insert (6, 4) required_615_i2 := by decide +kernel
theorem child_envelope_sub_615_i2 : ∀ j, childrenD_615_i2 j ⊆ envelope_615_i2 := by decide +kernel
theorem pivot_mem_615_i2 : (6, 4) ∈ envelope_615_i2 := by decide +kernel
theorem children_work_615_i2 : ∀ j, Template HasSnaky 6 (childrenC_615_i2 j) (childrenD_615_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_139 3 (2, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_148 5 (6, 4)).mono (by decide +kernel)
  · exact row_works_615_i3.mono (by decide +kernel)
theorem row_works_615_i2 : Template HasSnaky 7 required_615_i2 envelope_615_i2 := by
  refine compose HasSnaky 6 childrenC_615_i2 childrenD_615_i2 children_work_615_i2 (6, 4)
    required_615_i2 envelope_615_i2 pivot_mem_615_i2 child_required_sub_615_i2 child_envelope_sub_615_i2 ?_
  intro b hb
  exact common_sub_615_i2 (mem_commonEnvelope childrenD_615_i2 b hb)
def required_615_i1 : Finset Cell := ⟨(([(3, 3), (3, 4), (3, 5), (4, 5), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_615_i1 : Finset Cell := ⟨(([(0, 6), (1, 5), (1, 6), (2, 5), (2, 6), (3, 3), (3, 4), (3, 5), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 2), (6, 3), (6, 4), (6, 5), (7, 3), (7, 4), (7, 5), (8, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_615_i1 : Fin 3 → Finset Cell := ![(placed21 0 (3, 3) required_43), (placed21 4 (2, 8) required_57), required_615_i2]
def childrenD_615_i1 : Fin 3 → Finset Cell := ![(placed21 0 (3, 3) envelope_43), (placed21 4 (2, 8) envelope_57), envelope_615_i2]
theorem common_sub_615_i1 : commonEnvelope childrenD_615_i1 ⊆ insert (4, 6) required_615_i1 := by decide +kernel
theorem child_required_sub_615_i1 : ∀ j, childrenC_615_i1 j ⊆ insert (4, 6) required_615_i1 := by decide +kernel
theorem child_envelope_sub_615_i1 : ∀ j, childrenD_615_i1 j ⊆ envelope_615_i1 := by decide +kernel
theorem pivot_mem_615_i1 : (4, 6) ∈ envelope_615_i1 := by decide +kernel
theorem children_work_615_i1 : ∀ j, Template HasSnaky 7 (childrenC_615_i1 j) (childrenD_615_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_43 0 (3, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_57 4 (2, 8)).mono (by decide +kernel)
  · exact row_works_615_i2.mono (by decide +kernel)
theorem row_works_615_i1 : Template HasSnaky 8 required_615_i1 envelope_615_i1 := by
  refine compose HasSnaky 7 childrenC_615_i1 childrenD_615_i1 children_work_615_i1 (4, 6)
    required_615_i1 envelope_615_i1 pivot_mem_615_i1 child_required_sub_615_i1 child_envelope_sub_615_i1 ?_
  intro b hb
  exact common_sub_615_i1 (mem_commonEnvelope childrenD_615_i1 b hb)
def required_615_i0 : Finset Cell := ⟨(([(3, 3), (3, 4), (3, 5), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_615_i0 : Finset Cell := ⟨(([(0, 6), (1, 5), (1, 6), (2, 5), (2, 6), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (8, 4), (8, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_615_i0 : Fin 7 → Finset Cell := ![(placed21 2 (6, 2) required_116), (placed21 4 (2, 7) required_134), (placed21 4 (2, 7) required_180), (placed21 4 (2, 8) required_435), (placed21 4 (3, 7) required_558), (placed21 0 (2, 0) required_561), required_615_i1]
def childrenD_615_i0 : Fin 7 → Finset Cell := ![(placed21 2 (6, 2) envelope_116), (placed21 4 (2, 7) envelope_134), (placed21 4 (2, 7) envelope_180), (placed21 4 (2, 8) envelope_435), (placed21 4 (3, 7) envelope_558), (placed21 0 (2, 0) envelope_561), envelope_615_i1]
theorem common_sub_615_i0 : commonEnvelope childrenD_615_i0 ⊆ insert (5, 5) required_615_i0 := by decide +kernel
theorem child_required_sub_615_i0 : ∀ j, childrenC_615_i0 j ⊆ insert (5, 5) required_615_i0 := by decide +kernel
theorem child_envelope_sub_615_i0 : ∀ j, childrenD_615_i0 j ⊆ envelope_615_i0 := by decide +kernel
theorem pivot_mem_615_i0 : (5, 5) ∈ envelope_615_i0 := by decide +kernel
theorem children_work_615_i0 : ∀ j, Template HasSnaky 9 (childrenC_615_i0 j) (childrenD_615_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_116 2 (6, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_134 4 (2, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_180 4 (2, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_435 4 (2, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_558 4 (3, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_561 0 (2, 0)).mono (by decide +kernel)
  · exact row_works_615_i1.mono (by decide +kernel)
theorem row_works_615_i0 : Template HasSnaky 10 required_615_i0 envelope_615_i0 := by
  refine compose HasSnaky 9 childrenC_615_i0 childrenD_615_i0 children_work_615_i0 (5, 5)
    required_615_i0 envelope_615_i0 pivot_mem_615_i0 child_required_sub_615_i0 child_envelope_sub_615_i0 ?_
  intro b hb
  exact common_sub_615_i0 (mem_commonEnvelope childrenD_615_i0 b hb)
def required_615 : Finset Cell := ⟨(([(0, 3), (0, 4), (3, 3), (3, 4), (3, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_615 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 3), (0, 4), (0, 6), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 4), (2, 5), (2, 6), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (8, 2), (8, 4), (8, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_615 : Fin 3 → Finset Cell := ![(placed21 0 (0, 1) required_362), required_614, required_615_i0]
def childrenD_615 : Fin 3 → Finset Cell := ![(placed21 0 (0, 1) envelope_362), envelope_614, envelope_615_i0]
theorem common_sub_615 : commonEnvelope childrenD_615 ⊆ insert (4, 5) required_615 := by decide +kernel
theorem child_required_sub_615 : ∀ j, childrenC_615 j ⊆ insert (4, 5) required_615 := by decide +kernel
theorem child_envelope_sub_615 : ∀ j, childrenD_615 j ⊆ envelope_615 := by decide +kernel
theorem pivot_mem_615 : (4, 5) ∈ envelope_615 := by decide +kernel
theorem children_work_615 : ∀ j, Template HasSnaky 10 (childrenC_615 j) (childrenD_615 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_362 0 (0, 1)).mono (by decide +kernel)
  · exact row_works_614.mono (by decide +kernel)
  · exact row_works_615_i0.mono (by decide +kernel)
theorem row_works_615 : Template HasSnaky 11 required_615 envelope_615 := by
  refine compose HasSnaky 10 childrenC_615 childrenD_615 children_work_615 (4, 5)
    required_615 envelope_615 pivot_mem_615 child_required_sub_615 child_envelope_sub_615 ?_
  intro b hb
  exact common_sub_615 (mem_commonEnvelope childrenD_615 b hb)
def required_617 : Finset Cell := ⟨(([(3, 4), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_617 : Finset Cell := ⟨(([(0, 5), (0, 6), (1, 5), (1, 6), (2, 2), (2, 5), (2, 6), (3, 0), (3, 1), (3, 2), (3, 4), (3, 5), (3, 6), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (8, 3), (8, 4), (8, 5), (8, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_617 : Fin 4 → Finset Cell := ![(placed21 6 (5, 7) required_14), (placed21 4 (2, 6) required_136), (placed21 7 (7, 6) required_332), (placed21 0 (2, 1) required_616)]
def childrenD_617 : Fin 4 → Finset Cell := ![(placed21 6 (5, 7) envelope_14), (placed21 4 (2, 6) envelope_136), (placed21 7 (7, 6) envelope_332), (placed21 0 (2, 1) envelope_616)]
theorem common_sub_617 : commonEnvelope childrenD_617 ⊆ insert (4, 3) required_617 := by decide +kernel
theorem child_required_sub_617 : ∀ j, childrenC_617 j ⊆ insert (4, 3) required_617 := by decide +kernel
theorem child_envelope_sub_617 : ∀ j, childrenD_617 j ⊆ envelope_617 := by decide +kernel
theorem pivot_mem_617 : (4, 3) ∈ envelope_617 := by decide +kernel
theorem children_work_617 : ∀ j, Template HasSnaky 10 (childrenC_617 j) (childrenD_617 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_14 6 (5, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_136 4 (2, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_332 7 (7, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_616 0 (2, 1)).mono (by decide +kernel)
theorem row_works_617 : Template HasSnaky 11 required_617 envelope_617 := by
  refine compose HasSnaky 10 childrenC_617 childrenD_617 children_work_617 (4, 3)
    required_617 envelope_617 pivot_mem_617 child_required_sub_617 child_envelope_sub_617 ?_
  intro b hb
  exact common_sub_617 (mem_commonEnvelope childrenD_617 b hb)
def required_624_i1 : Finset Cell := ⟨(([(1, 4), (3, 3), (3, 4), (3, 5), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_624_i1 : Finset Cell := ⟨(([(0, 4), (1, 4), (2, 3), (2, 4), (2, 7), (2, 8), (2, 9), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 2), (4, 3), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, 3), (6, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_624_i1 : Fin 2 → Finset Cell := ![(placed21 3 (0, 4) required_64), (placed21 2 (4, 2) required_315)]
def childrenD_624_i1 : Fin 2 → Finset Cell := ![(placed21 3 (0, 4) envelope_64), (placed21 2 (4, 2) envelope_315)]
theorem common_sub_624_i1 : commonEnvelope childrenD_624_i1 ⊆ insert (4, 3) required_624_i1 := by decide +kernel
theorem child_required_sub_624_i1 : ∀ j, childrenC_624_i1 j ⊆ insert (4, 3) required_624_i1 := by decide +kernel
theorem child_envelope_sub_624_i1 : ∀ j, childrenD_624_i1 j ⊆ envelope_624_i1 := by decide +kernel
theorem pivot_mem_624_i1 : (4, 3) ∈ envelope_624_i1 := by decide +kernel
theorem children_work_624_i1 : ∀ j, Template HasSnaky 6 (childrenC_624_i1 j) (childrenD_624_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_64 3 (0, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_315 2 (4, 2)).mono (by decide +kernel)
theorem row_works_624_i1 : Template HasSnaky 7 required_624_i1 envelope_624_i1 := by
  refine compose HasSnaky 6 childrenC_624_i1 childrenD_624_i1 children_work_624_i1 (4, 3)
    required_624_i1 envelope_624_i1 pivot_mem_624_i1 child_required_sub_624_i1 child_envelope_sub_624_i1 ?_
  intro b hb
  exact common_sub_624_i1 (mem_commonEnvelope childrenD_624_i1 b hb)
def required_624_i0 : Finset Cell := ⟨(([(1, 4), (3, 4), (3, 5), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_624_i0 : Finset Cell := ⟨(([(0, 4), (1, 4), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 7), (2, 8), (2, 9), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 0), (4, 1), (4, 2), (4, 3), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, 3), (6, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_624_i0 : Fin 4 → Finset Cell := ![(placed21 6 (4, 6) required_10), (placed21 0 (3, 2) required_52), (placed21 4 (0, 6) required_82), required_624_i1]
def childrenD_624_i0 : Fin 4 → Finset Cell := ![(placed21 6 (4, 6) envelope_10), (placed21 0 (3, 2) envelope_52), (placed21 4 (0, 6) envelope_82), envelope_624_i1]
theorem common_sub_624_i0 : commonEnvelope childrenD_624_i0 ⊆ insert (3, 3) required_624_i0 := by decide +kernel
theorem child_required_sub_624_i0 : ∀ j, childrenC_624_i0 j ⊆ insert (3, 3) required_624_i0 := by decide +kernel
theorem child_envelope_sub_624_i0 : ∀ j, childrenD_624_i0 j ⊆ envelope_624_i0 := by decide +kernel
theorem pivot_mem_624_i0 : (3, 3) ∈ envelope_624_i0 := by decide +kernel
theorem children_work_624_i0 : ∀ j, Template HasSnaky 7 (childrenC_624_i0 j) (childrenD_624_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_10 6 (4, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_52 0 (3, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_82 4 (0, 6)).mono (by decide +kernel)
  · exact row_works_624_i1.mono (by decide +kernel)
theorem row_works_624_i0 : Template HasSnaky 8 required_624_i0 envelope_624_i0 := by
  refine compose HasSnaky 7 childrenC_624_i0 childrenD_624_i0 children_work_624_i0 (3, 3)
    required_624_i0 envelope_624_i0 pivot_mem_624_i0 child_required_sub_624_i0 child_envelope_sub_624_i0 ?_
  intro b hb
  exact common_sub_624_i0 (mem_commonEnvelope childrenD_624_i0 b hb)
def required_624 : Finset Cell := ⟨(([(1, 4), (3, 5), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_624 : Finset Cell := ⟨(([(0, 4), (1, 4), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 7), (2, 8), (2, 9), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, 2), (5, 3), (5, 4), (5, 5), (6, 2), (6, 3), (6, 4), (6, 5), (7, 2), (7, 3), (7, 4), (8, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_624 : Fin 3 → Finset Cell := ![(placed21 1 (0, 4) required_54), (placed21 0 (2, 0) required_545), required_624_i0]
def childrenD_624 : Fin 3 → Finset Cell := ![(placed21 1 (0, 4) envelope_54), (placed21 0 (2, 0) envelope_545), envelope_624_i0]
theorem common_sub_624 : commonEnvelope childrenD_624 ⊆ insert (3, 4) required_624 := by decide +kernel
theorem child_required_sub_624 : ∀ j, childrenC_624 j ⊆ insert (3, 4) required_624 := by decide +kernel
theorem child_envelope_sub_624 : ∀ j, childrenD_624 j ⊆ envelope_624 := by decide +kernel
theorem pivot_mem_624 : (3, 4) ∈ envelope_624 := by decide +kernel
theorem children_work_624 : ∀ j, Template HasSnaky 10 (childrenC_624 j) (childrenD_624 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_54 1 (0, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_545 0 (2, 0)).mono (by decide +kernel)
  · exact row_works_624_i0.mono (by decide +kernel)
theorem row_works_624 : Template HasSnaky 11 required_624 envelope_624 := by
  refine compose HasSnaky 10 childrenC_624 childrenD_624 children_work_624 (3, 4)
    required_624 envelope_624 pivot_mem_624 child_required_sub_624 child_envelope_sub_624 ?_
  intro b hb
  exact common_sub_624 (mem_commonEnvelope childrenD_624 b hb)
def required_625_i2 : Finset Cell := ⟨(([(1, 3), (3, 2), (3, 3), (3, 4), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_625_i2 : Finset Cell := ⟨(([(0, 1), (0, 3), (1, 1), (1, 3), (2, 0), (2, 1), (2, 3), (2, 4), (2, 5), (2, 6), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 1), (4, 2), (5, 2), (6, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_625_i2 : Fin 2 → Finset Cell := ![(placed21 7 (6, 4) required_56), (placed21 2 (4, 0) required_73)]
def childrenD_625_i2 : Fin 2 → Finset Cell := ![(placed21 7 (6, 4) envelope_56), (placed21 2 (4, 0) envelope_73)]
theorem common_sub_625_i2 : commonEnvelope childrenD_625_i2 ⊆ insert (3, 1) required_625_i2 := by decide +kernel
theorem child_required_sub_625_i2 : ∀ j, childrenC_625_i2 j ⊆ insert (3, 1) required_625_i2 := by decide +kernel
theorem child_envelope_sub_625_i2 : ∀ j, childrenD_625_i2 j ⊆ envelope_625_i2 := by decide +kernel
theorem pivot_mem_625_i2 : (3, 1) ∈ envelope_625_i2 := by decide +kernel
theorem children_work_625_i2 : ∀ j, Template HasSnaky 4 (childrenC_625_i2 j) (childrenD_625_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_56 7 (6, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_73 2 (4, 0)).mono (by decide +kernel)
theorem row_works_625_i2 : Template HasSnaky 5 required_625_i2 envelope_625_i2 := by
  refine compose HasSnaky 4 childrenC_625_i2 childrenD_625_i2 children_work_625_i2 (3, 1)
    required_625_i2 envelope_625_i2 pivot_mem_625_i2 child_required_sub_625_i2 child_envelope_sub_625_i2 ?_
  intro b hb
  exact common_sub_625_i2 (mem_commonEnvelope childrenD_625_i2 b hb)
def required_625_i1 : Finset Cell := ⟨(([(1, 3), (3, 2), (3, 3), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_625_i1 : Finset Cell := ⟨(([(0, 1), (0, 3), (1, 1), (1, 3), (2, 0), (2, 1), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 1), (4, 2), (4, 4), (4, 5), (4, 6), (4, 7), (5, 2), (5, 4), (6, 2), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_625_i1 : Fin 3 → Finset Cell := ![(placed21 2 (4, 1) required_10), (placed21 0 (0, 1) required_82), required_625_i2]
def childrenD_625_i1 : Fin 3 → Finset Cell := ![(placed21 2 (4, 1) envelope_10), (placed21 0 (0, 1) envelope_82), envelope_625_i2]
theorem common_sub_625_i1 : commonEnvelope childrenD_625_i1 ⊆ insert (3, 4) required_625_i1 := by decide +kernel
theorem child_required_sub_625_i1 : ∀ j, childrenC_625_i1 j ⊆ insert (3, 4) required_625_i1 := by decide +kernel
theorem child_envelope_sub_625_i1 : ∀ j, childrenD_625_i1 j ⊆ envelope_625_i1 := by decide +kernel
theorem pivot_mem_625_i1 : (3, 4) ∈ envelope_625_i1 := by decide +kernel
theorem children_work_625_i1 : ∀ j, Template HasSnaky 5 (childrenC_625_i1 j) (childrenD_625_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_10 2 (4, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_82 0 (0, 1)).mono (by decide +kernel)
  · exact row_works_625_i2.mono (by decide +kernel)
theorem row_works_625_i1 : Template HasSnaky 6 required_625_i1 envelope_625_i1 := by
  refine compose HasSnaky 5 childrenC_625_i1 childrenD_625_i1 children_work_625_i1 (3, 4)
    required_625_i1 envelope_625_i1 pivot_mem_625_i1 child_required_sub_625_i1 child_envelope_sub_625_i1 ?_
  intro b hb
  exact common_sub_625_i1 (mem_commonEnvelope childrenD_625_i1 b hb)
def required_625_i0 : Finset Cell := ⟨(([(1, 3), (3, 2), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_625_i0 : Finset Cell := ⟨(([(0, 1), (0, 3), (1, 1), (1, 3), (2, 0), (2, 1), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (6, 2), (6, 3), (6, 4), (6, 5), (7, 3), (7, 4), (7, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_625_i0 : Fin 4 → Finset Cell := ![(placed21 3 (0, 3) required_54), (placed21 5 (6, 1) required_294), (placed21 1 (0, 0) required_449), required_625_i1]
def childrenD_625_i0 : Fin 4 → Finset Cell := ![(placed21 3 (0, 3) envelope_54), (placed21 5 (6, 1) envelope_294), (placed21 1 (0, 0) envelope_449), envelope_625_i1]
theorem common_sub_625_i0 : commonEnvelope childrenD_625_i0 ⊆ insert (3, 3) required_625_i0 := by decide +kernel
theorem child_required_sub_625_i0 : ∀ j, childrenC_625_i0 j ⊆ insert (3, 3) required_625_i0 := by decide +kernel
theorem child_envelope_sub_625_i0 : ∀ j, childrenD_625_i0 j ⊆ envelope_625_i0 := by decide +kernel
theorem pivot_mem_625_i0 : (3, 3) ∈ envelope_625_i0 := by decide +kernel
theorem children_work_625_i0 : ∀ j, Template HasSnaky 9 (childrenC_625_i0 j) (childrenD_625_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_54 3 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_294 5 (6, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_449 1 (0, 0)).mono (by decide +kernel)
  · exact row_works_625_i1.mono (by decide +kernel)
theorem row_works_625_i0 : Template HasSnaky 10 required_625_i0 envelope_625_i0 := by
  refine compose HasSnaky 9 childrenC_625_i0 childrenD_625_i0 children_work_625_i0 (3, 3)
    required_625_i0 envelope_625_i0 pivot_mem_625_i0 child_required_sub_625_i0 child_envelope_sub_625_i0 ?_
  intro b hb
  exact common_sub_625_i0 (mem_commonEnvelope childrenD_625_i0 b hb)
def required_625 : Finset Cell := ⟨(([(1, 2), (1, 3), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_625 : Finset Cell := ⟨(([(0, 1), (0, 3), (1, 1), (1, 2), (1, 3), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (7, 3), (7, 4), (7, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_625 : Fin 5 → Finset Cell := ![(placed21 3 (0, 3) required_50), (placed21 3 (0, 3) required_125), (placed21 5 (5, 1) required_454), (placed21 0 (1, 1) required_455), required_625_i0]
def childrenD_625 : Fin 5 → Finset Cell := ![(placed21 3 (0, 3) envelope_50), (placed21 3 (0, 3) envelope_125), (placed21 5 (5, 1) envelope_454), (placed21 0 (1, 1) envelope_455), envelope_625_i0]
theorem common_sub_625 : commonEnvelope childrenD_625 ⊆ insert (3, 2) required_625 := by decide +kernel
theorem child_required_sub_625 : ∀ j, childrenC_625 j ⊆ insert (3, 2) required_625 := by decide +kernel
theorem child_envelope_sub_625 : ∀ j, childrenD_625 j ⊆ envelope_625 := by decide +kernel
theorem pivot_mem_625 : (3, 2) ∈ envelope_625 := by decide +kernel
theorem children_work_625 : ∀ j, Template HasSnaky 10 (childrenC_625 j) (childrenD_625 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_50 3 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_125 3 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_454 5 (5, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_455 0 (1, 1)).mono (by decide +kernel)
  · exact row_works_625_i0.mono (by decide +kernel)
theorem row_works_625 : Template HasSnaky 11 required_625 envelope_625 := by
  refine compose HasSnaky 10 childrenC_625 childrenD_625 children_work_625 (3, 2)
    required_625 envelope_625 pivot_mem_625 child_required_sub_625 child_envelope_sub_625 ?_
  intro b hb
  exact common_sub_625 (mem_commonEnvelope childrenD_625 b hb)
def required_626_i1 : Finset Cell := ⟨(([(2, 3), (3, 5), (3, 6), (4, 5), (5, 5), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_626_i1 : Finset Cell := ⟨(([(1, 4), (2, 2), (2, 3), (2, 4), (2, 5), (3, 5), (3, 6), (4, 5), (5, 5), (5, 6), (6, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_626_i1 : Fin 2 → Finset Cell := ![(placed21 0 (2, 5) required_5), (placed21 6 (5, 6) required_38)]
def childrenD_626_i1 : Fin 2 → Finset Cell := ![(placed21 0 (2, 5) envelope_5), (placed21 6 (5, 6) envelope_38)]
theorem common_sub_626_i1 : commonEnvelope childrenD_626_i1 ⊆ insert (2, 5) required_626_i1 := by decide +kernel
theorem child_required_sub_626_i1 : ∀ j, childrenC_626_i1 j ⊆ insert (2, 5) required_626_i1 := by decide +kernel
theorem child_envelope_sub_626_i1 : ∀ j, childrenD_626_i1 j ⊆ envelope_626_i1 := by decide +kernel
theorem pivot_mem_626_i1 : (2, 5) ∈ envelope_626_i1 := by decide +kernel
theorem children_work_626_i1 : ∀ j, Template HasSnaky 2 (childrenC_626_i1 j) (childrenD_626_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 0 (2, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_38 6 (5, 6)).mono (by decide +kernel)
theorem row_works_626_i1 : Template HasSnaky 3 required_626_i1 envelope_626_i1 := by
  refine compose HasSnaky 2 childrenC_626_i1 childrenD_626_i1 children_work_626_i1 (2, 5)
    required_626_i1 envelope_626_i1 pivot_mem_626_i1 child_required_sub_626_i1 child_envelope_sub_626_i1 ?_
  intro b hb
  exact common_sub_626_i1 (mem_commonEnvelope childrenD_626_i1 b hb)
def required_626_i0 : Finset Cell := ⟨(([(2, 3), (3, 5), (3, 6), (5, 5), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_626_i0 : Finset Cell := ⟨(([(1, 4), (2, 2), (2, 3), (2, 4), (2, 5), (2, 8), (3, 5), (3, 6), (3, 8), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 7), (4, 8), (4, 9), (4, 10), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (6, 1), (6, 2), (6, 3), (6, 4), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (7, 4), (7, 7), (8, 4), (8, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_626_i0 : Fin 3 → Finset Cell := ![(placed21 4 (2, 9) required_317), required_626_i1, (placed21 0 (2, 2) required_519)]
def childrenD_626_i0 : Fin 3 → Finset Cell := ![(placed21 4 (2, 9) envelope_317), envelope_626_i1, (placed21 0 (2, 2) envelope_519)]
theorem common_sub_626_i0 : commonEnvelope childrenD_626_i0 ⊆ insert (4, 5) required_626_i0 := by decide +kernel
theorem child_required_sub_626_i0 : ∀ j, childrenC_626_i0 j ⊆ insert (4, 5) required_626_i0 := by decide +kernel
theorem child_envelope_sub_626_i0 : ∀ j, childrenD_626_i0 j ⊆ envelope_626_i0 := by decide +kernel
theorem pivot_mem_626_i0 : (4, 5) ∈ envelope_626_i0 := by decide +kernel
theorem children_work_626_i0 : ∀ j, Template HasSnaky 9 (childrenC_626_i0 j) (childrenD_626_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_317 4 (2, 9)).mono (by decide +kernel)
  · exact row_works_626_i1.mono (by decide +kernel)
  · exact (placed21_template row_works_519 0 (2, 2)).mono (by decide +kernel)
theorem row_works_626_i0 : Template HasSnaky 10 required_626_i0 envelope_626_i0 := by
  refine compose HasSnaky 9 childrenC_626_i0 childrenD_626_i0 children_work_626_i0 (4, 5)
    required_626_i0 envelope_626_i0 pivot_mem_626_i0 child_required_sub_626_i0 child_envelope_sub_626_i0 ?_
  intro b hb
  exact common_sub_626_i0 (mem_commonEnvelope childrenD_626_i0 b hb)
def required_626_i3 : Finset Cell := ⟨(([(2, 6), (3, 5), (3, 6), (4, 6), (5, 5), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_626_i3 : Finset Cell := ⟨(([(1, 5), (1, 7), (1, 8), (1, 9), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, 5), (3, 6), (3, 8), (3, 9), (4, 6), (4, 7), (4, 8), (4, 9), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_626_i3 : Fin 2 → Finset Cell := ![(placed21 6 (5, 6) required_5), (placed21 1 (1, 5) required_412)]
def childrenD_626_i3 : Fin 2 → Finset Cell := ![(placed21 6 (5, 6) envelope_5), (placed21 1 (1, 5) envelope_412)]
theorem common_sub_626_i3 : commonEnvelope childrenD_626_i3 ⊆ insert (2, 5) required_626_i3 := by decide +kernel
theorem child_required_sub_626_i3 : ∀ j, childrenC_626_i3 j ⊆ insert (2, 5) required_626_i3 := by decide +kernel
theorem child_envelope_sub_626_i3 : ∀ j, childrenD_626_i3 j ⊆ envelope_626_i3 := by decide +kernel
theorem pivot_mem_626_i3 : (2, 5) ∈ envelope_626_i3 := by decide +kernel
theorem children_work_626_i3 : ∀ j, Template HasSnaky 8 (childrenC_626_i3 j) (childrenD_626_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 6 (5, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_412 1 (1, 5)).mono (by decide +kernel)
theorem row_works_626_i3 : Template HasSnaky 9 required_626_i3 envelope_626_i3 := by
  refine compose HasSnaky 8 childrenC_626_i3 childrenD_626_i3 children_work_626_i3 (2, 5)
    required_626_i3 envelope_626_i3 pivot_mem_626_i3 child_required_sub_626_i3 child_envelope_sub_626_i3 ?_
  intro b hb
  exact common_sub_626_i3 (mem_commonEnvelope childrenD_626_i3 b hb)
def required_626_i2 : Finset Cell := ⟨(([(2, 6), (3, 5), (3, 6), (5, 5), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_626_i2 : Finset Cell := ⟨(([(1, 5), (1, 7), (1, 8), (1, 9), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, 5), (3, 6), (3, 8), (3, 9), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 6), (6, 7), (7, 5), (7, 6), (7, 7), (8, 5), (8, 6), (8, 7), (9, 5), (9, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_626_i2 : Fin 3 → Finset Cell := ![(placed21 3 (1, 6) required_11), (placed21 1 (2, 5) required_336), required_626_i3]
def childrenD_626_i2 : Fin 3 → Finset Cell := ![(placed21 3 (1, 6) envelope_11), (placed21 1 (2, 5) envelope_336), envelope_626_i3]
theorem common_sub_626_i2 : commonEnvelope childrenD_626_i2 ⊆ insert (4, 6) required_626_i2 := by decide +kernel
theorem child_required_sub_626_i2 : ∀ j, childrenC_626_i2 j ⊆ insert (4, 6) required_626_i2 := by decide +kernel
theorem child_envelope_sub_626_i2 : ∀ j, childrenD_626_i2 j ⊆ envelope_626_i2 := by decide +kernel
theorem pivot_mem_626_i2 : (4, 6) ∈ envelope_626_i2 := by decide +kernel
theorem children_work_626_i2 : ∀ j, Template HasSnaky 9 (childrenC_626_i2 j) (childrenD_626_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_11 3 (1, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_336 1 (2, 5)).mono (by decide +kernel)
  · exact row_works_626_i3.mono (by decide +kernel)
theorem row_works_626_i2 : Template HasSnaky 10 required_626_i2 envelope_626_i2 := by
  refine compose HasSnaky 9 childrenC_626_i2 childrenD_626_i2 children_work_626_i2 (4, 6)
    required_626_i2 envelope_626_i2 pivot_mem_626_i2 child_required_sub_626_i2 child_envelope_sub_626_i2 ?_
  intro b hb
  exact common_sub_626_i2 (mem_commonEnvelope childrenD_626_i2 b hb)
def required_626 : Finset Cell := ⟨(([(2, 3), (2, 6), (3, 5), (3, 6), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_626 : Finset Cell := ⟨(([(0, 4), (1, 4), (1, 5), (1, 7), (1, 8), (1, 9), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, 5), (3, 6), (3, 8), (3, 9), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (6, 1), (6, 2), (6, 3), (6, 4), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (7, 4), (7, 5), (7, 6), (7, 7), (8, 4), (8, 5), (8, 6), (8, 7), (9, 5), (9, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_626 : Fin 5 → Finset Cell := ![(placed21 2 (6, 2) required_323), (placed21 0 (2, 2) required_430), (placed21 7 (6, 6) required_592), required_626_i0, required_626_i2]
def childrenD_626 : Fin 5 → Finset Cell := ![(placed21 2 (6, 2) envelope_323), (placed21 0 (2, 2) envelope_430), (placed21 7 (6, 6) envelope_592), envelope_626_i0, envelope_626_i2]
theorem common_sub_626 : commonEnvelope childrenD_626 ⊆ insert (5, 6) required_626 := by decide +kernel
theorem child_required_sub_626 : ∀ j, childrenC_626 j ⊆ insert (5, 6) required_626 := by decide +kernel
theorem child_envelope_sub_626 : ∀ j, childrenD_626 j ⊆ envelope_626 := by decide +kernel
theorem pivot_mem_626 : (5, 6) ∈ envelope_626 := by decide +kernel
theorem children_work_626 : ∀ j, Template HasSnaky 10 (childrenC_626 j) (childrenD_626 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_323 2 (6, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_430 0 (2, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_592 7 (6, 6)).mono (by decide +kernel)
  · exact row_works_626_i0.mono (by decide +kernel)
  · exact row_works_626_i2.mono (by decide +kernel)
theorem row_works_626 : Template HasSnaky 11 required_626 envelope_626 := by
  refine compose HasSnaky 10 childrenC_626 childrenD_626 children_work_626 (5, 6)
    required_626 envelope_626 pivot_mem_626 child_required_sub_626 child_envelope_sub_626 ?_
  intro b hb
  exact common_sub_626 (mem_commonEnvelope childrenD_626 b hb)
def height_615_i5 : ℕ := 4
def childrenH_615_i5 : Fin 3 → ℕ := ![height_11, height_20, height_402]
theorem height_exact_615_i5 : height_615_i5 = 1 + Finset.univ.sup childrenH_615_i5 := by decide +kernel
theorem required_origin_615_i5 : ∀ x ∈ required_615_i5,
    (∃ j, x ∈ childrenC_615_i5 j) ∨ ∀ j, x ∈ childrenD_615_i5 j := by decide +kernel
theorem required_exact_615_i5 : required_615_i5 =
    ((Finset.univ.biUnion childrenC_615_i5) ∪ commonEnvelope childrenD_615_i5).erase (4, 3) := by
  exact required_eq_combination childrenC_615_i5 childrenD_615_i5 (4, 3) required_615_i5
    (by decide +kernel) child_required_sub_615_i5 common_sub_615_i5 required_origin_615_i5
theorem envelope_origin_615_i5 : ∀ x ∈ envelope_615_i5,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_615_i5 j := by decide +kernel
theorem envelope_exact_615_i5 : envelope_615_i5 =
    insert (4, 3) (Finset.univ.biUnion childrenD_615_i5) := by
  exact envelope_eq_combination childrenD_615_i5 (4, 3) envelope_615_i5
    pivot_mem_615_i5 child_envelope_sub_615_i5 envelope_origin_615_i5
def checked_615_i5 : CheckedCard where
  required := required_615_i5
  envelope := envelope_615_i5
  height := height_615_i5
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_615_i5
def height_615_i4 : ℕ := 5
def childrenH_615_i4 : Fin 2 → ℕ := ![height_0, height_615_i5]
theorem height_exact_615_i4 : height_615_i4 = 1 + Finset.univ.sup childrenH_615_i4 := by decide +kernel
theorem required_origin_615_i4 : ∀ x ∈ required_615_i4,
    (∃ j, x ∈ childrenC_615_i4 j) ∨ ∀ j, x ∈ childrenD_615_i4 j := by decide +kernel
theorem required_exact_615_i4 : required_615_i4 =
    ((Finset.univ.biUnion childrenC_615_i4) ∪ commonEnvelope childrenD_615_i4).erase (4, 4) := by
  exact required_eq_combination childrenC_615_i4 childrenD_615_i4 (4, 4) required_615_i4
    (by decide +kernel) child_required_sub_615_i4 common_sub_615_i4 required_origin_615_i4
theorem envelope_origin_615_i4 : ∀ x ∈ envelope_615_i4,
    x = (4, 4) ∨ ∃ j, x ∈ childrenD_615_i4 j := by decide +kernel
theorem envelope_exact_615_i4 : envelope_615_i4 =
    insert (4, 4) (Finset.univ.biUnion childrenD_615_i4) := by
  exact envelope_eq_combination childrenD_615_i4 (4, 4) envelope_615_i4
    pivot_mem_615_i4 child_envelope_sub_615_i4 envelope_origin_615_i4
def checked_615_i4 : CheckedCard where
  required := required_615_i4
  envelope := envelope_615_i4
  height := height_615_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_615_i4
def height_615_i3 : ℕ := 6
def childrenH_615_i3 : Fin 2 → ℕ := ![height_5, height_615_i4]
theorem height_exact_615_i3 : height_615_i3 = 1 + Finset.univ.sup childrenH_615_i3 := by decide +kernel
theorem required_origin_615_i3 : ∀ x ∈ required_615_i3,
    (∃ j, x ∈ childrenC_615_i3 j) ∨ ∀ j, x ∈ childrenD_615_i3 j := by decide +kernel
theorem required_exact_615_i3 : required_615_i3 =
    ((Finset.univ.biUnion childrenC_615_i3) ∪ commonEnvelope childrenD_615_i3).erase (6, 5) := by
  exact required_eq_combination childrenC_615_i3 childrenD_615_i3 (6, 5) required_615_i3
    (by decide +kernel) child_required_sub_615_i3 common_sub_615_i3 required_origin_615_i3
theorem envelope_origin_615_i3 : ∀ x ∈ envelope_615_i3,
    x = (6, 5) ∨ ∃ j, x ∈ childrenD_615_i3 j := by decide +kernel
theorem envelope_exact_615_i3 : envelope_615_i3 =
    insert (6, 5) (Finset.univ.biUnion childrenD_615_i3) := by
  exact envelope_eq_combination childrenD_615_i3 (6, 5) envelope_615_i3
    pivot_mem_615_i3 child_envelope_sub_615_i3 envelope_origin_615_i3
def checked_615_i3 : CheckedCard where
  required := required_615_i3
  envelope := envelope_615_i3
  height := height_615_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_615_i3
def height_615_i2 : ℕ := 7
def childrenH_615_i2 : Fin 3 → ℕ := ![height_139, height_148, height_615_i3]
theorem height_exact_615_i2 : height_615_i2 = 1 + Finset.univ.sup childrenH_615_i2 := by decide +kernel
theorem required_origin_615_i2 : ∀ x ∈ required_615_i2,
    (∃ j, x ∈ childrenC_615_i2 j) ∨ ∀ j, x ∈ childrenD_615_i2 j := by decide +kernel
theorem required_exact_615_i2 : required_615_i2 =
    ((Finset.univ.biUnion childrenC_615_i2) ∪ commonEnvelope childrenD_615_i2).erase (6, 4) := by
  exact required_eq_combination childrenC_615_i2 childrenD_615_i2 (6, 4) required_615_i2
    (by decide +kernel) child_required_sub_615_i2 common_sub_615_i2 required_origin_615_i2
theorem envelope_origin_615_i2 : ∀ x ∈ envelope_615_i2,
    x = (6, 4) ∨ ∃ j, x ∈ childrenD_615_i2 j := by decide +kernel
theorem envelope_exact_615_i2 : envelope_615_i2 =
    insert (6, 4) (Finset.univ.biUnion childrenD_615_i2) := by
  exact envelope_eq_combination childrenD_615_i2 (6, 4) envelope_615_i2
    pivot_mem_615_i2 child_envelope_sub_615_i2 envelope_origin_615_i2
def checked_615_i2 : CheckedCard where
  required := required_615_i2
  envelope := envelope_615_i2
  height := height_615_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_615_i2
def height_615_i1 : ℕ := 8
def childrenH_615_i1 : Fin 3 → ℕ := ![height_43, height_57, height_615_i2]
theorem height_exact_615_i1 : height_615_i1 = 1 + Finset.univ.sup childrenH_615_i1 := by decide +kernel
theorem required_origin_615_i1 : ∀ x ∈ required_615_i1,
    (∃ j, x ∈ childrenC_615_i1 j) ∨ ∀ j, x ∈ childrenD_615_i1 j := by decide +kernel
theorem required_exact_615_i1 : required_615_i1 =
    ((Finset.univ.biUnion childrenC_615_i1) ∪ commonEnvelope childrenD_615_i1).erase (4, 6) := by
  exact required_eq_combination childrenC_615_i1 childrenD_615_i1 (4, 6) required_615_i1
    (by decide +kernel) child_required_sub_615_i1 common_sub_615_i1 required_origin_615_i1
theorem envelope_origin_615_i1 : ∀ x ∈ envelope_615_i1,
    x = (4, 6) ∨ ∃ j, x ∈ childrenD_615_i1 j := by decide +kernel
theorem envelope_exact_615_i1 : envelope_615_i1 =
    insert (4, 6) (Finset.univ.biUnion childrenD_615_i1) := by
  exact envelope_eq_combination childrenD_615_i1 (4, 6) envelope_615_i1
    pivot_mem_615_i1 child_envelope_sub_615_i1 envelope_origin_615_i1
def checked_615_i1 : CheckedCard where
  required := required_615_i1
  envelope := envelope_615_i1
  height := height_615_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_615_i1
def height_615_i0 : ℕ := 10
def childrenH_615_i0 : Fin 7 → ℕ := ![height_116, height_134, height_180, height_435, height_558, height_561, height_615_i1]
theorem height_exact_615_i0 : height_615_i0 = 1 + Finset.univ.sup childrenH_615_i0 := by decide +kernel
theorem required_origin_615_i0 : ∀ x ∈ required_615_i0,
    (∃ j, x ∈ childrenC_615_i0 j) ∨ ∀ j, x ∈ childrenD_615_i0 j := by decide +kernel
theorem required_exact_615_i0 : required_615_i0 =
    ((Finset.univ.biUnion childrenC_615_i0) ∪ commonEnvelope childrenD_615_i0).erase (5, 5) := by
  exact required_eq_combination childrenC_615_i0 childrenD_615_i0 (5, 5) required_615_i0
    (by decide +kernel) child_required_sub_615_i0 common_sub_615_i0 required_origin_615_i0
theorem envelope_origin_615_i0 : ∀ x ∈ envelope_615_i0,
    x = (5, 5) ∨ ∃ j, x ∈ childrenD_615_i0 j := by decide +kernel
theorem envelope_exact_615_i0 : envelope_615_i0 =
    insert (5, 5) (Finset.univ.biUnion childrenD_615_i0) := by
  exact envelope_eq_combination childrenD_615_i0 (5, 5) envelope_615_i0
    pivot_mem_615_i0 child_envelope_sub_615_i0 envelope_origin_615_i0
def checked_615_i0 : CheckedCard where
  required := required_615_i0
  envelope := envelope_615_i0
  height := height_615_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_615_i0
def height_615 : ℕ := 11
def childrenH_615 : Fin 3 → ℕ := ![height_362, height_614, height_615_i0]
theorem height_exact_615 : height_615 = 1 + Finset.univ.sup childrenH_615 := by decide +kernel
theorem required_origin_615 : ∀ x ∈ required_615,
    (∃ j, x ∈ childrenC_615 j) ∨ ∀ j, x ∈ childrenD_615 j := by decide +kernel
theorem required_exact_615 : required_615 =
    ((Finset.univ.biUnion childrenC_615) ∪ commonEnvelope childrenD_615).erase (4, 5) := by
  exact required_eq_combination childrenC_615 childrenD_615 (4, 5) required_615
    (by decide +kernel) child_required_sub_615 common_sub_615 required_origin_615
theorem envelope_origin_615 : ∀ x ∈ envelope_615,
    x = (4, 5) ∨ ∃ j, x ∈ childrenD_615 j := by decide +kernel
theorem envelope_exact_615 : envelope_615 =
    insert (4, 5) (Finset.univ.biUnion childrenD_615) := by
  exact envelope_eq_combination childrenD_615 (4, 5) envelope_615
    pivot_mem_615 child_envelope_sub_615 envelope_origin_615
def checked_615 : CheckedCard where
  required := required_615
  envelope := envelope_615
  height := height_615
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_615
def height_617 : ℕ := 11
def childrenH_617 : Fin 4 → ℕ := ![height_14, height_136, height_332, height_616]
theorem height_exact_617 : height_617 = 1 + Finset.univ.sup childrenH_617 := by decide +kernel
theorem required_origin_617 : ∀ x ∈ required_617,
    (∃ j, x ∈ childrenC_617 j) ∨ ∀ j, x ∈ childrenD_617 j := by decide +kernel
theorem required_exact_617 : required_617 =
    ((Finset.univ.biUnion childrenC_617) ∪ commonEnvelope childrenD_617).erase (4, 3) := by
  exact required_eq_combination childrenC_617 childrenD_617 (4, 3) required_617
    (by decide +kernel) child_required_sub_617 common_sub_617 required_origin_617
theorem envelope_origin_617 : ∀ x ∈ envelope_617,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_617 j := by decide +kernel
theorem envelope_exact_617 : envelope_617 =
    insert (4, 3) (Finset.univ.biUnion childrenD_617) := by
  exact envelope_eq_combination childrenD_617 (4, 3) envelope_617
    pivot_mem_617 child_envelope_sub_617 envelope_origin_617
def checked_617 : CheckedCard where
  required := required_617
  envelope := envelope_617
  height := height_617
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_617
def height_624_i1 : ℕ := 7
def childrenH_624_i1 : Fin 2 → ℕ := ![height_64, height_315]
theorem height_exact_624_i1 : height_624_i1 = 1 + Finset.univ.sup childrenH_624_i1 := by decide +kernel
theorem required_origin_624_i1 : ∀ x ∈ required_624_i1,
    (∃ j, x ∈ childrenC_624_i1 j) ∨ ∀ j, x ∈ childrenD_624_i1 j := by decide +kernel
theorem required_exact_624_i1 : required_624_i1 =
    ((Finset.univ.biUnion childrenC_624_i1) ∪ commonEnvelope childrenD_624_i1).erase (4, 3) := by
  exact required_eq_combination childrenC_624_i1 childrenD_624_i1 (4, 3) required_624_i1
    (by decide +kernel) child_required_sub_624_i1 common_sub_624_i1 required_origin_624_i1
theorem envelope_origin_624_i1 : ∀ x ∈ envelope_624_i1,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_624_i1 j := by decide +kernel
theorem envelope_exact_624_i1 : envelope_624_i1 =
    insert (4, 3) (Finset.univ.biUnion childrenD_624_i1) := by
  exact envelope_eq_combination childrenD_624_i1 (4, 3) envelope_624_i1
    pivot_mem_624_i1 child_envelope_sub_624_i1 envelope_origin_624_i1
def checked_624_i1 : CheckedCard where
  required := required_624_i1
  envelope := envelope_624_i1
  height := height_624_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_624_i1
def height_624_i0 : ℕ := 8
def childrenH_624_i0 : Fin 4 → ℕ := ![height_10, height_52, height_82, height_624_i1]
theorem height_exact_624_i0 : height_624_i0 = 1 + Finset.univ.sup childrenH_624_i0 := by decide +kernel
theorem required_origin_624_i0 : ∀ x ∈ required_624_i0,
    (∃ j, x ∈ childrenC_624_i0 j) ∨ ∀ j, x ∈ childrenD_624_i0 j := by decide +kernel
theorem required_exact_624_i0 : required_624_i0 =
    ((Finset.univ.biUnion childrenC_624_i0) ∪ commonEnvelope childrenD_624_i0).erase (3, 3) := by
  exact required_eq_combination childrenC_624_i0 childrenD_624_i0 (3, 3) required_624_i0
    (by decide +kernel) child_required_sub_624_i0 common_sub_624_i0 required_origin_624_i0
theorem envelope_origin_624_i0 : ∀ x ∈ envelope_624_i0,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_624_i0 j := by decide +kernel
theorem envelope_exact_624_i0 : envelope_624_i0 =
    insert (3, 3) (Finset.univ.biUnion childrenD_624_i0) := by
  exact envelope_eq_combination childrenD_624_i0 (3, 3) envelope_624_i0
    pivot_mem_624_i0 child_envelope_sub_624_i0 envelope_origin_624_i0
def checked_624_i0 : CheckedCard where
  required := required_624_i0
  envelope := envelope_624_i0
  height := height_624_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_624_i0
def height_624 : ℕ := 11
def childrenH_624 : Fin 3 → ℕ := ![height_54, height_545, height_624_i0]
theorem height_exact_624 : height_624 = 1 + Finset.univ.sup childrenH_624 := by decide +kernel
theorem required_origin_624 : ∀ x ∈ required_624,
    (∃ j, x ∈ childrenC_624 j) ∨ ∀ j, x ∈ childrenD_624 j := by decide +kernel
theorem required_exact_624 : required_624 =
    ((Finset.univ.biUnion childrenC_624) ∪ commonEnvelope childrenD_624).erase (3, 4) := by
  exact required_eq_combination childrenC_624 childrenD_624 (3, 4) required_624
    (by decide +kernel) child_required_sub_624 common_sub_624 required_origin_624
theorem envelope_origin_624 : ∀ x ∈ envelope_624,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_624 j := by decide +kernel
theorem envelope_exact_624 : envelope_624 =
    insert (3, 4) (Finset.univ.biUnion childrenD_624) := by
  exact envelope_eq_combination childrenD_624 (3, 4) envelope_624
    pivot_mem_624 child_envelope_sub_624 envelope_origin_624
def checked_624 : CheckedCard where
  required := required_624
  envelope := envelope_624
  height := height_624
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_624
def height_625_i2 : ℕ := 5
def childrenH_625_i2 : Fin 2 → ℕ := ![height_56, height_73]
theorem height_exact_625_i2 : height_625_i2 = 1 + Finset.univ.sup childrenH_625_i2 := by decide +kernel
theorem required_origin_625_i2 : ∀ x ∈ required_625_i2,
    (∃ j, x ∈ childrenC_625_i2 j) ∨ ∀ j, x ∈ childrenD_625_i2 j := by decide +kernel
theorem required_exact_625_i2 : required_625_i2 =
    ((Finset.univ.biUnion childrenC_625_i2) ∪ commonEnvelope childrenD_625_i2).erase (3, 1) := by
  exact required_eq_combination childrenC_625_i2 childrenD_625_i2 (3, 1) required_625_i2
    (by decide +kernel) child_required_sub_625_i2 common_sub_625_i2 required_origin_625_i2
theorem envelope_origin_625_i2 : ∀ x ∈ envelope_625_i2,
    x = (3, 1) ∨ ∃ j, x ∈ childrenD_625_i2 j := by decide +kernel
theorem envelope_exact_625_i2 : envelope_625_i2 =
    insert (3, 1) (Finset.univ.biUnion childrenD_625_i2) := by
  exact envelope_eq_combination childrenD_625_i2 (3, 1) envelope_625_i2
    pivot_mem_625_i2 child_envelope_sub_625_i2 envelope_origin_625_i2
def checked_625_i2 : CheckedCard where
  required := required_625_i2
  envelope := envelope_625_i2
  height := height_625_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_625_i2
def height_625_i1 : ℕ := 6
def childrenH_625_i1 : Fin 3 → ℕ := ![height_10, height_82, height_625_i2]
theorem height_exact_625_i1 : height_625_i1 = 1 + Finset.univ.sup childrenH_625_i1 := by decide +kernel
theorem required_origin_625_i1 : ∀ x ∈ required_625_i1,
    (∃ j, x ∈ childrenC_625_i1 j) ∨ ∀ j, x ∈ childrenD_625_i1 j := by decide +kernel
theorem required_exact_625_i1 : required_625_i1 =
    ((Finset.univ.biUnion childrenC_625_i1) ∪ commonEnvelope childrenD_625_i1).erase (3, 4) := by
  exact required_eq_combination childrenC_625_i1 childrenD_625_i1 (3, 4) required_625_i1
    (by decide +kernel) child_required_sub_625_i1 common_sub_625_i1 required_origin_625_i1
theorem envelope_origin_625_i1 : ∀ x ∈ envelope_625_i1,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_625_i1 j := by decide +kernel
theorem envelope_exact_625_i1 : envelope_625_i1 =
    insert (3, 4) (Finset.univ.biUnion childrenD_625_i1) := by
  exact envelope_eq_combination childrenD_625_i1 (3, 4) envelope_625_i1
    pivot_mem_625_i1 child_envelope_sub_625_i1 envelope_origin_625_i1
def checked_625_i1 : CheckedCard where
  required := required_625_i1
  envelope := envelope_625_i1
  height := height_625_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_625_i1
def height_625_i0 : ℕ := 10
def childrenH_625_i0 : Fin 4 → ℕ := ![height_54, height_294, height_449, height_625_i1]
theorem height_exact_625_i0 : height_625_i0 = 1 + Finset.univ.sup childrenH_625_i0 := by decide +kernel
theorem required_origin_625_i0 : ∀ x ∈ required_625_i0,
    (∃ j, x ∈ childrenC_625_i0 j) ∨ ∀ j, x ∈ childrenD_625_i0 j := by decide +kernel
theorem required_exact_625_i0 : required_625_i0 =
    ((Finset.univ.biUnion childrenC_625_i0) ∪ commonEnvelope childrenD_625_i0).erase (3, 3) := by
  exact required_eq_combination childrenC_625_i0 childrenD_625_i0 (3, 3) required_625_i0
    (by decide +kernel) child_required_sub_625_i0 common_sub_625_i0 required_origin_625_i0
theorem envelope_origin_625_i0 : ∀ x ∈ envelope_625_i0,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_625_i0 j := by decide +kernel
theorem envelope_exact_625_i0 : envelope_625_i0 =
    insert (3, 3) (Finset.univ.biUnion childrenD_625_i0) := by
  exact envelope_eq_combination childrenD_625_i0 (3, 3) envelope_625_i0
    pivot_mem_625_i0 child_envelope_sub_625_i0 envelope_origin_625_i0
def checked_625_i0 : CheckedCard where
  required := required_625_i0
  envelope := envelope_625_i0
  height := height_625_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_625_i0
def height_625 : ℕ := 11
def childrenH_625 : Fin 5 → ℕ := ![height_50, height_125, height_454, height_455, height_625_i0]
theorem height_exact_625 : height_625 = 1 + Finset.univ.sup childrenH_625 := by decide +kernel
theorem required_origin_625 : ∀ x ∈ required_625,
    (∃ j, x ∈ childrenC_625 j) ∨ ∀ j, x ∈ childrenD_625 j := by decide +kernel
theorem required_exact_625 : required_625 =
    ((Finset.univ.biUnion childrenC_625) ∪ commonEnvelope childrenD_625).erase (3, 2) := by
  exact required_eq_combination childrenC_625 childrenD_625 (3, 2) required_625
    (by decide +kernel) child_required_sub_625 common_sub_625 required_origin_625
theorem envelope_origin_625 : ∀ x ∈ envelope_625,
    x = (3, 2) ∨ ∃ j, x ∈ childrenD_625 j := by decide +kernel
theorem envelope_exact_625 : envelope_625 =
    insert (3, 2) (Finset.univ.biUnion childrenD_625) := by
  exact envelope_eq_combination childrenD_625 (3, 2) envelope_625
    pivot_mem_625 child_envelope_sub_625 envelope_origin_625
def checked_625 : CheckedCard where
  required := required_625
  envelope := envelope_625
  height := height_625
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_625
def height_626_i1 : ℕ := 3
def childrenH_626_i1 : Fin 2 → ℕ := ![height_5, height_38]
theorem height_exact_626_i1 : height_626_i1 = 1 + Finset.univ.sup childrenH_626_i1 := by decide +kernel
theorem required_origin_626_i1 : ∀ x ∈ required_626_i1,
    (∃ j, x ∈ childrenC_626_i1 j) ∨ ∀ j, x ∈ childrenD_626_i1 j := by decide +kernel
theorem required_exact_626_i1 : required_626_i1 =
    ((Finset.univ.biUnion childrenC_626_i1) ∪ commonEnvelope childrenD_626_i1).erase (2, 5) := by
  exact required_eq_combination childrenC_626_i1 childrenD_626_i1 (2, 5) required_626_i1
    (by decide +kernel) child_required_sub_626_i1 common_sub_626_i1 required_origin_626_i1
theorem envelope_origin_626_i1 : ∀ x ∈ envelope_626_i1,
    x = (2, 5) ∨ ∃ j, x ∈ childrenD_626_i1 j := by decide +kernel
theorem envelope_exact_626_i1 : envelope_626_i1 =
    insert (2, 5) (Finset.univ.biUnion childrenD_626_i1) := by
  exact envelope_eq_combination childrenD_626_i1 (2, 5) envelope_626_i1
    pivot_mem_626_i1 child_envelope_sub_626_i1 envelope_origin_626_i1
def checked_626_i1 : CheckedCard where
  required := required_626_i1
  envelope := envelope_626_i1
  height := height_626_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_626_i1
def height_626_i0 : ℕ := 10
def childrenH_626_i0 : Fin 3 → ℕ := ![height_317, height_626_i1, height_519]
theorem height_exact_626_i0 : height_626_i0 = 1 + Finset.univ.sup childrenH_626_i0 := by decide +kernel
theorem required_origin_626_i0 : ∀ x ∈ required_626_i0,
    (∃ j, x ∈ childrenC_626_i0 j) ∨ ∀ j, x ∈ childrenD_626_i0 j := by decide +kernel
theorem required_exact_626_i0 : required_626_i0 =
    ((Finset.univ.biUnion childrenC_626_i0) ∪ commonEnvelope childrenD_626_i0).erase (4, 5) := by
  exact required_eq_combination childrenC_626_i0 childrenD_626_i0 (4, 5) required_626_i0
    (by decide +kernel) child_required_sub_626_i0 common_sub_626_i0 required_origin_626_i0
theorem envelope_origin_626_i0 : ∀ x ∈ envelope_626_i0,
    x = (4, 5) ∨ ∃ j, x ∈ childrenD_626_i0 j := by decide +kernel
theorem envelope_exact_626_i0 : envelope_626_i0 =
    insert (4, 5) (Finset.univ.biUnion childrenD_626_i0) := by
  exact envelope_eq_combination childrenD_626_i0 (4, 5) envelope_626_i0
    pivot_mem_626_i0 child_envelope_sub_626_i0 envelope_origin_626_i0
def checked_626_i0 : CheckedCard where
  required := required_626_i0
  envelope := envelope_626_i0
  height := height_626_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_626_i0
def height_626_i3 : ℕ := 9
def childrenH_626_i3 : Fin 2 → ℕ := ![height_5, height_412]
theorem height_exact_626_i3 : height_626_i3 = 1 + Finset.univ.sup childrenH_626_i3 := by decide +kernel
theorem required_origin_626_i3 : ∀ x ∈ required_626_i3,
    (∃ j, x ∈ childrenC_626_i3 j) ∨ ∀ j, x ∈ childrenD_626_i3 j := by decide +kernel
theorem required_exact_626_i3 : required_626_i3 =
    ((Finset.univ.biUnion childrenC_626_i3) ∪ commonEnvelope childrenD_626_i3).erase (2, 5) := by
  exact required_eq_combination childrenC_626_i3 childrenD_626_i3 (2, 5) required_626_i3
    (by decide +kernel) child_required_sub_626_i3 common_sub_626_i3 required_origin_626_i3
theorem envelope_origin_626_i3 : ∀ x ∈ envelope_626_i3,
    x = (2, 5) ∨ ∃ j, x ∈ childrenD_626_i3 j := by decide +kernel
theorem envelope_exact_626_i3 : envelope_626_i3 =
    insert (2, 5) (Finset.univ.biUnion childrenD_626_i3) := by
  exact envelope_eq_combination childrenD_626_i3 (2, 5) envelope_626_i3
    pivot_mem_626_i3 child_envelope_sub_626_i3 envelope_origin_626_i3
def checked_626_i3 : CheckedCard where
  required := required_626_i3
  envelope := envelope_626_i3
  height := height_626_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_626_i3
def height_626_i2 : ℕ := 10
def childrenH_626_i2 : Fin 3 → ℕ := ![height_11, height_336, height_626_i3]
theorem height_exact_626_i2 : height_626_i2 = 1 + Finset.univ.sup childrenH_626_i2 := by decide +kernel
theorem required_origin_626_i2 : ∀ x ∈ required_626_i2,
    (∃ j, x ∈ childrenC_626_i2 j) ∨ ∀ j, x ∈ childrenD_626_i2 j := by decide +kernel
theorem required_exact_626_i2 : required_626_i2 =
    ((Finset.univ.biUnion childrenC_626_i2) ∪ commonEnvelope childrenD_626_i2).erase (4, 6) := by
  exact required_eq_combination childrenC_626_i2 childrenD_626_i2 (4, 6) required_626_i2
    (by decide +kernel) child_required_sub_626_i2 common_sub_626_i2 required_origin_626_i2
theorem envelope_origin_626_i2 : ∀ x ∈ envelope_626_i2,
    x = (4, 6) ∨ ∃ j, x ∈ childrenD_626_i2 j := by decide +kernel
theorem envelope_exact_626_i2 : envelope_626_i2 =
    insert (4, 6) (Finset.univ.biUnion childrenD_626_i2) := by
  exact envelope_eq_combination childrenD_626_i2 (4, 6) envelope_626_i2
    pivot_mem_626_i2 child_envelope_sub_626_i2 envelope_origin_626_i2
def checked_626_i2 : CheckedCard where
  required := required_626_i2
  envelope := envelope_626_i2
  height := height_626_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_626_i2
def height_626 : ℕ := 11
def childrenH_626 : Fin 5 → ℕ := ![height_323, height_430, height_592, height_626_i0, height_626_i2]
theorem height_exact_626 : height_626 = 1 + Finset.univ.sup childrenH_626 := by decide +kernel
theorem required_origin_626 : ∀ x ∈ required_626,
    (∃ j, x ∈ childrenC_626 j) ∨ ∀ j, x ∈ childrenD_626 j := by decide +kernel
theorem required_exact_626 : required_626 =
    ((Finset.univ.biUnion childrenC_626) ∪ commonEnvelope childrenD_626).erase (5, 6) := by
  exact required_eq_combination childrenC_626 childrenD_626 (5, 6) required_626
    (by decide +kernel) child_required_sub_626 common_sub_626 required_origin_626
theorem envelope_origin_626 : ∀ x ∈ envelope_626,
    x = (5, 6) ∨ ∃ j, x ∈ childrenD_626 j := by decide +kernel
theorem envelope_exact_626 : envelope_626 =
    insert (5, 6) (Finset.univ.biUnion childrenD_626) := by
  exact envelope_eq_combination childrenD_626 (5, 6) envelope_626
    pivot_mem_626 child_envelope_sub_626 envelope_origin_626
def checked_626 : CheckedCard where
  required := required_626
  envelope := envelope_626
  height := height_626
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_626
end SnakyPrototype.Certificate21

end OAI
