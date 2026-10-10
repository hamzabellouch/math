import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part06
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part06
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part07
import OAI.GameTheory.SnakyTwentyOne.Cards.Height10Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height10Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height10Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height11Part06
import OAI.GameTheory.SnakyTwentyOne.Cards.Height12Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height12Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height12Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height13Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height13Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height13Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height13Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height14Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height14Part04
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_698 : Finset Cell := ⟨(([(4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_698 : Finset Cell := ⟨(([(0, 5), (0, 6), (0, 7), (0, 8), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 1), (3, 2), (3, 3), (3, 4), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, 0), (5, 1), (5, 2), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (8, 11), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (10, 5), (10, 6), (10, 7), (10, 8), (10, 9), (11, 6), (11, 7), (11, 8), (11, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_698 : Fin 8 → Finset Cell := ![(placed21 0 (3, 2) required_12), (placed21 6 (6, 8) required_182), (placed21 0 (2, 2) required_188), (placed21 5 (7, 3) required_619), (placed21 0 (1, 0) required_620), (placed21 0 (1, 1) required_622), (placed21 1 (0, 1) required_687), (placed21 1 (1, 2) required_697)]
def childrenD_698 : Fin 8 → Finset Cell := ![(placed21 0 (3, 2) envelope_12), (placed21 6 (6, 8) envelope_182), (placed21 0 (2, 2) envelope_188), (placed21 5 (7, 3) envelope_619), (placed21 0 (1, 0) envelope_620), (placed21 0 (1, 1) envelope_622), (placed21 1 (0, 1) envelope_687), (placed21 1 (1, 2) envelope_697)]
theorem common_sub_698 : commonEnvelope childrenD_698 ⊆ insert (4, 6) required_698 := by decide +kernel
theorem child_required_sub_698 : ∀ j, childrenC_698 j ⊆ insert (4, 6) required_698 := by decide +kernel
theorem child_envelope_sub_698 : ∀ j, childrenD_698 j ⊆ envelope_698 := by decide +kernel
theorem pivot_mem_698 : (4, 6) ∈ envelope_698 := by decide +kernel
theorem children_work_698 : ∀ j, Template HasSnaky 14 (childrenC_698 j) (childrenD_698 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_12 0 (3, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_182 6 (6, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_188 0 (2, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_619 5 (7, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_620 0 (1, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_622 0 (1, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_687 1 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_697 1 (1, 2)).mono (by decide +kernel)
theorem row_works_698 : Template HasSnaky 15 required_698 envelope_698 := by
  refine compose HasSnaky 14 childrenC_698 childrenD_698 children_work_698 (4, 6)
    required_698 envelope_698 pivot_mem_698 child_required_sub_698 child_envelope_sub_698 ?_
  intro b hb
  exact common_sub_698 (mem_commonEnvelope childrenD_698 b hb)
def required_699_i3 : Finset Cell := ⟨(([(5, 5), (6, 5), (7, 5), (7, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_699_i3 : Finset Cell := ⟨(([(4, 5), (5, 5), (6, 4), (6, 5), (6, 6), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (8, 5), (8, 6), (8, 8), (8, 9), (8, 10), (9, 6), (10, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_699_i3 : Fin 2 → Finset Cell := ![(placed21 0 (6, 4) required_42), (placed21 1 (4, 5) required_52)]
def childrenD_699_i3 : Fin 2 → Finset Cell := ![(placed21 0 (6, 4) envelope_42), (placed21 1 (4, 5) envelope_52)]
theorem common_sub_699_i3 : commonEnvelope childrenD_699_i3 ⊆ insert (7, 6) required_699_i3 := by decide +kernel
theorem child_required_sub_699_i3 : ∀ j, childrenC_699_i3 j ⊆ insert (7, 6) required_699_i3 := by decide +kernel
theorem child_envelope_sub_699_i3 : ∀ j, childrenD_699_i3 j ⊆ envelope_699_i3 := by decide +kernel
theorem pivot_mem_699_i3 : (7, 6) ∈ envelope_699_i3 := by decide +kernel
theorem children_work_699_i3 : ∀ j, Template HasSnaky 4 (childrenC_699_i3 j) (childrenD_699_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_42 0 (6, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_52 1 (4, 5)).mono (by decide +kernel)
theorem row_works_699_i3 : Template HasSnaky 5 required_699_i3 envelope_699_i3 := by
  refine compose HasSnaky 4 childrenC_699_i3 childrenD_699_i3 children_work_699_i3 (7, 6)
    required_699_i3 envelope_699_i3 pivot_mem_699_i3 child_required_sub_699_i3 child_envelope_sub_699_i3 ?_
  intro b hb
  exact common_sub_699_i3 (mem_commonEnvelope childrenD_699_i3 b hb)
def required_699_i2 : Finset Cell := ⟨(([(4, 8), (5, 5), (6, 5), (6, 8), (7, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_699_i2 : Finset Cell := ⟨(([(1, 7), (1, 9), (2, 7), (2, 8), (2, 9), (3, 7), (3, 8), (3, 9), (4, 5), (4, 8), (4, 9), (5, 5), (5, 8), (5, 9), (6, 4), (6, 5), (6, 6), (6, 8), (6, 9), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (9, 6), (9, 7), (9, 8), (9, 9), (10, 6), (10, 7), (10, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_699_i2 : Fin 3 → Finset Cell := ![(placed21 7 (10, 9) required_95), (placed21 1 (4, 4) required_112), required_699_i3]
def childrenD_699_i2 : Fin 3 → Finset Cell := ![(placed21 7 (10, 9) envelope_95), (placed21 1 (4, 4) envelope_112), envelope_699_i3]
theorem common_sub_699_i2 : commonEnvelope childrenD_699_i2 ⊆ insert (7, 8) required_699_i2 := by decide +kernel
theorem child_required_sub_699_i2 : ∀ j, childrenC_699_i2 j ⊆ insert (7, 8) required_699_i2 := by decide +kernel
theorem child_envelope_sub_699_i2 : ∀ j, childrenD_699_i2 j ⊆ envelope_699_i2 := by decide +kernel
theorem pivot_mem_699_i2 : (7, 8) ∈ envelope_699_i2 := by decide +kernel
theorem children_work_699_i2 : ∀ j, Template HasSnaky 6 (childrenC_699_i2 j) (childrenD_699_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_95 7 (10, 9)).mono (by decide +kernel)
  · exact (placed21_template row_works_112 1 (4, 4)).mono (by decide +kernel)
  · exact row_works_699_i3.mono (by decide +kernel)
theorem row_works_699_i2 : Template HasSnaky 7 required_699_i2 envelope_699_i2 := by
  refine compose HasSnaky 6 childrenC_699_i2 childrenD_699_i2 children_work_699_i2 (7, 8)
    required_699_i2 envelope_699_i2 pivot_mem_699_i2 child_required_sub_699_i2 child_envelope_sub_699_i2 ?_
  intro b hb
  exact common_sub_699_i2 (mem_commonEnvelope childrenD_699_i2 b hb)
def required_699_i1 : Finset Cell := ⟨(([(4, 5), (4, 8), (5, 5), (6, 5), (7, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_699_i1 : Finset Cell := ⟨(([(1, 7), (1, 9), (2, 7), (2, 8), (2, 9), (3, 7), (3, 8), (3, 9), (4, 5), (4, 8), (4, 9), (4, 10), (5, 4), (5, 5), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (5, 12), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (6, 12), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (7, 12), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (8, 11), (8, 12), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (10, 4), (10, 5), (10, 6), (10, 7), (10, 9), (11, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_699_i1 : Fin 3 → Finset Cell := ![(placed21 0 (4, 4) required_371), (placed21 5 (9, 7) required_460), required_699_i2]
def childrenD_699_i1 : Fin 3 → Finset Cell := ![(placed21 0 (4, 4) envelope_371), (placed21 5 (9, 7) envelope_460), envelope_699_i2]
theorem common_sub_699_i1 : commonEnvelope childrenD_699_i1 ⊆ insert (6, 8) required_699_i1 := by decide +kernel
theorem child_required_sub_699_i1 : ∀ j, childrenC_699_i1 j ⊆ insert (6, 8) required_699_i1 := by decide +kernel
theorem child_envelope_sub_699_i1 : ∀ j, childrenD_699_i1 j ⊆ envelope_699_i1 := by decide +kernel
theorem pivot_mem_699_i1 : (6, 8) ∈ envelope_699_i1 := by decide +kernel
theorem children_work_699_i1 : ∀ j, Template HasSnaky 10 (childrenC_699_i1 j) (childrenD_699_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_371 0 (4, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_460 5 (9, 7)).mono (by decide +kernel)
  · exact row_works_699_i2.mono (by decide +kernel)
theorem row_works_699_i1 : Template HasSnaky 11 required_699_i1 envelope_699_i1 := by
  refine compose HasSnaky 10 childrenC_699_i1 childrenD_699_i1 children_work_699_i1 (6, 8)
    required_699_i1 envelope_699_i1 pivot_mem_699_i1 child_required_sub_699_i1 child_envelope_sub_699_i1 ?_
  intro b hb
  exact common_sub_699_i1 (mem_commonEnvelope childrenD_699_i1 b hb)
def required_699_i0 : Finset Cell := ⟨(([(4, 5), (5, 5), (6, 5), (7, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_699_i0 : Finset Cell := ⟨(([(0, 7), (0, 9), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (4, 13), (5, 4), (5, 5), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (5, 12), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (6, 12), (6, 13), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (7, 12), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (8, 11), (8, 12), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (9, 10), (9, 11), (10, 4), (10, 5), (10, 6), (10, 7), (10, 9), (11, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_699_i0 : Fin 4 → Finset Cell := ![(placed21 2 (7, 4) required_147), (placed21 3 (3, 8) required_249), (placed21 5 (9, 5) required_692), required_699_i1]
def childrenD_699_i0 : Fin 4 → Finset Cell := ![(placed21 2 (7, 4) envelope_147), (placed21 3 (3, 8) envelope_249), (placed21 5 (9, 5) envelope_692), envelope_699_i1]
theorem common_sub_699_i0 : commonEnvelope childrenD_699_i0 ⊆ insert (4, 8) required_699_i0 := by decide +kernel
theorem child_required_sub_699_i0 : ∀ j, childrenC_699_i0 j ⊆ insert (4, 8) required_699_i0 := by decide +kernel
theorem child_envelope_sub_699_i0 : ∀ j, childrenD_699_i0 j ⊆ envelope_699_i0 := by decide +kernel
theorem pivot_mem_699_i0 : (4, 8) ∈ envelope_699_i0 := by decide +kernel
theorem children_work_699_i0 : ∀ j, Template HasSnaky 13 (childrenC_699_i0 j) (childrenD_699_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_147 2 (7, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_249 3 (3, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_692 5 (9, 5)).mono (by decide +kernel)
  · exact row_works_699_i1.mono (by decide +kernel)
theorem row_works_699_i0 : Template HasSnaky 14 required_699_i0 envelope_699_i0 := by
  refine compose HasSnaky 13 childrenC_699_i0 childrenD_699_i0 children_work_699_i0 (4, 8)
    required_699_i0 envelope_699_i0 pivot_mem_699_i0 child_required_sub_699_i0 child_envelope_sub_699_i0 ?_
  intro b hb
  exact common_sub_699_i0 (mem_commonEnvelope childrenD_699_i0 b hb)
def required_699_i6 : Finset Cell := ⟨(([(4, 5), (5, 5), (6, 3), (6, 4), (6, 5), (7, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_699_i6 : Finset Cell := ⟨(([(4, 5), (5, 4), (5, 5), (6, 3), (6, 4), (6, 5), (6, 6), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (8, 2), (8, 3), (8, 4), (9, 3), (10, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_699_i6 : Fin 2 → Finset Cell := ![(placed21 4 (4, 5) required_5), (placed21 4 (5, 7) required_259)]
def childrenD_699_i6 : Fin 2 → Finset Cell := ![(placed21 4 (4, 5) envelope_5), (placed21 4 (5, 7) envelope_259)]
theorem common_sub_699_i6 : commonEnvelope childrenD_699_i6 ⊆ insert (7, 4) required_699_i6 := by decide +kernel
theorem child_required_sub_699_i6 : ∀ j, childrenC_699_i6 j ⊆ insert (7, 4) required_699_i6 := by decide +kernel
theorem child_envelope_sub_699_i6 : ∀ j, childrenD_699_i6 j ⊆ envelope_699_i6 := by decide +kernel
theorem pivot_mem_699_i6 : (7, 4) ∈ envelope_699_i6 := by decide +kernel
theorem children_work_699_i6 : ∀ j, Template HasSnaky 4 (childrenC_699_i6 j) (childrenD_699_i6 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 4 (4, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_259 4 (5, 7)).mono (by decide +kernel)
theorem row_works_699_i6 : Template HasSnaky 5 required_699_i6 envelope_699_i6 := by
  refine compose HasSnaky 4 childrenC_699_i6 childrenD_699_i6 children_work_699_i6 (7, 4)
    required_699_i6 envelope_699_i6 pivot_mem_699_i6 child_required_sub_699_i6 child_envelope_sub_699_i6 ?_
  intro b hb
  exact common_sub_699_i6 (mem_commonEnvelope childrenD_699_i6 b hb)
def required_699_i5 : Finset Cell := ⟨(([(4, 5), (5, 5), (6, 4), (6, 5), (7, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_699_i5 : Finset Cell := ⟨(([(4, 2), (4, 5), (5, 0), (5, 1), (5, 2), (5, 4), (5, 5), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (8, 2), (8, 3), (8, 4), (9, 3), (10, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_699_i5 : Fin 4 → Finset Cell := ![(placed21 6 (7, 6) required_10), (placed21 6 (7, 6) required_48), (placed21 3 (4, 6) required_134), required_699_i6]
def childrenD_699_i5 : Fin 4 → Finset Cell := ![(placed21 6 (7, 6) envelope_10), (placed21 6 (7, 6) envelope_48), (placed21 3 (4, 6) envelope_134), envelope_699_i6]
theorem common_sub_699_i5 : commonEnvelope childrenD_699_i5 ⊆ insert (6, 3) required_699_i5 := by decide +kernel
theorem child_required_sub_699_i5 : ∀ j, childrenC_699_i5 j ⊆ insert (6, 3) required_699_i5 := by decide +kernel
theorem child_envelope_sub_699_i5 : ∀ j, childrenD_699_i5 j ⊆ envelope_699_i5 := by decide +kernel
theorem pivot_mem_699_i5 : (6, 3) ∈ envelope_699_i5 := by decide +kernel
theorem children_work_699_i5 : ∀ j, Template HasSnaky 6 (childrenC_699_i5 j) (childrenD_699_i5 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_10 6 (7, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_48 6 (7, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_134 3 (4, 6)).mono (by decide +kernel)
  · exact row_works_699_i6.mono (by decide +kernel)
theorem row_works_699_i5 : Template HasSnaky 7 required_699_i5 envelope_699_i5 := by
  refine compose HasSnaky 6 childrenC_699_i5 childrenD_699_i5 children_work_699_i5 (6, 3)
    required_699_i5 envelope_699_i5 pivot_mem_699_i5 child_required_sub_699_i5 child_envelope_sub_699_i5 ?_
  intro b hb
  exact common_sub_699_i5 (mem_commonEnvelope childrenD_699_i5 b hb)
def required_699_i4 : Finset Cell := ⟨(([(4, 5), (5, 5), (6, 5), (7, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_699_i4 : Finset Cell := ⟨(([(4, 2), (4, 5), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 7), (5, 8), (5, 9), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, 2), (8, 3), (8, 4), (8, 5), (9, 2), (9, 3), (9, 4), (9, 5), (10, 2), (10, 3), (10, 4), (10, 5), (11, 2), (11, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_699_i4 : Fin 5 → Finset Cell := ![(placed21 3 (4, 5) required_389), (placed21 0 (5, 0) required_545), (placed21 4 (5, 9) required_546), (placed21 0 (5, 0) required_549), required_699_i5]
def childrenD_699_i4 : Fin 5 → Finset Cell := ![(placed21 3 (4, 5) envelope_389), (placed21 0 (5, 0) envelope_545), (placed21 4 (5, 9) envelope_546), (placed21 0 (5, 0) envelope_549), envelope_699_i5]
theorem common_sub_699_i4 : commonEnvelope childrenD_699_i4 ⊆ insert (6, 4) required_699_i4 := by decide +kernel
theorem child_required_sub_699_i4 : ∀ j, childrenC_699_i4 j ⊆ insert (6, 4) required_699_i4 := by decide +kernel
theorem child_envelope_sub_699_i4 : ∀ j, childrenD_699_i4 j ⊆ envelope_699_i4 := by decide +kernel
theorem pivot_mem_699_i4 : (6, 4) ∈ envelope_699_i4 := by decide +kernel
theorem children_work_699_i4 : ∀ j, Template HasSnaky 10 (childrenC_699_i4 j) (childrenD_699_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_389 3 (4, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_545 0 (5, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_546 4 (5, 9)).mono (by decide +kernel)
  · exact (placed21_template row_works_549 0 (5, 0)).mono (by decide +kernel)
  · exact row_works_699_i5.mono (by decide +kernel)
theorem row_works_699_i4 : Template HasSnaky 11 required_699_i4 envelope_699_i4 := by
  refine compose HasSnaky 10 childrenC_699_i4 childrenD_699_i4 children_work_699_i4 (6, 4)
    required_699_i4 envelope_699_i4 pivot_mem_699_i4 child_required_sub_699_i4 child_envelope_sub_699_i4 ?_
  intro b hb
  exact common_sub_699_i4 (mem_commonEnvelope childrenD_699_i4 b hb)
def required_699 : Finset Cell := ⟨(([(4, 5), (5, 5), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_699 : Finset Cell := ⟨(([(0, 7), (0, 9), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (4, 2), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (4, 13), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (5, 12), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (6, 12), (6, 13), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (7, 12), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (8, 11), (8, 12), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (9, 10), (9, 11), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 9), (11, 2), (11, 4), (11, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_699 : Fin 5 → Finset Cell := ![(placed21 0 (4, 4) required_197), (placed21 0 (4, 1) required_321), (placed21 2 (11, 0) required_693), required_699_i0, required_699_i4]
def childrenD_699 : Fin 5 → Finset Cell := ![(placed21 0 (4, 4) envelope_197), (placed21 0 (4, 1) envelope_321), (placed21 2 (11, 0) envelope_693), envelope_699_i0, envelope_699_i4]
theorem common_sub_699 : commonEnvelope childrenD_699 ⊆ insert (7, 5) required_699 := by decide +kernel
theorem child_required_sub_699 : ∀ j, childrenC_699 j ⊆ insert (7, 5) required_699 := by decide +kernel
theorem child_envelope_sub_699 : ∀ j, childrenD_699 j ⊆ envelope_699 := by decide +kernel
theorem pivot_mem_699 : (7, 5) ∈ envelope_699 := by decide +kernel
theorem children_work_699 : ∀ j, Template HasSnaky 14 (childrenC_699 j) (childrenD_699 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_197 0 (4, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_321 0 (4, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_693 2 (11, 0)).mono (by decide +kernel)
  · exact row_works_699_i0.mono (by decide +kernel)
  · exact row_works_699_i4.mono (by decide +kernel)
theorem row_works_699 : Template HasSnaky 15 required_699 envelope_699 := by
  refine compose HasSnaky 14 childrenC_699 childrenD_699 children_work_699 (7, 5)
    required_699 envelope_699 pivot_mem_699 child_required_sub_699 child_envelope_sub_699 ?_
  intro b hb
  exact common_sub_699 (mem_commonEnvelope childrenD_699 b hb)
def required_712_i1 : Finset Cell := ⟨(([(5, 4), (5, 5), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_712_i1 : Finset Cell := ⟨(([(0, 5), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5), (3, 3), (3, 4), (3, 5), (4, 4), (4, 5), (5, 4), (5, 5), (5, 6), (5, 7), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (9, 3), (9, 4), (9, 5), (10, 3), (10, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_712_i1 : Fin 3 → Finset Cell := ![(placed21 4 (5, 7) required_44), (placed21 5 (10, 3) required_545), (placed21 7 (10, 7) required_655)]
def childrenD_712_i1 : Fin 3 → Finset Cell := ![(placed21 4 (5, 7) envelope_44), (placed21 5 (10, 3) envelope_545), (placed21 7 (10, 7) envelope_655)]
theorem common_sub_712_i1 : commonEnvelope childrenD_712_i1 ⊆ insert (6, 4) required_712_i1 := by decide +kernel
theorem child_required_sub_712_i1 : ∀ j, childrenC_712_i1 j ⊆ insert (6, 4) required_712_i1 := by decide +kernel
theorem child_envelope_sub_712_i1 : ∀ j, childrenD_712_i1 j ⊆ envelope_712_i1 := by decide +kernel
theorem pivot_mem_712_i1 : (6, 4) ∈ envelope_712_i1 := by decide +kernel
theorem children_work_712_i1 : ∀ j, Template HasSnaky 10 (childrenC_712_i1 j) (childrenD_712_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_44 4 (5, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_545 5 (10, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_655 7 (10, 7)).mono (by decide +kernel)
theorem row_works_712_i1 : Template HasSnaky 11 required_712_i1 envelope_712_i1 := by
  refine compose HasSnaky 10 childrenC_712_i1 childrenD_712_i1 children_work_712_i1 (6, 4)
    required_712_i1 envelope_712_i1 pivot_mem_712_i1 child_required_sub_712_i1 child_envelope_sub_712_i1 ?_
  intro b hb
  exact common_sub_712_i1 (mem_commonEnvelope childrenD_712_i1 b hb)
def required_712_i0 : Finset Cell := ⟨(([(5, 5), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_712_i0 : Finset Cell := ⟨(([(0, 5), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (9, 3), (9, 4), (9, 5), (9, 7), (10, 3), (10, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_712_i0 : Fin 6 → Finset Cell := ![(placed21 3 (2, 7) required_116), (placed21 3 (2, 8) required_297), (placed21 5 (8, 3) required_435), (placed21 1 (2, 3) required_435), (placed21 7 (10, 8) required_649), required_712_i1]
def childrenD_712_i0 : Fin 6 → Finset Cell := ![(placed21 3 (2, 7) envelope_116), (placed21 3 (2, 8) envelope_297), (placed21 5 (8, 3) envelope_435), (placed21 1 (2, 3) envelope_435), (placed21 7 (10, 8) envelope_649), envelope_712_i1]
theorem common_sub_712_i0 : commonEnvelope childrenD_712_i0 ⊆ insert (5, 4) required_712_i0 := by decide +kernel
theorem child_required_sub_712_i0 : ∀ j, childrenC_712_i0 j ⊆ insert (5, 4) required_712_i0 := by decide +kernel
theorem child_envelope_sub_712_i0 : ∀ j, childrenD_712_i0 j ⊆ envelope_712_i0 := by decide +kernel
theorem pivot_mem_712_i0 : (5, 4) ∈ envelope_712_i0 := by decide +kernel
theorem children_work_712_i0 : ∀ j, Template HasSnaky 12 (childrenC_712_i0 j) (childrenD_712_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_116 3 (2, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_297 3 (2, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_435 5 (8, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_435 1 (2, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_649 7 (10, 8)).mono (by decide +kernel)
  · exact row_works_712_i1.mono (by decide +kernel)
theorem row_works_712_i0 : Template HasSnaky 13 required_712_i0 envelope_712_i0 := by
  refine compose HasSnaky 12 childrenC_712_i0 childrenD_712_i0 children_work_712_i0 (5, 4)
    required_712_i0 envelope_712_i0 pivot_mem_712_i0 child_required_sub_712_i0 child_envelope_sub_712_i0 ?_
  intro b hb
  exact common_sub_712_i0 (mem_commonEnvelope childrenD_712_i0 b hb)
def required_712 : Finset Cell := ⟨(([(5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_712 : Finset Cell := ⟨(([(0, 5), (0, 6), (0, 8), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (8, 11), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (11, 5), (11, 6), (11, 7), (12, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_712 : Fin 13 → Finset Cell := ![(placed21 4 (2, 9) required_174), (placed21 1 (2, 3) required_508), (placed21 5 (8, 3) required_508), (placed21 4 (2, 9) required_566), (placed21 1 (2, 3) required_605), (placed21 5 (8, 3) required_605), (placed21 4 (1, 10) required_647), (placed21 1 (0, 2) required_650), (placed21 5 (10, 2) required_650), required_712_i0, (placed21 2 (9, 1) required_661), (placed21 0 (2, 1) required_710), (placed21 0 (1, 0) required_711)]
def childrenD_712 : Fin 13 → Finset Cell := ![(placed21 4 (2, 9) envelope_174), (placed21 1 (2, 3) envelope_508), (placed21 5 (8, 3) envelope_508), (placed21 4 (2, 9) envelope_566), (placed21 1 (2, 3) envelope_605), (placed21 5 (8, 3) envelope_605), (placed21 4 (1, 10) envelope_647), (placed21 1 (0, 2) envelope_650), (placed21 5 (10, 2) envelope_650), envelope_712_i0, (placed21 2 (9, 1) envelope_661), (placed21 0 (2, 1) envelope_710), (placed21 0 (1, 0) envelope_711)]
theorem common_sub_712 : commonEnvelope childrenD_712 ⊆ insert (5, 6) required_712 := by decide +kernel
theorem child_required_sub_712 : ∀ j, childrenC_712 j ⊆ insert (5, 6) required_712 := by decide +kernel
theorem child_envelope_sub_712 : ∀ j, childrenD_712 j ⊆ envelope_712 := by decide +kernel
theorem pivot_mem_712 : (5, 6) ∈ envelope_712 := by decide +kernel
theorem children_work_712 : ∀ j, Template HasSnaky 14 (childrenC_712 j) (childrenD_712 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_174 4 (2, 9)).mono (by decide +kernel)
  · exact (placed21_template row_works_508 1 (2, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_508 5 (8, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_566 4 (2, 9)).mono (by decide +kernel)
  · exact (placed21_template row_works_605 1 (2, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_605 5 (8, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_647 4 (1, 10)).mono (by decide +kernel)
  · exact (placed21_template row_works_650 1 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_650 5 (10, 2)).mono (by decide +kernel)
  · exact row_works_712_i0.mono (by decide +kernel)
  · exact (placed21_template row_works_661 2 (9, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_710 0 (2, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_711 0 (1, 0)).mono (by decide +kernel)
theorem row_works_712 : Template HasSnaky 15 required_712 envelope_712 := by
  refine compose HasSnaky 14 childrenC_712 childrenD_712 children_work_712 (5, 6)
    required_712 envelope_712 pivot_mem_712 child_required_sub_712 child_envelope_sub_712 ?_
  intro b hb
  exact common_sub_712 (mem_commonEnvelope childrenD_712 b hb)
def required_713 : Finset Cell := ⟨(([(5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_713 : Finset Cell := ⟨(([(0, 4), (0, 6), (0, 8), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (8, 11), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (11, 5), (11, 6), (11, 7), (12, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_713 : Fin 11 → Finset Cell := ![(placed21 1 (2, 3) required_508), (placed21 5 (8, 3) required_508), (placed21 1 (2, 3) required_605), (placed21 5 (8, 3) required_605), (placed21 4 (1, 10) required_645), (placed21 4 (1, 10) required_647), (placed21 1 (0, 2) required_650), (placed21 5 (10, 2) required_650), (placed21 4 (2, 9) required_654), (placed21 6 (8, 9) required_654), (placed21 0 (1, 0) required_711)]
def childrenD_713 : Fin 11 → Finset Cell := ![(placed21 1 (2, 3) envelope_508), (placed21 5 (8, 3) envelope_508), (placed21 1 (2, 3) envelope_605), (placed21 5 (8, 3) envelope_605), (placed21 4 (1, 10) envelope_645), (placed21 4 (1, 10) envelope_647), (placed21 1 (0, 2) envelope_650), (placed21 5 (10, 2) envelope_650), (placed21 4 (2, 9) envelope_654), (placed21 6 (8, 9) envelope_654), (placed21 0 (1, 0) envelope_711)]
theorem common_sub_713 : commonEnvelope childrenD_713 ⊆ insert (5, 6) required_713 := by decide +kernel
theorem child_required_sub_713 : ∀ j, childrenC_713 j ⊆ insert (5, 6) required_713 := by decide +kernel
theorem child_envelope_sub_713 : ∀ j, childrenD_713 j ⊆ envelope_713 := by decide +kernel
theorem pivot_mem_713 : (5, 6) ∈ envelope_713 := by decide +kernel
theorem children_work_713 : ∀ j, Template HasSnaky 14 (childrenC_713 j) (childrenD_713 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_508 1 (2, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_508 5 (8, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_605 1 (2, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_605 5 (8, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_645 4 (1, 10)).mono (by decide +kernel)
  · exact (placed21_template row_works_647 4 (1, 10)).mono (by decide +kernel)
  · exact (placed21_template row_works_650 1 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_650 5 (10, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_654 4 (2, 9)).mono (by decide +kernel)
  · exact (placed21_template row_works_654 6 (8, 9)).mono (by decide +kernel)
  · exact (placed21_template row_works_711 0 (1, 0)).mono (by decide +kernel)
theorem row_works_713 : Template HasSnaky 15 required_713 envelope_713 := by
  refine compose HasSnaky 14 childrenC_713 childrenD_713 children_work_713 (5, 6)
    required_713 envelope_713 pivot_mem_713 child_required_sub_713 child_envelope_sub_713 ?_
  intro b hb
  exact common_sub_713 (mem_commonEnvelope childrenD_713 b hb)
def required_718_i0 : Finset Cell := ⟨(([(5, 5), (5, 6), (7, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_718_i0 : Finset Cell := ⟨(([(2, 4), (2, 6), (3, 4), (3, 5), (3, 6), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 5), (5, 6), (5, 7), (5, 8), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (8, 5), (8, 6), (9, 4), (9, 5), (9, 6), (10, 4), (10, 5), (10, 6), (11, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_718_i0 : Fin 4 → Finset Cell := ![(placed21 5 (8, 5) required_44), (placed21 5 (8, 5) required_52), (placed21 6 (8, 7) required_155), (placed21 3 (2, 8) required_341)]
def childrenD_718_i0 : Fin 4 → Finset Cell := ![(placed21 5 (8, 5) envelope_44), (placed21 5 (8, 5) envelope_52), (placed21 6 (8, 7) envelope_155), (placed21 3 (2, 8) envelope_341)]
theorem common_sub_718_i0 : commonEnvelope childrenD_718_i0 ⊆ insert (6, 5) required_718_i0 := by decide +kernel
theorem child_required_sub_718_i0 : ∀ j, childrenC_718_i0 j ⊆ insert (6, 5) required_718_i0 := by decide +kernel
theorem child_envelope_sub_718_i0 : ∀ j, childrenD_718_i0 j ⊆ envelope_718_i0 := by decide +kernel
theorem pivot_mem_718_i0 : (6, 5) ∈ envelope_718_i0 := by decide +kernel
theorem children_work_718_i0 : ∀ j, Template HasSnaky 7 (childrenC_718_i0 j) (childrenD_718_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_44 5 (8, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_52 5 (8, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_155 6 (8, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_341 3 (2, 8)).mono (by decide +kernel)
theorem row_works_718_i0 : Template HasSnaky 8 required_718_i0 envelope_718_i0 := by
  refine compose HasSnaky 7 childrenC_718_i0 childrenD_718_i0 children_work_718_i0 (6, 5)
    required_718_i0 envelope_718_i0 pivot_mem_718_i0 child_required_sub_718_i0 child_envelope_sub_718_i0 ?_
  intro b hb
  exact common_sub_718_i0 (mem_commonEnvelope childrenD_718_i0 b hb)
def required_718_i1 : Finset Cell := ⟨(([(5, 5), (5, 6), (7, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_718_i1 : Finset Cell := ⟨(([(2, 4), (2, 5), (2, 6), (3, 4), (3, 5), (3, 6), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 8), (5, 5), (5, 6), (5, 7), (5, 8), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (8, 1), (8, 2), (8, 3), (8, 4), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (8, 11), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_718_i1 : Fin 5 → Finset Cell := ![(placed21 0 (2, 2) required_452), (placed21 2 (10, 0) required_520), (placed21 4 (5, 9) required_587), (placed21 7 (8, 6) required_612), (placed21 0 (2, 1) required_633)]
def childrenD_718_i1 : Fin 5 → Finset Cell := ![(placed21 0 (2, 2) envelope_452), (placed21 2 (10, 0) envelope_520), (placed21 4 (5, 9) envelope_587), (placed21 7 (8, 6) envelope_612), (placed21 0 (2, 1) envelope_633)]
theorem common_sub_718_i1 : commonEnvelope childrenD_718_i1 ⊆ insert (7, 6) required_718_i1 := by decide +kernel
theorem child_required_sub_718_i1 : ∀ j, childrenC_718_i1 j ⊆ insert (7, 6) required_718_i1 := by decide +kernel
theorem child_envelope_sub_718_i1 : ∀ j, childrenD_718_i1 j ⊆ envelope_718_i1 := by decide +kernel
theorem pivot_mem_718_i1 : (7, 6) ∈ envelope_718_i1 := by decide +kernel
theorem children_work_718_i1 : ∀ j, Template HasSnaky 12 (childrenC_718_i1 j) (childrenD_718_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_452 0 (2, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_520 2 (10, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_587 4 (5, 9)).mono (by decide +kernel)
  · exact (placed21_template row_works_612 7 (8, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_633 0 (2, 1)).mono (by decide +kernel)
theorem row_works_718_i1 : Template HasSnaky 13 required_718_i1 envelope_718_i1 := by
  refine compose HasSnaky 12 childrenC_718_i1 childrenD_718_i1 children_work_718_i1 (7, 6)
    required_718_i1 envelope_718_i1 pivot_mem_718_i1 child_required_sub_718_i1 child_envelope_sub_718_i1 ?_
  intro b hb
  exact common_sub_718_i1 (mem_commonEnvelope childrenD_718_i1 b hb)
def required_718_i3 : Finset Cell := ⟨(([(5, 5), (5, 6), (7, 5), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_718_i3 : Finset Cell := ⟨(([(1, 7), (2, 5), (2, 6), (2, 7), (3, 5), (3, 6), (3, 7), (4, 5), (4, 6), (5, 5), (5, 6), (5, 7), (6, 6), (6, 7), (7, 5), (7, 6), (7, 7), (8, 5), (8, 6), (9, 5), (9, 6), (9, 7), (10, 5), (10, 6), (10, 7), (11, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_718_i3 : Fin 4 → Finset Cell := ![(placed21 3 (4, 6) required_52), (placed21 7 (8, 6) required_52), (placed21 1 (4, 5) required_232), (placed21 5 (8, 5) required_232)]
def childrenD_718_i3 : Fin 4 → Finset Cell := ![(placed21 3 (4, 6) envelope_52), (placed21 7 (8, 6) envelope_52), (placed21 1 (4, 5) envelope_232), (placed21 5 (8, 5) envelope_232)]
theorem common_sub_718_i3 : commonEnvelope childrenD_718_i3 ⊆ insert (6, 6) required_718_i3 := by decide +kernel
theorem child_required_sub_718_i3 : ∀ j, childrenC_718_i3 j ⊆ insert (6, 6) required_718_i3 := by decide +kernel
theorem child_envelope_sub_718_i3 : ∀ j, childrenD_718_i3 j ⊆ envelope_718_i3 := by decide +kernel
theorem pivot_mem_718_i3 : (6, 6) ∈ envelope_718_i3 := by decide +kernel
theorem children_work_718_i3 : ∀ j, Template HasSnaky 5 (childrenC_718_i3 j) (childrenD_718_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_52 3 (4, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_52 7 (8, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_232 1 (4, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_232 5 (8, 5)).mono (by decide +kernel)
theorem row_works_718_i3 : Template HasSnaky 6 required_718_i3 envelope_718_i3 := by
  refine compose HasSnaky 5 childrenC_718_i3 childrenD_718_i3 children_work_718_i3 (6, 6)
    required_718_i3 envelope_718_i3 pivot_mem_718_i3 child_required_sub_718_i3 child_envelope_sub_718_i3 ?_
  intro b hb
  exact common_sub_718_i3 (mem_commonEnvelope childrenD_718_i3 b hb)
def required_718_i5 : Finset Cell := ⟨(([(5, 6), (7, 4), (7, 5), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_718_i5 : Finset Cell := ⟨(([(4, 6), (5, 6), (6, 1), (6, 2), (6, 3), (6, 6), (6, 7), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (8, 1), (8, 2), (8, 3), (8, 5), (8, 6), (8, 7), (9, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_718_i5 : Fin 2 → Finset Cell := ![(placed21 3 (6, 6) required_8), (placed21 5 (9, 3) required_229)]
def childrenD_718_i5 : Fin 2 → Finset Cell := ![(placed21 3 (6, 6) envelope_8), (placed21 5 (9, 3) envelope_229)]
theorem common_sub_718_i5 : commonEnvelope childrenD_718_i5 ⊆ insert (7, 3) required_718_i5 := by decide +kernel
theorem child_required_sub_718_i5 : ∀ j, childrenC_718_i5 j ⊆ insert (7, 3) required_718_i5 := by decide +kernel
theorem child_envelope_sub_718_i5 : ∀ j, childrenD_718_i5 j ⊆ envelope_718_i5 := by decide +kernel
theorem pivot_mem_718_i5 : (7, 3) ∈ envelope_718_i5 := by decide +kernel
theorem children_work_718_i5 : ∀ j, Template HasSnaky 4 (childrenC_718_i5 j) (childrenD_718_i5 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_8 3 (6, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_229 5 (9, 3)).mono (by decide +kernel)
theorem row_works_718_i5 : Template HasSnaky 5 required_718_i5 envelope_718_i5 := by
  refine compose HasSnaky 4 childrenC_718_i5 childrenD_718_i5 children_work_718_i5 (7, 3)
    required_718_i5 envelope_718_i5 pivot_mem_718_i5 child_required_sub_718_i5 child_envelope_sub_718_i5 ?_
  intro b hb
  exact common_sub_718_i5 (mem_commonEnvelope childrenD_718_i5 b hb)
def required_718_i4 : Finset Cell := ⟨(([(5, 6), (7, 5), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_718_i4 : Finset Cell := ⟨(([(4, 6), (5, 6), (5, 7), (6, 1), (6, 2), (6, 3), (6, 4), (6, 6), (6, 7), (6, 8), (6, 9), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (9, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_718_i4 : Fin 5 → Finset Cell := ![(placed21 4 (6, 8) required_12), (placed21 6 (8, 8) required_12), (placed21 0 (6, 2) required_12), (placed21 2 (8, 3) required_377), required_718_i5]
def childrenD_718_i4 : Fin 5 → Finset Cell := ![(placed21 4 (6, 8) envelope_12), (placed21 6 (8, 8) envelope_12), (placed21 0 (6, 2) envelope_12), (placed21 2 (8, 3) envelope_377), envelope_718_i5]
theorem common_sub_718_i4 : commonEnvelope childrenD_718_i4 ⊆ insert (7, 4) required_718_i4 := by decide +kernel
theorem child_required_sub_718_i4 : ∀ j, childrenC_718_i4 j ⊆ insert (7, 4) required_718_i4 := by decide +kernel
theorem child_envelope_sub_718_i4 : ∀ j, childrenD_718_i4 j ⊆ envelope_718_i4 := by decide +kernel
theorem pivot_mem_718_i4 : (7, 4) ∈ envelope_718_i4 := by decide +kernel
theorem children_work_718_i4 : ∀ j, Template HasSnaky 5 (childrenC_718_i4 j) (childrenD_718_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_12 4 (6, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_12 6 (8, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_12 0 (6, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_377 2 (8, 3)).mono (by decide +kernel)
  · exact row_works_718_i5.mono (by decide +kernel)
theorem row_works_718_i4 : Template HasSnaky 6 required_718_i4 envelope_718_i4 := by
  refine compose HasSnaky 5 childrenC_718_i4 childrenD_718_i4 children_work_718_i4 (7, 4)
    required_718_i4 envelope_718_i4 pivot_mem_718_i4 child_required_sub_718_i4 child_envelope_sub_718_i4 ?_
  intro b hb
  exact common_sub_718_i4 (mem_commonEnvelope childrenD_718_i4 b hb)
def required_718_i6 : Finset Cell := ⟨(([(5, 5), (5, 6), (7, 5), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_718_i6 : Finset Cell := ⟨(([(0, 5), (1, 5), (1, 6), (1, 7), (2, 5), (2, 6), (2, 7), (3, 2), (3, 4), (3, 5), (3, 6), (3, 7), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 2), (5, 3), (5, 5), (5, 6), (6, 1), (6, 2), (6, 3), (6, 4), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 7), (8, 8), (8, 9), (8, 10), (9, 2), (9, 3), (9, 4), (9, 7), (10, 2), (10, 3), (10, 4), (10, 7), (11, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_718_i6 : Fin 3 → Finset Cell := ![(placed21 5 (8, 5) required_315), (placed21 0 (4, 2) required_317), (placed21 4 (3, 9) required_640)]
def childrenD_718_i6 : Fin 3 → Finset Cell := ![(placed21 5 (8, 5) envelope_315), (placed21 0 (4, 2) envelope_317), (placed21 4 (3, 9) envelope_640)]
theorem common_sub_718_i6 : commonEnvelope childrenD_718_i6 ⊆ insert (6, 6) required_718_i6 := by decide +kernel
theorem child_required_sub_718_i6 : ∀ j, childrenC_718_i6 j ⊆ insert (6, 6) required_718_i6 := by decide +kernel
theorem child_envelope_sub_718_i6 : ∀ j, childrenD_718_i6 j ⊆ envelope_718_i6 := by decide +kernel
theorem pivot_mem_718_i6 : (6, 6) ∈ envelope_718_i6 := by decide +kernel
theorem children_work_718_i6 : ∀ j, Template HasSnaky 9 (childrenC_718_i6 j) (childrenD_718_i6 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_315 5 (8, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_317 0 (4, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_640 4 (3, 9)).mono (by decide +kernel)
theorem row_works_718_i6 : Template HasSnaky 10 required_718_i6 envelope_718_i6 := by
  refine compose HasSnaky 9 childrenC_718_i6 childrenD_718_i6 children_work_718_i6 (6, 6)
    required_718_i6 envelope_718_i6 pivot_mem_718_i6 child_required_sub_718_i6 child_envelope_sub_718_i6 ?_
  intro b hb
  exact common_sub_718_i6 (mem_commonEnvelope childrenD_718_i6 b hb)
def required_718_i2 : Finset Cell := ⟨(([(5, 5), (5, 6), (7, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_718_i2 : Finset Cell := ⟨(([(0, 5), (1, 5), (1, 6), (1, 7), (2, 5), (2, 6), (2, 7), (3, 2), (3, 4), (3, 5), (3, 6), (3, 7), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 2), (5, 3), (5, 5), (5, 6), (5, 7), (6, 1), (6, 2), (6, 3), (6, 4), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (11, 2), (11, 4), (11, 6), (11, 7), (11, 8), (12, 6), (12, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_718_i2 : Fin 6 → Finset Cell := ![(placed21 5 (10, 5) required_329), (placed21 0 (2, 2) required_452), (placed21 4 (6, 9) required_462), required_718_i3, required_718_i4, required_718_i6]
def childrenD_718_i2 : Fin 6 → Finset Cell := ![(placed21 5 (10, 5) envelope_329), (placed21 0 (2, 2) envelope_452), (placed21 4 (6, 9) envelope_462), envelope_718_i3, envelope_718_i4, envelope_718_i6]
theorem common_sub_718_i2 : commonEnvelope childrenD_718_i2 ⊆ insert (7, 6) required_718_i2 := by decide +kernel
theorem child_required_sub_718_i2 : ∀ j, childrenC_718_i2 j ⊆ insert (7, 6) required_718_i2 := by decide +kernel
theorem child_envelope_sub_718_i2 : ∀ j, childrenD_718_i2 j ⊆ envelope_718_i2 := by decide +kernel
theorem pivot_mem_718_i2 : (7, 6) ∈ envelope_718_i2 := by decide +kernel
theorem children_work_718_i2 : ∀ j, Template HasSnaky 13 (childrenC_718_i2 j) (childrenD_718_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_329 5 (10, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_452 0 (2, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_462 4 (6, 9)).mono (by decide +kernel)
  · exact row_works_718_i3.mono (by decide +kernel)
  · exact row_works_718_i4.mono (by decide +kernel)
  · exact row_works_718_i6.mono (by decide +kernel)
theorem row_works_718_i2 : Template HasSnaky 14 required_718_i2 envelope_718_i2 := by
  refine compose HasSnaky 13 childrenC_718_i2 childrenD_718_i2 children_work_718_i2 (7, 6)
    required_718_i2 envelope_718_i2 pivot_mem_718_i2 child_required_sub_718_i2 child_envelope_sub_718_i2 ?_
  intro b hb
  exact common_sub_718_i2 (mem_commonEnvelope childrenD_718_i2 b hb)
def required_718 : Finset Cell := ⟨(([(5, 5), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_718 : Finset Cell := ⟨(([(0, 5), (1, 5), (1, 6), (1, 7), (2, 4), (2, 5), (2, 6), (2, 7), (3, 2), (3, 4), (3, 5), (3, 6), (3, 7), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 8), (5, 2), (5, 3), (5, 5), (5, 6), (5, 7), (5, 8), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (8, 11), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (11, 2), (11, 4), (11, 6), (11, 7), (11, 8), (12, 6), (12, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_718 : Fin 10 → Finset Cell := ![(placed21 6 (8, 8) required_120), (placed21 3 (2, 7) required_276), (placed21 3 (2, 7) required_338), (placed21 3 (2, 8) required_437), (placed21 3 (1, 7) required_611), (placed21 0 (4, 1) required_642), (placed21 0 (4, 1) required_643), required_718_i0, required_718_i1, required_718_i2]
def childrenD_718 : Fin 10 → Finset Cell := ![(placed21 6 (8, 8) envelope_120), (placed21 3 (2, 7) envelope_276), (placed21 3 (2, 7) envelope_338), (placed21 3 (2, 8) envelope_437), (placed21 3 (1, 7) envelope_611), (placed21 0 (4, 1) envelope_642), (placed21 0 (4, 1) envelope_643), envelope_718_i0, envelope_718_i1, envelope_718_i2]
theorem common_sub_718 : commonEnvelope childrenD_718 ⊆ insert (7, 5) required_718 := by decide +kernel
theorem child_required_sub_718 : ∀ j, childrenC_718 j ⊆ insert (7, 5) required_718 := by decide +kernel
theorem child_envelope_sub_718 : ∀ j, childrenD_718 j ⊆ envelope_718 := by decide +kernel
theorem pivot_mem_718 : (7, 5) ∈ envelope_718 := by decide +kernel
theorem children_work_718 : ∀ j, Template HasSnaky 14 (childrenC_718 j) (childrenD_718 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_120 6 (8, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_276 3 (2, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_338 3 (2, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_437 3 (2, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_611 3 (1, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_642 0 (4, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_643 0 (4, 1)).mono (by decide +kernel)
  · exact row_works_718_i0.mono (by decide +kernel)
  · exact row_works_718_i1.mono (by decide +kernel)
  · exact row_works_718_i2.mono (by decide +kernel)
theorem row_works_718 : Template HasSnaky 15 required_718 envelope_718 := by
  refine compose HasSnaky 14 childrenC_718 childrenD_718 children_work_718 (7, 5)
    required_718 envelope_718 pivot_mem_718 child_required_sub_718 child_envelope_sub_718 ?_
  intro b hb
  exact common_sub_718 (mem_commonEnvelope childrenD_718 b hb)
def height_698 : ℕ := 15
def childrenH_698 : Fin 8 → ℕ := ![height_12, height_182, height_188, height_619, height_620, height_622, height_687, height_697]
theorem height_exact_698 : height_698 = 1 + Finset.univ.sup childrenH_698 := by decide +kernel
theorem required_origin_698 : ∀ x ∈ required_698,
    (∃ j, x ∈ childrenC_698 j) ∨ ∀ j, x ∈ childrenD_698 j := by decide +kernel
theorem required_exact_698 : required_698 =
    ((Finset.univ.biUnion childrenC_698) ∪ commonEnvelope childrenD_698).erase (4, 6) := by
  exact required_eq_combination childrenC_698 childrenD_698 (4, 6) required_698
    (by decide +kernel) child_required_sub_698 common_sub_698 required_origin_698
theorem envelope_origin_698 : ∀ x ∈ envelope_698,
    x = (4, 6) ∨ ∃ j, x ∈ childrenD_698 j := by decide +kernel
theorem envelope_exact_698 : envelope_698 =
    insert (4, 6) (Finset.univ.biUnion childrenD_698) := by
  exact envelope_eq_combination childrenD_698 (4, 6) envelope_698
    pivot_mem_698 child_envelope_sub_698 envelope_origin_698
def checked_698 : CheckedCard where
  required := required_698
  envelope := envelope_698
  height := height_698
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_698
def height_699_i3 : ℕ := 5
def childrenH_699_i3 : Fin 2 → ℕ := ![height_42, height_52]
theorem height_exact_699_i3 : height_699_i3 = 1 + Finset.univ.sup childrenH_699_i3 := by decide +kernel
theorem required_origin_699_i3 : ∀ x ∈ required_699_i3,
    (∃ j, x ∈ childrenC_699_i3 j) ∨ ∀ j, x ∈ childrenD_699_i3 j := by decide +kernel
theorem required_exact_699_i3 : required_699_i3 =
    ((Finset.univ.biUnion childrenC_699_i3) ∪ commonEnvelope childrenD_699_i3).erase (7, 6) := by
  exact required_eq_combination childrenC_699_i3 childrenD_699_i3 (7, 6) required_699_i3
    (by decide +kernel) child_required_sub_699_i3 common_sub_699_i3 required_origin_699_i3
theorem envelope_origin_699_i3 : ∀ x ∈ envelope_699_i3,
    x = (7, 6) ∨ ∃ j, x ∈ childrenD_699_i3 j := by decide +kernel
theorem envelope_exact_699_i3 : envelope_699_i3 =
    insert (7, 6) (Finset.univ.biUnion childrenD_699_i3) := by
  exact envelope_eq_combination childrenD_699_i3 (7, 6) envelope_699_i3
    pivot_mem_699_i3 child_envelope_sub_699_i3 envelope_origin_699_i3
def checked_699_i3 : CheckedCard where
  required := required_699_i3
  envelope := envelope_699_i3
  height := height_699_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_699_i3
def height_699_i2 : ℕ := 7
def childrenH_699_i2 : Fin 3 → ℕ := ![height_95, height_112, height_699_i3]
theorem height_exact_699_i2 : height_699_i2 = 1 + Finset.univ.sup childrenH_699_i2 := by decide +kernel
theorem required_origin_699_i2 : ∀ x ∈ required_699_i2,
    (∃ j, x ∈ childrenC_699_i2 j) ∨ ∀ j, x ∈ childrenD_699_i2 j := by decide +kernel
theorem required_exact_699_i2 : required_699_i2 =
    ((Finset.univ.biUnion childrenC_699_i2) ∪ commonEnvelope childrenD_699_i2).erase (7, 8) := by
  exact required_eq_combination childrenC_699_i2 childrenD_699_i2 (7, 8) required_699_i2
    (by decide +kernel) child_required_sub_699_i2 common_sub_699_i2 required_origin_699_i2
theorem envelope_origin_699_i2 : ∀ x ∈ envelope_699_i2,
    x = (7, 8) ∨ ∃ j, x ∈ childrenD_699_i2 j := by decide +kernel
theorem envelope_exact_699_i2 : envelope_699_i2 =
    insert (7, 8) (Finset.univ.biUnion childrenD_699_i2) := by
  exact envelope_eq_combination childrenD_699_i2 (7, 8) envelope_699_i2
    pivot_mem_699_i2 child_envelope_sub_699_i2 envelope_origin_699_i2
def checked_699_i2 : CheckedCard where
  required := required_699_i2
  envelope := envelope_699_i2
  height := height_699_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_699_i2
def height_699_i1 : ℕ := 11
def childrenH_699_i1 : Fin 3 → ℕ := ![height_371, height_460, height_699_i2]
theorem height_exact_699_i1 : height_699_i1 = 1 + Finset.univ.sup childrenH_699_i1 := by decide +kernel
theorem required_origin_699_i1 : ∀ x ∈ required_699_i1,
    (∃ j, x ∈ childrenC_699_i1 j) ∨ ∀ j, x ∈ childrenD_699_i1 j := by decide +kernel
theorem required_exact_699_i1 : required_699_i1 =
    ((Finset.univ.biUnion childrenC_699_i1) ∪ commonEnvelope childrenD_699_i1).erase (6, 8) := by
  exact required_eq_combination childrenC_699_i1 childrenD_699_i1 (6, 8) required_699_i1
    (by decide +kernel) child_required_sub_699_i1 common_sub_699_i1 required_origin_699_i1
theorem envelope_origin_699_i1 : ∀ x ∈ envelope_699_i1,
    x = (6, 8) ∨ ∃ j, x ∈ childrenD_699_i1 j := by decide +kernel
theorem envelope_exact_699_i1 : envelope_699_i1 =
    insert (6, 8) (Finset.univ.biUnion childrenD_699_i1) := by
  exact envelope_eq_combination childrenD_699_i1 (6, 8) envelope_699_i1
    pivot_mem_699_i1 child_envelope_sub_699_i1 envelope_origin_699_i1
def checked_699_i1 : CheckedCard where
  required := required_699_i1
  envelope := envelope_699_i1
  height := height_699_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_699_i1
def height_699_i0 : ℕ := 14
def childrenH_699_i0 : Fin 4 → ℕ := ![height_147, height_249, height_692, height_699_i1]
theorem height_exact_699_i0 : height_699_i0 = 1 + Finset.univ.sup childrenH_699_i0 := by decide +kernel
theorem required_origin_699_i0 : ∀ x ∈ required_699_i0,
    (∃ j, x ∈ childrenC_699_i0 j) ∨ ∀ j, x ∈ childrenD_699_i0 j := by decide +kernel
theorem required_exact_699_i0 : required_699_i0 =
    ((Finset.univ.biUnion childrenC_699_i0) ∪ commonEnvelope childrenD_699_i0).erase (4, 8) := by
  exact required_eq_combination childrenC_699_i0 childrenD_699_i0 (4, 8) required_699_i0
    (by decide +kernel) child_required_sub_699_i0 common_sub_699_i0 required_origin_699_i0
theorem envelope_origin_699_i0 : ∀ x ∈ envelope_699_i0,
    x = (4, 8) ∨ ∃ j, x ∈ childrenD_699_i0 j := by decide +kernel
theorem envelope_exact_699_i0 : envelope_699_i0 =
    insert (4, 8) (Finset.univ.biUnion childrenD_699_i0) := by
  exact envelope_eq_combination childrenD_699_i0 (4, 8) envelope_699_i0
    pivot_mem_699_i0 child_envelope_sub_699_i0 envelope_origin_699_i0
def checked_699_i0 : CheckedCard where
  required := required_699_i0
  envelope := envelope_699_i0
  height := height_699_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_699_i0
def height_699_i6 : ℕ := 5
def childrenH_699_i6 : Fin 2 → ℕ := ![height_5, height_259]
theorem height_exact_699_i6 : height_699_i6 = 1 + Finset.univ.sup childrenH_699_i6 := by decide +kernel
theorem required_origin_699_i6 : ∀ x ∈ required_699_i6,
    (∃ j, x ∈ childrenC_699_i6 j) ∨ ∀ j, x ∈ childrenD_699_i6 j := by decide +kernel
theorem required_exact_699_i6 : required_699_i6 =
    ((Finset.univ.biUnion childrenC_699_i6) ∪ commonEnvelope childrenD_699_i6).erase (7, 4) := by
  exact required_eq_combination childrenC_699_i6 childrenD_699_i6 (7, 4) required_699_i6
    (by decide +kernel) child_required_sub_699_i6 common_sub_699_i6 required_origin_699_i6
theorem envelope_origin_699_i6 : ∀ x ∈ envelope_699_i6,
    x = (7, 4) ∨ ∃ j, x ∈ childrenD_699_i6 j := by decide +kernel
theorem envelope_exact_699_i6 : envelope_699_i6 =
    insert (7, 4) (Finset.univ.biUnion childrenD_699_i6) := by
  exact envelope_eq_combination childrenD_699_i6 (7, 4) envelope_699_i6
    pivot_mem_699_i6 child_envelope_sub_699_i6 envelope_origin_699_i6
def checked_699_i6 : CheckedCard where
  required := required_699_i6
  envelope := envelope_699_i6
  height := height_699_i6
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_699_i6
def height_699_i5 : ℕ := 7
def childrenH_699_i5 : Fin 4 → ℕ := ![height_10, height_48, height_134, height_699_i6]
theorem height_exact_699_i5 : height_699_i5 = 1 + Finset.univ.sup childrenH_699_i5 := by decide +kernel
theorem required_origin_699_i5 : ∀ x ∈ required_699_i5,
    (∃ j, x ∈ childrenC_699_i5 j) ∨ ∀ j, x ∈ childrenD_699_i5 j := by decide +kernel
theorem required_exact_699_i5 : required_699_i5 =
    ((Finset.univ.biUnion childrenC_699_i5) ∪ commonEnvelope childrenD_699_i5).erase (6, 3) := by
  exact required_eq_combination childrenC_699_i5 childrenD_699_i5 (6, 3) required_699_i5
    (by decide +kernel) child_required_sub_699_i5 common_sub_699_i5 required_origin_699_i5
theorem envelope_origin_699_i5 : ∀ x ∈ envelope_699_i5,
    x = (6, 3) ∨ ∃ j, x ∈ childrenD_699_i5 j := by decide +kernel
theorem envelope_exact_699_i5 : envelope_699_i5 =
    insert (6, 3) (Finset.univ.biUnion childrenD_699_i5) := by
  exact envelope_eq_combination childrenD_699_i5 (6, 3) envelope_699_i5
    pivot_mem_699_i5 child_envelope_sub_699_i5 envelope_origin_699_i5
def checked_699_i5 : CheckedCard where
  required := required_699_i5
  envelope := envelope_699_i5
  height := height_699_i5
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_699_i5
def height_699_i4 : ℕ := 11
def childrenH_699_i4 : Fin 5 → ℕ := ![height_389, height_545, height_546, height_549, height_699_i5]
theorem height_exact_699_i4 : height_699_i4 = 1 + Finset.univ.sup childrenH_699_i4 := by decide +kernel
theorem required_origin_699_i4 : ∀ x ∈ required_699_i4,
    (∃ j, x ∈ childrenC_699_i4 j) ∨ ∀ j, x ∈ childrenD_699_i4 j := by decide +kernel
theorem required_exact_699_i4 : required_699_i4 =
    ((Finset.univ.biUnion childrenC_699_i4) ∪ commonEnvelope childrenD_699_i4).erase (6, 4) := by
  exact required_eq_combination childrenC_699_i4 childrenD_699_i4 (6, 4) required_699_i4
    (by decide +kernel) child_required_sub_699_i4 common_sub_699_i4 required_origin_699_i4
theorem envelope_origin_699_i4 : ∀ x ∈ envelope_699_i4,
    x = (6, 4) ∨ ∃ j, x ∈ childrenD_699_i4 j := by decide +kernel
theorem envelope_exact_699_i4 : envelope_699_i4 =
    insert (6, 4) (Finset.univ.biUnion childrenD_699_i4) := by
  exact envelope_eq_combination childrenD_699_i4 (6, 4) envelope_699_i4
    pivot_mem_699_i4 child_envelope_sub_699_i4 envelope_origin_699_i4
def checked_699_i4 : CheckedCard where
  required := required_699_i4
  envelope := envelope_699_i4
  height := height_699_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_699_i4
def height_699 : ℕ := 15
def childrenH_699 : Fin 5 → ℕ := ![height_197, height_321, height_693, height_699_i0, height_699_i4]
theorem height_exact_699 : height_699 = 1 + Finset.univ.sup childrenH_699 := by decide +kernel
theorem required_origin_699 : ∀ x ∈ required_699,
    (∃ j, x ∈ childrenC_699 j) ∨ ∀ j, x ∈ childrenD_699 j := by decide +kernel
theorem required_exact_699 : required_699 =
    ((Finset.univ.biUnion childrenC_699) ∪ commonEnvelope childrenD_699).erase (7, 5) := by
  exact required_eq_combination childrenC_699 childrenD_699 (7, 5) required_699
    (by decide +kernel) child_required_sub_699 common_sub_699 required_origin_699
theorem envelope_origin_699 : ∀ x ∈ envelope_699,
    x = (7, 5) ∨ ∃ j, x ∈ childrenD_699 j := by decide +kernel
theorem envelope_exact_699 : envelope_699 =
    insert (7, 5) (Finset.univ.biUnion childrenD_699) := by
  exact envelope_eq_combination childrenD_699 (7, 5) envelope_699
    pivot_mem_699 child_envelope_sub_699 envelope_origin_699
def checked_699 : CheckedCard where
  required := required_699
  envelope := envelope_699
  height := height_699
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_699
def height_712_i1 : ℕ := 11
def childrenH_712_i1 : Fin 3 → ℕ := ![height_44, height_545, height_655]
theorem height_exact_712_i1 : height_712_i1 = 1 + Finset.univ.sup childrenH_712_i1 := by decide +kernel
theorem required_origin_712_i1 : ∀ x ∈ required_712_i1,
    (∃ j, x ∈ childrenC_712_i1 j) ∨ ∀ j, x ∈ childrenD_712_i1 j := by decide +kernel
theorem required_exact_712_i1 : required_712_i1 =
    ((Finset.univ.biUnion childrenC_712_i1) ∪ commonEnvelope childrenD_712_i1).erase (6, 4) := by
  exact required_eq_combination childrenC_712_i1 childrenD_712_i1 (6, 4) required_712_i1
    (by decide +kernel) child_required_sub_712_i1 common_sub_712_i1 required_origin_712_i1
theorem envelope_origin_712_i1 : ∀ x ∈ envelope_712_i1,
    x = (6, 4) ∨ ∃ j, x ∈ childrenD_712_i1 j := by decide +kernel
theorem envelope_exact_712_i1 : envelope_712_i1 =
    insert (6, 4) (Finset.univ.biUnion childrenD_712_i1) := by
  exact envelope_eq_combination childrenD_712_i1 (6, 4) envelope_712_i1
    pivot_mem_712_i1 child_envelope_sub_712_i1 envelope_origin_712_i1
def checked_712_i1 : CheckedCard where
  required := required_712_i1
  envelope := envelope_712_i1
  height := height_712_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_712_i1
def height_712_i0 : ℕ := 13
def childrenH_712_i0 : Fin 6 → ℕ := ![height_116, height_297, height_435, height_435, height_649, height_712_i1]
theorem height_exact_712_i0 : height_712_i0 = 1 + Finset.univ.sup childrenH_712_i0 := by decide +kernel
theorem required_origin_712_i0 : ∀ x ∈ required_712_i0,
    (∃ j, x ∈ childrenC_712_i0 j) ∨ ∀ j, x ∈ childrenD_712_i0 j := by decide +kernel
theorem required_exact_712_i0 : required_712_i0 =
    ((Finset.univ.biUnion childrenC_712_i0) ∪ commonEnvelope childrenD_712_i0).erase (5, 4) := by
  exact required_eq_combination childrenC_712_i0 childrenD_712_i0 (5, 4) required_712_i0
    (by decide +kernel) child_required_sub_712_i0 common_sub_712_i0 required_origin_712_i0
theorem envelope_origin_712_i0 : ∀ x ∈ envelope_712_i0,
    x = (5, 4) ∨ ∃ j, x ∈ childrenD_712_i0 j := by decide +kernel
theorem envelope_exact_712_i0 : envelope_712_i0 =
    insert (5, 4) (Finset.univ.biUnion childrenD_712_i0) := by
  exact envelope_eq_combination childrenD_712_i0 (5, 4) envelope_712_i0
    pivot_mem_712_i0 child_envelope_sub_712_i0 envelope_origin_712_i0
def checked_712_i0 : CheckedCard where
  required := required_712_i0
  envelope := envelope_712_i0
  height := height_712_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_712_i0
def height_712 : ℕ := 15
def childrenH_712 : Fin 13 → ℕ := ![height_174, height_508, height_508, height_566, height_605, height_605, height_647, height_650, height_650, height_712_i0, height_661, height_710, height_711]
theorem height_exact_712 : height_712 = 1 + Finset.univ.sup childrenH_712 := by decide +kernel
theorem required_origin_712 : ∀ x ∈ required_712,
    (∃ j, x ∈ childrenC_712 j) ∨ ∀ j, x ∈ childrenD_712 j := by decide +kernel
theorem required_exact_712 : required_712 =
    ((Finset.univ.biUnion childrenC_712) ∪ commonEnvelope childrenD_712).erase (5, 6) := by
  exact required_eq_combination childrenC_712 childrenD_712 (5, 6) required_712
    (by decide +kernel) child_required_sub_712 common_sub_712 required_origin_712
theorem envelope_origin_712 : ∀ x ∈ envelope_712,
    x = (5, 6) ∨ ∃ j, x ∈ childrenD_712 j := by decide +kernel
theorem envelope_exact_712 : envelope_712 =
    insert (5, 6) (Finset.univ.biUnion childrenD_712) := by
  exact envelope_eq_combination childrenD_712 (5, 6) envelope_712
    pivot_mem_712 child_envelope_sub_712 envelope_origin_712
def checked_712 : CheckedCard where
  required := required_712
  envelope := envelope_712
  height := height_712
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_712
def height_713 : ℕ := 15
def childrenH_713 : Fin 11 → ℕ := ![height_508, height_508, height_605, height_605, height_645, height_647, height_650, height_650, height_654, height_654, height_711]
theorem height_exact_713 : height_713 = 1 + Finset.univ.sup childrenH_713 := by decide +kernel
theorem required_origin_713 : ∀ x ∈ required_713,
    (∃ j, x ∈ childrenC_713 j) ∨ ∀ j, x ∈ childrenD_713 j := by decide +kernel
theorem required_exact_713 : required_713 =
    ((Finset.univ.biUnion childrenC_713) ∪ commonEnvelope childrenD_713).erase (5, 6) := by
  exact required_eq_combination childrenC_713 childrenD_713 (5, 6) required_713
    (by decide +kernel) child_required_sub_713 common_sub_713 required_origin_713
theorem envelope_origin_713 : ∀ x ∈ envelope_713,
    x = (5, 6) ∨ ∃ j, x ∈ childrenD_713 j := by decide +kernel
theorem envelope_exact_713 : envelope_713 =
    insert (5, 6) (Finset.univ.biUnion childrenD_713) := by
  exact envelope_eq_combination childrenD_713 (5, 6) envelope_713
    pivot_mem_713 child_envelope_sub_713 envelope_origin_713
def checked_713 : CheckedCard where
  required := required_713
  envelope := envelope_713
  height := height_713
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_713
def height_718_i0 : ℕ := 8
def childrenH_718_i0 : Fin 4 → ℕ := ![height_44, height_52, height_155, height_341]
theorem height_exact_718_i0 : height_718_i0 = 1 + Finset.univ.sup childrenH_718_i0 := by decide +kernel
theorem required_origin_718_i0 : ∀ x ∈ required_718_i0,
    (∃ j, x ∈ childrenC_718_i0 j) ∨ ∀ j, x ∈ childrenD_718_i0 j := by decide +kernel
theorem required_exact_718_i0 : required_718_i0 =
    ((Finset.univ.biUnion childrenC_718_i0) ∪ commonEnvelope childrenD_718_i0).erase (6, 5) := by
  exact required_eq_combination childrenC_718_i0 childrenD_718_i0 (6, 5) required_718_i0
    (by decide +kernel) child_required_sub_718_i0 common_sub_718_i0 required_origin_718_i0
theorem envelope_origin_718_i0 : ∀ x ∈ envelope_718_i0,
    x = (6, 5) ∨ ∃ j, x ∈ childrenD_718_i0 j := by decide +kernel
theorem envelope_exact_718_i0 : envelope_718_i0 =
    insert (6, 5) (Finset.univ.biUnion childrenD_718_i0) := by
  exact envelope_eq_combination childrenD_718_i0 (6, 5) envelope_718_i0
    pivot_mem_718_i0 child_envelope_sub_718_i0 envelope_origin_718_i0
def checked_718_i0 : CheckedCard where
  required := required_718_i0
  envelope := envelope_718_i0
  height := height_718_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_718_i0
def height_718_i1 : ℕ := 13
def childrenH_718_i1 : Fin 5 → ℕ := ![height_452, height_520, height_587, height_612, height_633]
theorem height_exact_718_i1 : height_718_i1 = 1 + Finset.univ.sup childrenH_718_i1 := by decide +kernel
theorem required_origin_718_i1 : ∀ x ∈ required_718_i1,
    (∃ j, x ∈ childrenC_718_i1 j) ∨ ∀ j, x ∈ childrenD_718_i1 j := by decide +kernel
theorem required_exact_718_i1 : required_718_i1 =
    ((Finset.univ.biUnion childrenC_718_i1) ∪ commonEnvelope childrenD_718_i1).erase (7, 6) := by
  exact required_eq_combination childrenC_718_i1 childrenD_718_i1 (7, 6) required_718_i1
    (by decide +kernel) child_required_sub_718_i1 common_sub_718_i1 required_origin_718_i1
theorem envelope_origin_718_i1 : ∀ x ∈ envelope_718_i1,
    x = (7, 6) ∨ ∃ j, x ∈ childrenD_718_i1 j := by decide +kernel
theorem envelope_exact_718_i1 : envelope_718_i1 =
    insert (7, 6) (Finset.univ.biUnion childrenD_718_i1) := by
  exact envelope_eq_combination childrenD_718_i1 (7, 6) envelope_718_i1
    pivot_mem_718_i1 child_envelope_sub_718_i1 envelope_origin_718_i1
def checked_718_i1 : CheckedCard where
  required := required_718_i1
  envelope := envelope_718_i1
  height := height_718_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_718_i1
def height_718_i3 : ℕ := 6
def childrenH_718_i3 : Fin 4 → ℕ := ![height_52, height_52, height_232, height_232]
theorem height_exact_718_i3 : height_718_i3 = 1 + Finset.univ.sup childrenH_718_i3 := by decide +kernel
theorem required_origin_718_i3 : ∀ x ∈ required_718_i3,
    (∃ j, x ∈ childrenC_718_i3 j) ∨ ∀ j, x ∈ childrenD_718_i3 j := by decide +kernel
theorem required_exact_718_i3 : required_718_i3 =
    ((Finset.univ.biUnion childrenC_718_i3) ∪ commonEnvelope childrenD_718_i3).erase (6, 6) := by
  exact required_eq_combination childrenC_718_i3 childrenD_718_i3 (6, 6) required_718_i3
    (by decide +kernel) child_required_sub_718_i3 common_sub_718_i3 required_origin_718_i3
theorem envelope_origin_718_i3 : ∀ x ∈ envelope_718_i3,
    x = (6, 6) ∨ ∃ j, x ∈ childrenD_718_i3 j := by decide +kernel
theorem envelope_exact_718_i3 : envelope_718_i3 =
    insert (6, 6) (Finset.univ.biUnion childrenD_718_i3) := by
  exact envelope_eq_combination childrenD_718_i3 (6, 6) envelope_718_i3
    pivot_mem_718_i3 child_envelope_sub_718_i3 envelope_origin_718_i3
def checked_718_i3 : CheckedCard where
  required := required_718_i3
  envelope := envelope_718_i3
  height := height_718_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_718_i3
def height_718_i5 : ℕ := 5
def childrenH_718_i5 : Fin 2 → ℕ := ![height_8, height_229]
theorem height_exact_718_i5 : height_718_i5 = 1 + Finset.univ.sup childrenH_718_i5 := by decide +kernel
theorem required_origin_718_i5 : ∀ x ∈ required_718_i5,
    (∃ j, x ∈ childrenC_718_i5 j) ∨ ∀ j, x ∈ childrenD_718_i5 j := by decide +kernel
theorem required_exact_718_i5 : required_718_i5 =
    ((Finset.univ.biUnion childrenC_718_i5) ∪ commonEnvelope childrenD_718_i5).erase (7, 3) := by
  exact required_eq_combination childrenC_718_i5 childrenD_718_i5 (7, 3) required_718_i5
    (by decide +kernel) child_required_sub_718_i5 common_sub_718_i5 required_origin_718_i5
theorem envelope_origin_718_i5 : ∀ x ∈ envelope_718_i5,
    x = (7, 3) ∨ ∃ j, x ∈ childrenD_718_i5 j := by decide +kernel
theorem envelope_exact_718_i5 : envelope_718_i5 =
    insert (7, 3) (Finset.univ.biUnion childrenD_718_i5) := by
  exact envelope_eq_combination childrenD_718_i5 (7, 3) envelope_718_i5
    pivot_mem_718_i5 child_envelope_sub_718_i5 envelope_origin_718_i5
def checked_718_i5 : CheckedCard where
  required := required_718_i5
  envelope := envelope_718_i5
  height := height_718_i5
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_718_i5
def height_718_i4 : ℕ := 6
def childrenH_718_i4 : Fin 5 → ℕ := ![height_12, height_12, height_12, height_377, height_718_i5]
theorem height_exact_718_i4 : height_718_i4 = 1 + Finset.univ.sup childrenH_718_i4 := by decide +kernel
theorem required_origin_718_i4 : ∀ x ∈ required_718_i4,
    (∃ j, x ∈ childrenC_718_i4 j) ∨ ∀ j, x ∈ childrenD_718_i4 j := by decide +kernel
theorem required_exact_718_i4 : required_718_i4 =
    ((Finset.univ.biUnion childrenC_718_i4) ∪ commonEnvelope childrenD_718_i4).erase (7, 4) := by
  exact required_eq_combination childrenC_718_i4 childrenD_718_i4 (7, 4) required_718_i4
    (by decide +kernel) child_required_sub_718_i4 common_sub_718_i4 required_origin_718_i4
theorem envelope_origin_718_i4 : ∀ x ∈ envelope_718_i4,
    x = (7, 4) ∨ ∃ j, x ∈ childrenD_718_i4 j := by decide +kernel
theorem envelope_exact_718_i4 : envelope_718_i4 =
    insert (7, 4) (Finset.univ.biUnion childrenD_718_i4) := by
  exact envelope_eq_combination childrenD_718_i4 (7, 4) envelope_718_i4
    pivot_mem_718_i4 child_envelope_sub_718_i4 envelope_origin_718_i4
def checked_718_i4 : CheckedCard where
  required := required_718_i4
  envelope := envelope_718_i4
  height := height_718_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_718_i4
def height_718_i6 : ℕ := 10
def childrenH_718_i6 : Fin 3 → ℕ := ![height_315, height_317, height_640]
theorem height_exact_718_i6 : height_718_i6 = 1 + Finset.univ.sup childrenH_718_i6 := by decide +kernel
theorem required_origin_718_i6 : ∀ x ∈ required_718_i6,
    (∃ j, x ∈ childrenC_718_i6 j) ∨ ∀ j, x ∈ childrenD_718_i6 j := by decide +kernel
theorem required_exact_718_i6 : required_718_i6 =
    ((Finset.univ.biUnion childrenC_718_i6) ∪ commonEnvelope childrenD_718_i6).erase (6, 6) := by
  exact required_eq_combination childrenC_718_i6 childrenD_718_i6 (6, 6) required_718_i6
    (by decide +kernel) child_required_sub_718_i6 common_sub_718_i6 required_origin_718_i6
theorem envelope_origin_718_i6 : ∀ x ∈ envelope_718_i6,
    x = (6, 6) ∨ ∃ j, x ∈ childrenD_718_i6 j := by decide +kernel
theorem envelope_exact_718_i6 : envelope_718_i6 =
    insert (6, 6) (Finset.univ.biUnion childrenD_718_i6) := by
  exact envelope_eq_combination childrenD_718_i6 (6, 6) envelope_718_i6
    pivot_mem_718_i6 child_envelope_sub_718_i6 envelope_origin_718_i6
def checked_718_i6 : CheckedCard where
  required := required_718_i6
  envelope := envelope_718_i6
  height := height_718_i6
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_718_i6
def height_718_i2 : ℕ := 14
def childrenH_718_i2 : Fin 6 → ℕ := ![height_329, height_452, height_462, height_718_i3, height_718_i4, height_718_i6]
theorem height_exact_718_i2 : height_718_i2 = 1 + Finset.univ.sup childrenH_718_i2 := by decide +kernel
theorem required_origin_718_i2 : ∀ x ∈ required_718_i2,
    (∃ j, x ∈ childrenC_718_i2 j) ∨ ∀ j, x ∈ childrenD_718_i2 j := by decide +kernel
theorem required_exact_718_i2 : required_718_i2 =
    ((Finset.univ.biUnion childrenC_718_i2) ∪ commonEnvelope childrenD_718_i2).erase (7, 6) := by
  exact required_eq_combination childrenC_718_i2 childrenD_718_i2 (7, 6) required_718_i2
    (by decide +kernel) child_required_sub_718_i2 common_sub_718_i2 required_origin_718_i2
theorem envelope_origin_718_i2 : ∀ x ∈ envelope_718_i2,
    x = (7, 6) ∨ ∃ j, x ∈ childrenD_718_i2 j := by decide +kernel
theorem envelope_exact_718_i2 : envelope_718_i2 =
    insert (7, 6) (Finset.univ.biUnion childrenD_718_i2) := by
  exact envelope_eq_combination childrenD_718_i2 (7, 6) envelope_718_i2
    pivot_mem_718_i2 child_envelope_sub_718_i2 envelope_origin_718_i2
def checked_718_i2 : CheckedCard where
  required := required_718_i2
  envelope := envelope_718_i2
  height := height_718_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_718_i2
def height_718 : ℕ := 15
def childrenH_718 : Fin 10 → ℕ := ![height_120, height_276, height_338, height_437, height_611, height_642, height_643, height_718_i0, height_718_i1, height_718_i2]
theorem height_exact_718 : height_718 = 1 + Finset.univ.sup childrenH_718 := by decide +kernel
theorem required_origin_718 : ∀ x ∈ required_718,
    (∃ j, x ∈ childrenC_718 j) ∨ ∀ j, x ∈ childrenD_718 j := by decide +kernel
theorem required_exact_718 : required_718 =
    ((Finset.univ.biUnion childrenC_718) ∪ commonEnvelope childrenD_718).erase (7, 5) := by
  exact required_eq_combination childrenC_718 childrenD_718 (7, 5) required_718
    (by decide +kernel) child_required_sub_718 common_sub_718 required_origin_718
theorem envelope_origin_718 : ∀ x ∈ envelope_718,
    x = (7, 5) ∨ ∃ j, x ∈ childrenD_718 j := by decide +kernel
theorem envelope_exact_718 : envelope_718 =
    insert (7, 5) (Finset.univ.biUnion childrenD_718) := by
  exact envelope_eq_combination childrenD_718 (7, 5) envelope_718
    pivot_mem_718 child_envelope_sub_718 envelope_origin_718
def checked_718 : CheckedCard where
  required := required_718
  envelope := envelope_718
  height := height_718
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_718
end SnakyPrototype.Certificate21

end OAI
