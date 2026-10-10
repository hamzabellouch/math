import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part07
import OAI.GameTheory.SnakyTwentyOne.Cards.Height10Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height10Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height10Part06
import OAI.GameTheory.SnakyTwentyOne.Cards.Height11Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height11Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height11Part06
import OAI.GameTheory.SnakyTwentyOne.Cards.Height12Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height14Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height16Part02
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_707_i0 : Finset Cell := ⟨(([(4, 5), (5, 5), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_707_i0 : Finset Cell := ⟨(([(0, 6), (1, 6), (1, 7), (1, 8), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 2), (6, 3), (6, 4), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (7, 6), (7, 7), (7, 8), (8, 6), (8, 7), (8, 8), (9, 6), (9, 7), (9, 8), (10, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_707_i0 : Fin 7 → Finset Cell := ![(placed21 3 (2, 8) required_116), (placed21 5 (7, 4) required_134), (placed21 5 (7, 4) required_180), (placed21 0 (4, 2) required_337), (placed21 5 (8, 4) required_435), (placed21 5 (7, 5) required_558), (placed21 1 (0, 3) required_662)]
def childrenD_707_i0 : Fin 7 → Finset Cell := ![(placed21 3 (2, 8) envelope_116), (placed21 5 (7, 4) envelope_134), (placed21 5 (7, 4) envelope_180), (placed21 0 (4, 2) envelope_337), (placed21 5 (8, 4) envelope_435), (placed21 5 (7, 5) envelope_558), (placed21 1 (0, 3) envelope_662)]
theorem common_sub_707_i0 : commonEnvelope childrenD_707_i0 ⊆ insert (5, 7) required_707_i0 := by decide +kernel
theorem child_required_sub_707_i0 : ∀ j, childrenC_707_i0 j ⊆ insert (5, 7) required_707_i0 := by decide +kernel
theorem child_envelope_sub_707_i0 : ∀ j, childrenD_707_i0 j ⊆ envelope_707_i0 := by decide +kernel
theorem pivot_mem_707_i0 : (5, 7) ∈ envelope_707_i0 := by decide +kernel
theorem children_work_707_i0 : ∀ j, Template HasSnaky 9 (childrenC_707_i0 j) (childrenD_707_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_116 3 (2, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_134 5 (7, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_180 5 (7, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_337 0 (4, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_435 5 (8, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_558 5 (7, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_662 1 (0, 3)).mono (by decide +kernel)
theorem row_works_707_i0 : Template HasSnaky 10 required_707_i0 envelope_707_i0 := by
  refine compose HasSnaky 9 childrenC_707_i0 childrenD_707_i0 children_work_707_i0 (5, 7)
    required_707_i0 envelope_707_i0 pivot_mem_707_i0 child_required_sub_707_i0 child_envelope_sub_707_i0 ?_
  intro b hb
  exact common_sub_707_i0 (mem_commonEnvelope childrenD_707_i0 b hb)
def required_707_i2 : Finset Cell := ⟨(([(4, 5), (5, 4), (5, 5), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_707_i2 : Finset Cell := ⟨(([(1, 6), (1, 8), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_707_i2 : Fin 3 → Finset Cell := ![(placed21 0 (5, 3) required_7), (placed21 2 (6, 3) required_9), (placed21 5 (6, 4) required_380)]
def childrenD_707_i2 : Fin 3 → Finset Cell := ![(placed21 0 (5, 3) envelope_7), (placed21 2 (6, 3) envelope_9), (placed21 5 (6, 4) envelope_380)]
theorem common_sub_707_i2 : commonEnvelope childrenD_707_i2 ⊆ insert (5, 7) required_707_i2 := by decide +kernel
theorem child_required_sub_707_i2 : ∀ j, childrenC_707_i2 j ⊆ insert (5, 7) required_707_i2 := by decide +kernel
theorem child_envelope_sub_707_i2 : ∀ j, childrenD_707_i2 j ⊆ envelope_707_i2 := by decide +kernel
theorem pivot_mem_707_i2 : (5, 7) ∈ envelope_707_i2 := by decide +kernel
theorem children_work_707_i2 : ∀ j, Template HasSnaky 9 (childrenC_707_i2 j) (childrenD_707_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 0 (5, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_9 2 (6, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_380 5 (6, 4)).mono (by decide +kernel)
theorem row_works_707_i2 : Template HasSnaky 10 required_707_i2 envelope_707_i2 := by
  refine compose HasSnaky 9 childrenC_707_i2 childrenD_707_i2 children_work_707_i2 (5, 7)
    required_707_i2 envelope_707_i2 pivot_mem_707_i2 child_required_sub_707_i2 child_envelope_sub_707_i2 ?_
  intro b hb
  exact common_sub_707_i2 (mem_commonEnvelope childrenD_707_i2 b hb)
def required_707_i1 : Finset Cell := ⟨(([(4, 5), (5, 5), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_707_i1 : Finset Cell := ⟨(([(1, 2), (1, 4), (1, 6), (1, 8), (2, 2), (2, 3), (2, 4), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, 2), (3, 3), (3, 4), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (4, 1), (4, 2), (4, 3), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (7, 2), (7, 3), (7, 4), (8, 2), (8, 3), (8, 4), (9, 2), (9, 3), (9, 4), (10, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_707_i1 : Fin 4 → Finset Cell := ![(placed21 6 (6, 8) required_14), (placed21 4 (4, 8) required_33), (placed21 3 (1, 7) required_322), required_707_i2]
def childrenD_707_i1 : Fin 4 → Finset Cell := ![(placed21 6 (6, 8) envelope_14), (placed21 4 (4, 8) envelope_33), (placed21 3 (1, 7) envelope_322), envelope_707_i2]
theorem common_sub_707_i1 : commonEnvelope childrenD_707_i1 ⊆ insert (5, 4) required_707_i1 := by decide +kernel
theorem child_required_sub_707_i1 : ∀ j, childrenC_707_i1 j ⊆ insert (5, 4) required_707_i1 := by decide +kernel
theorem child_envelope_sub_707_i1 : ∀ j, childrenD_707_i1 j ⊆ envelope_707_i1 := by decide +kernel
theorem pivot_mem_707_i1 : (5, 4) ∈ envelope_707_i1 := by decide +kernel
theorem children_work_707_i1 : ∀ j, Template HasSnaky 10 (childrenC_707_i1 j) (childrenD_707_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_14 6 (6, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_33 4 (4, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_322 3 (1, 7)).mono (by decide +kernel)
  · exact row_works_707_i2.mono (by decide +kernel)
theorem row_works_707_i1 : Template HasSnaky 11 required_707_i1 envelope_707_i1 := by
  refine compose HasSnaky 10 childrenC_707_i1 childrenD_707_i1 children_work_707_i1 (5, 4)
    required_707_i1 envelope_707_i1 pivot_mem_707_i1 child_required_sub_707_i1 child_envelope_sub_707_i1 ?_
  intro b hb
  exact common_sub_707_i1 (mem_commonEnvelope childrenD_707_i1 b hb)
def required_707_i4 : Finset Cell := ⟨(([(5, 4), (5, 5), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_707_i4 : Finset Cell := ⟨(([(4, 1), (4, 2), (4, 3), (4, 5), (4, 7), (4, 8), (4, 9), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 7), (6, 8), (6, 9), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (11, 2), (11, 3), (11, 4), (11, 5), (12, 2), (12, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_707_i4 : Fin 4 → Finset Cell := ![(placed21 0 (5, 3) required_7), (placed21 1 (4, 4) required_8), (placed21 2 (6, 3) required_9), (placed21 4 (4, 9) required_485)]
def childrenD_707_i4 : Fin 4 → Finset Cell := ![(placed21 0 (5, 3) envelope_7), (placed21 1 (4, 4) envelope_8), (placed21 2 (6, 3) envelope_9), (placed21 4 (4, 9) envelope_485)]
theorem common_sub_707_i4 : commonEnvelope childrenD_707_i4 ⊆ insert (5, 7) required_707_i4 := by decide +kernel
theorem child_required_sub_707_i4 : ∀ j, childrenC_707_i4 j ⊆ insert (5, 7) required_707_i4 := by decide +kernel
theorem child_envelope_sub_707_i4 : ∀ j, childrenD_707_i4 j ⊆ envelope_707_i4 := by decide +kernel
theorem pivot_mem_707_i4 : (5, 7) ∈ envelope_707_i4 := by decide +kernel
theorem children_work_707_i4 : ∀ j, Template HasSnaky 12 (childrenC_707_i4 j) (childrenD_707_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 0 (5, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_8 1 (4, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_9 2 (6, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_485 4 (4, 9)).mono (by decide +kernel)
theorem row_works_707_i4 : Template HasSnaky 13 required_707_i4 envelope_707_i4 := by
  refine compose HasSnaky 12 childrenC_707_i4 childrenD_707_i4 children_work_707_i4 (5, 7)
    required_707_i4 envelope_707_i4 pivot_mem_707_i4 child_required_sub_707_i4 child_envelope_sub_707_i4 ?_
  intro b hb
  exact common_sub_707_i4 (mem_commonEnvelope childrenD_707_i4 b hb)
def required_707_i3 : Finset Cell := ⟨(([(4, 5), (5, 5), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_707_i3 : Finset Cell := ⟨(([(0, 6), (1, 2), (1, 4), (1, 6), (1, 7), (1, 8), (2, 2), (2, 3), (2, 4), (2, 6), (2, 7), (2, 8), (3, 2), (3, 3), (3, 4), (3, 6), (3, 7), (3, 8), (4, 1), (4, 2), (4, 3), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 7), (6, 8), (6, 9), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (11, 2), (11, 3), (11, 4), (11, 5), (12, 2), (12, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_707_i3 : Fin 5 → Finset Cell := ![(placed21 4 (3, 7) required_136), (placed21 0 (3, 2) required_267), (placed21 3 (1, 7) required_322), (placed21 5 (9, 3) required_322), required_707_i4]
def childrenD_707_i3 : Fin 5 → Finset Cell := ![(placed21 4 (3, 7) envelope_136), (placed21 0 (3, 2) envelope_267), (placed21 3 (1, 7) envelope_322), (placed21 5 (9, 3) envelope_322), envelope_707_i4]
theorem common_sub_707_i3 : commonEnvelope childrenD_707_i3 ⊆ insert (5, 4) required_707_i3 := by decide +kernel
theorem child_required_sub_707_i3 : ∀ j, childrenC_707_i3 j ⊆ insert (5, 4) required_707_i3 := by decide +kernel
theorem child_envelope_sub_707_i3 : ∀ j, childrenD_707_i3 j ⊆ envelope_707_i3 := by decide +kernel
theorem pivot_mem_707_i3 : (5, 4) ∈ envelope_707_i3 := by decide +kernel
theorem children_work_707_i3 : ∀ j, Template HasSnaky 13 (childrenC_707_i3 j) (childrenD_707_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_136 4 (3, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_267 0 (3, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_322 3 (1, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_322 5 (9, 3)).mono (by decide +kernel)
  · exact row_works_707_i4.mono (by decide +kernel)
theorem row_works_707_i3 : Template HasSnaky 14 required_707_i3 envelope_707_i3 := by
  refine compose HasSnaky 13 childrenC_707_i3 childrenD_707_i3 children_work_707_i3 (5, 4)
    required_707_i3 envelope_707_i3 pivot_mem_707_i3 child_required_sub_707_i3 child_envelope_sub_707_i3 ?_
  intro b hb
  exact common_sub_707_i3 (mem_commonEnvelope childrenD_707_i3 b hb)
def required_707_i6 : Finset Cell := ⟨(([(5, 4), (5, 5), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_707_i6 : Finset Cell := ⟨(([(2, 6), (3, 6), (3, 7), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (7, 6), (7, 7), (7, 8), (8, 6), (8, 7), (8, 8), (9, 6), (9, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_707_i6 : Fin 4 → Finset Cell := ![(placed21 2 (6, 3) required_9), (placed21 1 (2, 4) required_115), (placed21 5 (8, 3) required_302), (placed21 5 (8, 3) required_303)]
def childrenD_707_i6 : Fin 4 → Finset Cell := ![(placed21 2 (6, 3) envelope_9), (placed21 1 (2, 4) envelope_115), (placed21 5 (8, 3) envelope_302), (placed21 5 (8, 3) envelope_303)]
theorem common_sub_707_i6 : commonEnvelope childrenD_707_i6 ⊆ insert (5, 7) required_707_i6 := by decide +kernel
theorem child_required_sub_707_i6 : ∀ j, childrenC_707_i6 j ⊆ insert (5, 7) required_707_i6 := by decide +kernel
theorem child_envelope_sub_707_i6 : ∀ j, childrenD_707_i6 j ⊆ envelope_707_i6 := by decide +kernel
theorem pivot_mem_707_i6 : (5, 7) ∈ envelope_707_i6 := by decide +kernel
theorem children_work_707_i6 : ∀ j, Template HasSnaky 6 (childrenC_707_i6 j) (childrenD_707_i6 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_9 2 (6, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_115 1 (2, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_302 5 (8, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_303 5 (8, 3)).mono (by decide +kernel)
theorem row_works_707_i6 : Template HasSnaky 7 required_707_i6 envelope_707_i6 := by
  refine compose HasSnaky 6 childrenC_707_i6 childrenD_707_i6 children_work_707_i6 (5, 7)
    required_707_i6 envelope_707_i6 pivot_mem_707_i6 child_required_sub_707_i6 child_envelope_sub_707_i6 ?_
  intro b hb
  exact common_sub_707_i6 (mem_commonEnvelope childrenD_707_i6 b hb)
def required_707_i5 : Finset Cell := ⟨(([(4, 5), (5, 5), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_707_i5 : Finset Cell := ⟨(([(1, 6), (1, 7), (2, 6), (2, 7), (3, 6), (3, 7), (4, 1), (4, 2), (4, 3), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (7, 5), (7, 6), (7, 7), (7, 8), (8, 5), (8, 6), (8, 7), (8, 8), (9, 6), (9, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_707_i5 : Fin 4 → Finset Cell := ![(placed21 4 (4, 8) required_13), (placed21 6 (6, 8) required_14), (placed21 7 (8, 7) required_332), required_707_i6]
def childrenD_707_i5 : Fin 4 → Finset Cell := ![(placed21 4 (4, 8) envelope_13), (placed21 6 (6, 8) envelope_14), (placed21 7 (8, 7) envelope_332), envelope_707_i6]
theorem common_sub_707_i5 : commonEnvelope childrenD_707_i5 ⊆ insert (5, 4) required_707_i5 := by decide +kernel
theorem child_required_sub_707_i5 : ∀ j, childrenC_707_i5 j ⊆ insert (5, 4) required_707_i5 := by decide +kernel
theorem child_envelope_sub_707_i5 : ∀ j, childrenD_707_i5 j ⊆ envelope_707_i5 := by decide +kernel
theorem pivot_mem_707_i5 : (5, 4) ∈ envelope_707_i5 := by decide +kernel
theorem children_work_707_i5 : ∀ j, Template HasSnaky 7 (childrenC_707_i5 j) (childrenD_707_i5 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_13 4 (4, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_14 6 (6, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_332 7 (8, 7)).mono (by decide +kernel)
  · exact row_works_707_i6.mono (by decide +kernel)
theorem row_works_707_i5 : Template HasSnaky 8 required_707_i5 envelope_707_i5 := by
  refine compose HasSnaky 7 childrenC_707_i5 childrenD_707_i5 children_work_707_i5 (5, 4)
    required_707_i5 envelope_707_i5 pivot_mem_707_i5 child_required_sub_707_i5 child_envelope_sub_707_i5 ?_
  intro b hb
  exact common_sub_707_i5 (mem_commonEnvelope childrenD_707_i5 b hb)
def required_707_i7 : Finset Cell := ⟨(([(4, 5), (5, 5), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_707_i7 : Finset Cell := ⟨(([(1, 6), (1, 7), (1, 8), (1, 9), (2, 6), (2, 7), (2, 8), (2, 9), (3, 6), (3, 7), (3, 8), (3, 9), (4, 1), (4, 2), (4, 3), (4, 5), (4, 7), (4, 8), (4, 9), (4, 10), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (10, 3), (10, 6), (10, 7), (10, 8), (11, 6), (11, 7), (11, 8), (12, 6), (12, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_707_i7 : Fin 7 → Finset Cell := ![(placed21 2 (6, 3) required_12), (placed21 2 (6, 3) required_13), (placed21 5 (8, 4) required_118), (placed21 6 (6, 10) required_369), (placed21 5 (8, 4) required_435), (placed21 0 (4, 1) required_528), (placed21 1 (1, 3) required_689)]
def childrenD_707_i7 : Fin 7 → Finset Cell := ![(placed21 2 (6, 3) envelope_12), (placed21 2 (6, 3) envelope_13), (placed21 5 (8, 4) envelope_118), (placed21 6 (6, 10) envelope_369), (placed21 5 (8, 4) envelope_435), (placed21 0 (4, 1) envelope_528), (placed21 1 (1, 3) envelope_689)]
theorem common_sub_707_i7 : commonEnvelope childrenD_707_i7 ⊆ insert (5, 7) required_707_i7 := by decide +kernel
theorem child_required_sub_707_i7 : ∀ j, childrenC_707_i7 j ⊆ insert (5, 7) required_707_i7 := by decide +kernel
theorem child_envelope_sub_707_i7 : ∀ j, childrenD_707_i7 j ⊆ envelope_707_i7 := by decide +kernel
theorem pivot_mem_707_i7 : (5, 7) ∈ envelope_707_i7 := by decide +kernel
theorem children_work_707_i7 : ∀ j, Template HasSnaky 11 (childrenC_707_i7 j) (childrenD_707_i7 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_12 2 (6, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_13 2 (6, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_118 5 (8, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_369 6 (6, 10)).mono (by decide +kernel)
  · exact (placed21_template row_works_435 5 (8, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_528 0 (4, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_689 1 (1, 3)).mono (by decide +kernel)
theorem row_works_707_i7 : Template HasSnaky 12 required_707_i7 envelope_707_i7 := by
  refine compose HasSnaky 11 childrenC_707_i7 childrenD_707_i7 children_work_707_i7 (5, 7)
    required_707_i7 envelope_707_i7 pivot_mem_707_i7 child_required_sub_707_i7 child_envelope_sub_707_i7 ?_
  intro b hb
  exact common_sub_707_i7 (mem_commonEnvelope childrenD_707_i7 b hb)
def required_707_i8 : Finset Cell := ⟨(([(4, 5), (5, 5), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_707_i8 : Finset Cell := ⟨(([(0, 7), (0, 9), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, 2), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (4, 2), (4, 3), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 8), (6, 9), (6, 10), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (9, 3), (9, 4), (9, 7), (9, 8), (9, 9), (10, 3), (10, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_707_i8 : Fin 6 → Finset Cell := ![(placed21 5 (8, 4) required_537), (placed21 4 (3, 9) required_537), (placed21 5 (7, 4) required_702), (placed21 4 (3, 8) required_702), (placed21 1 (0, 4) required_704), (placed21 0 (3, 1) required_704)]
def childrenD_707_i8 : Fin 6 → Finset Cell := ![(placed21 5 (8, 4) envelope_537), (placed21 4 (3, 9) envelope_537), (placed21 5 (7, 4) envelope_702), (placed21 4 (3, 8) envelope_702), (placed21 1 (0, 4) envelope_704), (placed21 0 (3, 1) envelope_704)]
theorem common_sub_707_i8 : commonEnvelope childrenD_707_i8 ⊆ insert (4, 6) required_707_i8 := by decide +kernel
theorem child_required_sub_707_i8 : ∀ j, childrenC_707_i8 j ⊆ insert (4, 6) required_707_i8 := by decide +kernel
theorem child_envelope_sub_707_i8 : ∀ j, childrenD_707_i8 j ⊆ envelope_707_i8 := by decide +kernel
theorem pivot_mem_707_i8 : (4, 6) ∈ envelope_707_i8 := by decide +kernel
theorem children_work_707_i8 : ∀ j, Template HasSnaky 10 (childrenC_707_i8 j) (childrenD_707_i8 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_537 5 (8, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_537 4 (3, 9)).mono (by decide +kernel)
  · exact (placed21_template row_works_702 5 (7, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_702 4 (3, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_704 1 (0, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_704 0 (3, 1)).mono (by decide +kernel)
theorem row_works_707_i8 : Template HasSnaky 11 required_707_i8 envelope_707_i8 := by
  refine compose HasSnaky 10 childrenC_707_i8 childrenD_707_i8 children_work_707_i8 (4, 6)
    required_707_i8 envelope_707_i8 pivot_mem_707_i8 child_required_sub_707_i8 child_envelope_sub_707_i8 ?_
  intro b hb
  exact common_sub_707_i8 (mem_commonEnvelope childrenD_707_i8 b hb)
def required_707 : Finset Cell := ⟨(([(4, 5), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_707 : Finset Cell := ⟨(([(0, 5), (0, 6), (0, 7), (0, 9), (1, 2), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, 2), (3, 3), (3, 4), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (4, 1), (4, 2), (4, 3), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (11, 2), (11, 3), (11, 4), (11, 5), (11, 6), (11, 7), (11, 8), (12, 2), (12, 3), (12, 4), (12, 5), (12, 6), (12, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_707 : Fin 13 → Finset Cell := ![(placed21 0 (4, 1) required_459), (placed21 4 (3, 10) required_535), (placed21 0 (1, 1) required_617), (placed21 1 (0, 1) required_660), (placed21 1 (0, 3) required_663), required_707_i0, required_707_i1, required_707_i3, required_707_i5, required_707_i7, required_707_i8, (placed21 4 (2, 10) required_705), (placed21 4 (0, 10) required_706)]
def childrenD_707 : Fin 13 → Finset Cell := ![(placed21 0 (4, 1) envelope_459), (placed21 4 (3, 10) envelope_535), (placed21 0 (1, 1) envelope_617), (placed21 1 (0, 1) envelope_660), (placed21 1 (0, 3) envelope_663), envelope_707_i0, envelope_707_i1, envelope_707_i3, envelope_707_i5, envelope_707_i7, envelope_707_i8, (placed21 4 (2, 10) envelope_705), (placed21 4 (0, 10) envelope_706)]
theorem common_sub_707 : commonEnvelope childrenD_707 ⊆ insert (5, 6) required_707 := by decide +kernel
theorem child_required_sub_707 : ∀ j, childrenC_707 j ⊆ insert (5, 6) required_707 := by decide +kernel
theorem child_envelope_sub_707 : ∀ j, childrenD_707 j ⊆ envelope_707 := by decide +kernel
theorem pivot_mem_707 : (5, 6) ∈ envelope_707 := by decide +kernel
theorem children_work_707 : ∀ j, Template HasSnaky 16 (childrenC_707 j) (childrenD_707 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_459 0 (4, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_535 4 (3, 10)).mono (by decide +kernel)
  · exact (placed21_template row_works_617 0 (1, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_660 1 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_663 1 (0, 3)).mono (by decide +kernel)
  · exact row_works_707_i0.mono (by decide +kernel)
  · exact row_works_707_i1.mono (by decide +kernel)
  · exact row_works_707_i3.mono (by decide +kernel)
  · exact row_works_707_i5.mono (by decide +kernel)
  · exact row_works_707_i7.mono (by decide +kernel)
  · exact row_works_707_i8.mono (by decide +kernel)
  · exact (placed21_template row_works_705 4 (2, 10)).mono (by decide +kernel)
  · exact (placed21_template row_works_706 4 (0, 10)).mono (by decide +kernel)
theorem row_works_707 : Template HasSnaky 17 required_707 envelope_707 := by
  refine compose HasSnaky 16 childrenC_707 childrenD_707 children_work_707 (5, 6)
    required_707 envelope_707 pivot_mem_707 child_required_sub_707 child_envelope_sub_707 ?_
  intro b hb
  exact common_sub_707 (mem_commonEnvelope childrenD_707 b hb)
def height_707_i0 : ℕ := 10
def childrenH_707_i0 : Fin 7 → ℕ := ![height_116, height_134, height_180, height_337, height_435, height_558, height_662]
theorem height_exact_707_i0 : height_707_i0 = 1 + Finset.univ.sup childrenH_707_i0 := by decide +kernel
theorem required_origin_707_i0 : ∀ x ∈ required_707_i0,
    (∃ j, x ∈ childrenC_707_i0 j) ∨ ∀ j, x ∈ childrenD_707_i0 j := by decide +kernel
theorem required_exact_707_i0 : required_707_i0 =
    ((Finset.univ.biUnion childrenC_707_i0) ∪ commonEnvelope childrenD_707_i0).erase (5, 7) := by
  exact required_eq_combination childrenC_707_i0 childrenD_707_i0 (5, 7) required_707_i0
    (by decide +kernel) child_required_sub_707_i0 common_sub_707_i0 required_origin_707_i0
theorem envelope_origin_707_i0 : ∀ x ∈ envelope_707_i0,
    x = (5, 7) ∨ ∃ j, x ∈ childrenD_707_i0 j := by decide +kernel
theorem envelope_exact_707_i0 : envelope_707_i0 =
    insert (5, 7) (Finset.univ.biUnion childrenD_707_i0) := by
  exact envelope_eq_combination childrenD_707_i0 (5, 7) envelope_707_i0
    pivot_mem_707_i0 child_envelope_sub_707_i0 envelope_origin_707_i0
def checked_707_i0 : CheckedCard where
  required := required_707_i0
  envelope := envelope_707_i0
  height := height_707_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_707_i0
def height_707_i2 : ℕ := 10
def childrenH_707_i2 : Fin 3 → ℕ := ![height_7, height_9, height_380]
theorem height_exact_707_i2 : height_707_i2 = 1 + Finset.univ.sup childrenH_707_i2 := by decide +kernel
theorem required_origin_707_i2 : ∀ x ∈ required_707_i2,
    (∃ j, x ∈ childrenC_707_i2 j) ∨ ∀ j, x ∈ childrenD_707_i2 j := by decide +kernel
theorem required_exact_707_i2 : required_707_i2 =
    ((Finset.univ.biUnion childrenC_707_i2) ∪ commonEnvelope childrenD_707_i2).erase (5, 7) := by
  exact required_eq_combination childrenC_707_i2 childrenD_707_i2 (5, 7) required_707_i2
    (by decide +kernel) child_required_sub_707_i2 common_sub_707_i2 required_origin_707_i2
theorem envelope_origin_707_i2 : ∀ x ∈ envelope_707_i2,
    x = (5, 7) ∨ ∃ j, x ∈ childrenD_707_i2 j := by decide +kernel
theorem envelope_exact_707_i2 : envelope_707_i2 =
    insert (5, 7) (Finset.univ.biUnion childrenD_707_i2) := by
  exact envelope_eq_combination childrenD_707_i2 (5, 7) envelope_707_i2
    pivot_mem_707_i2 child_envelope_sub_707_i2 envelope_origin_707_i2
def checked_707_i2 : CheckedCard where
  required := required_707_i2
  envelope := envelope_707_i2
  height := height_707_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_707_i2
def height_707_i1 : ℕ := 11
def childrenH_707_i1 : Fin 4 → ℕ := ![height_14, height_33, height_322, height_707_i2]
theorem height_exact_707_i1 : height_707_i1 = 1 + Finset.univ.sup childrenH_707_i1 := by decide +kernel
theorem required_origin_707_i1 : ∀ x ∈ required_707_i1,
    (∃ j, x ∈ childrenC_707_i1 j) ∨ ∀ j, x ∈ childrenD_707_i1 j := by decide +kernel
theorem required_exact_707_i1 : required_707_i1 =
    ((Finset.univ.biUnion childrenC_707_i1) ∪ commonEnvelope childrenD_707_i1).erase (5, 4) := by
  exact required_eq_combination childrenC_707_i1 childrenD_707_i1 (5, 4) required_707_i1
    (by decide +kernel) child_required_sub_707_i1 common_sub_707_i1 required_origin_707_i1
theorem envelope_origin_707_i1 : ∀ x ∈ envelope_707_i1,
    x = (5, 4) ∨ ∃ j, x ∈ childrenD_707_i1 j := by decide +kernel
theorem envelope_exact_707_i1 : envelope_707_i1 =
    insert (5, 4) (Finset.univ.biUnion childrenD_707_i1) := by
  exact envelope_eq_combination childrenD_707_i1 (5, 4) envelope_707_i1
    pivot_mem_707_i1 child_envelope_sub_707_i1 envelope_origin_707_i1
def checked_707_i1 : CheckedCard where
  required := required_707_i1
  envelope := envelope_707_i1
  height := height_707_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_707_i1
def height_707_i4 : ℕ := 13
def childrenH_707_i4 : Fin 4 → ℕ := ![height_7, height_8, height_9, height_485]
theorem height_exact_707_i4 : height_707_i4 = 1 + Finset.univ.sup childrenH_707_i4 := by decide +kernel
theorem required_origin_707_i4 : ∀ x ∈ required_707_i4,
    (∃ j, x ∈ childrenC_707_i4 j) ∨ ∀ j, x ∈ childrenD_707_i4 j := by decide +kernel
theorem required_exact_707_i4 : required_707_i4 =
    ((Finset.univ.biUnion childrenC_707_i4) ∪ commonEnvelope childrenD_707_i4).erase (5, 7) := by
  exact required_eq_combination childrenC_707_i4 childrenD_707_i4 (5, 7) required_707_i4
    (by decide +kernel) child_required_sub_707_i4 common_sub_707_i4 required_origin_707_i4
theorem envelope_origin_707_i4 : ∀ x ∈ envelope_707_i4,
    x = (5, 7) ∨ ∃ j, x ∈ childrenD_707_i4 j := by decide +kernel
theorem envelope_exact_707_i4 : envelope_707_i4 =
    insert (5, 7) (Finset.univ.biUnion childrenD_707_i4) := by
  exact envelope_eq_combination childrenD_707_i4 (5, 7) envelope_707_i4
    pivot_mem_707_i4 child_envelope_sub_707_i4 envelope_origin_707_i4
def checked_707_i4 : CheckedCard where
  required := required_707_i4
  envelope := envelope_707_i4
  height := height_707_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_707_i4
def height_707_i3 : ℕ := 14
def childrenH_707_i3 : Fin 5 → ℕ := ![height_136, height_267, height_322, height_322, height_707_i4]
theorem height_exact_707_i3 : height_707_i3 = 1 + Finset.univ.sup childrenH_707_i3 := by decide +kernel
theorem required_origin_707_i3 : ∀ x ∈ required_707_i3,
    (∃ j, x ∈ childrenC_707_i3 j) ∨ ∀ j, x ∈ childrenD_707_i3 j := by decide +kernel
theorem required_exact_707_i3 : required_707_i3 =
    ((Finset.univ.biUnion childrenC_707_i3) ∪ commonEnvelope childrenD_707_i3).erase (5, 4) := by
  exact required_eq_combination childrenC_707_i3 childrenD_707_i3 (5, 4) required_707_i3
    (by decide +kernel) child_required_sub_707_i3 common_sub_707_i3 required_origin_707_i3
theorem envelope_origin_707_i3 : ∀ x ∈ envelope_707_i3,
    x = (5, 4) ∨ ∃ j, x ∈ childrenD_707_i3 j := by decide +kernel
theorem envelope_exact_707_i3 : envelope_707_i3 =
    insert (5, 4) (Finset.univ.biUnion childrenD_707_i3) := by
  exact envelope_eq_combination childrenD_707_i3 (5, 4) envelope_707_i3
    pivot_mem_707_i3 child_envelope_sub_707_i3 envelope_origin_707_i3
def checked_707_i3 : CheckedCard where
  required := required_707_i3
  envelope := envelope_707_i3
  height := height_707_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_707_i3
def height_707_i6 : ℕ := 7
def childrenH_707_i6 : Fin 4 → ℕ := ![height_9, height_115, height_302, height_303]
theorem height_exact_707_i6 : height_707_i6 = 1 + Finset.univ.sup childrenH_707_i6 := by decide +kernel
theorem required_origin_707_i6 : ∀ x ∈ required_707_i6,
    (∃ j, x ∈ childrenC_707_i6 j) ∨ ∀ j, x ∈ childrenD_707_i6 j := by decide +kernel
theorem required_exact_707_i6 : required_707_i6 =
    ((Finset.univ.biUnion childrenC_707_i6) ∪ commonEnvelope childrenD_707_i6).erase (5, 7) := by
  exact required_eq_combination childrenC_707_i6 childrenD_707_i6 (5, 7) required_707_i6
    (by decide +kernel) child_required_sub_707_i6 common_sub_707_i6 required_origin_707_i6
theorem envelope_origin_707_i6 : ∀ x ∈ envelope_707_i6,
    x = (5, 7) ∨ ∃ j, x ∈ childrenD_707_i6 j := by decide +kernel
theorem envelope_exact_707_i6 : envelope_707_i6 =
    insert (5, 7) (Finset.univ.biUnion childrenD_707_i6) := by
  exact envelope_eq_combination childrenD_707_i6 (5, 7) envelope_707_i6
    pivot_mem_707_i6 child_envelope_sub_707_i6 envelope_origin_707_i6
def checked_707_i6 : CheckedCard where
  required := required_707_i6
  envelope := envelope_707_i6
  height := height_707_i6
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_707_i6
def height_707_i5 : ℕ := 8
def childrenH_707_i5 : Fin 4 → ℕ := ![height_13, height_14, height_332, height_707_i6]
theorem height_exact_707_i5 : height_707_i5 = 1 + Finset.univ.sup childrenH_707_i5 := by decide +kernel
theorem required_origin_707_i5 : ∀ x ∈ required_707_i5,
    (∃ j, x ∈ childrenC_707_i5 j) ∨ ∀ j, x ∈ childrenD_707_i5 j := by decide +kernel
theorem required_exact_707_i5 : required_707_i5 =
    ((Finset.univ.biUnion childrenC_707_i5) ∪ commonEnvelope childrenD_707_i5).erase (5, 4) := by
  exact required_eq_combination childrenC_707_i5 childrenD_707_i5 (5, 4) required_707_i5
    (by decide +kernel) child_required_sub_707_i5 common_sub_707_i5 required_origin_707_i5
theorem envelope_origin_707_i5 : ∀ x ∈ envelope_707_i5,
    x = (5, 4) ∨ ∃ j, x ∈ childrenD_707_i5 j := by decide +kernel
theorem envelope_exact_707_i5 : envelope_707_i5 =
    insert (5, 4) (Finset.univ.biUnion childrenD_707_i5) := by
  exact envelope_eq_combination childrenD_707_i5 (5, 4) envelope_707_i5
    pivot_mem_707_i5 child_envelope_sub_707_i5 envelope_origin_707_i5
def checked_707_i5 : CheckedCard where
  required := required_707_i5
  envelope := envelope_707_i5
  height := height_707_i5
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_707_i5
def height_707_i7 : ℕ := 12
def childrenH_707_i7 : Fin 7 → ℕ := ![height_12, height_13, height_118, height_369, height_435, height_528, height_689]
theorem height_exact_707_i7 : height_707_i7 = 1 + Finset.univ.sup childrenH_707_i7 := by decide +kernel
theorem required_origin_707_i7 : ∀ x ∈ required_707_i7,
    (∃ j, x ∈ childrenC_707_i7 j) ∨ ∀ j, x ∈ childrenD_707_i7 j := by decide +kernel
theorem required_exact_707_i7 : required_707_i7 =
    ((Finset.univ.biUnion childrenC_707_i7) ∪ commonEnvelope childrenD_707_i7).erase (5, 7) := by
  exact required_eq_combination childrenC_707_i7 childrenD_707_i7 (5, 7) required_707_i7
    (by decide +kernel) child_required_sub_707_i7 common_sub_707_i7 required_origin_707_i7
theorem envelope_origin_707_i7 : ∀ x ∈ envelope_707_i7,
    x = (5, 7) ∨ ∃ j, x ∈ childrenD_707_i7 j := by decide +kernel
theorem envelope_exact_707_i7 : envelope_707_i7 =
    insert (5, 7) (Finset.univ.biUnion childrenD_707_i7) := by
  exact envelope_eq_combination childrenD_707_i7 (5, 7) envelope_707_i7
    pivot_mem_707_i7 child_envelope_sub_707_i7 envelope_origin_707_i7
def checked_707_i7 : CheckedCard where
  required := required_707_i7
  envelope := envelope_707_i7
  height := height_707_i7
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_707_i7
def height_707_i8 : ℕ := 11
def childrenH_707_i8 : Fin 6 → ℕ := ![height_537, height_537, height_702, height_702, height_704, height_704]
theorem height_exact_707_i8 : height_707_i8 = 1 + Finset.univ.sup childrenH_707_i8 := by decide +kernel
theorem required_origin_707_i8 : ∀ x ∈ required_707_i8,
    (∃ j, x ∈ childrenC_707_i8 j) ∨ ∀ j, x ∈ childrenD_707_i8 j := by decide +kernel
theorem required_exact_707_i8 : required_707_i8 =
    ((Finset.univ.biUnion childrenC_707_i8) ∪ commonEnvelope childrenD_707_i8).erase (4, 6) := by
  exact required_eq_combination childrenC_707_i8 childrenD_707_i8 (4, 6) required_707_i8
    (by decide +kernel) child_required_sub_707_i8 common_sub_707_i8 required_origin_707_i8
theorem envelope_origin_707_i8 : ∀ x ∈ envelope_707_i8,
    x = (4, 6) ∨ ∃ j, x ∈ childrenD_707_i8 j := by decide +kernel
theorem envelope_exact_707_i8 : envelope_707_i8 =
    insert (4, 6) (Finset.univ.biUnion childrenD_707_i8) := by
  exact envelope_eq_combination childrenD_707_i8 (4, 6) envelope_707_i8
    pivot_mem_707_i8 child_envelope_sub_707_i8 envelope_origin_707_i8
def checked_707_i8 : CheckedCard where
  required := required_707_i8
  envelope := envelope_707_i8
  height := height_707_i8
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_707_i8
def height_707 : ℕ := 17
def childrenH_707 : Fin 13 → ℕ := ![height_459, height_535, height_617, height_660, height_663, height_707_i0, height_707_i1, height_707_i3, height_707_i5, height_707_i7, height_707_i8, height_705, height_706]
theorem height_exact_707 : height_707 = 1 + Finset.univ.sup childrenH_707 := by decide +kernel
theorem required_origin_707 : ∀ x ∈ required_707,
    (∃ j, x ∈ childrenC_707 j) ∨ ∀ j, x ∈ childrenD_707 j := by decide +kernel
theorem required_exact_707 : required_707 =
    ((Finset.univ.biUnion childrenC_707) ∪ commonEnvelope childrenD_707).erase (5, 6) := by
  exact required_eq_combination childrenC_707 childrenD_707 (5, 6) required_707
    (by decide +kernel) child_required_sub_707 common_sub_707 required_origin_707
theorem envelope_origin_707 : ∀ x ∈ envelope_707,
    x = (5, 6) ∨ ∃ j, x ∈ childrenD_707 j := by decide +kernel
theorem envelope_exact_707 : envelope_707 =
    insert (5, 6) (Finset.univ.biUnion childrenD_707) := by
  exact envelope_eq_combination childrenD_707 (5, 6) envelope_707
    pivot_mem_707 child_envelope_sub_707 envelope_origin_707
def checked_707 : CheckedCard where
  required := required_707
  envelope := envelope_707
  height := height_707
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_707
end SnakyPrototype.Certificate21

end OAI
