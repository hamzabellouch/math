import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part06
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height10Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height10Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height10Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height11Part04
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_599_i6 : Finset Cell := ⟨(([(2, 5), (3, 5), (4, 3), (4, 5), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_599_i6 : Finset Cell := ⟨(([(2, 5), (3, 5), (4, 2), (4, 3), (4, 4), (4, 5), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_599_i6 : Fin 2 → Finset Cell := ![(placed21 0 (2, 5) required_5), (placed21 0 (4, 2) required_64)]
def childrenD_599_i6 : Fin 2 → Finset Cell := ![(placed21 0 (2, 5) envelope_5), (placed21 0 (4, 2) envelope_64)]
theorem common_sub_599_i6 : commonEnvelope childrenD_599_i6 ⊆ insert (5, 6) required_599_i6 := by decide +kernel
theorem child_required_sub_599_i6 : ∀ j, childrenC_599_i6 j ⊆ insert (5, 6) required_599_i6 := by decide +kernel
theorem child_envelope_sub_599_i6 : ∀ j, childrenD_599_i6 j ⊆ envelope_599_i6 := by decide +kernel
theorem pivot_mem_599_i6 : (5, 6) ∈ envelope_599_i6 := by decide +kernel
theorem children_work_599_i6 : ∀ j, Template HasSnaky 3 (childrenC_599_i6 j) (childrenD_599_i6 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 0 (2, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_64 0 (4, 2)).mono (by decide +kernel)
theorem row_works_599_i6 : Template HasSnaky 4 required_599_i6 envelope_599_i6 := by
  refine compose HasSnaky 3 childrenC_599_i6 childrenD_599_i6 children_work_599_i6 (5, 6)
    required_599_i6 envelope_599_i6 pivot_mem_599_i6 child_required_sub_599_i6 child_envelope_sub_599_i6 ?_
  intro b hb
  exact common_sub_599_i6 (mem_commonEnvelope childrenD_599_i6 b hb)
def required_599_i8 : Finset Cell := ⟨(([(3, 4), (4, 3), (4, 5), (5, 5), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_599_i8 : Finset Cell := ⟨(([(3, 4), (4, 2), (4, 3), (4, 4), (4, 5), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 5), (7, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_599_i8 : Fin 2 → Finset Cell := ![(placed21 6 (7, 5) required_0), (placed21 0 (4, 2) required_44)]
def childrenD_599_i8 : Fin 2 → Finset Cell := ![(placed21 6 (7, 5) envelope_0), (placed21 0 (4, 2) envelope_44)]
theorem common_sub_599_i8 : commonEnvelope childrenD_599_i8 ⊆ insert (4, 4) required_599_i8 := by decide +kernel
theorem child_required_sub_599_i8 : ∀ j, childrenC_599_i8 j ⊆ insert (4, 4) required_599_i8 := by decide +kernel
theorem child_envelope_sub_599_i8 : ∀ j, childrenD_599_i8 j ⊆ envelope_599_i8 := by decide +kernel
theorem pivot_mem_599_i8 : (4, 4) ∈ envelope_599_i8 := by decide +kernel
theorem children_work_599_i8 : ∀ j, Template HasSnaky 3 (childrenC_599_i8 j) (childrenD_599_i8 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 6 (7, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_44 0 (4, 2)).mono (by decide +kernel)
theorem row_works_599_i8 : Template HasSnaky 4 required_599_i8 envelope_599_i8 := by
  refine compose HasSnaky 3 childrenC_599_i8 childrenD_599_i8 children_work_599_i8 (4, 4)
    required_599_i8 envelope_599_i8 pivot_mem_599_i8 child_required_sub_599_i8 child_envelope_sub_599_i8 ?_
  intro b hb
  exact common_sub_599_i8 (mem_commonEnvelope childrenD_599_i8 b hb)
def required_599_i7 : Finset Cell := ⟨(([(2, 5), (3, 4), (3, 5), (4, 3), (4, 5), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_599_i7 : Finset Cell := ⟨(([(2, 5), (3, 4), (3, 5), (4, 2), (4, 3), (4, 4), (4, 5), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 4), (6, 5), (7, 4), (7, 5), (8, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_599_i7 : Fin 3 → Finset Cell := ![(placed21 3 (2, 5) required_6), (placed21 3 (3, 5) required_16), required_599_i8]
def childrenD_599_i7 : Fin 3 → Finset Cell := ![(placed21 3 (2, 5) envelope_6), (placed21 3 (3, 5) envelope_16), envelope_599_i8]
theorem common_sub_599_i7 : commonEnvelope childrenD_599_i7 ⊆ insert (6, 5) required_599_i7 := by decide +kernel
theorem child_required_sub_599_i7 : ∀ j, childrenC_599_i7 j ⊆ insert (6, 5) required_599_i7 := by decide +kernel
theorem child_envelope_sub_599_i7 : ∀ j, childrenD_599_i7 j ⊆ envelope_599_i7 := by decide +kernel
theorem pivot_mem_599_i7 : (6, 5) ∈ envelope_599_i7 := by decide +kernel
theorem children_work_599_i7 : ∀ j, Template HasSnaky 4 (childrenC_599_i7 j) (childrenD_599_i7 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_6 3 (2, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_16 3 (3, 5)).mono (by decide +kernel)
  · exact row_works_599_i8.mono (by decide +kernel)
theorem row_works_599_i7 : Template HasSnaky 5 required_599_i7 envelope_599_i7 := by
  refine compose HasSnaky 4 childrenC_599_i7 childrenD_599_i7 children_work_599_i7 (6, 5)
    required_599_i7 envelope_599_i7 pivot_mem_599_i7 child_required_sub_599_i7 child_envelope_sub_599_i7 ?_
  intro b hb
  exact common_sub_599_i7 (mem_commonEnvelope childrenD_599_i7 b hb)
def required_599_i5 : Finset Cell := ⟨(([(2, 5), (3, 4), (3, 5), (4, 3), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_599_i5 : Finset Cell := ⟨(([(2, 5), (3, 4), (3, 5), (4, 2), (4, 3), (4, 4), (4, 5), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 4), (6, 5), (6, 6), (7, 4), (7, 5), (7, 6), (8, 4), (8, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_599_i5 : Fin 5 → Finset Cell := ![(placed21 0 (2, 4) required_8), (placed21 1 (2, 4) required_17), (placed21 1 (2, 4) required_41), required_599_i6, required_599_i7]
def childrenD_599_i5 : Fin 5 → Finset Cell := ![(placed21 0 (2, 4) envelope_8), (placed21 1 (2, 4) envelope_17), (placed21 1 (2, 4) envelope_41), envelope_599_i6, envelope_599_i7]
theorem common_sub_599_i5 : commonEnvelope childrenD_599_i5 ⊆ insert (5, 5) required_599_i5 := by decide +kernel
theorem child_required_sub_599_i5 : ∀ j, childrenC_599_i5 j ⊆ insert (5, 5) required_599_i5 := by decide +kernel
theorem child_envelope_sub_599_i5 : ∀ j, childrenD_599_i5 j ⊆ envelope_599_i5 := by decide +kernel
theorem pivot_mem_599_i5 : (5, 5) ∈ envelope_599_i5 := by decide +kernel
theorem children_work_599_i5 : ∀ j, Template HasSnaky 5 (childrenC_599_i5 j) (childrenD_599_i5 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_8 0 (2, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_17 1 (2, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_41 1 (2, 4)).mono (by decide +kernel)
  · exact row_works_599_i6.mono (by decide +kernel)
  · exact row_works_599_i7.mono (by decide +kernel)
theorem row_works_599_i5 : Template HasSnaky 6 required_599_i5 envelope_599_i5 := by
  refine compose HasSnaky 5 childrenC_599_i5 childrenD_599_i5 children_work_599_i5 (5, 5)
    required_599_i5 envelope_599_i5 pivot_mem_599_i5 child_required_sub_599_i5 child_envelope_sub_599_i5 ?_
  intro b hb
  exact common_sub_599_i5 (mem_commonEnvelope childrenD_599_i5 b hb)
def required_599_i4 : Finset Cell := ⟨(([(3, 2), (3, 3), (3, 4), (3, 5), (4, 3), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_599_i4 : Finset Cell := ⟨(([(2, 5), (2, 6), (3, 2), (3, 3), (3, 4), (3, 5), (4, 2), (4, 3), (4, 4), (4, 5), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 4), (6, 5), (6, 6), (7, 4), (7, 5), (7, 6), (8, 4), (8, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_599_i4 : Fin 2 → Finset Cell := ![(placed21 5 (3, 2) required_5), required_599_i5]
def childrenD_599_i4 : Fin 2 → Finset Cell := ![(placed21 5 (3, 2) envelope_5), envelope_599_i5]
theorem common_sub_599_i4 : commonEnvelope childrenD_599_i4 ⊆ insert (2, 5) required_599_i4 := by decide +kernel
theorem child_required_sub_599_i4 : ∀ j, childrenC_599_i4 j ⊆ insert (2, 5) required_599_i4 := by decide +kernel
theorem child_envelope_sub_599_i4 : ∀ j, childrenD_599_i4 j ⊆ envelope_599_i4 := by decide +kernel
theorem pivot_mem_599_i4 : (2, 5) ∈ envelope_599_i4 := by decide +kernel
theorem children_work_599_i4 : ∀ j, Template HasSnaky 6 (childrenC_599_i4 j) (childrenD_599_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 5 (3, 2)).mono (by decide +kernel)
  · exact row_works_599_i5.mono (by decide +kernel)
theorem row_works_599_i4 : Template HasSnaky 7 required_599_i4 envelope_599_i4 := by
  refine compose HasSnaky 6 childrenC_599_i4 childrenD_599_i4 children_work_599_i4 (2, 5)
    required_599_i4 envelope_599_i4 pivot_mem_599_i4 child_required_sub_599_i4 child_envelope_sub_599_i4 ?_
  intro b hb
  exact common_sub_599_i4 (mem_commonEnvelope childrenD_599_i4 b hb)
def required_599_i3 : Finset Cell := ⟨(([(3, 2), (3, 3), (3, 4), (3, 5), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_599_i3 : Finset Cell := ⟨(([(2, 5), (2, 6), (3, 2), (3, 3), (3, 4), (3, 5), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 4), (6, 5), (6, 6), (7, 4), (7, 5), (7, 6), (8, 4), (8, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_599_i3 : Fin 2 → Finset Cell := ![(placed21 1 (3, 2) required_5), required_599_i4]
def childrenD_599_i3 : Fin 2 → Finset Cell := ![(placed21 1 (3, 2) envelope_5), envelope_599_i4]
theorem common_sub_599_i3 : commonEnvelope childrenD_599_i3 ⊆ insert (4, 5) required_599_i3 := by decide +kernel
theorem child_required_sub_599_i3 : ∀ j, childrenC_599_i3 j ⊆ insert (4, 5) required_599_i3 := by decide +kernel
theorem child_envelope_sub_599_i3 : ∀ j, childrenD_599_i3 j ⊆ envelope_599_i3 := by decide +kernel
theorem pivot_mem_599_i3 : (4, 5) ∈ envelope_599_i3 := by decide +kernel
theorem children_work_599_i3 : ∀ j, Template HasSnaky 7 (childrenC_599_i3 j) (childrenD_599_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 1 (3, 2)).mono (by decide +kernel)
  · exact row_works_599_i4.mono (by decide +kernel)
theorem row_works_599_i3 : Template HasSnaky 8 required_599_i3 envelope_599_i3 := by
  refine compose HasSnaky 7 childrenC_599_i3 childrenD_599_i3 children_work_599_i3 (4, 5)
    required_599_i3 envelope_599_i3 pivot_mem_599_i3 child_required_sub_599_i3 child_envelope_sub_599_i3 ?_
  intro b hb
  exact common_sub_599_i3 (mem_commonEnvelope childrenD_599_i3 b hb)
def required_599_i2 : Finset Cell := ⟨(([(0, 1), (1, 1), (3, 3), (3, 4), (3, 5), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_599_i2 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 0), (2, 1), (2, 2), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 4), (6, 5), (6, 6), (7, 4), (7, 5), (7, 6), (8, 4), (8, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_599_i2 : Fin 3 → Finset Cell := ![(placed21 6 (4, 6) required_9), (placed21 7 (4, 5) required_251), required_599_i3]
def childrenD_599_i2 : Fin 3 → Finset Cell := ![(placed21 6 (4, 6) envelope_9), (placed21 7 (4, 5) envelope_251), envelope_599_i3]
theorem common_sub_599_i2 : commonEnvelope childrenD_599_i2 ⊆ insert (3, 2) required_599_i2 := by decide +kernel
theorem child_required_sub_599_i2 : ∀ j, childrenC_599_i2 j ⊆ insert (3, 2) required_599_i2 := by decide +kernel
theorem child_envelope_sub_599_i2 : ∀ j, childrenD_599_i2 j ⊆ envelope_599_i2 := by decide +kernel
theorem pivot_mem_599_i2 : (3, 2) ∈ envelope_599_i2 := by decide +kernel
theorem children_work_599_i2 : ∀ j, Template HasSnaky 8 (childrenC_599_i2 j) (childrenD_599_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_9 6 (4, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_251 7 (4, 5)).mono (by decide +kernel)
  · exact row_works_599_i3.mono (by decide +kernel)
theorem row_works_599_i2 : Template HasSnaky 9 required_599_i2 envelope_599_i2 := by
  refine compose HasSnaky 8 childrenC_599_i2 childrenD_599_i2 children_work_599_i2 (3, 2)
    required_599_i2 envelope_599_i2 pivot_mem_599_i2 child_required_sub_599_i2 child_envelope_sub_599_i2 ?_
  intro b hb
  exact common_sub_599_i2 (mem_commonEnvelope childrenD_599_i2 b hb)
def required_599_i1 : Finset Cell := ⟨(([(0, 1), (1, 1), (3, 3), (3, 4), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_599_i1 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 0), (2, 1), (2, 2), (2, 5), (2, 6), (2, 7), (2, 8), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 4), (6, 5), (6, 6), (7, 4), (7, 5), (7, 6), (8, 4), (8, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_599_i1 : Fin 5 → Finset Cell := ![(placed21 2 (4, 2) required_10), (placed21 0 (3, 2) required_27), (placed21 2 (4, 2) required_48), (placed21 2 (4, 2) required_63), required_599_i2]
def childrenD_599_i1 : Fin 5 → Finset Cell := ![(placed21 2 (4, 2) envelope_10), (placed21 0 (3, 2) envelope_27), (placed21 2 (4, 2) envelope_48), (placed21 2 (4, 2) envelope_63), envelope_599_i2]
theorem common_sub_599_i1 : commonEnvelope childrenD_599_i1 ⊆ insert (3, 5) required_599_i1 := by decide +kernel
theorem child_required_sub_599_i1 : ∀ j, childrenC_599_i1 j ⊆ insert (3, 5) required_599_i1 := by decide +kernel
theorem child_envelope_sub_599_i1 : ∀ j, childrenD_599_i1 j ⊆ envelope_599_i1 := by decide +kernel
theorem pivot_mem_599_i1 : (3, 5) ∈ envelope_599_i1 := by decide +kernel
theorem children_work_599_i1 : ∀ j, Template HasSnaky 9 (childrenC_599_i1 j) (childrenD_599_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_10 2 (4, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_27 0 (3, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_48 2 (4, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_63 2 (4, 2)).mono (by decide +kernel)
  · exact row_works_599_i2.mono (by decide +kernel)
theorem row_works_599_i1 : Template HasSnaky 10 required_599_i1 envelope_599_i1 := by
  refine compose HasSnaky 9 childrenC_599_i1 childrenD_599_i1 children_work_599_i1 (3, 5)
    required_599_i1 envelope_599_i1 pivot_mem_599_i1 child_required_sub_599_i1 child_envelope_sub_599_i1 ?_
  intro b hb
  exact common_sub_599_i1 (mem_commonEnvelope childrenD_599_i1 b hb)
def required_599_i0 : Finset Cell := ⟨(([(0, 1), (0, 4), (1, 1), (1, 4), (3, 3), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_599_i0 : Finset Cell := ⟨(([(0, 1), (0, 4), (1, 1), (1, 4), (2, 0), (2, 1), (2, 2), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 4), (6, 5), (6, 6), (7, 4), (7, 5), (7, 6), (8, 4), (8, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_599_i0 : Fin 2 → Finset Cell := ![(placed21 4 (0, 4) required_2), required_599_i1]
def childrenD_599_i0 : Fin 2 → Finset Cell := ![(placed21 4 (0, 4) envelope_2), envelope_599_i1]
theorem common_sub_599_i0 : commonEnvelope childrenD_599_i0 ⊆ insert (3, 4) required_599_i0 := by decide +kernel
theorem child_required_sub_599_i0 : ∀ j, childrenC_599_i0 j ⊆ insert (3, 4) required_599_i0 := by decide +kernel
theorem child_envelope_sub_599_i0 : ∀ j, childrenD_599_i0 j ⊆ envelope_599_i0 := by decide +kernel
theorem pivot_mem_599_i0 : (3, 4) ∈ envelope_599_i0 := by decide +kernel
theorem children_work_599_i0 : ∀ j, Template HasSnaky 10 (childrenC_599_i0 j) (childrenD_599_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_2 4 (0, 4)).mono (by decide +kernel)
  · exact row_works_599_i1.mono (by decide +kernel)
theorem row_works_599_i0 : Template HasSnaky 11 required_599_i0 envelope_599_i0 := by
  refine compose HasSnaky 10 childrenC_599_i0 childrenD_599_i0 children_work_599_i0 (3, 4)
    required_599_i0 envelope_599_i0 pivot_mem_599_i0 child_required_sub_599_i0 child_envelope_sub_599_i0 ?_
  intro b hb
  exact common_sub_599_i0 (mem_commonEnvelope childrenD_599_i0 b hb)
def required_599 : Finset Cell := ⟨(([(0, 1), (0, 4), (1, 1), (1, 4), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_599 : Finset Cell := ⟨(([(0, 1), (0, 4), (1, 1), (1, 3), (1, 4), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (8, 4), (8, 5), (8, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_599 : Fin 4 → Finset Cell := ![(placed21 3 (0, 4) required_107), (placed21 3 (0, 4) required_163), (placed21 4 (0, 7) required_401), required_599_i0]
def childrenD_599 : Fin 4 → Finset Cell := ![(placed21 3 (0, 4) envelope_107), (placed21 3 (0, 4) envelope_163), (placed21 4 (0, 7) envelope_401), envelope_599_i0]
theorem common_sub_599 : commonEnvelope childrenD_599 ⊆ insert (4, 3) required_599 := by decide +kernel
theorem child_required_sub_599 : ∀ j, childrenC_599 j ⊆ insert (4, 3) required_599 := by decide +kernel
theorem child_envelope_sub_599 : ∀ j, childrenD_599 j ⊆ envelope_599 := by decide +kernel
theorem pivot_mem_599 : (4, 3) ∈ envelope_599 := by decide +kernel
theorem children_work_599 : ∀ j, Template HasSnaky 11 (childrenC_599 j) (childrenD_599 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_107 3 (0, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_163 3 (0, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_401 4 (0, 7)).mono (by decide +kernel)
  · exact row_works_599_i0.mono (by decide +kernel)
theorem row_works_599 : Template HasSnaky 12 required_599 envelope_599 := by
  refine compose HasSnaky 11 childrenC_599 childrenD_599 children_work_599 (4, 3)
    required_599 envelope_599 pivot_mem_599 child_required_sub_599 child_envelope_sub_599 ?_
  intro b hb
  exact common_sub_599 (mem_commonEnvelope childrenD_599 b hb)
def required_605_i0 : Finset Cell := ⟨(([(2, 3), (3, 3), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_605_i0 : Finset Cell := ⟨(([(0, 2), (0, 4), (0, 5), (0, 6), (0, 7), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 2), (5, 4), (5, 5), (5, 6), (5, 7), (6, 5), (7, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_605_i0 : Fin 3 → Finset Cell := ![(placed21 2 (4, 0) required_115), (placed21 0 (0, 1) required_585), (placed21 0 (1, 0) required_604)]
def childrenD_605_i0 : Fin 3 → Finset Cell := ![(placed21 2 (4, 0) envelope_115), (placed21 0 (0, 1) envelope_585), (placed21 0 (1, 0) envelope_604)]
theorem common_sub_605_i0 : commonEnvelope childrenD_605_i0 ⊆ insert (1, 3) required_605_i0 := by decide +kernel
theorem child_required_sub_605_i0 : ∀ j, childrenC_605_i0 j ⊆ insert (1, 3) required_605_i0 := by decide +kernel
theorem child_envelope_sub_605_i0 : ∀ j, childrenD_605_i0 j ⊆ envelope_605_i0 := by decide +kernel
theorem pivot_mem_605_i0 : (1, 3) ∈ envelope_605_i0 := by decide +kernel
theorem children_work_605_i0 : ∀ j, Template HasSnaky 10 (childrenC_605_i0 j) (childrenD_605_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_115 2 (4, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_585 0 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_604 0 (1, 0)).mono (by decide +kernel)
theorem row_works_605_i0 : Template HasSnaky 11 required_605_i0 envelope_605_i0 := by
  refine compose HasSnaky 10 childrenC_605_i0 childrenD_605_i0 children_work_605_i0 (1, 3)
    required_605_i0 envelope_605_i0 pivot_mem_605_i0 child_required_sub_605_i0 child_envelope_sub_605_i0 ?_
  intro b hb
  exact common_sub_605_i0 (mem_commonEnvelope childrenD_605_i0 b hb)
def required_605 : Finset Cell := ⟨(([(2, 3), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_605 : Finset Cell := ⟨(([(0, 2), (0, 4), (0, 5), (0, 6), (0, 7), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (7, 2), (7, 4), (7, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_605 : Fin 5 → Finset Cell := ![(placed21 1 (0, 2) required_12), (placed21 1 (0, 1) required_135), (placed21 3 (0, 5) required_182), (placed21 0 (1, 1) required_474), required_605_i0]
def childrenD_605 : Fin 5 → Finset Cell := ![(placed21 1 (0, 2) envelope_12), (placed21 1 (0, 1) envelope_135), (placed21 3 (0, 5) envelope_182), (placed21 0 (1, 1) envelope_474), envelope_605_i0]
theorem common_sub_605 : commonEnvelope childrenD_605 ⊆ insert (4, 3) required_605 := by decide +kernel
theorem child_required_sub_605 : ∀ j, childrenC_605 j ⊆ insert (4, 3) required_605 := by decide +kernel
theorem child_envelope_sub_605 : ∀ j, childrenD_605 j ⊆ envelope_605 := by decide +kernel
theorem pivot_mem_605 : (4, 3) ∈ envelope_605 := by decide +kernel
theorem children_work_605 : ∀ j, Template HasSnaky 11 (childrenC_605 j) (childrenD_605 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_12 1 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_135 1 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_182 3 (0, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_474 0 (1, 1)).mono (by decide +kernel)
  · exact row_works_605_i0.mono (by decide +kernel)
theorem row_works_605 : Template HasSnaky 12 required_605 envelope_605 := by
  refine compose HasSnaky 11 childrenC_605 childrenD_605 children_work_605 (4, 3)
    required_605 envelope_605 pivot_mem_605 child_required_sub_605 child_envelope_sub_605 ?_
  intro b hb
  exact common_sub_605 (mem_commonEnvelope childrenD_605 b hb)
def required_618_i2 : Finset Cell := ⟨(([(2, 3), (2, 4), (3, 4), (5, 3), (5, 4), (5, 5), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_618_i2 : Finset Cell := ⟨(([(2, 1), (2, 2), (2, 3), (2, 4), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 5), (4, 6), (4, 7), (5, 3), (5, 4), (5, 5), (5, 6), (6, 6), (6, 7), (7, 5), (7, 6), (7, 7), (8, 5), (8, 6), (8, 7), (9, 5), (9, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_618_i2 : Fin 2 → Finset Cell := ![(placed21 6 (3, 7) required_53), (placed21 1 (3, 3) required_378)]
def childrenD_618_i2 : Fin 2 → Finset Cell := ![(placed21 6 (3, 7) envelope_53), (placed21 1 (3, 3) envelope_378)]
theorem common_sub_618_i2 : commonEnvelope childrenD_618_i2 ⊆ insert (3, 5) required_618_i2 := by decide +kernel
theorem child_required_sub_618_i2 : ∀ j, childrenC_618_i2 j ⊆ insert (3, 5) required_618_i2 := by decide +kernel
theorem child_envelope_sub_618_i2 : ∀ j, childrenD_618_i2 j ⊆ envelope_618_i2 := by decide +kernel
theorem pivot_mem_618_i2 : (3, 5) ∈ envelope_618_i2 := by decide +kernel
theorem children_work_618_i2 : ∀ j, Template HasSnaky 6 (childrenC_618_i2 j) (childrenD_618_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_53 6 (3, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_378 1 (3, 3)).mono (by decide +kernel)
theorem row_works_618_i2 : Template HasSnaky 7 required_618_i2 envelope_618_i2 := by
  refine compose HasSnaky 6 childrenC_618_i2 childrenD_618_i2 children_work_618_i2 (3, 5)
    required_618_i2 envelope_618_i2 pivot_mem_618_i2 child_required_sub_618_i2 child_envelope_sub_618_i2 ?_
  intro b hb
  exact common_sub_618_i2 (mem_commonEnvelope childrenD_618_i2 b hb)
def required_618_i1 : Finset Cell := ⟨(([(2, 3), (2, 4), (5, 3), (5, 4), (5, 5), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_618_i1 : Finset Cell := ⟨(([(2, 1), (2, 2), (2, 3), (2, 4), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 4), (4, 5), (4, 6), (4, 7), (5, 3), (5, 4), (5, 5), (5, 6), (6, 2), (6, 3), (6, 6), (6, 7), (7, 5), (7, 6), (7, 7), (8, 5), (8, 6), (8, 7), (9, 5), (9, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_618_i1 : Fin 2 → Finset Cell := ![(placed21 7 (6, 6) required_25), required_618_i2]
def childrenD_618_i1 : Fin 2 → Finset Cell := ![(placed21 7 (6, 6) envelope_25), envelope_618_i2]
theorem common_sub_618_i1 : commonEnvelope childrenD_618_i1 ⊆ insert (3, 4) required_618_i1 := by decide +kernel
theorem child_required_sub_618_i1 : ∀ j, childrenC_618_i1 j ⊆ insert (3, 4) required_618_i1 := by decide +kernel
theorem child_envelope_sub_618_i1 : ∀ j, childrenD_618_i1 j ⊆ envelope_618_i1 := by decide +kernel
theorem pivot_mem_618_i1 : (3, 4) ∈ envelope_618_i1 := by decide +kernel
theorem children_work_618_i1 : ∀ j, Template HasSnaky 7 (childrenC_618_i1 j) (childrenD_618_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_25 7 (6, 6)).mono (by decide +kernel)
  · exact row_works_618_i2.mono (by decide +kernel)
theorem row_works_618_i1 : Template HasSnaky 8 required_618_i1 envelope_618_i1 := by
  refine compose HasSnaky 7 childrenC_618_i1 childrenD_618_i1 children_work_618_i1 (3, 4)
    required_618_i1 envelope_618_i1 pivot_mem_618_i1 child_required_sub_618_i1 child_envelope_sub_618_i1 ?_
  intro b hb
  exact common_sub_618_i1 (mem_commonEnvelope childrenD_618_i1 b hb)
def required_618_i0 : Finset Cell := ⟨(([(2, 3), (2, 4), (5, 3), (5, 4), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_618_i0 : Finset Cell := ⟨(([(2, 1), (2, 2), (2, 3), (2, 4), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 2), (6, 3), (6, 4), (6, 6), (6, 7), (6, 8), (7, 5), (7, 6), (7, 7), (8, 5), (8, 6), (8, 7), (9, 5), (9, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_618_i0 : Fin 4 → Finset Cell := ![(placed21 0 (5, 2) required_7), (placed21 1 (4, 3) required_8), (placed21 2 (6, 2) required_9), required_618_i1]
def childrenD_618_i0 : Fin 4 → Finset Cell := ![(placed21 0 (5, 2) envelope_7), (placed21 1 (4, 3) envelope_8), (placed21 2 (6, 2) envelope_9), envelope_618_i1]
theorem common_sub_618_i0 : commonEnvelope childrenD_618_i0 ⊆ insert (5, 6) required_618_i0 := by decide +kernel
theorem child_required_sub_618_i0 : ∀ j, childrenC_618_i0 j ⊆ insert (5, 6) required_618_i0 := by decide +kernel
theorem child_envelope_sub_618_i0 : ∀ j, childrenD_618_i0 j ⊆ envelope_618_i0 := by decide +kernel
theorem pivot_mem_618_i0 : (5, 6) ∈ envelope_618_i0 := by decide +kernel
theorem children_work_618_i0 : ∀ j, Template HasSnaky 8 (childrenC_618_i0 j) (childrenD_618_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 0 (5, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_8 1 (4, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_9 2 (6, 2)).mono (by decide +kernel)
  · exact row_works_618_i1.mono (by decide +kernel)
theorem row_works_618_i0 : Template HasSnaky 9 required_618_i0 envelope_618_i0 := by
  refine compose HasSnaky 8 childrenC_618_i0 childrenD_618_i0 children_work_618_i0 (5, 6)
    required_618_i0 envelope_618_i0 pivot_mem_618_i0 child_required_sub_618_i0 child_envelope_sub_618_i0 ?_
  intro b hb
  exact common_sub_618_i0 (mem_commonEnvelope childrenD_618_i0 b hb)
def required_618_i3 : Finset Cell := ⟨(([(5, 3), (5, 4), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_618_i3 : Finset Cell := ⟨(([(2, 6), (3, 6), (4, 6), (4, 7), (4, 8), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (8, 5), (8, 6), (8, 7), (9, 5), (9, 6), (9, 7), (10, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_618_i3 : Fin 4 → Finset Cell := ![(placed21 0 (5, 2) required_7), (placed21 1 (4, 3) required_8), (placed21 2 (6, 2) required_9), (placed21 1 (2, 3) required_604)]
def childrenD_618_i3 : Fin 4 → Finset Cell := ![(placed21 0 (5, 2) envelope_7), (placed21 1 (4, 3) envelope_8), (placed21 2 (6, 2) envelope_9), (placed21 1 (2, 3) envelope_604)]
theorem common_sub_618_i3 : commonEnvelope childrenD_618_i3 ⊆ insert (5, 6) required_618_i3 := by decide +kernel
theorem child_required_sub_618_i3 : ∀ j, childrenC_618_i3 j ⊆ insert (5, 6) required_618_i3 := by decide +kernel
theorem child_envelope_sub_618_i3 : ∀ j, childrenD_618_i3 j ⊆ envelope_618_i3 := by decide +kernel
theorem pivot_mem_618_i3 : (5, 6) ∈ envelope_618_i3 := by decide +kernel
theorem children_work_618_i3 : ∀ j, Template HasSnaky 8 (childrenC_618_i3 j) (childrenD_618_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 0 (5, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_8 1 (4, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_9 2 (6, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_604 1 (2, 3)).mono (by decide +kernel)
theorem row_works_618_i3 : Template HasSnaky 9 required_618_i3 envelope_618_i3 := by
  refine compose HasSnaky 8 childrenC_618_i3 childrenD_618_i3 children_work_618_i3 (5, 6)
    required_618_i3 envelope_618_i3 pivot_mem_618_i3 child_required_sub_618_i3 child_envelope_sub_618_i3 ?_
  intro b hb
  exact common_sub_618_i3 (mem_commonEnvelope childrenD_618_i3 b hb)
def required_618_i4 : Finset Cell := ⟨(([(2, 3), (2, 4), (5, 3), (5, 4), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_618_i4 : Finset Cell := ⟨(([(0, 7), (1, 6), (1, 7), (2, 1), (2, 2), (2, 3), (2, 4), (2, 6), (2, 7), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 8), (6, 9), (6, 10), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (8, 3), (8, 4), (8, 5), (8, 6), (9, 4), (9, 5), (9, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_618_i4 : Fin 4 → Finset Cell := ![(placed21 2 (6, 2) required_9), (placed21 1 (2, 3) required_171), (placed21 3 (3, 7) required_577), (placed21 6 (6, 7) required_609)]
def childrenD_618_i4 : Fin 4 → Finset Cell := ![(placed21 2 (6, 2) envelope_9), (placed21 1 (2, 3) envelope_171), (placed21 3 (3, 7) envelope_577), (placed21 6 (6, 7) envelope_609)]
theorem common_sub_618_i4 : commonEnvelope childrenD_618_i4 ⊆ insert (5, 6) required_618_i4 := by decide +kernel
theorem child_required_sub_618_i4 : ∀ j, childrenC_618_i4 j ⊆ insert (5, 6) required_618_i4 := by decide +kernel
theorem child_envelope_sub_618_i4 : ∀ j, childrenD_618_i4 j ⊆ envelope_618_i4 := by decide +kernel
theorem pivot_mem_618_i4 : (5, 6) ∈ envelope_618_i4 := by decide +kernel
theorem children_work_618_i4 : ∀ j, Template HasSnaky 9 (childrenC_618_i4 j) (childrenD_618_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_9 2 (6, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_171 1 (2, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_577 3 (3, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_609 6 (6, 7)).mono (by decide +kernel)
theorem row_works_618_i4 : Template HasSnaky 10 required_618_i4 envelope_618_i4 := by
  refine compose HasSnaky 9 childrenC_618_i4 childrenD_618_i4 children_work_618_i4 (5, 6)
    required_618_i4 envelope_618_i4 pivot_mem_618_i4 child_required_sub_618_i4 child_envelope_sub_618_i4 ?_
  intro b hb
  exact common_sub_618_i4 (mem_commonEnvelope childrenD_618_i4 b hb)
def required_618_i5 : Finset Cell := ⟨(([(5, 3), (5, 4), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_618_i5 : Finset Cell := ⟨(([(1, 6), (1, 7), (2, 6), (2, 7), (3, 4), (3, 5), (3, 6), (3, 7), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (8, 3), (8, 4), (8, 5), (8, 6), (9, 4), (9, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_618_i5 : Fin 3 → Finset Cell := ![(placed21 2 (6, 2) required_9), (placed21 5 (8, 3) required_256), (placed21 3 (3, 7) required_577)]
def childrenD_618_i5 : Fin 3 → Finset Cell := ![(placed21 2 (6, 2) envelope_9), (placed21 5 (8, 3) envelope_256), (placed21 3 (3, 7) envelope_577)]
theorem common_sub_618_i5 : commonEnvelope childrenD_618_i5 ⊆ insert (5, 6) required_618_i5 := by decide +kernel
theorem child_required_sub_618_i5 : ∀ j, childrenC_618_i5 j ⊆ insert (5, 6) required_618_i5 := by decide +kernel
theorem child_envelope_sub_618_i5 : ∀ j, childrenD_618_i5 j ⊆ envelope_618_i5 := by decide +kernel
theorem pivot_mem_618_i5 : (5, 6) ∈ envelope_618_i5 := by decide +kernel
theorem children_work_618_i5 : ∀ j, Template HasSnaky 9 (childrenC_618_i5 j) (childrenD_618_i5 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_9 2 (6, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_256 5 (8, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_577 3 (3, 7)).mono (by decide +kernel)
theorem row_works_618_i5 : Template HasSnaky 10 required_618_i5 envelope_618_i5 := by
  refine compose HasSnaky 9 childrenC_618_i5 childrenD_618_i5 children_work_618_i5 (5, 6)
    required_618_i5 envelope_618_i5 pivot_mem_618_i5 child_required_sub_618_i5 child_envelope_sub_618_i5 ?_
  intro b hb
  exact common_sub_618_i5 (mem_commonEnvelope childrenD_618_i5 b hb)
def required_618_i8 : Finset Cell := ⟨(([(2, 3), (2, 4), (3, 4), (4, 4), (5, 4), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_618_i8 : Finset Cell := ⟨(([(1, 4), (2, 3), (2, 4), (3, 3), (3, 4), (3, 5), (4, 4), (4, 5), (5, 4), (5, 5), (6, 4), (7, 4), (8, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_618_i8 : Fin 2 → Finset Cell := ![(placed21 6 (6, 4) required_4), (placed21 1 (1, 4) required_113)]
def childrenD_618_i8 : Fin 2 → Finset Cell := ![(placed21 6 (6, 4) envelope_4), (placed21 1 (1, 4) envelope_113)]
theorem common_sub_618_i8 : commonEnvelope childrenD_618_i8 ⊆ insert (6, 4) required_618_i8 := by decide +kernel
theorem child_required_sub_618_i8 : ∀ j, childrenC_618_i8 j ⊆ insert (6, 4) required_618_i8 := by decide +kernel
theorem child_envelope_sub_618_i8 : ∀ j, childrenD_618_i8 j ⊆ envelope_618_i8 := by decide +kernel
theorem pivot_mem_618_i8 : (6, 4) ∈ envelope_618_i8 := by decide +kernel
theorem children_work_618_i8 : ∀ j, Template HasSnaky 3 (childrenC_618_i8 j) (childrenD_618_i8 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_4 6 (6, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_113 1 (1, 4)).mono (by decide +kernel)
theorem row_works_618_i8 : Template HasSnaky 4 required_618_i8 envelope_618_i8 := by
  refine compose HasSnaky 3 childrenC_618_i8 childrenD_618_i8 children_work_618_i8 (6, 4)
    required_618_i8 envelope_618_i8 pivot_mem_618_i8 child_required_sub_618_i8 child_envelope_sub_618_i8 ?_
  intro b hb
  exact common_sub_618_i8 (mem_commonEnvelope childrenD_618_i8 b hb)
def required_618_i7 : Finset Cell := ⟨(([(2, 3), (2, 4), (4, 4), (5, 4), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_618_i7 : Finset Cell := ⟨(([(1, 4), (2, 3), (2, 4), (3, 3), (3, 4), (3, 5), (4, 4), (4, 5), (5, 4), (5, 5), (6, 4), (6, 5), (7, 4), (8, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_618_i7 : Fin 2 → Finset Cell := ![(placed21 0 (2, 4) required_5), required_618_i8]
def childrenD_618_i7 : Fin 2 → Finset Cell := ![(placed21 0 (2, 4) envelope_5), envelope_618_i8]
theorem common_sub_618_i7 : commonEnvelope childrenD_618_i7 ⊆ insert (3, 4) required_618_i7 := by decide +kernel
theorem child_required_sub_618_i7 : ∀ j, childrenC_618_i7 j ⊆ insert (3, 4) required_618_i7 := by decide +kernel
theorem child_envelope_sub_618_i7 : ∀ j, childrenD_618_i7 j ⊆ envelope_618_i7 := by decide +kernel
theorem pivot_mem_618_i7 : (3, 4) ∈ envelope_618_i7 := by decide +kernel
theorem children_work_618_i7 : ∀ j, Template HasSnaky 4 (childrenC_618_i7 j) (childrenD_618_i7 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 0 (2, 4)).mono (by decide +kernel)
  · exact row_works_618_i8.mono (by decide +kernel)
theorem row_works_618_i7 : Template HasSnaky 5 required_618_i7 envelope_618_i7 := by
  refine compose HasSnaky 4 childrenC_618_i7 childrenD_618_i7 children_work_618_i7 (3, 4)
    required_618_i7 envelope_618_i7 pivot_mem_618_i7 child_required_sub_618_i7 child_envelope_sub_618_i7 ?_
  intro b hb
  exact common_sub_618_i7 (mem_commonEnvelope childrenD_618_i7 b hb)
def required_618_i6 : Finset Cell := ⟨(([(2, 3), (2, 4), (5, 3), (5, 4), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_618_i6 : Finset Cell := ⟨(([(1, 4), (2, 3), (2, 4), (3, 3), (3, 4), (3, 5), (4, 4), (4, 5), (4, 7), (4, 8), (4, 9), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (9, 3), (9, 4), (9, 5), (9, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_618_i6 : Fin 4 → Finset Cell := ![(placed21 5 (6, 3) required_80), (placed21 1 (2, 2) required_111), (placed21 0 (3, 1) required_616), required_618_i7]
def childrenD_618_i6 : Fin 4 → Finset Cell := ![(placed21 5 (6, 3) envelope_80), (placed21 1 (2, 2) envelope_111), (placed21 0 (3, 1) envelope_616), envelope_618_i7]
theorem common_sub_618_i6 : commonEnvelope childrenD_618_i6 ⊆ insert (4, 4) required_618_i6 := by decide +kernel
theorem child_required_sub_618_i6 : ∀ j, childrenC_618_i6 j ⊆ insert (4, 4) required_618_i6 := by decide +kernel
theorem child_envelope_sub_618_i6 : ∀ j, childrenD_618_i6 j ⊆ envelope_618_i6 := by decide +kernel
theorem pivot_mem_618_i6 : (4, 4) ∈ envelope_618_i6 := by decide +kernel
theorem children_work_618_i6 : ∀ j, Template HasSnaky 10 (childrenC_618_i6 j) (childrenD_618_i6 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_80 5 (6, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_111 1 (2, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_616 0 (3, 1)).mono (by decide +kernel)
  · exact row_works_618_i7.mono (by decide +kernel)
theorem row_works_618_i6 : Template HasSnaky 11 required_618_i6 envelope_618_i6 := by
  refine compose HasSnaky 10 childrenC_618_i6 childrenD_618_i6 children_work_618_i6 (4, 4)
    required_618_i6 envelope_618_i6 pivot_mem_618_i6 child_required_sub_618_i6 child_envelope_sub_618_i6 ?_
  intro b hb
  exact common_sub_618_i6 (mem_commonEnvelope childrenD_618_i6 b hb)
def required_618 : Finset Cell := ⟨(([(2, 3), (2, 4), (5, 3), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_618 : Finset Cell := ⟨(([(0, 7), (1, 4), (1, 6), (1, 7), (2, 1), (2, 2), (2, 3), (2, 4), (2, 6), (2, 7), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (10, 2), (10, 4), (10, 5), (10, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_618 : Fin 9 → Finset Cell := ![(placed21 1 (2, 3) required_398), (placed21 0 (1, 2) required_434), (placed21 2 (6, 1) required_610), required_618_i0, required_618_i3, required_618_i4, required_618_i5, (placed21 0 (2, 0) required_615), required_618_i6]
def childrenD_618 : Fin 9 → Finset Cell := ![(placed21 1 (2, 3) envelope_398), (placed21 0 (1, 2) envelope_434), (placed21 2 (6, 1) envelope_610), envelope_618_i0, envelope_618_i3, envelope_618_i4, envelope_618_i5, (placed21 0 (2, 0) envelope_615), envelope_618_i6]
theorem common_sub_618 : commonEnvelope childrenD_618 ⊆ insert (5, 5) required_618 := by decide +kernel
theorem child_required_sub_618 : ∀ j, childrenC_618 j ⊆ insert (5, 5) required_618 := by decide +kernel
theorem child_envelope_sub_618 : ∀ j, childrenD_618 j ⊆ envelope_618 := by decide +kernel
theorem pivot_mem_618 : (5, 5) ∈ envelope_618 := by decide +kernel
theorem children_work_618 : ∀ j, Template HasSnaky 11 (childrenC_618 j) (childrenD_618 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_398 1 (2, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_434 0 (1, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_610 2 (6, 1)).mono (by decide +kernel)
  · exact row_works_618_i0.mono (by decide +kernel)
  · exact row_works_618_i3.mono (by decide +kernel)
  · exact row_works_618_i4.mono (by decide +kernel)
  · exact row_works_618_i5.mono (by decide +kernel)
  · exact (placed21_template row_works_615 0 (2, 0)).mono (by decide +kernel)
  · exact row_works_618_i6.mono (by decide +kernel)
theorem row_works_618 : Template HasSnaky 12 required_618 envelope_618 := by
  refine compose HasSnaky 11 childrenC_618 childrenD_618 children_work_618 (5, 5)
    required_618 envelope_618 pivot_mem_618 child_required_sub_618 child_envelope_sub_618 ?_
  intro b hb
  exact common_sub_618 (mem_commonEnvelope childrenD_618 b hb)
def height_599_i6 : ℕ := 4
def childrenH_599_i6 : Fin 2 → ℕ := ![height_5, height_64]
theorem height_exact_599_i6 : height_599_i6 = 1 + Finset.univ.sup childrenH_599_i6 := by decide +kernel
theorem required_origin_599_i6 : ∀ x ∈ required_599_i6,
    (∃ j, x ∈ childrenC_599_i6 j) ∨ ∀ j, x ∈ childrenD_599_i6 j := by decide +kernel
theorem required_exact_599_i6 : required_599_i6 =
    ((Finset.univ.biUnion childrenC_599_i6) ∪ commonEnvelope childrenD_599_i6).erase (5, 6) := by
  exact required_eq_combination childrenC_599_i6 childrenD_599_i6 (5, 6) required_599_i6
    (by decide +kernel) child_required_sub_599_i6 common_sub_599_i6 required_origin_599_i6
theorem envelope_origin_599_i6 : ∀ x ∈ envelope_599_i6,
    x = (5, 6) ∨ ∃ j, x ∈ childrenD_599_i6 j := by decide +kernel
theorem envelope_exact_599_i6 : envelope_599_i6 =
    insert (5, 6) (Finset.univ.biUnion childrenD_599_i6) := by
  exact envelope_eq_combination childrenD_599_i6 (5, 6) envelope_599_i6
    pivot_mem_599_i6 child_envelope_sub_599_i6 envelope_origin_599_i6
def checked_599_i6 : CheckedCard where
  required := required_599_i6
  envelope := envelope_599_i6
  height := height_599_i6
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_599_i6
def height_599_i8 : ℕ := 4
def childrenH_599_i8 : Fin 2 → ℕ := ![height_0, height_44]
theorem height_exact_599_i8 : height_599_i8 = 1 + Finset.univ.sup childrenH_599_i8 := by decide +kernel
theorem required_origin_599_i8 : ∀ x ∈ required_599_i8,
    (∃ j, x ∈ childrenC_599_i8 j) ∨ ∀ j, x ∈ childrenD_599_i8 j := by decide +kernel
theorem required_exact_599_i8 : required_599_i8 =
    ((Finset.univ.biUnion childrenC_599_i8) ∪ commonEnvelope childrenD_599_i8).erase (4, 4) := by
  exact required_eq_combination childrenC_599_i8 childrenD_599_i8 (4, 4) required_599_i8
    (by decide +kernel) child_required_sub_599_i8 common_sub_599_i8 required_origin_599_i8
theorem envelope_origin_599_i8 : ∀ x ∈ envelope_599_i8,
    x = (4, 4) ∨ ∃ j, x ∈ childrenD_599_i8 j := by decide +kernel
theorem envelope_exact_599_i8 : envelope_599_i8 =
    insert (4, 4) (Finset.univ.biUnion childrenD_599_i8) := by
  exact envelope_eq_combination childrenD_599_i8 (4, 4) envelope_599_i8
    pivot_mem_599_i8 child_envelope_sub_599_i8 envelope_origin_599_i8
def checked_599_i8 : CheckedCard where
  required := required_599_i8
  envelope := envelope_599_i8
  height := height_599_i8
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_599_i8
def height_599_i7 : ℕ := 5
def childrenH_599_i7 : Fin 3 → ℕ := ![height_6, height_16, height_599_i8]
theorem height_exact_599_i7 : height_599_i7 = 1 + Finset.univ.sup childrenH_599_i7 := by decide +kernel
theorem required_origin_599_i7 : ∀ x ∈ required_599_i7,
    (∃ j, x ∈ childrenC_599_i7 j) ∨ ∀ j, x ∈ childrenD_599_i7 j := by decide +kernel
theorem required_exact_599_i7 : required_599_i7 =
    ((Finset.univ.biUnion childrenC_599_i7) ∪ commonEnvelope childrenD_599_i7).erase (6, 5) := by
  exact required_eq_combination childrenC_599_i7 childrenD_599_i7 (6, 5) required_599_i7
    (by decide +kernel) child_required_sub_599_i7 common_sub_599_i7 required_origin_599_i7
theorem envelope_origin_599_i7 : ∀ x ∈ envelope_599_i7,
    x = (6, 5) ∨ ∃ j, x ∈ childrenD_599_i7 j := by decide +kernel
theorem envelope_exact_599_i7 : envelope_599_i7 =
    insert (6, 5) (Finset.univ.biUnion childrenD_599_i7) := by
  exact envelope_eq_combination childrenD_599_i7 (6, 5) envelope_599_i7
    pivot_mem_599_i7 child_envelope_sub_599_i7 envelope_origin_599_i7
def checked_599_i7 : CheckedCard where
  required := required_599_i7
  envelope := envelope_599_i7
  height := height_599_i7
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_599_i7
def height_599_i5 : ℕ := 6
def childrenH_599_i5 : Fin 5 → ℕ := ![height_8, height_17, height_41, height_599_i6, height_599_i7]
theorem height_exact_599_i5 : height_599_i5 = 1 + Finset.univ.sup childrenH_599_i5 := by decide +kernel
theorem required_origin_599_i5 : ∀ x ∈ required_599_i5,
    (∃ j, x ∈ childrenC_599_i5 j) ∨ ∀ j, x ∈ childrenD_599_i5 j := by decide +kernel
theorem required_exact_599_i5 : required_599_i5 =
    ((Finset.univ.biUnion childrenC_599_i5) ∪ commonEnvelope childrenD_599_i5).erase (5, 5) := by
  exact required_eq_combination childrenC_599_i5 childrenD_599_i5 (5, 5) required_599_i5
    (by decide +kernel) child_required_sub_599_i5 common_sub_599_i5 required_origin_599_i5
theorem envelope_origin_599_i5 : ∀ x ∈ envelope_599_i5,
    x = (5, 5) ∨ ∃ j, x ∈ childrenD_599_i5 j := by decide +kernel
theorem envelope_exact_599_i5 : envelope_599_i5 =
    insert (5, 5) (Finset.univ.biUnion childrenD_599_i5) := by
  exact envelope_eq_combination childrenD_599_i5 (5, 5) envelope_599_i5
    pivot_mem_599_i5 child_envelope_sub_599_i5 envelope_origin_599_i5
def checked_599_i5 : CheckedCard where
  required := required_599_i5
  envelope := envelope_599_i5
  height := height_599_i5
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_599_i5
def height_599_i4 : ℕ := 7
def childrenH_599_i4 : Fin 2 → ℕ := ![height_5, height_599_i5]
theorem height_exact_599_i4 : height_599_i4 = 1 + Finset.univ.sup childrenH_599_i4 := by decide +kernel
theorem required_origin_599_i4 : ∀ x ∈ required_599_i4,
    (∃ j, x ∈ childrenC_599_i4 j) ∨ ∀ j, x ∈ childrenD_599_i4 j := by decide +kernel
theorem required_exact_599_i4 : required_599_i4 =
    ((Finset.univ.biUnion childrenC_599_i4) ∪ commonEnvelope childrenD_599_i4).erase (2, 5) := by
  exact required_eq_combination childrenC_599_i4 childrenD_599_i4 (2, 5) required_599_i4
    (by decide +kernel) child_required_sub_599_i4 common_sub_599_i4 required_origin_599_i4
theorem envelope_origin_599_i4 : ∀ x ∈ envelope_599_i4,
    x = (2, 5) ∨ ∃ j, x ∈ childrenD_599_i4 j := by decide +kernel
theorem envelope_exact_599_i4 : envelope_599_i4 =
    insert (2, 5) (Finset.univ.biUnion childrenD_599_i4) := by
  exact envelope_eq_combination childrenD_599_i4 (2, 5) envelope_599_i4
    pivot_mem_599_i4 child_envelope_sub_599_i4 envelope_origin_599_i4
def checked_599_i4 : CheckedCard where
  required := required_599_i4
  envelope := envelope_599_i4
  height := height_599_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_599_i4
def height_599_i3 : ℕ := 8
def childrenH_599_i3 : Fin 2 → ℕ := ![height_5, height_599_i4]
theorem height_exact_599_i3 : height_599_i3 = 1 + Finset.univ.sup childrenH_599_i3 := by decide +kernel
theorem required_origin_599_i3 : ∀ x ∈ required_599_i3,
    (∃ j, x ∈ childrenC_599_i3 j) ∨ ∀ j, x ∈ childrenD_599_i3 j := by decide +kernel
theorem required_exact_599_i3 : required_599_i3 =
    ((Finset.univ.biUnion childrenC_599_i3) ∪ commonEnvelope childrenD_599_i3).erase (4, 5) := by
  exact required_eq_combination childrenC_599_i3 childrenD_599_i3 (4, 5) required_599_i3
    (by decide +kernel) child_required_sub_599_i3 common_sub_599_i3 required_origin_599_i3
theorem envelope_origin_599_i3 : ∀ x ∈ envelope_599_i3,
    x = (4, 5) ∨ ∃ j, x ∈ childrenD_599_i3 j := by decide +kernel
theorem envelope_exact_599_i3 : envelope_599_i3 =
    insert (4, 5) (Finset.univ.biUnion childrenD_599_i3) := by
  exact envelope_eq_combination childrenD_599_i3 (4, 5) envelope_599_i3
    pivot_mem_599_i3 child_envelope_sub_599_i3 envelope_origin_599_i3
def checked_599_i3 : CheckedCard where
  required := required_599_i3
  envelope := envelope_599_i3
  height := height_599_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_599_i3
def height_599_i2 : ℕ := 9
def childrenH_599_i2 : Fin 3 → ℕ := ![height_9, height_251, height_599_i3]
theorem height_exact_599_i2 : height_599_i2 = 1 + Finset.univ.sup childrenH_599_i2 := by decide +kernel
theorem required_origin_599_i2 : ∀ x ∈ required_599_i2,
    (∃ j, x ∈ childrenC_599_i2 j) ∨ ∀ j, x ∈ childrenD_599_i2 j := by decide +kernel
theorem required_exact_599_i2 : required_599_i2 =
    ((Finset.univ.biUnion childrenC_599_i2) ∪ commonEnvelope childrenD_599_i2).erase (3, 2) := by
  exact required_eq_combination childrenC_599_i2 childrenD_599_i2 (3, 2) required_599_i2
    (by decide +kernel) child_required_sub_599_i2 common_sub_599_i2 required_origin_599_i2
theorem envelope_origin_599_i2 : ∀ x ∈ envelope_599_i2,
    x = (3, 2) ∨ ∃ j, x ∈ childrenD_599_i2 j := by decide +kernel
theorem envelope_exact_599_i2 : envelope_599_i2 =
    insert (3, 2) (Finset.univ.biUnion childrenD_599_i2) := by
  exact envelope_eq_combination childrenD_599_i2 (3, 2) envelope_599_i2
    pivot_mem_599_i2 child_envelope_sub_599_i2 envelope_origin_599_i2
def checked_599_i2 : CheckedCard where
  required := required_599_i2
  envelope := envelope_599_i2
  height := height_599_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_599_i2
def height_599_i1 : ℕ := 10
def childrenH_599_i1 : Fin 5 → ℕ := ![height_10, height_27, height_48, height_63, height_599_i2]
theorem height_exact_599_i1 : height_599_i1 = 1 + Finset.univ.sup childrenH_599_i1 := by decide +kernel
theorem required_origin_599_i1 : ∀ x ∈ required_599_i1,
    (∃ j, x ∈ childrenC_599_i1 j) ∨ ∀ j, x ∈ childrenD_599_i1 j := by decide +kernel
theorem required_exact_599_i1 : required_599_i1 =
    ((Finset.univ.biUnion childrenC_599_i1) ∪ commonEnvelope childrenD_599_i1).erase (3, 5) := by
  exact required_eq_combination childrenC_599_i1 childrenD_599_i1 (3, 5) required_599_i1
    (by decide +kernel) child_required_sub_599_i1 common_sub_599_i1 required_origin_599_i1
theorem envelope_origin_599_i1 : ∀ x ∈ envelope_599_i1,
    x = (3, 5) ∨ ∃ j, x ∈ childrenD_599_i1 j := by decide +kernel
theorem envelope_exact_599_i1 : envelope_599_i1 =
    insert (3, 5) (Finset.univ.biUnion childrenD_599_i1) := by
  exact envelope_eq_combination childrenD_599_i1 (3, 5) envelope_599_i1
    pivot_mem_599_i1 child_envelope_sub_599_i1 envelope_origin_599_i1
def checked_599_i1 : CheckedCard where
  required := required_599_i1
  envelope := envelope_599_i1
  height := height_599_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_599_i1
def height_599_i0 : ℕ := 11
def childrenH_599_i0 : Fin 2 → ℕ := ![height_2, height_599_i1]
theorem height_exact_599_i0 : height_599_i0 = 1 + Finset.univ.sup childrenH_599_i0 := by decide +kernel
theorem required_origin_599_i0 : ∀ x ∈ required_599_i0,
    (∃ j, x ∈ childrenC_599_i0 j) ∨ ∀ j, x ∈ childrenD_599_i0 j := by decide +kernel
theorem required_exact_599_i0 : required_599_i0 =
    ((Finset.univ.biUnion childrenC_599_i0) ∪ commonEnvelope childrenD_599_i0).erase (3, 4) := by
  exact required_eq_combination childrenC_599_i0 childrenD_599_i0 (3, 4) required_599_i0
    (by decide +kernel) child_required_sub_599_i0 common_sub_599_i0 required_origin_599_i0
theorem envelope_origin_599_i0 : ∀ x ∈ envelope_599_i0,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_599_i0 j := by decide +kernel
theorem envelope_exact_599_i0 : envelope_599_i0 =
    insert (3, 4) (Finset.univ.biUnion childrenD_599_i0) := by
  exact envelope_eq_combination childrenD_599_i0 (3, 4) envelope_599_i0
    pivot_mem_599_i0 child_envelope_sub_599_i0 envelope_origin_599_i0
def checked_599_i0 : CheckedCard where
  required := required_599_i0
  envelope := envelope_599_i0
  height := height_599_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_599_i0
def height_599 : ℕ := 12
def childrenH_599 : Fin 4 → ℕ := ![height_107, height_163, height_401, height_599_i0]
theorem height_exact_599 : height_599 = 1 + Finset.univ.sup childrenH_599 := by decide +kernel
theorem required_origin_599 : ∀ x ∈ required_599,
    (∃ j, x ∈ childrenC_599 j) ∨ ∀ j, x ∈ childrenD_599 j := by decide +kernel
theorem required_exact_599 : required_599 =
    ((Finset.univ.biUnion childrenC_599) ∪ commonEnvelope childrenD_599).erase (4, 3) := by
  exact required_eq_combination childrenC_599 childrenD_599 (4, 3) required_599
    (by decide +kernel) child_required_sub_599 common_sub_599 required_origin_599
theorem envelope_origin_599 : ∀ x ∈ envelope_599,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_599 j := by decide +kernel
theorem envelope_exact_599 : envelope_599 =
    insert (4, 3) (Finset.univ.biUnion childrenD_599) := by
  exact envelope_eq_combination childrenD_599 (4, 3) envelope_599
    pivot_mem_599 child_envelope_sub_599 envelope_origin_599
def checked_599 : CheckedCard where
  required := required_599
  envelope := envelope_599
  height := height_599
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_599
def height_605_i0 : ℕ := 11
def childrenH_605_i0 : Fin 3 → ℕ := ![height_115, height_585, height_604]
theorem height_exact_605_i0 : height_605_i0 = 1 + Finset.univ.sup childrenH_605_i0 := by decide +kernel
theorem required_origin_605_i0 : ∀ x ∈ required_605_i0,
    (∃ j, x ∈ childrenC_605_i0 j) ∨ ∀ j, x ∈ childrenD_605_i0 j := by decide +kernel
theorem required_exact_605_i0 : required_605_i0 =
    ((Finset.univ.biUnion childrenC_605_i0) ∪ commonEnvelope childrenD_605_i0).erase (1, 3) := by
  exact required_eq_combination childrenC_605_i0 childrenD_605_i0 (1, 3) required_605_i0
    (by decide +kernel) child_required_sub_605_i0 common_sub_605_i0 required_origin_605_i0
theorem envelope_origin_605_i0 : ∀ x ∈ envelope_605_i0,
    x = (1, 3) ∨ ∃ j, x ∈ childrenD_605_i0 j := by decide +kernel
theorem envelope_exact_605_i0 : envelope_605_i0 =
    insert (1, 3) (Finset.univ.biUnion childrenD_605_i0) := by
  exact envelope_eq_combination childrenD_605_i0 (1, 3) envelope_605_i0
    pivot_mem_605_i0 child_envelope_sub_605_i0 envelope_origin_605_i0
def checked_605_i0 : CheckedCard where
  required := required_605_i0
  envelope := envelope_605_i0
  height := height_605_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_605_i0
def height_605 : ℕ := 12
def childrenH_605 : Fin 5 → ℕ := ![height_12, height_135, height_182, height_474, height_605_i0]
theorem height_exact_605 : height_605 = 1 + Finset.univ.sup childrenH_605 := by decide +kernel
theorem required_origin_605 : ∀ x ∈ required_605,
    (∃ j, x ∈ childrenC_605 j) ∨ ∀ j, x ∈ childrenD_605 j := by decide +kernel
theorem required_exact_605 : required_605 =
    ((Finset.univ.biUnion childrenC_605) ∪ commonEnvelope childrenD_605).erase (4, 3) := by
  exact required_eq_combination childrenC_605 childrenD_605 (4, 3) required_605
    (by decide +kernel) child_required_sub_605 common_sub_605 required_origin_605
theorem envelope_origin_605 : ∀ x ∈ envelope_605,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_605 j := by decide +kernel
theorem envelope_exact_605 : envelope_605 =
    insert (4, 3) (Finset.univ.biUnion childrenD_605) := by
  exact envelope_eq_combination childrenD_605 (4, 3) envelope_605
    pivot_mem_605 child_envelope_sub_605 envelope_origin_605
def checked_605 : CheckedCard where
  required := required_605
  envelope := envelope_605
  height := height_605
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_605
def height_618_i2 : ℕ := 7
def childrenH_618_i2 : Fin 2 → ℕ := ![height_53, height_378]
theorem height_exact_618_i2 : height_618_i2 = 1 + Finset.univ.sup childrenH_618_i2 := by decide +kernel
theorem required_origin_618_i2 : ∀ x ∈ required_618_i2,
    (∃ j, x ∈ childrenC_618_i2 j) ∨ ∀ j, x ∈ childrenD_618_i2 j := by decide +kernel
theorem required_exact_618_i2 : required_618_i2 =
    ((Finset.univ.biUnion childrenC_618_i2) ∪ commonEnvelope childrenD_618_i2).erase (3, 5) := by
  exact required_eq_combination childrenC_618_i2 childrenD_618_i2 (3, 5) required_618_i2
    (by decide +kernel) child_required_sub_618_i2 common_sub_618_i2 required_origin_618_i2
theorem envelope_origin_618_i2 : ∀ x ∈ envelope_618_i2,
    x = (3, 5) ∨ ∃ j, x ∈ childrenD_618_i2 j := by decide +kernel
theorem envelope_exact_618_i2 : envelope_618_i2 =
    insert (3, 5) (Finset.univ.biUnion childrenD_618_i2) := by
  exact envelope_eq_combination childrenD_618_i2 (3, 5) envelope_618_i2
    pivot_mem_618_i2 child_envelope_sub_618_i2 envelope_origin_618_i2
def checked_618_i2 : CheckedCard where
  required := required_618_i2
  envelope := envelope_618_i2
  height := height_618_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_618_i2
def height_618_i1 : ℕ := 8
def childrenH_618_i1 : Fin 2 → ℕ := ![height_25, height_618_i2]
theorem height_exact_618_i1 : height_618_i1 = 1 + Finset.univ.sup childrenH_618_i1 := by decide +kernel
theorem required_origin_618_i1 : ∀ x ∈ required_618_i1,
    (∃ j, x ∈ childrenC_618_i1 j) ∨ ∀ j, x ∈ childrenD_618_i1 j := by decide +kernel
theorem required_exact_618_i1 : required_618_i1 =
    ((Finset.univ.biUnion childrenC_618_i1) ∪ commonEnvelope childrenD_618_i1).erase (3, 4) := by
  exact required_eq_combination childrenC_618_i1 childrenD_618_i1 (3, 4) required_618_i1
    (by decide +kernel) child_required_sub_618_i1 common_sub_618_i1 required_origin_618_i1
theorem envelope_origin_618_i1 : ∀ x ∈ envelope_618_i1,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_618_i1 j := by decide +kernel
theorem envelope_exact_618_i1 : envelope_618_i1 =
    insert (3, 4) (Finset.univ.biUnion childrenD_618_i1) := by
  exact envelope_eq_combination childrenD_618_i1 (3, 4) envelope_618_i1
    pivot_mem_618_i1 child_envelope_sub_618_i1 envelope_origin_618_i1
def checked_618_i1 : CheckedCard where
  required := required_618_i1
  envelope := envelope_618_i1
  height := height_618_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_618_i1
def height_618_i0 : ℕ := 9
def childrenH_618_i0 : Fin 4 → ℕ := ![height_7, height_8, height_9, height_618_i1]
theorem height_exact_618_i0 : height_618_i0 = 1 + Finset.univ.sup childrenH_618_i0 := by decide +kernel
theorem required_origin_618_i0 : ∀ x ∈ required_618_i0,
    (∃ j, x ∈ childrenC_618_i0 j) ∨ ∀ j, x ∈ childrenD_618_i0 j := by decide +kernel
theorem required_exact_618_i0 : required_618_i0 =
    ((Finset.univ.biUnion childrenC_618_i0) ∪ commonEnvelope childrenD_618_i0).erase (5, 6) := by
  exact required_eq_combination childrenC_618_i0 childrenD_618_i0 (5, 6) required_618_i0
    (by decide +kernel) child_required_sub_618_i0 common_sub_618_i0 required_origin_618_i0
theorem envelope_origin_618_i0 : ∀ x ∈ envelope_618_i0,
    x = (5, 6) ∨ ∃ j, x ∈ childrenD_618_i0 j := by decide +kernel
theorem envelope_exact_618_i0 : envelope_618_i0 =
    insert (5, 6) (Finset.univ.biUnion childrenD_618_i0) := by
  exact envelope_eq_combination childrenD_618_i0 (5, 6) envelope_618_i0
    pivot_mem_618_i0 child_envelope_sub_618_i0 envelope_origin_618_i0
def checked_618_i0 : CheckedCard where
  required := required_618_i0
  envelope := envelope_618_i0
  height := height_618_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_618_i0
def height_618_i3 : ℕ := 9
def childrenH_618_i3 : Fin 4 → ℕ := ![height_7, height_8, height_9, height_604]
theorem height_exact_618_i3 : height_618_i3 = 1 + Finset.univ.sup childrenH_618_i3 := by decide +kernel
theorem required_origin_618_i3 : ∀ x ∈ required_618_i3,
    (∃ j, x ∈ childrenC_618_i3 j) ∨ ∀ j, x ∈ childrenD_618_i3 j := by decide +kernel
theorem required_exact_618_i3 : required_618_i3 =
    ((Finset.univ.biUnion childrenC_618_i3) ∪ commonEnvelope childrenD_618_i3).erase (5, 6) := by
  exact required_eq_combination childrenC_618_i3 childrenD_618_i3 (5, 6) required_618_i3
    (by decide +kernel) child_required_sub_618_i3 common_sub_618_i3 required_origin_618_i3
theorem envelope_origin_618_i3 : ∀ x ∈ envelope_618_i3,
    x = (5, 6) ∨ ∃ j, x ∈ childrenD_618_i3 j := by decide +kernel
theorem envelope_exact_618_i3 : envelope_618_i3 =
    insert (5, 6) (Finset.univ.biUnion childrenD_618_i3) := by
  exact envelope_eq_combination childrenD_618_i3 (5, 6) envelope_618_i3
    pivot_mem_618_i3 child_envelope_sub_618_i3 envelope_origin_618_i3
def checked_618_i3 : CheckedCard where
  required := required_618_i3
  envelope := envelope_618_i3
  height := height_618_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_618_i3
def height_618_i4 : ℕ := 10
def childrenH_618_i4 : Fin 4 → ℕ := ![height_9, height_171, height_577, height_609]
theorem height_exact_618_i4 : height_618_i4 = 1 + Finset.univ.sup childrenH_618_i4 := by decide +kernel
theorem required_origin_618_i4 : ∀ x ∈ required_618_i4,
    (∃ j, x ∈ childrenC_618_i4 j) ∨ ∀ j, x ∈ childrenD_618_i4 j := by decide +kernel
theorem required_exact_618_i4 : required_618_i4 =
    ((Finset.univ.biUnion childrenC_618_i4) ∪ commonEnvelope childrenD_618_i4).erase (5, 6) := by
  exact required_eq_combination childrenC_618_i4 childrenD_618_i4 (5, 6) required_618_i4
    (by decide +kernel) child_required_sub_618_i4 common_sub_618_i4 required_origin_618_i4
theorem envelope_origin_618_i4 : ∀ x ∈ envelope_618_i4,
    x = (5, 6) ∨ ∃ j, x ∈ childrenD_618_i4 j := by decide +kernel
theorem envelope_exact_618_i4 : envelope_618_i4 =
    insert (5, 6) (Finset.univ.biUnion childrenD_618_i4) := by
  exact envelope_eq_combination childrenD_618_i4 (5, 6) envelope_618_i4
    pivot_mem_618_i4 child_envelope_sub_618_i4 envelope_origin_618_i4
def checked_618_i4 : CheckedCard where
  required := required_618_i4
  envelope := envelope_618_i4
  height := height_618_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_618_i4
def height_618_i5 : ℕ := 10
def childrenH_618_i5 : Fin 3 → ℕ := ![height_9, height_256, height_577]
theorem height_exact_618_i5 : height_618_i5 = 1 + Finset.univ.sup childrenH_618_i5 := by decide +kernel
theorem required_origin_618_i5 : ∀ x ∈ required_618_i5,
    (∃ j, x ∈ childrenC_618_i5 j) ∨ ∀ j, x ∈ childrenD_618_i5 j := by decide +kernel
theorem required_exact_618_i5 : required_618_i5 =
    ((Finset.univ.biUnion childrenC_618_i5) ∪ commonEnvelope childrenD_618_i5).erase (5, 6) := by
  exact required_eq_combination childrenC_618_i5 childrenD_618_i5 (5, 6) required_618_i5
    (by decide +kernel) child_required_sub_618_i5 common_sub_618_i5 required_origin_618_i5
theorem envelope_origin_618_i5 : ∀ x ∈ envelope_618_i5,
    x = (5, 6) ∨ ∃ j, x ∈ childrenD_618_i5 j := by decide +kernel
theorem envelope_exact_618_i5 : envelope_618_i5 =
    insert (5, 6) (Finset.univ.biUnion childrenD_618_i5) := by
  exact envelope_eq_combination childrenD_618_i5 (5, 6) envelope_618_i5
    pivot_mem_618_i5 child_envelope_sub_618_i5 envelope_origin_618_i5
def checked_618_i5 : CheckedCard where
  required := required_618_i5
  envelope := envelope_618_i5
  height := height_618_i5
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_618_i5
def height_618_i8 : ℕ := 4
def childrenH_618_i8 : Fin 2 → ℕ := ![height_4, height_113]
theorem height_exact_618_i8 : height_618_i8 = 1 + Finset.univ.sup childrenH_618_i8 := by decide +kernel
theorem required_origin_618_i8 : ∀ x ∈ required_618_i8,
    (∃ j, x ∈ childrenC_618_i8 j) ∨ ∀ j, x ∈ childrenD_618_i8 j := by decide +kernel
theorem required_exact_618_i8 : required_618_i8 =
    ((Finset.univ.biUnion childrenC_618_i8) ∪ commonEnvelope childrenD_618_i8).erase (6, 4) := by
  exact required_eq_combination childrenC_618_i8 childrenD_618_i8 (6, 4) required_618_i8
    (by decide +kernel) child_required_sub_618_i8 common_sub_618_i8 required_origin_618_i8
theorem envelope_origin_618_i8 : ∀ x ∈ envelope_618_i8,
    x = (6, 4) ∨ ∃ j, x ∈ childrenD_618_i8 j := by decide +kernel
theorem envelope_exact_618_i8 : envelope_618_i8 =
    insert (6, 4) (Finset.univ.biUnion childrenD_618_i8) := by
  exact envelope_eq_combination childrenD_618_i8 (6, 4) envelope_618_i8
    pivot_mem_618_i8 child_envelope_sub_618_i8 envelope_origin_618_i8
def checked_618_i8 : CheckedCard where
  required := required_618_i8
  envelope := envelope_618_i8
  height := height_618_i8
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_618_i8
def height_618_i7 : ℕ := 5
def childrenH_618_i7 : Fin 2 → ℕ := ![height_5, height_618_i8]
theorem height_exact_618_i7 : height_618_i7 = 1 + Finset.univ.sup childrenH_618_i7 := by decide +kernel
theorem required_origin_618_i7 : ∀ x ∈ required_618_i7,
    (∃ j, x ∈ childrenC_618_i7 j) ∨ ∀ j, x ∈ childrenD_618_i7 j := by decide +kernel
theorem required_exact_618_i7 : required_618_i7 =
    ((Finset.univ.biUnion childrenC_618_i7) ∪ commonEnvelope childrenD_618_i7).erase (3, 4) := by
  exact required_eq_combination childrenC_618_i7 childrenD_618_i7 (3, 4) required_618_i7
    (by decide +kernel) child_required_sub_618_i7 common_sub_618_i7 required_origin_618_i7
theorem envelope_origin_618_i7 : ∀ x ∈ envelope_618_i7,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_618_i7 j := by decide +kernel
theorem envelope_exact_618_i7 : envelope_618_i7 =
    insert (3, 4) (Finset.univ.biUnion childrenD_618_i7) := by
  exact envelope_eq_combination childrenD_618_i7 (3, 4) envelope_618_i7
    pivot_mem_618_i7 child_envelope_sub_618_i7 envelope_origin_618_i7
def checked_618_i7 : CheckedCard where
  required := required_618_i7
  envelope := envelope_618_i7
  height := height_618_i7
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_618_i7
def height_618_i6 : ℕ := 11
def childrenH_618_i6 : Fin 4 → ℕ := ![height_80, height_111, height_616, height_618_i7]
theorem height_exact_618_i6 : height_618_i6 = 1 + Finset.univ.sup childrenH_618_i6 := by decide +kernel
theorem required_origin_618_i6 : ∀ x ∈ required_618_i6,
    (∃ j, x ∈ childrenC_618_i6 j) ∨ ∀ j, x ∈ childrenD_618_i6 j := by decide +kernel
theorem required_exact_618_i6 : required_618_i6 =
    ((Finset.univ.biUnion childrenC_618_i6) ∪ commonEnvelope childrenD_618_i6).erase (4, 4) := by
  exact required_eq_combination childrenC_618_i6 childrenD_618_i6 (4, 4) required_618_i6
    (by decide +kernel) child_required_sub_618_i6 common_sub_618_i6 required_origin_618_i6
theorem envelope_origin_618_i6 : ∀ x ∈ envelope_618_i6,
    x = (4, 4) ∨ ∃ j, x ∈ childrenD_618_i6 j := by decide +kernel
theorem envelope_exact_618_i6 : envelope_618_i6 =
    insert (4, 4) (Finset.univ.biUnion childrenD_618_i6) := by
  exact envelope_eq_combination childrenD_618_i6 (4, 4) envelope_618_i6
    pivot_mem_618_i6 child_envelope_sub_618_i6 envelope_origin_618_i6
def checked_618_i6 : CheckedCard where
  required := required_618_i6
  envelope := envelope_618_i6
  height := height_618_i6
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_618_i6
def height_618 : ℕ := 12
def childrenH_618 : Fin 9 → ℕ := ![height_398, height_434, height_610, height_618_i0, height_618_i3, height_618_i4, height_618_i5, height_615, height_618_i6]
theorem height_exact_618 : height_618 = 1 + Finset.univ.sup childrenH_618 := by decide +kernel
theorem required_origin_618 : ∀ x ∈ required_618,
    (∃ j, x ∈ childrenC_618 j) ∨ ∀ j, x ∈ childrenD_618 j := by decide +kernel
theorem required_exact_618 : required_618 =
    ((Finset.univ.biUnion childrenC_618) ∪ commonEnvelope childrenD_618).erase (5, 5) := by
  exact required_eq_combination childrenC_618 childrenD_618 (5, 5) required_618
    (by decide +kernel) child_required_sub_618 common_sub_618 required_origin_618
theorem envelope_origin_618 : ∀ x ∈ envelope_618,
    x = (5, 5) ∨ ∃ j, x ∈ childrenD_618 j := by decide +kernel
theorem envelope_exact_618 : envelope_618 =
    insert (5, 5) (Finset.univ.biUnion childrenD_618) := by
  exact envelope_eq_combination childrenD_618 (5, 5) envelope_618
    pivot_mem_618 child_envelope_sub_618 envelope_origin_618
def checked_618 : CheckedCard where
  required := required_618
  envelope := envelope_618
  height := height_618
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_618
end SnakyPrototype.Certificate21

end OAI
