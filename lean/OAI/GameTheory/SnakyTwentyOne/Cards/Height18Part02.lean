import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height11Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height11Part06
import OAI.GameTheory.SnakyTwentyOne.Cards.Height14Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height15Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height16Part02
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_701_i1 : Finset Cell := ⟨(([(5, 7), (5, 10), (6, 7), (7, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_701_i1 : Finset Cell := ⟨(([(4, 8), (4, 10), (4, 11), (4, 12), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (6, 6), (6, 7), (6, 10), (6, 11), (6, 12), (7, 7), (8, 6), (8, 7), (8, 8), (9, 6), (9, 7), (9, 8), (10, 6), (10, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_701_i1 : Fin 2 → Finset Cell := ![(placed21 3 (4, 8) required_10), (placed21 2 (6, 6) required_39)]
def childrenD_701_i1 : Fin 2 → Finset Cell := ![(placed21 3 (4, 8) envelope_10), (placed21 2 (6, 6) envelope_39)]
theorem common_sub_701_i1 : commonEnvelope childrenD_701_i1 ⊆ insert (5, 8) required_701_i1 := by decide +kernel
theorem child_required_sub_701_i1 : ∀ j, childrenC_701_i1 j ⊆ insert (5, 8) required_701_i1 := by decide +kernel
theorem child_envelope_sub_701_i1 : ∀ j, childrenD_701_i1 j ⊆ envelope_701_i1 := by decide +kernel
theorem pivot_mem_701_i1 : (5, 8) ∈ envelope_701_i1 := by decide +kernel
theorem children_work_701_i1 : ∀ j, Template HasSnaky 4 (childrenC_701_i1 j) (childrenD_701_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_10 3 (4, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_39 2 (6, 6)).mono (by decide +kernel)
theorem row_works_701_i1 : Template HasSnaky 5 required_701_i1 envelope_701_i1 := by
  refine compose HasSnaky 4 childrenC_701_i1 childrenD_701_i1 children_work_701_i1 (5, 8)
    required_701_i1 envelope_701_i1 pivot_mem_701_i1 child_required_sub_701_i1 child_envelope_sub_701_i1 ?_
  intro b hb
  exact common_sub_701_i1 (mem_commonEnvelope childrenD_701_i1 b hb)
def required_701_i2 : Finset Cell := ⟨(([(5, 7), (5, 10), (6, 7), (7, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_701_i2 : Finset Cell := ⟨(([(1, 9), (1, 11), (2, 8), (2, 9), (2, 10), (2, 11), (3, 8), (3, 9), (3, 10), (3, 11), (4, 7), (4, 8), (4, 10), (4, 11), (5, 7), (5, 8), (5, 9), (5, 10), (6, 6), (6, 7), (6, 9), (6, 10), (6, 11), (7, 7), (7, 9), (7, 10), (7, 11), (8, 7), (8, 9), (8, 10), (8, 11), (9, 9), (9, 10), (9, 11), (10, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_701_i2 : Fin 2 → Finset Cell := ![(placed21 5 (8, 7) required_52), (placed21 1 (1, 6) required_325)]
def childrenD_701_i2 : Fin 2 → Finset Cell := ![(placed21 5 (8, 7) envelope_52), (placed21 1 (1, 6) envelope_325)]
theorem common_sub_701_i2 : commonEnvelope childrenD_701_i2 ⊆ insert (5, 8) required_701_i2 := by decide +kernel
theorem child_required_sub_701_i2 : ∀ j, childrenC_701_i2 j ⊆ insert (5, 8) required_701_i2 := by decide +kernel
theorem child_envelope_sub_701_i2 : ∀ j, childrenD_701_i2 j ⊆ envelope_701_i2 := by decide +kernel
theorem pivot_mem_701_i2 : (5, 8) ∈ envelope_701_i2 := by decide +kernel
theorem children_work_701_i2 : ∀ j, Template HasSnaky 9 (childrenC_701_i2 j) (childrenD_701_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_52 5 (8, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_325 1 (1, 6)).mono (by decide +kernel)
theorem row_works_701_i2 : Template HasSnaky 10 required_701_i2 envelope_701_i2 := by
  refine compose HasSnaky 9 childrenC_701_i2 childrenD_701_i2 children_work_701_i2 (5, 8)
    required_701_i2 envelope_701_i2 pivot_mem_701_i2 child_required_sub_701_i2 child_envelope_sub_701_i2 ?_
  intro b hb
  exact common_sub_701_i2 (mem_commonEnvelope childrenD_701_i2 b hb)
def required_701_i3 : Finset Cell := ⟨(([(5, 7), (5, 10), (6, 7), (7, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_701_i3 : Finset Cell := ⟨(([(2, 6), (2, 8), (2, 9), (2, 11), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (5, 7), (5, 10), (5, 11), (5, 12), (6, 6), (6, 7), (6, 9), (6, 10), (6, 11), (6, 12), (6, 13), (6, 14), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (7, 12), (7, 13), (7, 14), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (8, 11), (8, 12), (8, 13), (8, 14), (9, 6), (9, 7), (9, 8), (9, 9), (9, 10), (9, 11), (9, 12), (9, 13), (9, 14), (10, 6), (10, 9), (10, 10), (10, 11), (11, 9), (11, 11)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_701_i3 : Fin 2 → Finset Cell := ![(placed21 2 (7, 6) required_8), (placed21 1 (2, 6) required_463)]
def childrenD_701_i3 : Fin 2 → Finset Cell := ![(placed21 2 (7, 6) envelope_8), (placed21 1 (2, 6) envelope_463)]
theorem common_sub_701_i3 : commonEnvelope childrenD_701_i3 ⊆ insert (4, 7) required_701_i3 := by decide +kernel
theorem child_required_sub_701_i3 : ∀ j, childrenC_701_i3 j ⊆ insert (4, 7) required_701_i3 := by decide +kernel
theorem child_envelope_sub_701_i3 : ∀ j, childrenD_701_i3 j ⊆ envelope_701_i3 := by decide +kernel
theorem pivot_mem_701_i3 : (4, 7) ∈ envelope_701_i3 := by decide +kernel
theorem children_work_701_i3 : ∀ j, Template HasSnaky 11 (childrenC_701_i3 j) (childrenD_701_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_8 2 (7, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_463 1 (2, 6)).mono (by decide +kernel)
theorem row_works_701_i3 : Template HasSnaky 12 required_701_i3 envelope_701_i3 := by
  refine compose HasSnaky 11 childrenC_701_i3 childrenD_701_i3 children_work_701_i3 (4, 7)
    required_701_i3 envelope_701_i3 pivot_mem_701_i3 child_required_sub_701_i3 child_envelope_sub_701_i3 ?_
  intro b hb
  exact common_sub_701_i3 (mem_commonEnvelope childrenD_701_i3 b hb)
def required_701_i4 : Finset Cell := ⟨(([(5, 7), (5, 10), (6, 7), (7, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_701_i4 : Finset Cell := ⟨(([(3, 6), (3, 8), (3, 9), (3, 10), (3, 11), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (6, 7), (7, 7), (8, 6), (8, 7), (8, 8), (9, 6), (9, 7), (9, 8), (10, 6), (10, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_701_i4 : Fin 2 → Finset Cell := ![(placed21 3 (4, 8) required_18), (placed21 2 (7, 6) required_348)]
def childrenD_701_i4 : Fin 2 → Finset Cell := ![(placed21 3 (4, 8) envelope_18), (placed21 2 (7, 6) envelope_348)]
theorem common_sub_701_i4 : commonEnvelope childrenD_701_i4 ⊆ insert (4, 8) required_701_i4 := by decide +kernel
theorem child_required_sub_701_i4 : ∀ j, childrenC_701_i4 j ⊆ insert (4, 8) required_701_i4 := by decide +kernel
theorem child_envelope_sub_701_i4 : ∀ j, childrenD_701_i4 j ⊆ envelope_701_i4 := by decide +kernel
theorem pivot_mem_701_i4 : (4, 8) ∈ envelope_701_i4 := by decide +kernel
theorem children_work_701_i4 : ∀ j, Template HasSnaky 6 (childrenC_701_i4 j) (childrenD_701_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_18 3 (4, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_348 2 (7, 6)).mono (by decide +kernel)
theorem row_works_701_i4 : Template HasSnaky 7 required_701_i4 envelope_701_i4 := by
  refine compose HasSnaky 6 childrenC_701_i4 childrenD_701_i4 children_work_701_i4 (4, 8)
    required_701_i4 envelope_701_i4 pivot_mem_701_i4 child_required_sub_701_i4 child_envelope_sub_701_i4 ?_
  intro b hb
  exact common_sub_701_i4 (mem_commonEnvelope childrenD_701_i4 b hb)
def required_701_i6 : Finset Cell := ⟨(([(5, 7), (5, 8), (5, 10), (6, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_701_i6 : Finset Cell := ⟨(([(4, 6), (4, 7), (4, 8), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (6, 6), (6, 7), (6, 10), (6, 11), (6, 12)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_701_i6 : Fin 2 → Finset Cell := ![(placed21 3 (5, 10) required_5), (placed21 0 (4, 6) required_9)]
def childrenD_701_i6 : Fin 2 → Finset Cell := ![(placed21 3 (5, 10) envelope_5), (placed21 0 (4, 6) envelope_9)]
theorem common_sub_701_i6 : commonEnvelope childrenD_701_i6 ⊆ insert (5, 9) required_701_i6 := by decide +kernel
theorem child_required_sub_701_i6 : ∀ j, childrenC_701_i6 j ⊆ insert (5, 9) required_701_i6 := by decide +kernel
theorem child_envelope_sub_701_i6 : ∀ j, childrenD_701_i6 j ⊆ envelope_701_i6 := by decide +kernel
theorem pivot_mem_701_i6 : (5, 9) ∈ envelope_701_i6 := by decide +kernel
theorem children_work_701_i6 : ∀ j, Template HasSnaky 3 (childrenC_701_i6 j) (childrenD_701_i6 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 3 (5, 10)).mono (by decide +kernel)
  · exact (placed21_template row_works_9 0 (4, 6)).mono (by decide +kernel)
theorem row_works_701_i6 : Template HasSnaky 4 required_701_i6 envelope_701_i6 := by
  refine compose HasSnaky 3 childrenC_701_i6 childrenD_701_i6 children_work_701_i6 (5, 9)
    required_701_i6 envelope_701_i6 pivot_mem_701_i6 child_required_sub_701_i6 child_envelope_sub_701_i6 ?_
  intro b hb
  exact common_sub_701_i6 (mem_commonEnvelope childrenD_701_i6 b hb)
def required_701_i7 : Finset Cell := ⟨(([(5, 7), (5, 8), (5, 10), (6, 7), (7, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_701_i7 : Finset Cell := ⟨(([(4, 6), (4, 7), (4, 9), (5, 7), (5, 8), (5, 9), (5, 10), (6, 6), (6, 7), (6, 9), (6, 10), (6, 11), (7, 7), (7, 8), (7, 10), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (8, 11), (9, 6), (9, 7), (9, 8), (9, 10), (9, 11), (10, 6), (10, 11)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_701_i7 : Fin 2 → Finset Cell := ![(placed21 3 (5, 10) required_5), (placed21 0 (4, 6) required_372)]
def childrenD_701_i7 : Fin 2 → Finset Cell := ![(placed21 3 (5, 10) envelope_5), (placed21 0 (4, 6) envelope_372)]
theorem common_sub_701_i7 : commonEnvelope childrenD_701_i7 ⊆ insert (5, 9) required_701_i7 := by decide +kernel
theorem child_required_sub_701_i7 : ∀ j, childrenC_701_i7 j ⊆ insert (5, 9) required_701_i7 := by decide +kernel
theorem child_envelope_sub_701_i7 : ∀ j, childrenD_701_i7 j ⊆ envelope_701_i7 := by decide +kernel
theorem pivot_mem_701_i7 : (5, 9) ∈ envelope_701_i7 := by decide +kernel
theorem children_work_701_i7 : ∀ j, Template HasSnaky 7 (childrenC_701_i7 j) (childrenD_701_i7 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 3 (5, 10)).mono (by decide +kernel)
  · exact (placed21_template row_works_372 0 (4, 6)).mono (by decide +kernel)
theorem row_works_701_i7 : Template HasSnaky 8 required_701_i7 envelope_701_i7 := by
  refine compose HasSnaky 7 childrenC_701_i7 childrenD_701_i7 children_work_701_i7 (5, 9)
    required_701_i7 envelope_701_i7 pivot_mem_701_i7 child_required_sub_701_i7 child_envelope_sub_701_i7 ?_
  intro b hb
  exact common_sub_701_i7 (mem_commonEnvelope childrenD_701_i7 b hb)
def required_701_i5 : Finset Cell := ⟨(([(5, 7), (5, 10), (6, 7), (7, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_701_i5 : Finset Cell := ⟨(([(4, 6), (4, 7), (4, 8), (4, 9), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (6, 6), (6, 7), (6, 9), (6, 10), (6, 11), (6, 12), (7, 7), (7, 8), (7, 10), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (8, 11), (9, 6), (9, 7), (9, 8), (9, 10), (9, 11), (10, 6), (10, 8), (10, 11)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_701_i5 : Fin 3 → Finset Cell := ![(placed21 3 (4, 8) required_10), required_701_i6, required_701_i7]
def childrenD_701_i5 : Fin 3 → Finset Cell := ![(placed21 3 (4, 8) envelope_10), envelope_701_i6, envelope_701_i7]
theorem common_sub_701_i5 : commonEnvelope childrenD_701_i5 ⊆ insert (5, 8) required_701_i5 := by decide +kernel
theorem child_required_sub_701_i5 : ∀ j, childrenC_701_i5 j ⊆ insert (5, 8) required_701_i5 := by decide +kernel
theorem child_envelope_sub_701_i5 : ∀ j, childrenD_701_i5 j ⊆ envelope_701_i5 := by decide +kernel
theorem pivot_mem_701_i5 : (5, 8) ∈ envelope_701_i5 := by decide +kernel
theorem children_work_701_i5 : ∀ j, Template HasSnaky 8 (childrenC_701_i5 j) (childrenD_701_i5 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_10 3 (4, 8)).mono (by decide +kernel)
  · exact row_works_701_i6.mono (by decide +kernel)
  · exact row_works_701_i7.mono (by decide +kernel)
theorem row_works_701_i5 : Template HasSnaky 9 required_701_i5 envelope_701_i5 := by
  refine compose HasSnaky 8 childrenC_701_i5 childrenD_701_i5 children_work_701_i5 (5, 8)
    required_701_i5 envelope_701_i5 pivot_mem_701_i5 child_required_sub_701_i5 child_envelope_sub_701_i5 ?_
  intro b hb
  exact common_sub_701_i5 (mem_commonEnvelope childrenD_701_i5 b hb)
def required_701_i0 : Finset Cell := ⟨(([(5, 7), (6, 7), (7, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_701_i0 : Finset Cell := ⟨(([(0, 8), (0, 9), (0, 11), (0, 13), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (1, 13), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (2, 13), (2, 14), (2, 15), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (3, 13), (3, 14), (3, 15), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (4, 13), (4, 14), (4, 15), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (5, 12), (5, 13), (5, 14), (5, 15), (6, 6), (6, 7), (6, 9), (6, 10), (6, 11), (6, 12), (6, 13), (6, 14), (6, 15), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (7, 12), (7, 13), (7, 14), (7, 15), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (8, 11), (8, 12), (8, 13), (8, 14), (9, 6), (9, 7), (9, 8), (9, 9), (9, 10), (9, 11), (9, 12), (9, 13), (9, 14), (10, 6), (10, 8), (10, 9), (10, 10), (10, 11), (10, 13), (11, 9), (11, 11)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_701_i0 : Fin 7 → Finset Cell := ![required_701_i1, (placed21 5 (10, 6) required_683), required_701_i2, required_701_i3, required_701_i4, (placed21 1 (2, 6) required_700), required_701_i5]
def childrenD_701_i0 : Fin 7 → Finset Cell := ![envelope_701_i1, (placed21 5 (10, 6) envelope_683), envelope_701_i2, envelope_701_i3, envelope_701_i4, (placed21 1 (2, 6) envelope_700), envelope_701_i5]
theorem common_sub_701_i0 : commonEnvelope childrenD_701_i0 ⊆ insert (5, 10) required_701_i0 := by decide +kernel
theorem child_required_sub_701_i0 : ∀ j, childrenC_701_i0 j ⊆ insert (5, 10) required_701_i0 := by decide +kernel
theorem child_envelope_sub_701_i0 : ∀ j, childrenD_701_i0 j ⊆ envelope_701_i0 := by decide +kernel
theorem pivot_mem_701_i0 : (5, 10) ∈ envelope_701_i0 := by decide +kernel
theorem children_work_701_i0 : ∀ j, Template HasSnaky 16 (childrenC_701_i0 j) (childrenD_701_i0 j) := by
  intro j
  fin_cases j
  · exact row_works_701_i1.mono (by decide +kernel)
  · exact (placed21_template row_works_683 5 (10, 6)).mono (by decide +kernel)
  · exact row_works_701_i2.mono (by decide +kernel)
  · exact row_works_701_i3.mono (by decide +kernel)
  · exact row_works_701_i4.mono (by decide +kernel)
  · exact (placed21_template row_works_700 1 (2, 6)).mono (by decide +kernel)
  · exact row_works_701_i5.mono (by decide +kernel)
theorem row_works_701_i0 : Template HasSnaky 17 required_701_i0 envelope_701_i0 := by
  refine compose HasSnaky 16 childrenC_701_i0 childrenD_701_i0 children_work_701_i0 (5, 10)
    required_701_i0 envelope_701_i0 pivot_mem_701_i0 child_required_sub_701_i0 child_envelope_sub_701_i0 ?_
  intro b hb
  exact common_sub_701_i0 (mem_commonEnvelope childrenD_701_i0 b hb)
def required_701 : Finset Cell := ⟨(([(5, 7), (6, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_701 : Finset Cell := ⟨(([(0, 3), (0, 5), (0, 8), (0, 9), (0, 11), (0, 13), (1, 3), (1, 4), (1, 5), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (1, 13), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (2, 13), (2, 14), (2, 15), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (3, 13), (3, 14), (3, 15), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (4, 13), (4, 14), (4, 15), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (5, 12), (5, 13), (5, 14), (5, 15), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 9), (6, 10), (6, 11), (6, 12), (6, 13), (6, 14), (6, 15), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (7, 12), (7, 13), (7, 14), (7, 15), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (8, 11), (8, 12), (8, 13), (8, 14), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (9, 10), (9, 11), (9, 12), (9, 13), (9, 14), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (10, 9), (10, 10), (10, 11), (10, 12), (10, 13), (11, 4), (11, 5), (11, 6), (11, 7), (11, 8), (11, 9), (11, 11), (12, 4), (12, 6), (12, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_701 : Fin 6 → Finset Cell := ![(placed21 3 (3, 8) required_12), (placed21 2 (8, 3) required_322), (placed21 0 (4, 4) required_435), (placed21 6 (9, 10) required_697), (placed21 0 (1, 2) required_699), required_701_i0]
def childrenD_701 : Fin 6 → Finset Cell := ![(placed21 3 (3, 8) envelope_12), (placed21 2 (8, 3) envelope_322), (placed21 0 (4, 4) envelope_435), (placed21 6 (9, 10) envelope_697), (placed21 0 (1, 2) envelope_699), envelope_701_i0]
theorem common_sub_701 : commonEnvelope childrenD_701 ⊆ insert (7, 7) required_701 := by decide +kernel
theorem child_required_sub_701 : ∀ j, childrenC_701 j ⊆ insert (7, 7) required_701 := by decide +kernel
theorem child_envelope_sub_701 : ∀ j, childrenD_701 j ⊆ envelope_701 := by decide +kernel
theorem pivot_mem_701 : (7, 7) ∈ envelope_701 := by decide +kernel
theorem children_work_701 : ∀ j, Template HasSnaky 17 (childrenC_701 j) (childrenD_701 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_12 3 (3, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_322 2 (8, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_435 0 (4, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_697 6 (9, 10)).mono (by decide +kernel)
  · exact (placed21_template row_works_699 0 (1, 2)).mono (by decide +kernel)
  · exact row_works_701_i0.mono (by decide +kernel)
theorem row_works_701 : Template HasSnaky 18 required_701 envelope_701 := by
  refine compose HasSnaky 17 childrenC_701 childrenD_701 children_work_701 (7, 7)
    required_701 envelope_701 pivot_mem_701 child_required_sub_701 child_envelope_sub_701 ?_
  intro b hb
  exact common_sub_701 (mem_commonEnvelope childrenD_701 b hb)
def height_701_i1 : ℕ := 5
def childrenH_701_i1 : Fin 2 → ℕ := ![height_10, height_39]
theorem height_exact_701_i1 : height_701_i1 = 1 + Finset.univ.sup childrenH_701_i1 := by decide +kernel
theorem required_origin_701_i1 : ∀ x ∈ required_701_i1,
    (∃ j, x ∈ childrenC_701_i1 j) ∨ ∀ j, x ∈ childrenD_701_i1 j := by decide +kernel
theorem required_exact_701_i1 : required_701_i1 =
    ((Finset.univ.biUnion childrenC_701_i1) ∪ commonEnvelope childrenD_701_i1).erase (5, 8) := by
  exact required_eq_combination childrenC_701_i1 childrenD_701_i1 (5, 8) required_701_i1
    (by decide +kernel) child_required_sub_701_i1 common_sub_701_i1 required_origin_701_i1
theorem envelope_origin_701_i1 : ∀ x ∈ envelope_701_i1,
    x = (5, 8) ∨ ∃ j, x ∈ childrenD_701_i1 j := by decide +kernel
theorem envelope_exact_701_i1 : envelope_701_i1 =
    insert (5, 8) (Finset.univ.biUnion childrenD_701_i1) := by
  exact envelope_eq_combination childrenD_701_i1 (5, 8) envelope_701_i1
    pivot_mem_701_i1 child_envelope_sub_701_i1 envelope_origin_701_i1
def checked_701_i1 : CheckedCard where
  required := required_701_i1
  envelope := envelope_701_i1
  height := height_701_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_701_i1
def height_701_i2 : ℕ := 10
def childrenH_701_i2 : Fin 2 → ℕ := ![height_52, height_325]
theorem height_exact_701_i2 : height_701_i2 = 1 + Finset.univ.sup childrenH_701_i2 := by decide +kernel
theorem required_origin_701_i2 : ∀ x ∈ required_701_i2,
    (∃ j, x ∈ childrenC_701_i2 j) ∨ ∀ j, x ∈ childrenD_701_i2 j := by decide +kernel
theorem required_exact_701_i2 : required_701_i2 =
    ((Finset.univ.biUnion childrenC_701_i2) ∪ commonEnvelope childrenD_701_i2).erase (5, 8) := by
  exact required_eq_combination childrenC_701_i2 childrenD_701_i2 (5, 8) required_701_i2
    (by decide +kernel) child_required_sub_701_i2 common_sub_701_i2 required_origin_701_i2
theorem envelope_origin_701_i2 : ∀ x ∈ envelope_701_i2,
    x = (5, 8) ∨ ∃ j, x ∈ childrenD_701_i2 j := by decide +kernel
theorem envelope_exact_701_i2 : envelope_701_i2 =
    insert (5, 8) (Finset.univ.biUnion childrenD_701_i2) := by
  exact envelope_eq_combination childrenD_701_i2 (5, 8) envelope_701_i2
    pivot_mem_701_i2 child_envelope_sub_701_i2 envelope_origin_701_i2
def checked_701_i2 : CheckedCard where
  required := required_701_i2
  envelope := envelope_701_i2
  height := height_701_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_701_i2
def height_701_i3 : ℕ := 12
def childrenH_701_i3 : Fin 2 → ℕ := ![height_8, height_463]
theorem height_exact_701_i3 : height_701_i3 = 1 + Finset.univ.sup childrenH_701_i3 := by decide +kernel
theorem required_origin_701_i3 : ∀ x ∈ required_701_i3,
    (∃ j, x ∈ childrenC_701_i3 j) ∨ ∀ j, x ∈ childrenD_701_i3 j := by decide +kernel
theorem required_exact_701_i3 : required_701_i3 =
    ((Finset.univ.biUnion childrenC_701_i3) ∪ commonEnvelope childrenD_701_i3).erase (4, 7) := by
  exact required_eq_combination childrenC_701_i3 childrenD_701_i3 (4, 7) required_701_i3
    (by decide +kernel) child_required_sub_701_i3 common_sub_701_i3 required_origin_701_i3
theorem envelope_origin_701_i3 : ∀ x ∈ envelope_701_i3,
    x = (4, 7) ∨ ∃ j, x ∈ childrenD_701_i3 j := by decide +kernel
theorem envelope_exact_701_i3 : envelope_701_i3 =
    insert (4, 7) (Finset.univ.biUnion childrenD_701_i3) := by
  exact envelope_eq_combination childrenD_701_i3 (4, 7) envelope_701_i3
    pivot_mem_701_i3 child_envelope_sub_701_i3 envelope_origin_701_i3
def checked_701_i3 : CheckedCard where
  required := required_701_i3
  envelope := envelope_701_i3
  height := height_701_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_701_i3
def height_701_i4 : ℕ := 7
def childrenH_701_i4 : Fin 2 → ℕ := ![height_18, height_348]
theorem height_exact_701_i4 : height_701_i4 = 1 + Finset.univ.sup childrenH_701_i4 := by decide +kernel
theorem required_origin_701_i4 : ∀ x ∈ required_701_i4,
    (∃ j, x ∈ childrenC_701_i4 j) ∨ ∀ j, x ∈ childrenD_701_i4 j := by decide +kernel
theorem required_exact_701_i4 : required_701_i4 =
    ((Finset.univ.biUnion childrenC_701_i4) ∪ commonEnvelope childrenD_701_i4).erase (4, 8) := by
  exact required_eq_combination childrenC_701_i4 childrenD_701_i4 (4, 8) required_701_i4
    (by decide +kernel) child_required_sub_701_i4 common_sub_701_i4 required_origin_701_i4
theorem envelope_origin_701_i4 : ∀ x ∈ envelope_701_i4,
    x = (4, 8) ∨ ∃ j, x ∈ childrenD_701_i4 j := by decide +kernel
theorem envelope_exact_701_i4 : envelope_701_i4 =
    insert (4, 8) (Finset.univ.biUnion childrenD_701_i4) := by
  exact envelope_eq_combination childrenD_701_i4 (4, 8) envelope_701_i4
    pivot_mem_701_i4 child_envelope_sub_701_i4 envelope_origin_701_i4
def checked_701_i4 : CheckedCard where
  required := required_701_i4
  envelope := envelope_701_i4
  height := height_701_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_701_i4
def height_701_i6 : ℕ := 4
def childrenH_701_i6 : Fin 2 → ℕ := ![height_5, height_9]
theorem height_exact_701_i6 : height_701_i6 = 1 + Finset.univ.sup childrenH_701_i6 := by decide +kernel
theorem required_origin_701_i6 : ∀ x ∈ required_701_i6,
    (∃ j, x ∈ childrenC_701_i6 j) ∨ ∀ j, x ∈ childrenD_701_i6 j := by decide +kernel
theorem required_exact_701_i6 : required_701_i6 =
    ((Finset.univ.biUnion childrenC_701_i6) ∪ commonEnvelope childrenD_701_i6).erase (5, 9) := by
  exact required_eq_combination childrenC_701_i6 childrenD_701_i6 (5, 9) required_701_i6
    (by decide +kernel) child_required_sub_701_i6 common_sub_701_i6 required_origin_701_i6
theorem envelope_origin_701_i6 : ∀ x ∈ envelope_701_i6,
    x = (5, 9) ∨ ∃ j, x ∈ childrenD_701_i6 j := by decide +kernel
theorem envelope_exact_701_i6 : envelope_701_i6 =
    insert (5, 9) (Finset.univ.biUnion childrenD_701_i6) := by
  exact envelope_eq_combination childrenD_701_i6 (5, 9) envelope_701_i6
    pivot_mem_701_i6 child_envelope_sub_701_i6 envelope_origin_701_i6
def checked_701_i6 : CheckedCard where
  required := required_701_i6
  envelope := envelope_701_i6
  height := height_701_i6
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_701_i6
def height_701_i7 : ℕ := 8
def childrenH_701_i7 : Fin 2 → ℕ := ![height_5, height_372]
theorem height_exact_701_i7 : height_701_i7 = 1 + Finset.univ.sup childrenH_701_i7 := by decide +kernel
theorem required_origin_701_i7 : ∀ x ∈ required_701_i7,
    (∃ j, x ∈ childrenC_701_i7 j) ∨ ∀ j, x ∈ childrenD_701_i7 j := by decide +kernel
theorem required_exact_701_i7 : required_701_i7 =
    ((Finset.univ.biUnion childrenC_701_i7) ∪ commonEnvelope childrenD_701_i7).erase (5, 9) := by
  exact required_eq_combination childrenC_701_i7 childrenD_701_i7 (5, 9) required_701_i7
    (by decide +kernel) child_required_sub_701_i7 common_sub_701_i7 required_origin_701_i7
theorem envelope_origin_701_i7 : ∀ x ∈ envelope_701_i7,
    x = (5, 9) ∨ ∃ j, x ∈ childrenD_701_i7 j := by decide +kernel
theorem envelope_exact_701_i7 : envelope_701_i7 =
    insert (5, 9) (Finset.univ.biUnion childrenD_701_i7) := by
  exact envelope_eq_combination childrenD_701_i7 (5, 9) envelope_701_i7
    pivot_mem_701_i7 child_envelope_sub_701_i7 envelope_origin_701_i7
def checked_701_i7 : CheckedCard where
  required := required_701_i7
  envelope := envelope_701_i7
  height := height_701_i7
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_701_i7
def height_701_i5 : ℕ := 9
def childrenH_701_i5 : Fin 3 → ℕ := ![height_10, height_701_i6, height_701_i7]
theorem height_exact_701_i5 : height_701_i5 = 1 + Finset.univ.sup childrenH_701_i5 := by decide +kernel
theorem required_origin_701_i5 : ∀ x ∈ required_701_i5,
    (∃ j, x ∈ childrenC_701_i5 j) ∨ ∀ j, x ∈ childrenD_701_i5 j := by decide +kernel
theorem required_exact_701_i5 : required_701_i5 =
    ((Finset.univ.biUnion childrenC_701_i5) ∪ commonEnvelope childrenD_701_i5).erase (5, 8) := by
  exact required_eq_combination childrenC_701_i5 childrenD_701_i5 (5, 8) required_701_i5
    (by decide +kernel) child_required_sub_701_i5 common_sub_701_i5 required_origin_701_i5
theorem envelope_origin_701_i5 : ∀ x ∈ envelope_701_i5,
    x = (5, 8) ∨ ∃ j, x ∈ childrenD_701_i5 j := by decide +kernel
theorem envelope_exact_701_i5 : envelope_701_i5 =
    insert (5, 8) (Finset.univ.biUnion childrenD_701_i5) := by
  exact envelope_eq_combination childrenD_701_i5 (5, 8) envelope_701_i5
    pivot_mem_701_i5 child_envelope_sub_701_i5 envelope_origin_701_i5
def checked_701_i5 : CheckedCard where
  required := required_701_i5
  envelope := envelope_701_i5
  height := height_701_i5
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_701_i5
def height_701_i0 : ℕ := 17
def childrenH_701_i0 : Fin 7 → ℕ := ![height_701_i1, height_683, height_701_i2, height_701_i3, height_701_i4, height_700, height_701_i5]
theorem height_exact_701_i0 : height_701_i0 = 1 + Finset.univ.sup childrenH_701_i0 := by decide +kernel
theorem required_origin_701_i0 : ∀ x ∈ required_701_i0,
    (∃ j, x ∈ childrenC_701_i0 j) ∨ ∀ j, x ∈ childrenD_701_i0 j := by decide +kernel
theorem required_exact_701_i0 : required_701_i0 =
    ((Finset.univ.biUnion childrenC_701_i0) ∪ commonEnvelope childrenD_701_i0).erase (5, 10) := by
  exact required_eq_combination childrenC_701_i0 childrenD_701_i0 (5, 10) required_701_i0
    (by decide +kernel) child_required_sub_701_i0 common_sub_701_i0 required_origin_701_i0
theorem envelope_origin_701_i0 : ∀ x ∈ envelope_701_i0,
    x = (5, 10) ∨ ∃ j, x ∈ childrenD_701_i0 j := by decide +kernel
theorem envelope_exact_701_i0 : envelope_701_i0 =
    insert (5, 10) (Finset.univ.biUnion childrenD_701_i0) := by
  exact envelope_eq_combination childrenD_701_i0 (5, 10) envelope_701_i0
    pivot_mem_701_i0 child_envelope_sub_701_i0 envelope_origin_701_i0
def checked_701_i0 : CheckedCard where
  required := required_701_i0
  envelope := envelope_701_i0
  height := height_701_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_701_i0
def height_701 : ℕ := 18
def childrenH_701 : Fin 6 → ℕ := ![height_12, height_322, height_435, height_697, height_699, height_701_i0]
theorem height_exact_701 : height_701 = 1 + Finset.univ.sup childrenH_701 := by decide +kernel
theorem required_origin_701 : ∀ x ∈ required_701,
    (∃ j, x ∈ childrenC_701 j) ∨ ∀ j, x ∈ childrenD_701 j := by decide +kernel
theorem required_exact_701 : required_701 =
    ((Finset.univ.biUnion childrenC_701) ∪ commonEnvelope childrenD_701).erase (7, 7) := by
  exact required_eq_combination childrenC_701 childrenD_701 (7, 7) required_701
    (by decide +kernel) child_required_sub_701 common_sub_701 required_origin_701
theorem envelope_origin_701 : ∀ x ∈ envelope_701,
    x = (7, 7) ∨ ∃ j, x ∈ childrenD_701 j := by decide +kernel
theorem envelope_exact_701 : envelope_701 =
    insert (7, 7) (Finset.univ.biUnion childrenD_701) := by
  exact envelope_eq_combination childrenD_701 (7, 7) envelope_701
    pivot_mem_701 child_envelope_sub_701 envelope_origin_701
def checked_701 : CheckedCard where
  required := required_701
  envelope := envelope_701
  height := height_701
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_701
end SnakyPrototype.Certificate21

end OAI
