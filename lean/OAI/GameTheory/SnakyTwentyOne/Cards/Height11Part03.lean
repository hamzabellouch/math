import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part06
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part06
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part06
import OAI.GameTheory.SnakyTwentyOne.Cards.Height10Part01
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_596_i1 : Finset Cell := ⟨(([(1, 4), (2, 4), (3, 1), (3, 2), (3, 4), (4, 2), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_596_i1 : Finset Cell := ⟨(([(1, 4), (2, 4), (3, 1), (3, 2), (3, 4), (4, 2), (4, 3), (4, 4), (4, 5), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_596_i1 : Fin 2 → Finset Cell := ![(placed21 7 (4, 5) required_2), (placed21 0 (1, 4) required_5)]
def childrenD_596_i1 : Fin 2 → Finset Cell := ![(placed21 7 (4, 5) envelope_2), (placed21 0 (1, 4) envelope_5)]
theorem common_sub_596_i1 : commonEnvelope childrenD_596_i1 ⊆ insert (4, 5) required_596_i1 := by decide +kernel
theorem child_required_sub_596_i1 : ∀ j, childrenC_596_i1 j ⊆ insert (4, 5) required_596_i1 := by decide +kernel
theorem child_envelope_sub_596_i1 : ∀ j, childrenD_596_i1 j ⊆ envelope_596_i1 := by decide +kernel
theorem pivot_mem_596_i1 : (4, 5) ∈ envelope_596_i1 := by decide +kernel
theorem children_work_596_i1 : ∀ j, Template HasSnaky 1 (childrenC_596_i1 j) (childrenD_596_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_2 7 (4, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_5 0 (1, 4)).mono (by decide +kernel)
theorem row_works_596_i1 : Template HasSnaky 2 required_596_i1 envelope_596_i1 := by
  refine compose HasSnaky 1 childrenC_596_i1 childrenD_596_i1 children_work_596_i1 (4, 5)
    required_596_i1 envelope_596_i1 pivot_mem_596_i1 child_required_sub_596_i1 child_envelope_sub_596_i1 ?_
  intro b hb
  exact common_sub_596_i1 (mem_commonEnvelope childrenD_596_i1 b hb)
def required_596_i0 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 4), (2, 4), (3, 1), (3, 2), (3, 4), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_596_i0 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 4), (2, 1), (2, 4), (3, 1), (3, 2), (3, 4), (4, 2), (4, 3), (4, 4), (4, 5), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_596_i0 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) required_2), required_596_i1]
def childrenD_596_i0 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) envelope_2), envelope_596_i1]
theorem common_sub_596_i0 : commonEnvelope childrenD_596_i0 ⊆ insert (4, 2) required_596_i0 := by decide +kernel
theorem child_required_sub_596_i0 : ∀ j, childrenC_596_i0 j ⊆ insert (4, 2) required_596_i0 := by decide +kernel
theorem child_envelope_sub_596_i0 : ∀ j, childrenD_596_i0 j ⊆ envelope_596_i0 := by decide +kernel
theorem pivot_mem_596_i0 : (4, 2) ∈ envelope_596_i0 := by decide +kernel
theorem children_work_596_i0 : ∀ j, Template HasSnaky 2 (childrenC_596_i0 j) (childrenD_596_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_2 0 (0, 1)).mono (by decide +kernel)
  · exact row_works_596_i1.mono (by decide +kernel)
theorem row_works_596_i0 : Template HasSnaky 3 required_596_i0 envelope_596_i0 := by
  refine compose HasSnaky 2 childrenC_596_i0 childrenD_596_i0 children_work_596_i0 (4, 2)
    required_596_i0 envelope_596_i0 pivot_mem_596_i0 child_required_sub_596_i0 child_envelope_sub_596_i0 ?_
  intro b hb
  exact common_sub_596_i0 (mem_commonEnvelope childrenD_596_i0 b hb)
def required_596_i3 : Finset Cell := ⟨(([(1, 4), (2, 4), (3, 1), (3, 2), (3, 4), (4, 2), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_596_i3 : Finset Cell := ⟨(([(1, 4), (2, 4), (3, 1), (3, 2), (3, 4), (4, 2), (4, 3), (4, 4), (4, 5), (5, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_596_i3 : Fin 2 → Finset Cell := ![(placed21 7 (4, 5) required_0), (placed21 4 (1, 4) required_5)]
def childrenD_596_i3 : Fin 2 → Finset Cell := ![(placed21 7 (4, 5) envelope_0), (placed21 4 (1, 4) envelope_5)]
theorem common_sub_596_i3 : commonEnvelope childrenD_596_i3 ⊆ insert (4, 3) required_596_i3 := by decide +kernel
theorem child_required_sub_596_i3 : ∀ j, childrenC_596_i3 j ⊆ insert (4, 3) required_596_i3 := by decide +kernel
theorem child_envelope_sub_596_i3 : ∀ j, childrenD_596_i3 j ⊆ envelope_596_i3 := by decide +kernel
theorem pivot_mem_596_i3 : (4, 3) ∈ envelope_596_i3 := by decide +kernel
theorem children_work_596_i3 : ∀ j, Template HasSnaky 1 (childrenC_596_i3 j) (childrenD_596_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 7 (4, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_5 4 (1, 4)).mono (by decide +kernel)
theorem row_works_596_i3 : Template HasSnaky 2 required_596_i3 envelope_596_i3 := by
  refine compose HasSnaky 1 childrenC_596_i3 childrenD_596_i3 children_work_596_i3 (4, 3)
    required_596_i3 envelope_596_i3 pivot_mem_596_i3 child_required_sub_596_i3 child_envelope_sub_596_i3 ?_
  intro b hb
  exact common_sub_596_i3 (mem_commonEnvelope childrenD_596_i3 b hb)
def required_596_i2 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 4), (2, 4), (3, 1), (3, 2), (3, 4), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_596_i2 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 4), (2, 1), (2, 4), (3, 1), (3, 2), (3, 4), (4, 2), (4, 3), (4, 4), (4, 5), (5, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_596_i2 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) required_2), required_596_i3]
def childrenD_596_i2 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) envelope_2), envelope_596_i3]
theorem common_sub_596_i2 : commonEnvelope childrenD_596_i2 ⊆ insert (4, 2) required_596_i2 := by decide +kernel
theorem child_required_sub_596_i2 : ∀ j, childrenC_596_i2 j ⊆ insert (4, 2) required_596_i2 := by decide +kernel
theorem child_envelope_sub_596_i2 : ∀ j, childrenD_596_i2 j ⊆ envelope_596_i2 := by decide +kernel
theorem pivot_mem_596_i2 : (4, 2) ∈ envelope_596_i2 := by decide +kernel
theorem children_work_596_i2 : ∀ j, Template HasSnaky 2 (childrenC_596_i2 j) (childrenD_596_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_2 0 (0, 1)).mono (by decide +kernel)
  · exact row_works_596_i3.mono (by decide +kernel)
theorem row_works_596_i2 : Template HasSnaky 3 required_596_i2 envelope_596_i2 := by
  refine compose HasSnaky 2 childrenC_596_i2 childrenD_596_i2 children_work_596_i2 (4, 2)
    required_596_i2 envelope_596_i2 pivot_mem_596_i2 child_required_sub_596_i2 child_envelope_sub_596_i2 ?_
  intro b hb
  exact common_sub_596_i2 (mem_commonEnvelope childrenD_596_i2 b hb)
def required_596_i5 : Finset Cell := ⟨(([(0, 1), (1, 1), (3, 1), (3, 2), (3, 4), (4, 4), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_596_i5 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (2, 4), (3, 1), (3, 2), (3, 4), (4, 1), (4, 2), (4, 3), (4, 4), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 4), (6, 5), (7, 5), (8, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_596_i5 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) required_2), (placed21 1 (2, 1) required_82)]
def childrenD_596_i5 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) envelope_2), (placed21 1 (2, 1) envelope_82)]
theorem common_sub_596_i5 : commonEnvelope childrenD_596_i5 ⊆ insert (4, 2) required_596_i5 := by decide +kernel
theorem child_required_sub_596_i5 : ∀ j, childrenC_596_i5 j ⊆ insert (4, 2) required_596_i5 := by decide +kernel
theorem child_envelope_sub_596_i5 : ∀ j, childrenD_596_i5 j ⊆ envelope_596_i5 := by decide +kernel
theorem pivot_mem_596_i5 : (4, 2) ∈ envelope_596_i5 := by decide +kernel
theorem children_work_596_i5 : ∀ j, Template HasSnaky 4 (childrenC_596_i5 j) (childrenD_596_i5 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_2 0 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_82 1 (2, 1)).mono (by decide +kernel)
theorem row_works_596_i5 : Template HasSnaky 5 required_596_i5 envelope_596_i5 := by
  refine compose HasSnaky 4 childrenC_596_i5 childrenD_596_i5 children_work_596_i5 (4, 2)
    required_596_i5 envelope_596_i5 pivot_mem_596_i5 child_required_sub_596_i5 child_envelope_sub_596_i5 ?_
  intro b hb
  exact common_sub_596_i5 (mem_commonEnvelope childrenD_596_i5 b hb)
def required_596_i4 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 4), (2, 4), (3, 1), (3, 2), (3, 4), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_596_i4 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 4), (2, 1), (2, 4), (3, 1), (3, 2), (3, 4), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (7, 0), (7, 1), (7, 2), (7, 3), (7, 5), (8, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_596_i4 : Fin 3 → Finset Cell := ![(placed21 3 (1, 4) required_6), required_595, required_596_i5]
def childrenD_596_i4 : Fin 3 → Finset Cell := ![(placed21 3 (1, 4) envelope_6), envelope_595, envelope_596_i5]
theorem common_sub_596_i4 : commonEnvelope childrenD_596_i4 ⊆ insert (5, 4) required_596_i4 := by decide +kernel
theorem child_required_sub_596_i4 : ∀ j, childrenC_596_i4 j ⊆ insert (5, 4) required_596_i4 := by decide +kernel
theorem child_envelope_sub_596_i4 : ∀ j, childrenD_596_i4 j ⊆ envelope_596_i4 := by decide +kernel
theorem pivot_mem_596_i4 : (5, 4) ∈ envelope_596_i4 := by decide +kernel
theorem children_work_596_i4 : ∀ j, Template HasSnaky 9 (childrenC_596_i4 j) (childrenD_596_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_6 3 (1, 4)).mono (by decide +kernel)
  · exact row_works_595.mono (by decide +kernel)
  · exact row_works_596_i5.mono (by decide +kernel)
theorem row_works_596_i4 : Template HasSnaky 10 required_596_i4 envelope_596_i4 := by
  refine compose HasSnaky 9 childrenC_596_i4 childrenD_596_i4 children_work_596_i4 (5, 4)
    required_596_i4 envelope_596_i4 pivot_mem_596_i4 child_required_sub_596_i4 child_envelope_sub_596_i4 ?_
  intro b hb
  exact common_sub_596_i4 (mem_commonEnvelope childrenD_596_i4 b hb)
def required_596 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 4), (2, 4), (3, 1), (3, 2), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_596 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 4), (2, 1), (2, 4), (2, 5), (3, 1), (3, 2), (3, 4), (3, 5), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (8, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_596 : Fin 4 → Finset Cell := ![(placed21 4 (1, 5) required_197), required_596_i0, required_596_i2, required_596_i4]
def childrenD_596 : Fin 4 → Finset Cell := ![(placed21 4 (1, 5) envelope_197), envelope_596_i0, envelope_596_i2, envelope_596_i4]
theorem common_sub_596 : commonEnvelope childrenD_596 ⊆ insert (4, 4) required_596 := by decide +kernel
theorem child_required_sub_596 : ∀ j, childrenC_596 j ⊆ insert (4, 4) required_596 := by decide +kernel
theorem child_envelope_sub_596 : ∀ j, childrenD_596 j ⊆ envelope_596 := by decide +kernel
theorem pivot_mem_596 : (4, 4) ∈ envelope_596 := by decide +kernel
theorem children_work_596 : ∀ j, Template HasSnaky 10 (childrenC_596 j) (childrenD_596 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_197 4 (1, 5)).mono (by decide +kernel)
  · exact row_works_596_i0.mono (by decide +kernel)
  · exact row_works_596_i2.mono (by decide +kernel)
  · exact row_works_596_i4.mono (by decide +kernel)
theorem row_works_596 : Template HasSnaky 11 required_596 envelope_596 := by
  refine compose HasSnaky 10 childrenC_596 childrenD_596 children_work_596 (4, 4)
    required_596 envelope_596 pivot_mem_596 child_required_sub_596 child_envelope_sub_596 ?_
  intro b hb
  exact common_sub_596 (mem_commonEnvelope childrenD_596 b hb)
def required_601_i1 : Finset Cell := ⟨(([(0, 2), (3, 2), (3, 3), (3, 4), (4, 3), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_601_i1 : Finset Cell := ⟨(([(0, 2), (1, 2), (2, 1), (2, 2), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_601_i1 : Fin 2 → Finset Cell := ![(placed21 0 (3, 2) required_29), (placed21 7 (4, 5) required_35)]
def childrenD_601_i1 : Fin 2 → Finset Cell := ![(placed21 0 (3, 2) envelope_29), (placed21 7 (4, 5) envelope_35)]
theorem common_sub_601_i1 : commonEnvelope childrenD_601_i1 ⊆ insert (3, 5) required_601_i1 := by decide +kernel
theorem child_required_sub_601_i1 : ∀ j, childrenC_601_i1 j ⊆ insert (3, 5) required_601_i1 := by decide +kernel
theorem child_envelope_sub_601_i1 : ∀ j, childrenD_601_i1 j ⊆ envelope_601_i1 := by decide +kernel
theorem pivot_mem_601_i1 : (3, 5) ∈ envelope_601_i1 := by decide +kernel
theorem children_work_601_i1 : ∀ j, Template HasSnaky 3 (childrenC_601_i1 j) (childrenD_601_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_29 0 (3, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_35 7 (4, 5)).mono (by decide +kernel)
theorem row_works_601_i1 : Template HasSnaky 4 required_601_i1 envelope_601_i1 := by
  refine compose HasSnaky 3 childrenC_601_i1 childrenD_601_i1 children_work_601_i1 (3, 5)
    required_601_i1 envelope_601_i1 pivot_mem_601_i1 child_required_sub_601_i1 child_envelope_sub_601_i1 ?_
  intro b hb
  exact common_sub_601_i1 (mem_commonEnvelope childrenD_601_i1 b hb)
def required_601_i0 : Finset Cell := ⟨(([(0, 2), (0, 3), (0, 5), (1, 5), (3, 2), (3, 3), (3, 4), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_601_i0 : Finset Cell := ⟨(([(0, 2), (0, 3), (0, 5), (0, 6), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 1), (2, 2), (2, 4), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 3), (6, 4), (6, 5), (7, 3), (7, 4), (7, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_601_i0 : Fin 3 → Finset Cell := ![required_601_i1, (placed21 1 (1, 2) required_499), (placed21 0 (0, 1) required_501)]
def childrenD_601_i0 : Fin 3 → Finset Cell := ![envelope_601_i1, (placed21 1 (1, 2) envelope_499), (placed21 0 (0, 1) envelope_501)]
theorem common_sub_601_i0 : commonEnvelope childrenD_601_i0 ⊆ insert (4, 4) required_601_i0 := by decide +kernel
theorem child_required_sub_601_i0 : ∀ j, childrenC_601_i0 j ⊆ insert (4, 4) required_601_i0 := by decide +kernel
theorem child_envelope_sub_601_i0 : ∀ j, childrenD_601_i0 j ⊆ envelope_601_i0 := by decide +kernel
theorem pivot_mem_601_i0 : (4, 4) ∈ envelope_601_i0 := by decide +kernel
theorem children_work_601_i0 : ∀ j, Template HasSnaky 7 (childrenC_601_i0 j) (childrenD_601_i0 j) := by
  intro j
  fin_cases j
  · exact row_works_601_i1.mono (by decide +kernel)
  · exact (placed21_template row_works_499 1 (1, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_501 0 (0, 1)).mono (by decide +kernel)
theorem row_works_601_i0 : Template HasSnaky 8 required_601_i0 envelope_601_i0 := by
  refine compose HasSnaky 7 childrenC_601_i0 childrenD_601_i0 children_work_601_i0 (4, 4)
    required_601_i0 envelope_601_i0 pivot_mem_601_i0 child_required_sub_601_i0 child_envelope_sub_601_i0 ?_
  intro b hb
  exact common_sub_601_i0 (mem_commonEnvelope childrenD_601_i0 b hb)
def required_601_i6 : Finset Cell := ⟨(([(3, 2), (3, 3), (4, 2), (4, 3), (4, 4), (6, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_601_i6 : Finset Cell := ⟨(([(3, 2), (3, 3), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 1), (5, 2), (6, 2), (6, 3), (7, 2), (7, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_601_i6 : Fin 2 → Finset Cell := ![(placed21 0 (3, 1) required_66), (placed21 1 (3, 2) required_94)]
def childrenD_601_i6 : Fin 2 → Finset Cell := ![(placed21 0 (3, 1) envelope_66), (placed21 1 (3, 2) envelope_94)]
theorem common_sub_601_i6 : commonEnvelope childrenD_601_i6 ⊆ insert (5, 2) required_601_i6 := by decide +kernel
theorem child_required_sub_601_i6 : ∀ j, childrenC_601_i6 j ⊆ insert (5, 2) required_601_i6 := by decide +kernel
theorem child_envelope_sub_601_i6 : ∀ j, childrenD_601_i6 j ⊆ envelope_601_i6 := by decide +kernel
theorem pivot_mem_601_i6 : (5, 2) ∈ envelope_601_i6 := by decide +kernel
theorem children_work_601_i6 : ∀ j, Template HasSnaky 2 (childrenC_601_i6 j) (childrenD_601_i6 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_66 0 (3, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_94 1 (3, 2)).mono (by decide +kernel)
theorem row_works_601_i6 : Template HasSnaky 3 required_601_i6 envelope_601_i6 := by
  refine compose HasSnaky 2 childrenC_601_i6 childrenD_601_i6 children_work_601_i6 (5, 2)
    required_601_i6 envelope_601_i6 pivot_mem_601_i6 child_required_sub_601_i6 child_envelope_sub_601_i6 ?_
  intro b hb
  exact common_sub_601_i6 (mem_commonEnvelope childrenD_601_i6 b hb)
def required_601_i5 : Finset Cell := ⟨(([(3, 2), (3, 3), (3, 4), (4, 3), (4, 4), (6, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_601_i5 : Finset Cell := ⟨(([(3, 2), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 1), (5, 2), (6, 2), (6, 3), (7, 2), (7, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_601_i5 : Fin 2 → Finset Cell := ![(placed21 4 (3, 5) required_15), required_601_i6]
def childrenD_601_i5 : Fin 2 → Finset Cell := ![(placed21 4 (3, 5) envelope_15), envelope_601_i6]
theorem common_sub_601_i5 : commonEnvelope childrenD_601_i5 ⊆ insert (4, 2) required_601_i5 := by decide +kernel
theorem child_required_sub_601_i5 : ∀ j, childrenC_601_i5 j ⊆ insert (4, 2) required_601_i5 := by decide +kernel
theorem child_envelope_sub_601_i5 : ∀ j, childrenD_601_i5 j ⊆ envelope_601_i5 := by decide +kernel
theorem pivot_mem_601_i5 : (4, 2) ∈ envelope_601_i5 := by decide +kernel
theorem children_work_601_i5 : ∀ j, Template HasSnaky 3 (childrenC_601_i5 j) (childrenD_601_i5 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_15 4 (3, 5)).mono (by decide +kernel)
  · exact row_works_601_i6.mono (by decide +kernel)
theorem row_works_601_i5 : Template HasSnaky 4 required_601_i5 envelope_601_i5 := by
  refine compose HasSnaky 3 childrenC_601_i5 childrenD_601_i5 children_work_601_i5 (4, 2)
    required_601_i5 envelope_601_i5 pivot_mem_601_i5 child_required_sub_601_i5 child_envelope_sub_601_i5 ?_
  intro b hb
  exact common_sub_601_i5 (mem_commonEnvelope childrenD_601_i5 b hb)
def required_601_i4 : Finset Cell := ⟨(([(2, 4), (3, 2), (3, 3), (3, 4), (4, 3), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_601_i4 : Finset Cell := ⟨(([(2, 4), (3, 2), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 1), (5, 2), (5, 3), (6, 2), (6, 3), (7, 2), (7, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_601_i4 : Fin 2 → Finset Cell := ![(placed21 2 (6, 3) required_1), required_601_i5]
def childrenD_601_i4 : Fin 2 → Finset Cell := ![(placed21 2 (6, 3) envelope_1), envelope_601_i5]
theorem common_sub_601_i4 : commonEnvelope childrenD_601_i4 ⊆ insert (6, 3) required_601_i4 := by decide +kernel
theorem child_required_sub_601_i4 : ∀ j, childrenC_601_i4 j ⊆ insert (6, 3) required_601_i4 := by decide +kernel
theorem child_envelope_sub_601_i4 : ∀ j, childrenD_601_i4 j ⊆ envelope_601_i4 := by decide +kernel
theorem pivot_mem_601_i4 : (6, 3) ∈ envelope_601_i4 := by decide +kernel
theorem children_work_601_i4 : ∀ j, Template HasSnaky 4 (childrenC_601_i4 j) (childrenD_601_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_1 2 (6, 3)).mono (by decide +kernel)
  · exact row_works_601_i5.mono (by decide +kernel)
theorem row_works_601_i4 : Template HasSnaky 5 required_601_i4 envelope_601_i4 := by
  refine compose HasSnaky 4 childrenC_601_i4 childrenD_601_i4 children_work_601_i4 (6, 3)
    required_601_i4 envelope_601_i4 pivot_mem_601_i4 child_required_sub_601_i4 child_envelope_sub_601_i4 ?_
  intro b hb
  exact common_sub_601_i4 (mem_commonEnvelope childrenD_601_i4 b hb)
def required_601_i3 : Finset Cell := ⟨(([(0, 5), (1, 5), (3, 2), (3, 3), (3, 4), (4, 3), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_601_i3 : Finset Cell := ⟨(([(0, 5), (1, 4), (1, 5), (2, 4), (3, 2), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 1), (5, 2), (5, 3), (6, 2), (6, 3), (7, 2), (7, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_601_i3 : Fin 2 → Finset Cell := ![(placed21 2 (4, 4) required_3), required_601_i4]
def childrenD_601_i3 : Fin 2 → Finset Cell := ![(placed21 2 (4, 4) envelope_3), envelope_601_i4]
theorem common_sub_601_i3 : commonEnvelope childrenD_601_i3 ⊆ insert (2, 4) required_601_i3 := by decide +kernel
theorem child_required_sub_601_i3 : ∀ j, childrenC_601_i3 j ⊆ insert (2, 4) required_601_i3 := by decide +kernel
theorem child_envelope_sub_601_i3 : ∀ j, childrenD_601_i3 j ⊆ envelope_601_i3 := by decide +kernel
theorem pivot_mem_601_i3 : (2, 4) ∈ envelope_601_i3 := by decide +kernel
theorem children_work_601_i3 : ∀ j, Template HasSnaky 5 (childrenC_601_i3 j) (childrenD_601_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_3 2 (4, 4)).mono (by decide +kernel)
  · exact row_works_601_i4.mono (by decide +kernel)
theorem row_works_601_i3 : Template HasSnaky 6 required_601_i3 envelope_601_i3 := by
  refine compose HasSnaky 5 childrenC_601_i3 childrenD_601_i3 children_work_601_i3 (2, 4)
    required_601_i3 envelope_601_i3 pivot_mem_601_i3 child_required_sub_601_i3 child_envelope_sub_601_i3 ?_
  intro b hb
  exact common_sub_601_i3 (mem_commonEnvelope childrenD_601_i3 b hb)
def required_601_i7 : Finset Cell := ⟨(([(0, 5), (1, 5), (3, 3), (3, 4), (4, 3), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_601_i7 : Finset Cell := ⟨(([(0, 5), (1, 4), (1, 5), (2, 4), (3, 3), (3, 4), (4, 2), (4, 3), (4, 4), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 3), (6, 4), (6, 5), (7, 3), (7, 4), (7, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_601_i7 : Fin 2 → Finset Cell := ![(placed21 2 (4, 4) required_3), (placed21 0 (2, 2) required_72)]
def childrenD_601_i7 : Fin 2 → Finset Cell := ![(placed21 2 (4, 4) envelope_3), (placed21 0 (2, 2) envelope_72)]
theorem common_sub_601_i7 : commonEnvelope childrenD_601_i7 ⊆ insert (2, 4) required_601_i7 := by decide +kernel
theorem child_required_sub_601_i7 : ∀ j, childrenC_601_i7 j ⊆ insert (2, 4) required_601_i7 := by decide +kernel
theorem child_envelope_sub_601_i7 : ∀ j, childrenD_601_i7 j ⊆ envelope_601_i7 := by decide +kernel
theorem pivot_mem_601_i7 : (2, 4) ∈ envelope_601_i7 := by decide +kernel
theorem children_work_601_i7 : ∀ j, Template HasSnaky 5 (childrenC_601_i7 j) (childrenD_601_i7 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_3 2 (4, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_72 0 (2, 2)).mono (by decide +kernel)
theorem row_works_601_i7 : Template HasSnaky 6 required_601_i7 envelope_601_i7 := by
  refine compose HasSnaky 5 childrenC_601_i7 childrenD_601_i7 children_work_601_i7 (2, 4)
    required_601_i7 envelope_601_i7 pivot_mem_601_i7 child_required_sub_601_i7 child_envelope_sub_601_i7 ?_
  intro b hb
  exact common_sub_601_i7 (mem_commonEnvelope childrenD_601_i7 b hb)
def required_601_i2 : Finset Cell := ⟨(([(0, 5), (1, 5), (3, 2), (3, 3), (3, 4), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_601_i2 : Finset Cell := ⟨(([(0, 5), (1, 4), (1, 5), (2, 4), (3, 2), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_601_i2 : Fin 5 → Finset Cell := ![(placed21 4 (3, 6) required_406), (placed21 1 (1, 2) required_499), required_601_i3, (placed21 4 (1, 7) required_600), required_601_i7]
def childrenD_601_i2 : Fin 5 → Finset Cell := ![(placed21 4 (3, 6) envelope_406), (placed21 1 (1, 2) envelope_499), envelope_601_i3, (placed21 4 (1, 7) envelope_600), envelope_601_i7]
theorem common_sub_601_i2 : commonEnvelope childrenD_601_i2 ⊆ insert (4, 4) required_601_i2 := by decide +kernel
theorem child_required_sub_601_i2 : ∀ j, childrenC_601_i2 j ⊆ insert (4, 4) required_601_i2 := by decide +kernel
theorem child_envelope_sub_601_i2 : ∀ j, childrenD_601_i2 j ⊆ envelope_601_i2 := by decide +kernel
theorem pivot_mem_601_i2 : (4, 4) ∈ envelope_601_i2 := by decide +kernel
theorem children_work_601_i2 : ∀ j, Template HasSnaky 9 (childrenC_601_i2 j) (childrenD_601_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_406 4 (3, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_499 1 (1, 2)).mono (by decide +kernel)
  · exact row_works_601_i3.mono (by decide +kernel)
  · exact (placed21_template row_works_600 4 (1, 7)).mono (by decide +kernel)
  · exact row_works_601_i7.mono (by decide +kernel)
theorem row_works_601_i2 : Template HasSnaky 10 required_601_i2 envelope_601_i2 := by
  refine compose HasSnaky 9 childrenC_601_i2 childrenD_601_i2 children_work_601_i2 (4, 4)
    required_601_i2 envelope_601_i2 pivot_mem_601_i2 child_required_sub_601_i2 child_envelope_sub_601_i2 ?_
  intro b hb
  exact common_sub_601_i2 (mem_commonEnvelope childrenD_601_i2 b hb)
def required_601_i8 : Finset Cell := ⟨(([(0, 2), (0, 3), (0, 5), (1, 5), (3, 2), (3, 3), (3, 4), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_601_i8 : Finset Cell := ⟨(([(0, 2), (0, 3), (0, 5), (0, 6), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 1), (2, 2), (2, 4), (3, 2), (3, 3), (3, 4), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_601_i8 : Fin 2 → Finset Cell := ![(placed21 4 (3, 6) required_406), (placed21 0 (0, 1) required_501)]
def childrenD_601_i8 : Fin 2 → Finset Cell := ![(placed21 4 (3, 6) envelope_406), (placed21 0 (0, 1) envelope_501)]
theorem common_sub_601_i8 : commonEnvelope childrenD_601_i8 ⊆ insert (4, 4) required_601_i8 := by decide +kernel
theorem child_required_sub_601_i8 : ∀ j, childrenC_601_i8 j ⊆ insert (4, 4) required_601_i8 := by decide +kernel
theorem child_envelope_sub_601_i8 : ∀ j, childrenD_601_i8 j ⊆ envelope_601_i8 := by decide +kernel
theorem pivot_mem_601_i8 : (4, 4) ∈ envelope_601_i8 := by decide +kernel
theorem children_work_601_i8 : ∀ j, Template HasSnaky 9 (childrenC_601_i8 j) (childrenD_601_i8 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_406 4 (3, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_501 0 (0, 1)).mono (by decide +kernel)
theorem row_works_601_i8 : Template HasSnaky 10 required_601_i8 envelope_601_i8 := by
  refine compose HasSnaky 9 childrenC_601_i8 childrenD_601_i8 children_work_601_i8 (4, 4)
    required_601_i8 envelope_601_i8 pivot_mem_601_i8 child_required_sub_601_i8 child_envelope_sub_601_i8 ?_
  intro b hb
  exact common_sub_601_i8 (mem_commonEnvelope childrenD_601_i8 b hb)
def required_601 : Finset Cell := ⟨(([(0, 2), (0, 3), (0, 5), (1, 5), (3, 2), (3, 3), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_601 : Finset Cell := ⟨(([(0, 2), (0, 3), (0, 5), (0, 6), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 1), (2, 2), (2, 4), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_601 : Fin 4 → Finset Cell := ![(placed21 0 (0, 1) required_247), required_601_i0, required_601_i2, required_601_i8]
def childrenD_601 : Fin 4 → Finset Cell := ![(placed21 0 (0, 1) envelope_247), envelope_601_i0, envelope_601_i2, envelope_601_i8]
theorem common_sub_601 : commonEnvelope childrenD_601 ⊆ insert (4, 3) required_601 := by decide +kernel
theorem child_required_sub_601 : ∀ j, childrenC_601 j ⊆ insert (4, 3) required_601 := by decide +kernel
theorem child_envelope_sub_601 : ∀ j, childrenD_601 j ⊆ envelope_601 := by decide +kernel
theorem pivot_mem_601 : (4, 3) ∈ envelope_601 := by decide +kernel
theorem children_work_601 : ∀ j, Template HasSnaky 10 (childrenC_601 j) (childrenD_601 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_247 0 (0, 1)).mono (by decide +kernel)
  · exact row_works_601_i0.mono (by decide +kernel)
  · exact row_works_601_i2.mono (by decide +kernel)
  · exact row_works_601_i8.mono (by decide +kernel)
theorem row_works_601 : Template HasSnaky 11 required_601 envelope_601 := by
  refine compose HasSnaky 10 childrenC_601 childrenD_601 children_work_601 (4, 3)
    required_601 envelope_601 pivot_mem_601 child_required_sub_601 child_envelope_sub_601 ?_
  intro b hb
  exact common_sub_601 (mem_commonEnvelope childrenD_601 b hb)
def required_613 : Finset Cell := ⟨(([(1, 3), (1, 5), (2, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_613 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 7), (0, 8), (0, 9), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 4), (4, 5), (4, 6), (4, 7), (5, 5), (5, 6), (5, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_613 : Fin 6 → Finset Cell := ![(placed21 0 (1, 0) required_104), (placed21 2 (2, 0) required_329), (placed21 4 (1, 8) required_409), (placed21 0 (1, 2) required_612), (placed21 4 (1, 6) required_612), (placed21 6 (2, 6) required_612)]
def childrenD_613 : Fin 6 → Finset Cell := ![(placed21 0 (1, 0) envelope_104), (placed21 2 (2, 0) envelope_329), (placed21 4 (1, 8) envelope_409), (placed21 0 (1, 2) envelope_612), (placed21 4 (1, 6) envelope_612), (placed21 6 (2, 6) envelope_612)]
theorem common_sub_613 : commonEnvelope childrenD_613 ⊆ insert (2, 5) required_613 := by decide +kernel
theorem child_required_sub_613 : ∀ j, childrenC_613 j ⊆ insert (2, 5) required_613 := by decide +kernel
theorem child_envelope_sub_613 : ∀ j, childrenD_613 j ⊆ envelope_613 := by decide +kernel
theorem pivot_mem_613 : (2, 5) ∈ envelope_613 := by decide +kernel
theorem children_work_613 : ∀ j, Template HasSnaky 10 (childrenC_613 j) (childrenD_613 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_104 0 (1, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_329 2 (2, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_409 4 (1, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_612 0 (1, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_612 4 (1, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_612 6 (2, 6)).mono (by decide +kernel)
theorem row_works_613 : Template HasSnaky 11 required_613 envelope_613 := by
  refine compose HasSnaky 10 childrenC_613 childrenD_613 children_work_613 (2, 5)
    required_613 envelope_613 pivot_mem_613 child_required_sub_613 child_envelope_sub_613 ?_
  intro b hb
  exact common_sub_613 (mem_commonEnvelope childrenD_613 b hb)
def height_596_i1 : ℕ := 2
def childrenH_596_i1 : Fin 2 → ℕ := ![height_2, height_5]
theorem height_exact_596_i1 : height_596_i1 = 1 + Finset.univ.sup childrenH_596_i1 := by decide +kernel
theorem required_origin_596_i1 : ∀ x ∈ required_596_i1,
    (∃ j, x ∈ childrenC_596_i1 j) ∨ ∀ j, x ∈ childrenD_596_i1 j := by decide +kernel
theorem required_exact_596_i1 : required_596_i1 =
    ((Finset.univ.biUnion childrenC_596_i1) ∪ commonEnvelope childrenD_596_i1).erase (4, 5) := by
  exact required_eq_combination childrenC_596_i1 childrenD_596_i1 (4, 5) required_596_i1
    (by decide +kernel) child_required_sub_596_i1 common_sub_596_i1 required_origin_596_i1
theorem envelope_origin_596_i1 : ∀ x ∈ envelope_596_i1,
    x = (4, 5) ∨ ∃ j, x ∈ childrenD_596_i1 j := by decide +kernel
theorem envelope_exact_596_i1 : envelope_596_i1 =
    insert (4, 5) (Finset.univ.biUnion childrenD_596_i1) := by
  exact envelope_eq_combination childrenD_596_i1 (4, 5) envelope_596_i1
    pivot_mem_596_i1 child_envelope_sub_596_i1 envelope_origin_596_i1
def checked_596_i1 : CheckedCard where
  required := required_596_i1
  envelope := envelope_596_i1
  height := height_596_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_596_i1
def height_596_i0 : ℕ := 3
def childrenH_596_i0 : Fin 2 → ℕ := ![height_2, height_596_i1]
theorem height_exact_596_i0 : height_596_i0 = 1 + Finset.univ.sup childrenH_596_i0 := by decide +kernel
theorem required_origin_596_i0 : ∀ x ∈ required_596_i0,
    (∃ j, x ∈ childrenC_596_i0 j) ∨ ∀ j, x ∈ childrenD_596_i0 j := by decide +kernel
theorem required_exact_596_i0 : required_596_i0 =
    ((Finset.univ.biUnion childrenC_596_i0) ∪ commonEnvelope childrenD_596_i0).erase (4, 2) := by
  exact required_eq_combination childrenC_596_i0 childrenD_596_i0 (4, 2) required_596_i0
    (by decide +kernel) child_required_sub_596_i0 common_sub_596_i0 required_origin_596_i0
theorem envelope_origin_596_i0 : ∀ x ∈ envelope_596_i0,
    x = (4, 2) ∨ ∃ j, x ∈ childrenD_596_i0 j := by decide +kernel
theorem envelope_exact_596_i0 : envelope_596_i0 =
    insert (4, 2) (Finset.univ.biUnion childrenD_596_i0) := by
  exact envelope_eq_combination childrenD_596_i0 (4, 2) envelope_596_i0
    pivot_mem_596_i0 child_envelope_sub_596_i0 envelope_origin_596_i0
def checked_596_i0 : CheckedCard where
  required := required_596_i0
  envelope := envelope_596_i0
  height := height_596_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_596_i0
def height_596_i3 : ℕ := 2
def childrenH_596_i3 : Fin 2 → ℕ := ![height_0, height_5]
theorem height_exact_596_i3 : height_596_i3 = 1 + Finset.univ.sup childrenH_596_i3 := by decide +kernel
theorem required_origin_596_i3 : ∀ x ∈ required_596_i3,
    (∃ j, x ∈ childrenC_596_i3 j) ∨ ∀ j, x ∈ childrenD_596_i3 j := by decide +kernel
theorem required_exact_596_i3 : required_596_i3 =
    ((Finset.univ.biUnion childrenC_596_i3) ∪ commonEnvelope childrenD_596_i3).erase (4, 3) := by
  exact required_eq_combination childrenC_596_i3 childrenD_596_i3 (4, 3) required_596_i3
    (by decide +kernel) child_required_sub_596_i3 common_sub_596_i3 required_origin_596_i3
theorem envelope_origin_596_i3 : ∀ x ∈ envelope_596_i3,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_596_i3 j := by decide +kernel
theorem envelope_exact_596_i3 : envelope_596_i3 =
    insert (4, 3) (Finset.univ.biUnion childrenD_596_i3) := by
  exact envelope_eq_combination childrenD_596_i3 (4, 3) envelope_596_i3
    pivot_mem_596_i3 child_envelope_sub_596_i3 envelope_origin_596_i3
def checked_596_i3 : CheckedCard where
  required := required_596_i3
  envelope := envelope_596_i3
  height := height_596_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_596_i3
def height_596_i2 : ℕ := 3
def childrenH_596_i2 : Fin 2 → ℕ := ![height_2, height_596_i3]
theorem height_exact_596_i2 : height_596_i2 = 1 + Finset.univ.sup childrenH_596_i2 := by decide +kernel
theorem required_origin_596_i2 : ∀ x ∈ required_596_i2,
    (∃ j, x ∈ childrenC_596_i2 j) ∨ ∀ j, x ∈ childrenD_596_i2 j := by decide +kernel
theorem required_exact_596_i2 : required_596_i2 =
    ((Finset.univ.biUnion childrenC_596_i2) ∪ commonEnvelope childrenD_596_i2).erase (4, 2) := by
  exact required_eq_combination childrenC_596_i2 childrenD_596_i2 (4, 2) required_596_i2
    (by decide +kernel) child_required_sub_596_i2 common_sub_596_i2 required_origin_596_i2
theorem envelope_origin_596_i2 : ∀ x ∈ envelope_596_i2,
    x = (4, 2) ∨ ∃ j, x ∈ childrenD_596_i2 j := by decide +kernel
theorem envelope_exact_596_i2 : envelope_596_i2 =
    insert (4, 2) (Finset.univ.biUnion childrenD_596_i2) := by
  exact envelope_eq_combination childrenD_596_i2 (4, 2) envelope_596_i2
    pivot_mem_596_i2 child_envelope_sub_596_i2 envelope_origin_596_i2
def checked_596_i2 : CheckedCard where
  required := required_596_i2
  envelope := envelope_596_i2
  height := height_596_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_596_i2
def height_596_i5 : ℕ := 5
def childrenH_596_i5 : Fin 2 → ℕ := ![height_2, height_82]
theorem height_exact_596_i5 : height_596_i5 = 1 + Finset.univ.sup childrenH_596_i5 := by decide +kernel
theorem required_origin_596_i5 : ∀ x ∈ required_596_i5,
    (∃ j, x ∈ childrenC_596_i5 j) ∨ ∀ j, x ∈ childrenD_596_i5 j := by decide +kernel
theorem required_exact_596_i5 : required_596_i5 =
    ((Finset.univ.biUnion childrenC_596_i5) ∪ commonEnvelope childrenD_596_i5).erase (4, 2) := by
  exact required_eq_combination childrenC_596_i5 childrenD_596_i5 (4, 2) required_596_i5
    (by decide +kernel) child_required_sub_596_i5 common_sub_596_i5 required_origin_596_i5
theorem envelope_origin_596_i5 : ∀ x ∈ envelope_596_i5,
    x = (4, 2) ∨ ∃ j, x ∈ childrenD_596_i5 j := by decide +kernel
theorem envelope_exact_596_i5 : envelope_596_i5 =
    insert (4, 2) (Finset.univ.biUnion childrenD_596_i5) := by
  exact envelope_eq_combination childrenD_596_i5 (4, 2) envelope_596_i5
    pivot_mem_596_i5 child_envelope_sub_596_i5 envelope_origin_596_i5
def checked_596_i5 : CheckedCard where
  required := required_596_i5
  envelope := envelope_596_i5
  height := height_596_i5
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_596_i5
def height_596_i4 : ℕ := 10
def childrenH_596_i4 : Fin 3 → ℕ := ![height_6, height_595, height_596_i5]
theorem height_exact_596_i4 : height_596_i4 = 1 + Finset.univ.sup childrenH_596_i4 := by decide +kernel
theorem required_origin_596_i4 : ∀ x ∈ required_596_i4,
    (∃ j, x ∈ childrenC_596_i4 j) ∨ ∀ j, x ∈ childrenD_596_i4 j := by decide +kernel
theorem required_exact_596_i4 : required_596_i4 =
    ((Finset.univ.biUnion childrenC_596_i4) ∪ commonEnvelope childrenD_596_i4).erase (5, 4) := by
  exact required_eq_combination childrenC_596_i4 childrenD_596_i4 (5, 4) required_596_i4
    (by decide +kernel) child_required_sub_596_i4 common_sub_596_i4 required_origin_596_i4
theorem envelope_origin_596_i4 : ∀ x ∈ envelope_596_i4,
    x = (5, 4) ∨ ∃ j, x ∈ childrenD_596_i4 j := by decide +kernel
theorem envelope_exact_596_i4 : envelope_596_i4 =
    insert (5, 4) (Finset.univ.biUnion childrenD_596_i4) := by
  exact envelope_eq_combination childrenD_596_i4 (5, 4) envelope_596_i4
    pivot_mem_596_i4 child_envelope_sub_596_i4 envelope_origin_596_i4
def checked_596_i4 : CheckedCard where
  required := required_596_i4
  envelope := envelope_596_i4
  height := height_596_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_596_i4
def height_596 : ℕ := 11
def childrenH_596 : Fin 4 → ℕ := ![height_197, height_596_i0, height_596_i2, height_596_i4]
theorem height_exact_596 : height_596 = 1 + Finset.univ.sup childrenH_596 := by decide +kernel
theorem required_origin_596 : ∀ x ∈ required_596,
    (∃ j, x ∈ childrenC_596 j) ∨ ∀ j, x ∈ childrenD_596 j := by decide +kernel
theorem required_exact_596 : required_596 =
    ((Finset.univ.biUnion childrenC_596) ∪ commonEnvelope childrenD_596).erase (4, 4) := by
  exact required_eq_combination childrenC_596 childrenD_596 (4, 4) required_596
    (by decide +kernel) child_required_sub_596 common_sub_596 required_origin_596
theorem envelope_origin_596 : ∀ x ∈ envelope_596,
    x = (4, 4) ∨ ∃ j, x ∈ childrenD_596 j := by decide +kernel
theorem envelope_exact_596 : envelope_596 =
    insert (4, 4) (Finset.univ.biUnion childrenD_596) := by
  exact envelope_eq_combination childrenD_596 (4, 4) envelope_596
    pivot_mem_596 child_envelope_sub_596 envelope_origin_596
def checked_596 : CheckedCard where
  required := required_596
  envelope := envelope_596
  height := height_596
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_596
def height_601_i1 : ℕ := 4
def childrenH_601_i1 : Fin 2 → ℕ := ![height_29, height_35]
theorem height_exact_601_i1 : height_601_i1 = 1 + Finset.univ.sup childrenH_601_i1 := by decide +kernel
theorem required_origin_601_i1 : ∀ x ∈ required_601_i1,
    (∃ j, x ∈ childrenC_601_i1 j) ∨ ∀ j, x ∈ childrenD_601_i1 j := by decide +kernel
theorem required_exact_601_i1 : required_601_i1 =
    ((Finset.univ.biUnion childrenC_601_i1) ∪ commonEnvelope childrenD_601_i1).erase (3, 5) := by
  exact required_eq_combination childrenC_601_i1 childrenD_601_i1 (3, 5) required_601_i1
    (by decide +kernel) child_required_sub_601_i1 common_sub_601_i1 required_origin_601_i1
theorem envelope_origin_601_i1 : ∀ x ∈ envelope_601_i1,
    x = (3, 5) ∨ ∃ j, x ∈ childrenD_601_i1 j := by decide +kernel
theorem envelope_exact_601_i1 : envelope_601_i1 =
    insert (3, 5) (Finset.univ.biUnion childrenD_601_i1) := by
  exact envelope_eq_combination childrenD_601_i1 (3, 5) envelope_601_i1
    pivot_mem_601_i1 child_envelope_sub_601_i1 envelope_origin_601_i1
def checked_601_i1 : CheckedCard where
  required := required_601_i1
  envelope := envelope_601_i1
  height := height_601_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_601_i1
def height_601_i0 : ℕ := 8
def childrenH_601_i0 : Fin 3 → ℕ := ![height_601_i1, height_499, height_501]
theorem height_exact_601_i0 : height_601_i0 = 1 + Finset.univ.sup childrenH_601_i0 := by decide +kernel
theorem required_origin_601_i0 : ∀ x ∈ required_601_i0,
    (∃ j, x ∈ childrenC_601_i0 j) ∨ ∀ j, x ∈ childrenD_601_i0 j := by decide +kernel
theorem required_exact_601_i0 : required_601_i0 =
    ((Finset.univ.biUnion childrenC_601_i0) ∪ commonEnvelope childrenD_601_i0).erase (4, 4) := by
  exact required_eq_combination childrenC_601_i0 childrenD_601_i0 (4, 4) required_601_i0
    (by decide +kernel) child_required_sub_601_i0 common_sub_601_i0 required_origin_601_i0
theorem envelope_origin_601_i0 : ∀ x ∈ envelope_601_i0,
    x = (4, 4) ∨ ∃ j, x ∈ childrenD_601_i0 j := by decide +kernel
theorem envelope_exact_601_i0 : envelope_601_i0 =
    insert (4, 4) (Finset.univ.biUnion childrenD_601_i0) := by
  exact envelope_eq_combination childrenD_601_i0 (4, 4) envelope_601_i0
    pivot_mem_601_i0 child_envelope_sub_601_i0 envelope_origin_601_i0
def checked_601_i0 : CheckedCard where
  required := required_601_i0
  envelope := envelope_601_i0
  height := height_601_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_601_i0
def height_601_i6 : ℕ := 3
def childrenH_601_i6 : Fin 2 → ℕ := ![height_66, height_94]
theorem height_exact_601_i6 : height_601_i6 = 1 + Finset.univ.sup childrenH_601_i6 := by decide +kernel
theorem required_origin_601_i6 : ∀ x ∈ required_601_i6,
    (∃ j, x ∈ childrenC_601_i6 j) ∨ ∀ j, x ∈ childrenD_601_i6 j := by decide +kernel
theorem required_exact_601_i6 : required_601_i6 =
    ((Finset.univ.biUnion childrenC_601_i6) ∪ commonEnvelope childrenD_601_i6).erase (5, 2) := by
  exact required_eq_combination childrenC_601_i6 childrenD_601_i6 (5, 2) required_601_i6
    (by decide +kernel) child_required_sub_601_i6 common_sub_601_i6 required_origin_601_i6
theorem envelope_origin_601_i6 : ∀ x ∈ envelope_601_i6,
    x = (5, 2) ∨ ∃ j, x ∈ childrenD_601_i6 j := by decide +kernel
theorem envelope_exact_601_i6 : envelope_601_i6 =
    insert (5, 2) (Finset.univ.biUnion childrenD_601_i6) := by
  exact envelope_eq_combination childrenD_601_i6 (5, 2) envelope_601_i6
    pivot_mem_601_i6 child_envelope_sub_601_i6 envelope_origin_601_i6
def checked_601_i6 : CheckedCard where
  required := required_601_i6
  envelope := envelope_601_i6
  height := height_601_i6
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_601_i6
def height_601_i5 : ℕ := 4
def childrenH_601_i5 : Fin 2 → ℕ := ![height_15, height_601_i6]
theorem height_exact_601_i5 : height_601_i5 = 1 + Finset.univ.sup childrenH_601_i5 := by decide +kernel
theorem required_origin_601_i5 : ∀ x ∈ required_601_i5,
    (∃ j, x ∈ childrenC_601_i5 j) ∨ ∀ j, x ∈ childrenD_601_i5 j := by decide +kernel
theorem required_exact_601_i5 : required_601_i5 =
    ((Finset.univ.biUnion childrenC_601_i5) ∪ commonEnvelope childrenD_601_i5).erase (4, 2) := by
  exact required_eq_combination childrenC_601_i5 childrenD_601_i5 (4, 2) required_601_i5
    (by decide +kernel) child_required_sub_601_i5 common_sub_601_i5 required_origin_601_i5
theorem envelope_origin_601_i5 : ∀ x ∈ envelope_601_i5,
    x = (4, 2) ∨ ∃ j, x ∈ childrenD_601_i5 j := by decide +kernel
theorem envelope_exact_601_i5 : envelope_601_i5 =
    insert (4, 2) (Finset.univ.biUnion childrenD_601_i5) := by
  exact envelope_eq_combination childrenD_601_i5 (4, 2) envelope_601_i5
    pivot_mem_601_i5 child_envelope_sub_601_i5 envelope_origin_601_i5
def checked_601_i5 : CheckedCard where
  required := required_601_i5
  envelope := envelope_601_i5
  height := height_601_i5
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_601_i5
def height_601_i4 : ℕ := 5
def childrenH_601_i4 : Fin 2 → ℕ := ![height_1, height_601_i5]
theorem height_exact_601_i4 : height_601_i4 = 1 + Finset.univ.sup childrenH_601_i4 := by decide +kernel
theorem required_origin_601_i4 : ∀ x ∈ required_601_i4,
    (∃ j, x ∈ childrenC_601_i4 j) ∨ ∀ j, x ∈ childrenD_601_i4 j := by decide +kernel
theorem required_exact_601_i4 : required_601_i4 =
    ((Finset.univ.biUnion childrenC_601_i4) ∪ commonEnvelope childrenD_601_i4).erase (6, 3) := by
  exact required_eq_combination childrenC_601_i4 childrenD_601_i4 (6, 3) required_601_i4
    (by decide +kernel) child_required_sub_601_i4 common_sub_601_i4 required_origin_601_i4
theorem envelope_origin_601_i4 : ∀ x ∈ envelope_601_i4,
    x = (6, 3) ∨ ∃ j, x ∈ childrenD_601_i4 j := by decide +kernel
theorem envelope_exact_601_i4 : envelope_601_i4 =
    insert (6, 3) (Finset.univ.biUnion childrenD_601_i4) := by
  exact envelope_eq_combination childrenD_601_i4 (6, 3) envelope_601_i4
    pivot_mem_601_i4 child_envelope_sub_601_i4 envelope_origin_601_i4
def checked_601_i4 : CheckedCard where
  required := required_601_i4
  envelope := envelope_601_i4
  height := height_601_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_601_i4
def height_601_i3 : ℕ := 6
def childrenH_601_i3 : Fin 2 → ℕ := ![height_3, height_601_i4]
theorem height_exact_601_i3 : height_601_i3 = 1 + Finset.univ.sup childrenH_601_i3 := by decide +kernel
theorem required_origin_601_i3 : ∀ x ∈ required_601_i3,
    (∃ j, x ∈ childrenC_601_i3 j) ∨ ∀ j, x ∈ childrenD_601_i3 j := by decide +kernel
theorem required_exact_601_i3 : required_601_i3 =
    ((Finset.univ.biUnion childrenC_601_i3) ∪ commonEnvelope childrenD_601_i3).erase (2, 4) := by
  exact required_eq_combination childrenC_601_i3 childrenD_601_i3 (2, 4) required_601_i3
    (by decide +kernel) child_required_sub_601_i3 common_sub_601_i3 required_origin_601_i3
theorem envelope_origin_601_i3 : ∀ x ∈ envelope_601_i3,
    x = (2, 4) ∨ ∃ j, x ∈ childrenD_601_i3 j := by decide +kernel
theorem envelope_exact_601_i3 : envelope_601_i3 =
    insert (2, 4) (Finset.univ.biUnion childrenD_601_i3) := by
  exact envelope_eq_combination childrenD_601_i3 (2, 4) envelope_601_i3
    pivot_mem_601_i3 child_envelope_sub_601_i3 envelope_origin_601_i3
def checked_601_i3 : CheckedCard where
  required := required_601_i3
  envelope := envelope_601_i3
  height := height_601_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_601_i3
def height_601_i7 : ℕ := 6
def childrenH_601_i7 : Fin 2 → ℕ := ![height_3, height_72]
theorem height_exact_601_i7 : height_601_i7 = 1 + Finset.univ.sup childrenH_601_i7 := by decide +kernel
theorem required_origin_601_i7 : ∀ x ∈ required_601_i7,
    (∃ j, x ∈ childrenC_601_i7 j) ∨ ∀ j, x ∈ childrenD_601_i7 j := by decide +kernel
theorem required_exact_601_i7 : required_601_i7 =
    ((Finset.univ.biUnion childrenC_601_i7) ∪ commonEnvelope childrenD_601_i7).erase (2, 4) := by
  exact required_eq_combination childrenC_601_i7 childrenD_601_i7 (2, 4) required_601_i7
    (by decide +kernel) child_required_sub_601_i7 common_sub_601_i7 required_origin_601_i7
theorem envelope_origin_601_i7 : ∀ x ∈ envelope_601_i7,
    x = (2, 4) ∨ ∃ j, x ∈ childrenD_601_i7 j := by decide +kernel
theorem envelope_exact_601_i7 : envelope_601_i7 =
    insert (2, 4) (Finset.univ.biUnion childrenD_601_i7) := by
  exact envelope_eq_combination childrenD_601_i7 (2, 4) envelope_601_i7
    pivot_mem_601_i7 child_envelope_sub_601_i7 envelope_origin_601_i7
def checked_601_i7 : CheckedCard where
  required := required_601_i7
  envelope := envelope_601_i7
  height := height_601_i7
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_601_i7
def height_601_i2 : ℕ := 10
def childrenH_601_i2 : Fin 5 → ℕ := ![height_406, height_499, height_601_i3, height_600, height_601_i7]
theorem height_exact_601_i2 : height_601_i2 = 1 + Finset.univ.sup childrenH_601_i2 := by decide +kernel
theorem required_origin_601_i2 : ∀ x ∈ required_601_i2,
    (∃ j, x ∈ childrenC_601_i2 j) ∨ ∀ j, x ∈ childrenD_601_i2 j := by decide +kernel
theorem required_exact_601_i2 : required_601_i2 =
    ((Finset.univ.biUnion childrenC_601_i2) ∪ commonEnvelope childrenD_601_i2).erase (4, 4) := by
  exact required_eq_combination childrenC_601_i2 childrenD_601_i2 (4, 4) required_601_i2
    (by decide +kernel) child_required_sub_601_i2 common_sub_601_i2 required_origin_601_i2
theorem envelope_origin_601_i2 : ∀ x ∈ envelope_601_i2,
    x = (4, 4) ∨ ∃ j, x ∈ childrenD_601_i2 j := by decide +kernel
theorem envelope_exact_601_i2 : envelope_601_i2 =
    insert (4, 4) (Finset.univ.biUnion childrenD_601_i2) := by
  exact envelope_eq_combination childrenD_601_i2 (4, 4) envelope_601_i2
    pivot_mem_601_i2 child_envelope_sub_601_i2 envelope_origin_601_i2
def checked_601_i2 : CheckedCard where
  required := required_601_i2
  envelope := envelope_601_i2
  height := height_601_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_601_i2
def height_601_i8 : ℕ := 10
def childrenH_601_i8 : Fin 2 → ℕ := ![height_406, height_501]
theorem height_exact_601_i8 : height_601_i8 = 1 + Finset.univ.sup childrenH_601_i8 := by decide +kernel
theorem required_origin_601_i8 : ∀ x ∈ required_601_i8,
    (∃ j, x ∈ childrenC_601_i8 j) ∨ ∀ j, x ∈ childrenD_601_i8 j := by decide +kernel
theorem required_exact_601_i8 : required_601_i8 =
    ((Finset.univ.biUnion childrenC_601_i8) ∪ commonEnvelope childrenD_601_i8).erase (4, 4) := by
  exact required_eq_combination childrenC_601_i8 childrenD_601_i8 (4, 4) required_601_i8
    (by decide +kernel) child_required_sub_601_i8 common_sub_601_i8 required_origin_601_i8
theorem envelope_origin_601_i8 : ∀ x ∈ envelope_601_i8,
    x = (4, 4) ∨ ∃ j, x ∈ childrenD_601_i8 j := by decide +kernel
theorem envelope_exact_601_i8 : envelope_601_i8 =
    insert (4, 4) (Finset.univ.biUnion childrenD_601_i8) := by
  exact envelope_eq_combination childrenD_601_i8 (4, 4) envelope_601_i8
    pivot_mem_601_i8 child_envelope_sub_601_i8 envelope_origin_601_i8
def checked_601_i8 : CheckedCard where
  required := required_601_i8
  envelope := envelope_601_i8
  height := height_601_i8
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_601_i8
def height_601 : ℕ := 11
def childrenH_601 : Fin 4 → ℕ := ![height_247, height_601_i0, height_601_i2, height_601_i8]
theorem height_exact_601 : height_601 = 1 + Finset.univ.sup childrenH_601 := by decide +kernel
theorem required_origin_601 : ∀ x ∈ required_601,
    (∃ j, x ∈ childrenC_601 j) ∨ ∀ j, x ∈ childrenD_601 j := by decide +kernel
theorem required_exact_601 : required_601 =
    ((Finset.univ.biUnion childrenC_601) ∪ commonEnvelope childrenD_601).erase (4, 3) := by
  exact required_eq_combination childrenC_601 childrenD_601 (4, 3) required_601
    (by decide +kernel) child_required_sub_601 common_sub_601 required_origin_601
theorem envelope_origin_601 : ∀ x ∈ envelope_601,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_601 j := by decide +kernel
theorem envelope_exact_601 : envelope_601 =
    insert (4, 3) (Finset.univ.biUnion childrenD_601) := by
  exact envelope_eq_combination childrenD_601 (4, 3) envelope_601
    pivot_mem_601 child_envelope_sub_601 envelope_origin_601
def checked_601 : CheckedCard where
  required := required_601
  envelope := envelope_601
  height := height_601
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_601
def height_613 : ℕ := 11
def childrenH_613 : Fin 6 → ℕ := ![height_104, height_329, height_409, height_612, height_612, height_612]
theorem height_exact_613 : height_613 = 1 + Finset.univ.sup childrenH_613 := by decide +kernel
theorem required_origin_613 : ∀ x ∈ required_613,
    (∃ j, x ∈ childrenC_613 j) ∨ ∀ j, x ∈ childrenD_613 j := by decide +kernel
theorem required_exact_613 : required_613 =
    ((Finset.univ.biUnion childrenC_613) ∪ commonEnvelope childrenD_613).erase (2, 5) := by
  exact required_eq_combination childrenC_613 childrenD_613 (2, 5) required_613
    (by decide +kernel) child_required_sub_613 common_sub_613 required_origin_613
theorem envelope_origin_613 : ∀ x ∈ envelope_613,
    x = (2, 5) ∨ ∃ j, x ∈ childrenD_613 j := by decide +kernel
theorem envelope_exact_613 : envelope_613 =
    insert (2, 5) (Finset.univ.biUnion childrenD_613) := by
  exact envelope_eq_combination childrenD_613 (2, 5) envelope_613
    pivot_mem_613 child_envelope_sub_613 envelope_origin_613
def checked_613 : CheckedCard where
  required := required_613
  envelope := envelope_613
  height := height_613
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_613
end SnakyPrototype.Certificate21

end OAI
