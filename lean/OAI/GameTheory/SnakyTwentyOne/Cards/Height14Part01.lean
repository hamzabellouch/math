import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height10Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height13Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height13Part02
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_553_i3 : Finset Cell := ⟨(([(3, 7), (4, 4), (4, 7), (5, 4), (5, 5), (5, 6), (6, 6), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_553_i3 : Finset Cell := ⟨(([(3, 7), (4, 3), (4, 4), (4, 7), (5, 4), (5, 5), (5, 6), (5, 7), (6, 6), (6, 7), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_553_i3 : Fin 2 → Finset Cell := ![(placed21 4 (3, 7) required_3), (placed21 7 (5, 7) required_5)]
def childrenD_553_i3 : Fin 2 → Finset Cell := ![(placed21 4 (3, 7) envelope_3), (placed21 7 (5, 7) envelope_5)]
theorem common_sub_553_i3 : commonEnvelope childrenD_553_i3 ⊆ insert (5, 7) required_553_i3 := by decide +kernel
theorem child_required_sub_553_i3 : ∀ j, childrenC_553_i3 j ⊆ insert (5, 7) required_553_i3 := by decide +kernel
theorem child_envelope_sub_553_i3 : ∀ j, childrenD_553_i3 j ⊆ envelope_553_i3 := by decide +kernel
theorem pivot_mem_553_i3 : (5, 7) ∈ envelope_553_i3 := by decide +kernel
theorem children_work_553_i3 : ∀ j, Template HasSnaky 1 (childrenC_553_i3 j) (childrenD_553_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_3 4 (3, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_5 7 (5, 7)).mono (by decide +kernel)
theorem row_works_553_i3 : Template HasSnaky 2 required_553_i3 envelope_553_i3 := by
  refine compose HasSnaky 1 childrenC_553_i3 childrenD_553_i3 children_work_553_i3 (5, 7)
    required_553_i3 envelope_553_i3 pivot_mem_553_i3 child_required_sub_553_i3 child_envelope_sub_553_i3 ?_
  intro b hb
  exact common_sub_553_i3 (mem_commonEnvelope childrenD_553_i3 b hb)
def required_553_i2 : Finset Cell := ⟨(([(3, 7), (4, 4), (4, 7), (5, 4), (5, 6), (6, 6), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_553_i2 : Finset Cell := ⟨(([(3, 7), (4, 1), (4, 2), (4, 3), (4, 4), (4, 7), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 1), (6, 2), (6, 3), (6, 6), (6, 7), (6, 8), (6, 9), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_553_i2 : Fin 4 → Finset Cell := ![(placed21 6 (6, 7) required_10), (placed21 6 (5, 7) required_52), (placed21 0 (5, 3) required_52), required_553_i3]
def childrenD_553_i2 : Fin 4 → Finset Cell := ![(placed21 6 (6, 7) envelope_10), (placed21 6 (5, 7) envelope_52), (placed21 0 (5, 3) envelope_52), envelope_553_i3]
theorem common_sub_553_i2 : commonEnvelope childrenD_553_i2 ⊆ insert (5, 5) required_553_i2 := by decide +kernel
theorem child_required_sub_553_i2 : ∀ j, childrenC_553_i2 j ⊆ insert (5, 5) required_553_i2 := by decide +kernel
theorem child_envelope_sub_553_i2 : ∀ j, childrenD_553_i2 j ⊆ envelope_553_i2 := by decide +kernel
theorem pivot_mem_553_i2 : (5, 5) ∈ envelope_553_i2 := by decide +kernel
theorem children_work_553_i2 : ∀ j, Template HasSnaky 4 (childrenC_553_i2 j) (childrenD_553_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_10 6 (6, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_52 6 (5, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_52 0 (5, 3)).mono (by decide +kernel)
  · exact row_works_553_i3.mono (by decide +kernel)
theorem row_works_553_i2 : Template HasSnaky 5 required_553_i2 envelope_553_i2 := by
  refine compose HasSnaky 4 childrenC_553_i2 childrenD_553_i2 children_work_553_i2 (5, 5)
    required_553_i2 envelope_553_i2 pivot_mem_553_i2 child_required_sub_553_i2 child_envelope_sub_553_i2 ?_
  intro b hb
  exact common_sub_553_i2 (mem_commonEnvelope childrenD_553_i2 b hb)
def required_553_i1 : Finset Cell := ⟨(([(3, 7), (4, 4), (4, 7), (5, 4), (6, 6), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_553_i1 : Finset Cell := ⟨(([(3, 7), (4, 1), (4, 2), (4, 3), (4, 4), (4, 6), (4, 7), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 1), (6, 2), (6, 3), (6, 6), (6, 7), (6, 8), (6, 9), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_553_i1 : Fin 2 → Finset Cell := ![(placed21 2 (7, 6) required_3), required_553_i2]
def childrenD_553_i1 : Fin 2 → Finset Cell := ![(placed21 2 (7, 6) envelope_3), envelope_553_i2]
theorem common_sub_553_i1 : commonEnvelope childrenD_553_i1 ⊆ insert (5, 6) required_553_i1 := by decide +kernel
theorem child_required_sub_553_i1 : ∀ j, childrenC_553_i1 j ⊆ insert (5, 6) required_553_i1 := by decide +kernel
theorem child_envelope_sub_553_i1 : ∀ j, childrenD_553_i1 j ⊆ envelope_553_i1 := by decide +kernel
theorem pivot_mem_553_i1 : (5, 6) ∈ envelope_553_i1 := by decide +kernel
theorem children_work_553_i1 : ∀ j, Template HasSnaky 5 (childrenC_553_i1 j) (childrenD_553_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_3 2 (7, 6)).mono (by decide +kernel)
  · exact row_works_553_i2.mono (by decide +kernel)
theorem row_works_553_i1 : Template HasSnaky 6 required_553_i1 envelope_553_i1 := by
  refine compose HasSnaky 5 childrenC_553_i1 childrenD_553_i1 children_work_553_i1 (5, 6)
    required_553_i1 envelope_553_i1 pivot_mem_553_i1 child_required_sub_553_i1 child_envelope_sub_553_i1 ?_
  intro b hb
  exact common_sub_553_i1 (mem_commonEnvelope childrenD_553_i1 b hb)
def required_553_i6 : Finset Cell := ⟨(([(3, 4), (4, 4), (5, 4), (7, 4), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_553_i6 : Finset Cell := ⟨(([(2, 3), (3, 3), (3, 4), (4, 3), (4, 4), (5, 4), (6, 3), (6, 4), (6, 7), (6, 8), (6, 9), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (8, 5), (8, 7), (8, 8), (8, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_553_i6 : Fin 2 → Finset Cell := ![(placed21 7 (7, 4) required_6), (placed21 0 (4, 3) required_145)]
def childrenD_553_i6 : Fin 2 → Finset Cell := ![(placed21 7 (7, 4) envelope_6), (placed21 0 (4, 3) envelope_145)]
theorem common_sub_553_i6 : commonEnvelope childrenD_553_i6 ⊆ insert (6, 4) required_553_i6 := by decide +kernel
theorem child_required_sub_553_i6 : ∀ j, childrenC_553_i6 j ⊆ insert (6, 4) required_553_i6 := by decide +kernel
theorem child_envelope_sub_553_i6 : ∀ j, childrenD_553_i6 j ⊆ envelope_553_i6 := by decide +kernel
theorem pivot_mem_553_i6 : (6, 4) ∈ envelope_553_i6 := by decide +kernel
theorem children_work_553_i6 : ∀ j, Template HasSnaky 5 (childrenC_553_i6 j) (childrenD_553_i6 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_6 7 (7, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_145 0 (4, 3)).mono (by decide +kernel)
theorem row_works_553_i6 : Template HasSnaky 6 required_553_i6 envelope_553_i6 := by
  refine compose HasSnaky 5 childrenC_553_i6 childrenD_553_i6 children_work_553_i6 (6, 4)
    required_553_i6 envelope_553_i6 pivot_mem_553_i6 child_required_sub_553_i6 child_envelope_sub_553_i6 ?_
  intro b hb
  exact common_sub_553_i6 (mem_commonEnvelope childrenD_553_i6 b hb)
def required_553_i5 : Finset Cell := ⟨(([(3, 4), (4, 4), (5, 4), (6, 6), (6, 7), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_553_i5 : Finset Cell := ⟨(([(2, 3), (3, 3), (3, 4), (4, 3), (4, 4), (5, 4), (6, 3), (6, 4), (6, 6), (6, 7), (6, 8), (6, 9), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (8, 3), (8, 5), (8, 7), (8, 8), (8, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_553_i5 : Fin 3 → Finset Cell := ![(placed21 2 (7, 3) required_54), (placed21 3 (2, 4) required_158), required_553_i6]
def childrenD_553_i5 : Fin 3 → Finset Cell := ![(placed21 2 (7, 3) envelope_54), (placed21 3 (2, 4) envelope_158), envelope_553_i6]
theorem common_sub_553_i5 : commonEnvelope childrenD_553_i5 ⊆ insert (7, 4) required_553_i5 := by decide +kernel
theorem child_required_sub_553_i5 : ∀ j, childrenC_553_i5 j ⊆ insert (7, 4) required_553_i5 := by decide +kernel
theorem child_envelope_sub_553_i5 : ∀ j, childrenD_553_i5 j ⊆ envelope_553_i5 := by decide +kernel
theorem pivot_mem_553_i5 : (7, 4) ∈ envelope_553_i5 := by decide +kernel
theorem children_work_553_i5 : ∀ j, Template HasSnaky 6 (childrenC_553_i5 j) (childrenD_553_i5 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_54 2 (7, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_158 3 (2, 4)).mono (by decide +kernel)
  · exact row_works_553_i6.mono (by decide +kernel)
theorem row_works_553_i5 : Template HasSnaky 7 required_553_i5 envelope_553_i5 := by
  refine compose HasSnaky 6 childrenC_553_i5 childrenD_553_i5 children_work_553_i5 (7, 4)
    required_553_i5 envelope_553_i5 pivot_mem_553_i5 child_required_sub_553_i5 child_envelope_sub_553_i5 ?_
  intro b hb
  exact common_sub_553_i5 (mem_commonEnvelope childrenD_553_i5 b hb)
def required_553_i4 : Finset Cell := ⟨(([(3, 4), (3, 7), (4, 4), (4, 7), (5, 4), (6, 6), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_553_i4 : Finset Cell := ⟨(([(2, 3), (3, 3), (3, 4), (3, 7), (4, 3), (4, 4), (4, 7), (5, 4), (5, 7), (6, 3), (6, 4), (6, 6), (6, 7), (6, 8), (6, 9), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (8, 3), (8, 5), (8, 7), (8, 8), (8, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_553_i4 : Fin 2 → Finset Cell := ![(placed21 4 (3, 7) required_2), required_553_i5]
def childrenD_553_i4 : Fin 2 → Finset Cell := ![(placed21 4 (3, 7) envelope_2), envelope_553_i5]
theorem common_sub_553_i4 : commonEnvelope childrenD_553_i4 ⊆ insert (6, 7) required_553_i4 := by decide +kernel
theorem child_required_sub_553_i4 : ∀ j, childrenC_553_i4 j ⊆ insert (6, 7) required_553_i4 := by decide +kernel
theorem child_envelope_sub_553_i4 : ∀ j, childrenD_553_i4 j ⊆ envelope_553_i4 := by decide +kernel
theorem pivot_mem_553_i4 : (6, 7) ∈ envelope_553_i4 := by decide +kernel
theorem children_work_553_i4 : ∀ j, Template HasSnaky 7 (childrenC_553_i4 j) (childrenD_553_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_2 4 (3, 7)).mono (by decide +kernel)
  · exact row_works_553_i5.mono (by decide +kernel)
theorem row_works_553_i4 : Template HasSnaky 8 required_553_i4 envelope_553_i4 := by
  refine compose HasSnaky 7 childrenC_553_i4 childrenD_553_i4 children_work_553_i4 (6, 7)
    required_553_i4 envelope_553_i4 pivot_mem_553_i4 child_required_sub_553_i4 child_envelope_sub_553_i4 ?_
  intro b hb
  exact common_sub_553_i4 (mem_commonEnvelope childrenD_553_i4 b hb)
def required_553_i8 : Finset Cell := ⟨(([(3, 4), (3, 7), (4, 4), (5, 4), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_553_i8 : Finset Cell := ⟨(([(2, 3), (2, 5), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 1), (4, 2), (4, 3), (4, 4), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 4), (7, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_553_i8 : Fin 2 → Finset Cell := ![(placed21 6 (5, 7) required_54), (placed21 3 (2, 7) required_247)]
def childrenD_553_i8 : Fin 2 → Finset Cell := ![(placed21 6 (5, 7) envelope_54), (placed21 3 (2, 7) envelope_247)]
theorem common_sub_553_i8 : commonEnvelope childrenD_553_i8 ⊆ insert (4, 3) required_553_i8 := by decide +kernel
theorem child_required_sub_553_i8 : ∀ j, childrenC_553_i8 j ⊆ insert (4, 3) required_553_i8 := by decide +kernel
theorem child_envelope_sub_553_i8 : ∀ j, childrenD_553_i8 j ⊆ envelope_553_i8 := by decide +kernel
theorem pivot_mem_553_i8 : (4, 3) ∈ envelope_553_i8 := by decide +kernel
theorem children_work_553_i8 : ∀ j, Template HasSnaky 3 (childrenC_553_i8 j) (childrenD_553_i8 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_54 6 (5, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_247 3 (2, 7)).mono (by decide +kernel)
theorem row_works_553_i8 : Template HasSnaky 4 required_553_i8 envelope_553_i8 := by
  refine compose HasSnaky 3 childrenC_553_i8 childrenD_553_i8 children_work_553_i8 (4, 3)
    required_553_i8 envelope_553_i8 pivot_mem_553_i8 child_required_sub_553_i8 child_envelope_sub_553_i8 ?_
  intro b hb
  exact common_sub_553_i8 (mem_commonEnvelope childrenD_553_i8 b hb)
def required_553_i7 : Finset Cell := ⟨(([(3, 4), (3, 7), (4, 4), (4, 7), (5, 4), (6, 6), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_553_i7 : Finset Cell := ⟨(([(2, 3), (2, 5), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 1), (4, 2), (4, 3), (4, 4), (4, 6), (4, 7), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 4), (6, 6), (7, 4), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_553_i7 : Fin 2 → Finset Cell := ![(placed21 2 (7, 6) required_3), required_553_i8]
def childrenD_553_i7 : Fin 2 → Finset Cell := ![(placed21 2 (7, 6) envelope_3), envelope_553_i8]
theorem common_sub_553_i7 : commonEnvelope childrenD_553_i7 ⊆ insert (5, 6) required_553_i7 := by decide +kernel
theorem child_required_sub_553_i7 : ∀ j, childrenC_553_i7 j ⊆ insert (5, 6) required_553_i7 := by decide +kernel
theorem child_envelope_sub_553_i7 : ∀ j, childrenD_553_i7 j ⊆ envelope_553_i7 := by decide +kernel
theorem pivot_mem_553_i7 : (5, 6) ∈ envelope_553_i7 := by decide +kernel
theorem children_work_553_i7 : ∀ j, Template HasSnaky 4 (childrenC_553_i7 j) (childrenD_553_i7 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_3 2 (7, 6)).mono (by decide +kernel)
  · exact row_works_553_i8.mono (by decide +kernel)
theorem row_works_553_i7 : Template HasSnaky 5 required_553_i7 envelope_553_i7 := by
  refine compose HasSnaky 4 childrenC_553_i7 childrenD_553_i7 children_work_553_i7 (5, 6)
    required_553_i7 envelope_553_i7 pivot_mem_553_i7 child_required_sub_553_i7 child_envelope_sub_553_i7 ?_
  intro b hb
  exact common_sub_553_i7 (mem_commonEnvelope childrenD_553_i7 b hb)
def required_553_i0 : Finset Cell := ⟨(([(3, 4), (3, 7), (4, 4), (4, 7), (6, 6), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_553_i0 : Finset Cell := ⟨(([(2, 3), (2, 5), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 1), (4, 2), (4, 3), (4, 4), (4, 6), (4, 7), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 1), (6, 2), (6, 3), (6, 4), (6, 6), (6, 7), (6, 8), (6, 9), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (8, 3), (8, 5), (8, 7), (8, 8), (8, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_553_i0 : Fin 4 → Finset Cell := ![(placed21 3 (2, 7) required_433), required_553_i1, required_553_i4, required_553_i7]
def childrenD_553_i0 : Fin 4 → Finset Cell := ![(placed21 3 (2, 7) envelope_433), envelope_553_i1, envelope_553_i4, envelope_553_i7]
theorem common_sub_553_i0 : commonEnvelope childrenD_553_i0 ⊆ insert (5, 4) required_553_i0 := by decide +kernel
theorem child_required_sub_553_i0 : ∀ j, childrenC_553_i0 j ⊆ insert (5, 4) required_553_i0 := by decide +kernel
theorem child_envelope_sub_553_i0 : ∀ j, childrenD_553_i0 j ⊆ envelope_553_i0 := by decide +kernel
theorem pivot_mem_553_i0 : (5, 4) ∈ envelope_553_i0 := by decide +kernel
theorem children_work_553_i0 : ∀ j, Template HasSnaky 8 (childrenC_553_i0 j) (childrenD_553_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_433 3 (2, 7)).mono (by decide +kernel)
  · exact row_works_553_i1.mono (by decide +kernel)
  · exact row_works_553_i4.mono (by decide +kernel)
  · exact row_works_553_i7.mono (by decide +kernel)
theorem row_works_553_i0 : Template HasSnaky 9 required_553_i0 envelope_553_i0 := by
  refine compose HasSnaky 8 childrenC_553_i0 childrenD_553_i0 children_work_553_i0 (5, 4)
    required_553_i0 envelope_553_i0 pivot_mem_553_i0 child_required_sub_553_i0 child_envelope_sub_553_i0 ?_
  intro b hb
  exact common_sub_553_i0 (mem_commonEnvelope childrenD_553_i0 b hb)
def required_553 : Finset Cell := ⟨(([(3, 4), (3, 7), (4, 4), (4, 7), (6, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_553 : Finset Cell := ⟨(([(0, 3), (1, 2), (1, 3), (2, 0), (2, 1), (2, 2), (2, 3), (2, 5), (2, 6), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 9), (3, 10), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 6), (4, 7), (4, 9), (4, 10), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 1), (6, 2), (6, 3), (6, 4), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (6, 12), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (7, 12), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (8, 11), (8, 12), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (9, 10), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (10, 9), (10, 10), (10, 11), (11, 4), (11, 5), (11, 6), (11, 7), (11, 8), (11, 9), (11, 10), (12, 5), (12, 7), (12, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_553 : Fin 5 → Finset Cell := ![(placed21 3 (3, 7) required_107), (placed21 3 (3, 7) required_163), (placed21 0 (2, 1) required_538), required_552, required_553_i0]
def childrenD_553 : Fin 5 → Finset Cell := ![(placed21 3 (3, 7) envelope_107), (placed21 3 (3, 7) envelope_163), (placed21 0 (2, 1) envelope_538), envelope_552, envelope_553_i0]
theorem common_sub_553 : commonEnvelope childrenD_553 ⊆ insert (7, 6) required_553 := by decide +kernel
theorem child_required_sub_553 : ∀ j, childrenC_553 j ⊆ insert (7, 6) required_553 := by decide +kernel
theorem child_envelope_sub_553 : ∀ j, childrenD_553 j ⊆ envelope_553 := by decide +kernel
theorem pivot_mem_553 : (7, 6) ∈ envelope_553 := by decide +kernel
theorem children_work_553 : ∀ j, Template HasSnaky 13 (childrenC_553 j) (childrenD_553 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_107 3 (3, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_163 3 (3, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_538 0 (2, 1)).mono (by decide +kernel)
  · exact row_works_552.mono (by decide +kernel)
  · exact row_works_553_i0.mono (by decide +kernel)
theorem row_works_553 : Template HasSnaky 14 required_553 envelope_553 := by
  refine compose HasSnaky 13 childrenC_553 childrenD_553 children_work_553 (7, 6)
    required_553 envelope_553 pivot_mem_553 child_required_sub_553 child_envelope_sub_553 ?_
  intro b hb
  exact common_sub_553 (mem_commonEnvelope childrenD_553 b hb)
def required_557_i0 : Finset Cell := ⟨(([(1, 6), (2, 6), (4, 5), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_557_i0 : Finset Cell := ⟨(([(1, 6), (2, 6), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_557_i0 : Fin 3 → Finset Cell := ![(placed21 6 (5, 9) required_13), (placed21 7 (5, 7) required_28), (placed21 4 (1, 8) required_58)]
def childrenD_557_i0 : Fin 3 → Finset Cell := ![(placed21 6 (5, 9) envelope_13), (placed21 7 (5, 7) envelope_28), (placed21 4 (1, 8) envelope_58)]
theorem common_sub_557_i0 : commonEnvelope childrenD_557_i0 ⊆ insert (4, 7) required_557_i0 := by decide +kernel
theorem child_required_sub_557_i0 : ∀ j, childrenC_557_i0 j ⊆ insert (4, 7) required_557_i0 := by decide +kernel
theorem child_envelope_sub_557_i0 : ∀ j, childrenD_557_i0 j ⊆ envelope_557_i0 := by decide +kernel
theorem pivot_mem_557_i0 : (4, 7) ∈ envelope_557_i0 := by decide +kernel
theorem children_work_557_i0 : ∀ j, Template HasSnaky 4 (childrenC_557_i0 j) (childrenD_557_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_13 6 (5, 9)).mono (by decide +kernel)
  · exact (placed21_template row_works_28 7 (5, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_58 4 (1, 8)).mono (by decide +kernel)
theorem row_works_557_i0 : Template HasSnaky 5 required_557_i0 envelope_557_i0 := by
  refine compose HasSnaky 4 childrenC_557_i0 childrenD_557_i0 children_work_557_i0 (4, 7)
    required_557_i0 envelope_557_i0 pivot_mem_557_i0 child_required_sub_557_i0 child_envelope_sub_557_i0 ?_
  intro b hb
  exact common_sub_557_i0 (mem_commonEnvelope childrenD_557_i0 b hb)
def required_557_i4 : Finset Cell := ⟨(([(1, 3), (1, 6), (2, 2), (2, 3), (2, 6), (3, 6), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_557_i4 : Finset Cell := ⟨(([(0, 5), (1, 3), (1, 4), (1, 5), (1, 6), (2, 2), (2, 3), (2, 6), (3, 6), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_557_i4 : Fin 2 → Finset Cell := ![(placed21 3 (1, 6) required_2), (placed21 6 (4, 6) required_5)]
def childrenD_557_i4 : Fin 2 → Finset Cell := ![(placed21 3 (1, 6) envelope_2), (placed21 6 (4, 6) envelope_5)]
theorem common_sub_557_i4 : commonEnvelope childrenD_557_i4 ⊆ insert (1, 5) required_557_i4 := by decide +kernel
theorem child_required_sub_557_i4 : ∀ j, childrenC_557_i4 j ⊆ insert (1, 5) required_557_i4 := by decide +kernel
theorem child_envelope_sub_557_i4 : ∀ j, childrenD_557_i4 j ⊆ envelope_557_i4 := by decide +kernel
theorem pivot_mem_557_i4 : (1, 5) ∈ envelope_557_i4 := by decide +kernel
theorem children_work_557_i4 : ∀ j, Template HasSnaky 1 (childrenC_557_i4 j) (childrenD_557_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_2 3 (1, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_5 6 (4, 6)).mono (by decide +kernel)
theorem row_works_557_i4 : Template HasSnaky 2 required_557_i4 envelope_557_i4 := by
  refine compose HasSnaky 1 childrenC_557_i4 childrenD_557_i4 children_work_557_i4 (1, 5)
    required_557_i4 envelope_557_i4 pivot_mem_557_i4 child_required_sub_557_i4 child_envelope_sub_557_i4 ?_
  intro b hb
  exact common_sub_557_i4 (mem_commonEnvelope childrenD_557_i4 b hb)
def required_557_i6 : Finset Cell := ⟨(([(1, 3), (2, 2), (2, 3), (3, 3), (3, 6), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_557_i6 : Finset Cell := ⟨(([(0, 2), (1, 2), (1, 3), (2, 0), (2, 1), (2, 2), (2, 3), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 0), (4, 1), (4, 2), (4, 3), (5, 1), (5, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_557_i6 : Fin 2 → Finset Cell := ![(placed21 7 (3, 6) required_1), (placed21 7 (5, 4) required_392)]
def childrenD_557_i6 : Fin 2 → Finset Cell := ![(placed21 7 (3, 6) envelope_1), (placed21 7 (5, 4) envelope_392)]
theorem common_sub_557_i6 : commonEnvelope childrenD_557_i6 ⊆ insert (3, 4) required_557_i6 := by decide +kernel
theorem child_required_sub_557_i6 : ∀ j, childrenC_557_i6 j ⊆ insert (3, 4) required_557_i6 := by decide +kernel
theorem child_envelope_sub_557_i6 : ∀ j, childrenD_557_i6 j ⊆ envelope_557_i6 := by decide +kernel
theorem pivot_mem_557_i6 : (3, 4) ∈ envelope_557_i6 := by decide +kernel
theorem children_work_557_i6 : ∀ j, Template HasSnaky 6 (childrenC_557_i6 j) (childrenD_557_i6 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_1 7 (3, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_392 7 (5, 4)).mono (by decide +kernel)
theorem row_works_557_i6 : Template HasSnaky 7 required_557_i6 envelope_557_i6 := by
  refine compose HasSnaky 6 childrenC_557_i6 childrenD_557_i6 children_work_557_i6 (3, 4)
    required_557_i6 envelope_557_i6 pivot_mem_557_i6 child_required_sub_557_i6 child_envelope_sub_557_i6 ?_
  intro b hb
  exact common_sub_557_i6 (mem_commonEnvelope childrenD_557_i6 b hb)
def required_557_i5 : Finset Cell := ⟨(([(1, 3), (2, 2), (2, 3), (3, 6), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_557_i5 : Finset Cell := ⟨(([(0, 2), (1, 2), (1, 3), (2, 0), (2, 1), (2, 2), (2, 3), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 0), (4, 1), (4, 2), (4, 3), (5, 1), (5, 2), (5, 3), (5, 4), (6, 2), (6, 3), (6, 4), (7, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_557_i5 : Fin 3 → Finset Cell := ![(placed21 3 (0, 3) required_11), (placed21 1 (1, 2) required_41), required_557_i6]
def childrenD_557_i5 : Fin 3 → Finset Cell := ![(placed21 3 (0, 3) envelope_11), (placed21 1 (1, 2) envelope_41), envelope_557_i6]
theorem common_sub_557_i5 : commonEnvelope childrenD_557_i5 ⊆ insert (3, 3) required_557_i5 := by decide +kernel
theorem child_required_sub_557_i5 : ∀ j, childrenC_557_i5 j ⊆ insert (3, 3) required_557_i5 := by decide +kernel
theorem child_envelope_sub_557_i5 : ∀ j, childrenD_557_i5 j ⊆ envelope_557_i5 := by decide +kernel
theorem pivot_mem_557_i5 : (3, 3) ∈ envelope_557_i5 := by decide +kernel
theorem children_work_557_i5 : ∀ j, Template HasSnaky 7 (childrenC_557_i5 j) (childrenD_557_i5 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_11 3 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_41 1 (1, 2)).mono (by decide +kernel)
  · exact row_works_557_i6.mono (by decide +kernel)
theorem row_works_557_i5 : Template HasSnaky 8 required_557_i5 envelope_557_i5 := by
  refine compose HasSnaky 7 childrenC_557_i5 childrenD_557_i5 children_work_557_i5 (3, 3)
    required_557_i5 envelope_557_i5 pivot_mem_557_i5 child_required_sub_557_i5 child_envelope_sub_557_i5 ?_
  intro b hb
  exact common_sub_557_i5 (mem_commonEnvelope childrenD_557_i5 b hb)
def required_557_i3 : Finset Cell := ⟨(([(1, 3), (1, 6), (2, 3), (2, 6), (3, 6), (4, 3), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_557_i3 : Finset Cell := ⟨(([(0, 2), (0, 5), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 0), (2, 1), (2, 2), (2, 3), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 0), (4, 1), (4, 2), (4, 3), (4, 6), (5, 1), (5, 2), (5, 3), (5, 4), (6, 2), (6, 3), (6, 4), (7, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_557_i3 : Fin 2 → Finset Cell := ![required_557_i4, required_557_i5]
def childrenD_557_i3 : Fin 2 → Finset Cell := ![envelope_557_i4, envelope_557_i5]
theorem common_sub_557_i3 : commonEnvelope childrenD_557_i3 ⊆ insert (2, 2) required_557_i3 := by decide +kernel
theorem child_required_sub_557_i3 : ∀ j, childrenC_557_i3 j ⊆ insert (2, 2) required_557_i3 := by decide +kernel
theorem child_envelope_sub_557_i3 : ∀ j, childrenD_557_i3 j ⊆ envelope_557_i3 := by decide +kernel
theorem pivot_mem_557_i3 : (2, 2) ∈ envelope_557_i3 := by decide +kernel
theorem children_work_557_i3 : ∀ j, Template HasSnaky 8 (childrenC_557_i3 j) (childrenD_557_i3 j) := by
  intro j
  fin_cases j
  · exact row_works_557_i4.mono (by decide +kernel)
  · exact row_works_557_i5.mono (by decide +kernel)
theorem row_works_557_i3 : Template HasSnaky 9 required_557_i3 envelope_557_i3 := by
  refine compose HasSnaky 8 childrenC_557_i3 childrenD_557_i3 children_work_557_i3 (2, 2)
    required_557_i3 envelope_557_i3 pivot_mem_557_i3 child_required_sub_557_i3 child_envelope_sub_557_i3 ?_
  intro b hb
  exact common_sub_557_i3 (mem_commonEnvelope childrenD_557_i3 b hb)
def required_557_i2 : Finset Cell := ⟨(([(1, 3), (1, 6), (2, 3), (2, 6), (3, 6), (4, 5), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_557_i2 : Finset Cell := ⟨(([(0, 2), (0, 5), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 0), (2, 1), (2, 2), (2, 3), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 1), (5, 2), (5, 3), (5, 4), (6, 2), (6, 3), (6, 4), (7, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_557_i2 : Fin 3 → Finset Cell := ![(placed21 4 (3, 7) required_42), (placed21 1 (1, 2) required_152), required_557_i3]
def childrenD_557_i2 : Fin 3 → Finset Cell := ![(placed21 4 (3, 7) envelope_42), (placed21 1 (1, 2) envelope_152), envelope_557_i3]
theorem common_sub_557_i2 : commonEnvelope childrenD_557_i2 ⊆ insert (4, 3) required_557_i2 := by decide +kernel
theorem child_required_sub_557_i2 : ∀ j, childrenC_557_i2 j ⊆ insert (4, 3) required_557_i2 := by decide +kernel
theorem child_envelope_sub_557_i2 : ∀ j, childrenD_557_i2 j ⊆ envelope_557_i2 := by decide +kernel
theorem pivot_mem_557_i2 : (4, 3) ∈ envelope_557_i2 := by decide +kernel
theorem children_work_557_i2 : ∀ j, Template HasSnaky 9 (childrenC_557_i2 j) (childrenD_557_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_42 4 (3, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_152 1 (1, 2)).mono (by decide +kernel)
  · exact row_works_557_i3.mono (by decide +kernel)
theorem row_works_557_i2 : Template HasSnaky 10 required_557_i2 envelope_557_i2 := by
  refine compose HasSnaky 9 childrenC_557_i2 childrenD_557_i2 children_work_557_i2 (4, 3)
    required_557_i2 envelope_557_i2 pivot_mem_557_i2 child_required_sub_557_i2 child_envelope_sub_557_i2 ?_
  intro b hb
  exact common_sub_557_i2 (mem_commonEnvelope childrenD_557_i2 b hb)
def required_557_i1 : Finset Cell := ⟨(([(1, 3), (1, 6), (2, 3), (2, 6), (4, 5), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_557_i1 : Finset Cell := ⟨(([(0, 2), (0, 5), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 0), (2, 1), (2, 2), (2, 3), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (6, 2), (6, 3), (6, 4), (7, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_557_i1 : Fin 2 → Finset Cell := ![(placed21 4 (1, 6) required_5), required_557_i2]
def childrenD_557_i1 : Fin 2 → Finset Cell := ![(placed21 4 (1, 6) envelope_5), envelope_557_i2]
theorem common_sub_557_i1 : commonEnvelope childrenD_557_i1 ⊆ insert (3, 6) required_557_i1 := by decide +kernel
theorem child_required_sub_557_i1 : ∀ j, childrenC_557_i1 j ⊆ insert (3, 6) required_557_i1 := by decide +kernel
theorem child_envelope_sub_557_i1 : ∀ j, childrenD_557_i1 j ⊆ envelope_557_i1 := by decide +kernel
theorem pivot_mem_557_i1 : (3, 6) ∈ envelope_557_i1 := by decide +kernel
theorem children_work_557_i1 : ∀ j, Template HasSnaky 10 (childrenC_557_i1 j) (childrenD_557_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 4 (1, 6)).mono (by decide +kernel)
  · exact row_works_557_i2.mono (by decide +kernel)
theorem row_works_557_i1 : Template HasSnaky 11 required_557_i1 envelope_557_i1 := by
  refine compose HasSnaky 10 childrenC_557_i1 childrenD_557_i1 children_work_557_i1 (3, 6)
    required_557_i1 envelope_557_i1 pivot_mem_557_i1 child_required_sub_557_i1 child_envelope_sub_557_i1 ?_
  intro b hb
  exact common_sub_557_i1 (mem_commonEnvelope childrenD_557_i1 b hb)
def required_557 : Finset Cell := ⟨(([(1, 3), (1, 6), (2, 3), (2, 6), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_557 : Finset Cell := ⟨(([(0, 2), (0, 5), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 8), (2, 0), (2, 1), (2, 2), (2, 3), (2, 6), (2, 8), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (8, 6), (8, 7), (8, 8), (8, 9), (9, 6), (9, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_557 : Fin 7 → Finset Cell := ![(placed21 0 (1, 3) required_110), (placed21 0 (1, 3) required_119), (placed21 0 (1, 2) required_430), (placed21 0 (1, 4) required_461), (placed21 0 (1, 1) required_555), required_557_i0, required_557_i1]
def childrenD_557 : Fin 7 → Finset Cell := ![(placed21 0 (1, 3) envelope_110), (placed21 0 (1, 3) envelope_119), (placed21 0 (1, 2) envelope_430), (placed21 0 (1, 4) envelope_461), (placed21 0 (1, 1) envelope_555), envelope_557_i0, envelope_557_i1]
theorem common_sub_557 : commonEnvelope childrenD_557 ⊆ insert (4, 6) required_557 := by decide +kernel
theorem child_required_sub_557 : ∀ j, childrenC_557 j ⊆ insert (4, 6) required_557 := by decide +kernel
theorem child_envelope_sub_557 : ∀ j, childrenD_557 j ⊆ envelope_557 := by decide +kernel
theorem pivot_mem_557 : (4, 6) ∈ envelope_557 := by decide +kernel
theorem children_work_557 : ∀ j, Template HasSnaky 13 (childrenC_557 j) (childrenD_557 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_110 0 (1, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_119 0 (1, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_430 0 (1, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_461 0 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_555 0 (1, 1)).mono (by decide +kernel)
  · exact row_works_557_i0.mono (by decide +kernel)
  · exact row_works_557_i1.mono (by decide +kernel)
theorem row_works_557 : Template HasSnaky 14 required_557 envelope_557 := by
  refine compose HasSnaky 13 childrenC_557 childrenD_557 children_work_557 (4, 6)
    required_557 envelope_557 pivot_mem_557 child_required_sub_557 child_envelope_sub_557 ?_
  intro b hb
  exact common_sub_557 (mem_commonEnvelope childrenD_557 b hb)
def required_582_i1 : Finset Cell := ⟨(([(2, 6), (2, 7), (4, 3), (4, 4), (4, 5), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_582_i1 : Finset Cell := ⟨(([(1, 6), (1, 7), (2, 6), (2, 7), (3, 6), (4, 3), (4, 4), (4, 5), (4, 6), (5, 5), (5, 6), (5, 7), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_582_i1 : Fin 2 → Finset Cell := ![(placed21 1 (4, 3) required_5), (placed21 3 (1, 7) required_160)]
def childrenD_582_i1 : Fin 2 → Finset Cell := ![(placed21 1 (4, 3) envelope_5), (placed21 3 (1, 7) envelope_160)]
theorem common_sub_582_i1 : commonEnvelope childrenD_582_i1 ⊆ insert (5, 6) required_582_i1 := by decide +kernel
theorem child_required_sub_582_i1 : ∀ j, childrenC_582_i1 j ⊆ insert (5, 6) required_582_i1 := by decide +kernel
theorem child_envelope_sub_582_i1 : ∀ j, childrenD_582_i1 j ⊆ envelope_582_i1 := by decide +kernel
theorem pivot_mem_582_i1 : (5, 6) ∈ envelope_582_i1 := by decide +kernel
theorem children_work_582_i1 : ∀ j, Template HasSnaky 3 (childrenC_582_i1 j) (childrenD_582_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 1 (4, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_160 3 (1, 7)).mono (by decide +kernel)
theorem row_works_582_i1 : Template HasSnaky 4 required_582_i1 envelope_582_i1 := by
  refine compose HasSnaky 3 childrenC_582_i1 childrenD_582_i1 children_work_582_i1 (5, 6)
    required_582_i1 envelope_582_i1 pivot_mem_582_i1 child_required_sub_582_i1 child_envelope_sub_582_i1 ?_
  intro b hb
  exact common_sub_582_i1 (mem_commonEnvelope childrenD_582_i1 b hb)
def required_582_i0 : Finset Cell := ⟨(([(2, 6), (2, 7), (4, 3), (4, 4), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_582_i0 : Finset Cell := ⟨(([(1, 6), (1, 7), (2, 3), (2, 6), (2, 7), (3, 2), (3, 3), (3, 6), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 4), (6, 5), (7, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_582_i0 : Fin 2 → Finset Cell := ![(placed21 1 (2, 2) required_133), required_582_i1]
def childrenD_582_i0 : Fin 2 → Finset Cell := ![(placed21 1 (2, 2) envelope_133), envelope_582_i1]
theorem common_sub_582_i0 : commonEnvelope childrenD_582_i0 ⊆ insert (4, 5) required_582_i0 := by decide +kernel
theorem child_required_sub_582_i0 : ∀ j, childrenC_582_i0 j ⊆ insert (4, 5) required_582_i0 := by decide +kernel
theorem child_envelope_sub_582_i0 : ∀ j, childrenD_582_i0 j ⊆ envelope_582_i0 := by decide +kernel
theorem pivot_mem_582_i0 : (4, 5) ∈ envelope_582_i0 := by decide +kernel
theorem children_work_582_i0 : ∀ j, Template HasSnaky 5 (childrenC_582_i0 j) (childrenD_582_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_133 1 (2, 2)).mono (by decide +kernel)
  · exact row_works_582_i1.mono (by decide +kernel)
theorem row_works_582_i0 : Template HasSnaky 6 required_582_i0 envelope_582_i0 := by
  refine compose HasSnaky 5 childrenC_582_i0 childrenD_582_i0 children_work_582_i0 (4, 5)
    required_582_i0 envelope_582_i0 pivot_mem_582_i0 child_required_sub_582_i0 child_envelope_sub_582_i0 ?_
  intro b hb
  exact common_sub_582_i0 (mem_commonEnvelope childrenD_582_i0 b hb)
def required_582_i2 : Finset Cell := ⟨(([(2, 6), (4, 3), (4, 4), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_582_i2 : Finset Cell := ⟨(([(0, 7), (1, 6), (1, 7), (2, 6), (2, 7), (3, 5), (3, 6), (3, 7), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 5), (5, 6), (5, 7), (6, 5), (6, 6), (6, 7), (7, 5), (7, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_582_i2 : Fin 4 → Finset Cell := ![(placed21 3 (0, 7) required_12), (placed21 3 (0, 7) required_14), (placed21 1 (1, 3) required_109), (placed21 1 (1, 3) required_424)]
def childrenD_582_i2 : Fin 4 → Finset Cell := ![(placed21 3 (0, 7) envelope_12), (placed21 3 (0, 7) envelope_14), (placed21 1 (1, 3) envelope_109), (placed21 1 (1, 3) envelope_424)]
theorem common_sub_582_i2 : commonEnvelope childrenD_582_i2 ⊆ insert (3, 6) required_582_i2 := by decide +kernel
theorem child_required_sub_582_i2 : ∀ j, childrenC_582_i2 j ⊆ insert (3, 6) required_582_i2 := by decide +kernel
theorem child_envelope_sub_582_i2 : ∀ j, childrenD_582_i2 j ⊆ envelope_582_i2 := by decide +kernel
theorem pivot_mem_582_i2 : (3, 6) ∈ envelope_582_i2 := by decide +kernel
theorem children_work_582_i2 : ∀ j, Template HasSnaky 4 (childrenC_582_i2 j) (childrenD_582_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_12 3 (0, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_14 3 (0, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_109 1 (1, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_424 1 (1, 3)).mono (by decide +kernel)
theorem row_works_582_i2 : Template HasSnaky 5 required_582_i2 envelope_582_i2 := by
  refine compose HasSnaky 4 childrenC_582_i2 childrenD_582_i2 children_work_582_i2 (3, 6)
    required_582_i2 envelope_582_i2 pivot_mem_582_i2 child_required_sub_582_i2 child_envelope_sub_582_i2 ?_
  intro b hb
  exact common_sub_582_i2 (mem_commonEnvelope childrenD_582_i2 b hb)
def required_582_i3 : Finset Cell := ⟨(([(1, 4), (2, 6), (2, 7), (4, 3), (4, 4), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_582_i3 : Finset Cell := ⟨(([(1, 3), (1, 4), (1, 6), (2, 3), (2, 4), (2, 6), (2, 7), (3, 2), (3, 3), (3, 7), (3, 8), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 2), (5, 3), (5, 4), (5, 6), (5, 7), (5, 8), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_582_i3 : Fin 2 → Finset Cell := ![(placed21 7 (6, 6) required_383), (placed21 5 (5, 3) required_432)]
def childrenD_582_i3 : Fin 2 → Finset Cell := ![(placed21 7 (6, 6) envelope_383), (placed21 5 (5, 3) envelope_432)]
theorem common_sub_582_i3 : commonEnvelope childrenD_582_i3 ⊆ insert (4, 5) required_582_i3 := by decide +kernel
theorem child_required_sub_582_i3 : ∀ j, childrenC_582_i3 j ⊆ insert (4, 5) required_582_i3 := by decide +kernel
theorem child_envelope_sub_582_i3 : ∀ j, childrenD_582_i3 j ⊆ envelope_582_i3 := by decide +kernel
theorem pivot_mem_582_i3 : (4, 5) ∈ envelope_582_i3 := by decide +kernel
theorem children_work_582_i3 : ∀ j, Template HasSnaky 5 (childrenC_582_i3 j) (childrenD_582_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_383 7 (6, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_432 5 (5, 3)).mono (by decide +kernel)
theorem row_works_582_i3 : Template HasSnaky 6 required_582_i3 envelope_582_i3 := by
  refine compose HasSnaky 5 childrenC_582_i3 childrenD_582_i3 children_work_582_i3 (4, 5)
    required_582_i3 envelope_582_i3 pivot_mem_582_i3 child_required_sub_582_i3 child_envelope_sub_582_i3 ?_
  intro b hb
  exact common_sub_582_i3 (mem_commonEnvelope childrenD_582_i3 b hb)
def required_582 : Finset Cell := ⟨(([(1, 3), (1, 4), (2, 6), (2, 7), (4, 3), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_582 : Finset Cell := ⟨(([(0, 7), (1, 3), (1, 4), (1, 6), (1, 7), (2, 3), (2, 4), (2, 6), (2, 7), (3, 2), (3, 3), (3, 5), (3, 6), (3, 7), (3, 8), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (9, 5), (9, 6), (9, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_582 : Fin 6 → Finset Cell := ![(placed21 3 (1, 7) required_184), (placed21 3 (1, 7) required_423), (placed21 0 (1, 0) required_572), required_582_i0, required_582_i2, required_582_i3]
def childrenD_582 : Fin 6 → Finset Cell := ![(placed21 3 (1, 7) envelope_184), (placed21 3 (1, 7) envelope_423), (placed21 0 (1, 0) envelope_572), envelope_582_i0, envelope_582_i2, envelope_582_i3]
theorem common_sub_582 : commonEnvelope childrenD_582 ⊆ insert (4, 6) required_582 := by decide +kernel
theorem child_required_sub_582 : ∀ j, childrenC_582 j ⊆ insert (4, 6) required_582 := by decide +kernel
theorem child_envelope_sub_582 : ∀ j, childrenD_582 j ⊆ envelope_582 := by decide +kernel
theorem pivot_mem_582 : (4, 6) ∈ envelope_582 := by decide +kernel
theorem children_work_582 : ∀ j, Template HasSnaky 13 (childrenC_582 j) (childrenD_582 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_184 3 (1, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_423 3 (1, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_572 0 (1, 0)).mono (by decide +kernel)
  · exact row_works_582_i0.mono (by decide +kernel)
  · exact row_works_582_i2.mono (by decide +kernel)
  · exact row_works_582_i3.mono (by decide +kernel)
theorem row_works_582 : Template HasSnaky 14 required_582 envelope_582 := by
  refine compose HasSnaky 13 childrenC_582 childrenD_582 children_work_582 (4, 6)
    required_582 envelope_582 pivot_mem_582 child_required_sub_582 child_envelope_sub_582 ?_
  intro b hb
  exact common_sub_582 (mem_commonEnvelope childrenD_582 b hb)
def height_553_i3 : ℕ := 2
def childrenH_553_i3 : Fin 2 → ℕ := ![height_3, height_5]
theorem height_exact_553_i3 : height_553_i3 = 1 + Finset.univ.sup childrenH_553_i3 := by decide +kernel
theorem required_origin_553_i3 : ∀ x ∈ required_553_i3,
    (∃ j, x ∈ childrenC_553_i3 j) ∨ ∀ j, x ∈ childrenD_553_i3 j := by decide +kernel
theorem required_exact_553_i3 : required_553_i3 =
    ((Finset.univ.biUnion childrenC_553_i3) ∪ commonEnvelope childrenD_553_i3).erase (5, 7) := by
  exact required_eq_combination childrenC_553_i3 childrenD_553_i3 (5, 7) required_553_i3
    (by decide +kernel) child_required_sub_553_i3 common_sub_553_i3 required_origin_553_i3
theorem envelope_origin_553_i3 : ∀ x ∈ envelope_553_i3,
    x = (5, 7) ∨ ∃ j, x ∈ childrenD_553_i3 j := by decide +kernel
theorem envelope_exact_553_i3 : envelope_553_i3 =
    insert (5, 7) (Finset.univ.biUnion childrenD_553_i3) := by
  exact envelope_eq_combination childrenD_553_i3 (5, 7) envelope_553_i3
    pivot_mem_553_i3 child_envelope_sub_553_i3 envelope_origin_553_i3
def checked_553_i3 : CheckedCard where
  required := required_553_i3
  envelope := envelope_553_i3
  height := height_553_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_553_i3
def height_553_i2 : ℕ := 5
def childrenH_553_i2 : Fin 4 → ℕ := ![height_10, height_52, height_52, height_553_i3]
theorem height_exact_553_i2 : height_553_i2 = 1 + Finset.univ.sup childrenH_553_i2 := by decide +kernel
theorem required_origin_553_i2 : ∀ x ∈ required_553_i2,
    (∃ j, x ∈ childrenC_553_i2 j) ∨ ∀ j, x ∈ childrenD_553_i2 j := by decide +kernel
theorem required_exact_553_i2 : required_553_i2 =
    ((Finset.univ.biUnion childrenC_553_i2) ∪ commonEnvelope childrenD_553_i2).erase (5, 5) := by
  exact required_eq_combination childrenC_553_i2 childrenD_553_i2 (5, 5) required_553_i2
    (by decide +kernel) child_required_sub_553_i2 common_sub_553_i2 required_origin_553_i2
theorem envelope_origin_553_i2 : ∀ x ∈ envelope_553_i2,
    x = (5, 5) ∨ ∃ j, x ∈ childrenD_553_i2 j := by decide +kernel
theorem envelope_exact_553_i2 : envelope_553_i2 =
    insert (5, 5) (Finset.univ.biUnion childrenD_553_i2) := by
  exact envelope_eq_combination childrenD_553_i2 (5, 5) envelope_553_i2
    pivot_mem_553_i2 child_envelope_sub_553_i2 envelope_origin_553_i2
def checked_553_i2 : CheckedCard where
  required := required_553_i2
  envelope := envelope_553_i2
  height := height_553_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_553_i2
def height_553_i1 : ℕ := 6
def childrenH_553_i1 : Fin 2 → ℕ := ![height_3, height_553_i2]
theorem height_exact_553_i1 : height_553_i1 = 1 + Finset.univ.sup childrenH_553_i1 := by decide +kernel
theorem required_origin_553_i1 : ∀ x ∈ required_553_i1,
    (∃ j, x ∈ childrenC_553_i1 j) ∨ ∀ j, x ∈ childrenD_553_i1 j := by decide +kernel
theorem required_exact_553_i1 : required_553_i1 =
    ((Finset.univ.biUnion childrenC_553_i1) ∪ commonEnvelope childrenD_553_i1).erase (5, 6) := by
  exact required_eq_combination childrenC_553_i1 childrenD_553_i1 (5, 6) required_553_i1
    (by decide +kernel) child_required_sub_553_i1 common_sub_553_i1 required_origin_553_i1
theorem envelope_origin_553_i1 : ∀ x ∈ envelope_553_i1,
    x = (5, 6) ∨ ∃ j, x ∈ childrenD_553_i1 j := by decide +kernel
theorem envelope_exact_553_i1 : envelope_553_i1 =
    insert (5, 6) (Finset.univ.biUnion childrenD_553_i1) := by
  exact envelope_eq_combination childrenD_553_i1 (5, 6) envelope_553_i1
    pivot_mem_553_i1 child_envelope_sub_553_i1 envelope_origin_553_i1
def checked_553_i1 : CheckedCard where
  required := required_553_i1
  envelope := envelope_553_i1
  height := height_553_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_553_i1
def height_553_i6 : ℕ := 6
def childrenH_553_i6 : Fin 2 → ℕ := ![height_6, height_145]
theorem height_exact_553_i6 : height_553_i6 = 1 + Finset.univ.sup childrenH_553_i6 := by decide +kernel
theorem required_origin_553_i6 : ∀ x ∈ required_553_i6,
    (∃ j, x ∈ childrenC_553_i6 j) ∨ ∀ j, x ∈ childrenD_553_i6 j := by decide +kernel
theorem required_exact_553_i6 : required_553_i6 =
    ((Finset.univ.biUnion childrenC_553_i6) ∪ commonEnvelope childrenD_553_i6).erase (6, 4) := by
  exact required_eq_combination childrenC_553_i6 childrenD_553_i6 (6, 4) required_553_i6
    (by decide +kernel) child_required_sub_553_i6 common_sub_553_i6 required_origin_553_i6
theorem envelope_origin_553_i6 : ∀ x ∈ envelope_553_i6,
    x = (6, 4) ∨ ∃ j, x ∈ childrenD_553_i6 j := by decide +kernel
theorem envelope_exact_553_i6 : envelope_553_i6 =
    insert (6, 4) (Finset.univ.biUnion childrenD_553_i6) := by
  exact envelope_eq_combination childrenD_553_i6 (6, 4) envelope_553_i6
    pivot_mem_553_i6 child_envelope_sub_553_i6 envelope_origin_553_i6
def checked_553_i6 : CheckedCard where
  required := required_553_i6
  envelope := envelope_553_i6
  height := height_553_i6
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_553_i6
def height_553_i5 : ℕ := 7
def childrenH_553_i5 : Fin 3 → ℕ := ![height_54, height_158, height_553_i6]
theorem height_exact_553_i5 : height_553_i5 = 1 + Finset.univ.sup childrenH_553_i5 := by decide +kernel
theorem required_origin_553_i5 : ∀ x ∈ required_553_i5,
    (∃ j, x ∈ childrenC_553_i5 j) ∨ ∀ j, x ∈ childrenD_553_i5 j := by decide +kernel
theorem required_exact_553_i5 : required_553_i5 =
    ((Finset.univ.biUnion childrenC_553_i5) ∪ commonEnvelope childrenD_553_i5).erase (7, 4) := by
  exact required_eq_combination childrenC_553_i5 childrenD_553_i5 (7, 4) required_553_i5
    (by decide +kernel) child_required_sub_553_i5 common_sub_553_i5 required_origin_553_i5
theorem envelope_origin_553_i5 : ∀ x ∈ envelope_553_i5,
    x = (7, 4) ∨ ∃ j, x ∈ childrenD_553_i5 j := by decide +kernel
theorem envelope_exact_553_i5 : envelope_553_i5 =
    insert (7, 4) (Finset.univ.biUnion childrenD_553_i5) := by
  exact envelope_eq_combination childrenD_553_i5 (7, 4) envelope_553_i5
    pivot_mem_553_i5 child_envelope_sub_553_i5 envelope_origin_553_i5
def checked_553_i5 : CheckedCard where
  required := required_553_i5
  envelope := envelope_553_i5
  height := height_553_i5
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_553_i5
def height_553_i4 : ℕ := 8
def childrenH_553_i4 : Fin 2 → ℕ := ![height_2, height_553_i5]
theorem height_exact_553_i4 : height_553_i4 = 1 + Finset.univ.sup childrenH_553_i4 := by decide +kernel
theorem required_origin_553_i4 : ∀ x ∈ required_553_i4,
    (∃ j, x ∈ childrenC_553_i4 j) ∨ ∀ j, x ∈ childrenD_553_i4 j := by decide +kernel
theorem required_exact_553_i4 : required_553_i4 =
    ((Finset.univ.biUnion childrenC_553_i4) ∪ commonEnvelope childrenD_553_i4).erase (6, 7) := by
  exact required_eq_combination childrenC_553_i4 childrenD_553_i4 (6, 7) required_553_i4
    (by decide +kernel) child_required_sub_553_i4 common_sub_553_i4 required_origin_553_i4
theorem envelope_origin_553_i4 : ∀ x ∈ envelope_553_i4,
    x = (6, 7) ∨ ∃ j, x ∈ childrenD_553_i4 j := by decide +kernel
theorem envelope_exact_553_i4 : envelope_553_i4 =
    insert (6, 7) (Finset.univ.biUnion childrenD_553_i4) := by
  exact envelope_eq_combination childrenD_553_i4 (6, 7) envelope_553_i4
    pivot_mem_553_i4 child_envelope_sub_553_i4 envelope_origin_553_i4
def checked_553_i4 : CheckedCard where
  required := required_553_i4
  envelope := envelope_553_i4
  height := height_553_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_553_i4
def height_553_i8 : ℕ := 4
def childrenH_553_i8 : Fin 2 → ℕ := ![height_54, height_247]
theorem height_exact_553_i8 : height_553_i8 = 1 + Finset.univ.sup childrenH_553_i8 := by decide +kernel
theorem required_origin_553_i8 : ∀ x ∈ required_553_i8,
    (∃ j, x ∈ childrenC_553_i8 j) ∨ ∀ j, x ∈ childrenD_553_i8 j := by decide +kernel
theorem required_exact_553_i8 : required_553_i8 =
    ((Finset.univ.biUnion childrenC_553_i8) ∪ commonEnvelope childrenD_553_i8).erase (4, 3) := by
  exact required_eq_combination childrenC_553_i8 childrenD_553_i8 (4, 3) required_553_i8
    (by decide +kernel) child_required_sub_553_i8 common_sub_553_i8 required_origin_553_i8
theorem envelope_origin_553_i8 : ∀ x ∈ envelope_553_i8,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_553_i8 j := by decide +kernel
theorem envelope_exact_553_i8 : envelope_553_i8 =
    insert (4, 3) (Finset.univ.biUnion childrenD_553_i8) := by
  exact envelope_eq_combination childrenD_553_i8 (4, 3) envelope_553_i8
    pivot_mem_553_i8 child_envelope_sub_553_i8 envelope_origin_553_i8
def checked_553_i8 : CheckedCard where
  required := required_553_i8
  envelope := envelope_553_i8
  height := height_553_i8
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_553_i8
def height_553_i7 : ℕ := 5
def childrenH_553_i7 : Fin 2 → ℕ := ![height_3, height_553_i8]
theorem height_exact_553_i7 : height_553_i7 = 1 + Finset.univ.sup childrenH_553_i7 := by decide +kernel
theorem required_origin_553_i7 : ∀ x ∈ required_553_i7,
    (∃ j, x ∈ childrenC_553_i7 j) ∨ ∀ j, x ∈ childrenD_553_i7 j := by decide +kernel
theorem required_exact_553_i7 : required_553_i7 =
    ((Finset.univ.biUnion childrenC_553_i7) ∪ commonEnvelope childrenD_553_i7).erase (5, 6) := by
  exact required_eq_combination childrenC_553_i7 childrenD_553_i7 (5, 6) required_553_i7
    (by decide +kernel) child_required_sub_553_i7 common_sub_553_i7 required_origin_553_i7
theorem envelope_origin_553_i7 : ∀ x ∈ envelope_553_i7,
    x = (5, 6) ∨ ∃ j, x ∈ childrenD_553_i7 j := by decide +kernel
theorem envelope_exact_553_i7 : envelope_553_i7 =
    insert (5, 6) (Finset.univ.biUnion childrenD_553_i7) := by
  exact envelope_eq_combination childrenD_553_i7 (5, 6) envelope_553_i7
    pivot_mem_553_i7 child_envelope_sub_553_i7 envelope_origin_553_i7
def checked_553_i7 : CheckedCard where
  required := required_553_i7
  envelope := envelope_553_i7
  height := height_553_i7
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_553_i7
def height_553_i0 : ℕ := 9
def childrenH_553_i0 : Fin 4 → ℕ := ![height_433, height_553_i1, height_553_i4, height_553_i7]
theorem height_exact_553_i0 : height_553_i0 = 1 + Finset.univ.sup childrenH_553_i0 := by decide +kernel
theorem required_origin_553_i0 : ∀ x ∈ required_553_i0,
    (∃ j, x ∈ childrenC_553_i0 j) ∨ ∀ j, x ∈ childrenD_553_i0 j := by decide +kernel
theorem required_exact_553_i0 : required_553_i0 =
    ((Finset.univ.biUnion childrenC_553_i0) ∪ commonEnvelope childrenD_553_i0).erase (5, 4) := by
  exact required_eq_combination childrenC_553_i0 childrenD_553_i0 (5, 4) required_553_i0
    (by decide +kernel) child_required_sub_553_i0 common_sub_553_i0 required_origin_553_i0
theorem envelope_origin_553_i0 : ∀ x ∈ envelope_553_i0,
    x = (5, 4) ∨ ∃ j, x ∈ childrenD_553_i0 j := by decide +kernel
theorem envelope_exact_553_i0 : envelope_553_i0 =
    insert (5, 4) (Finset.univ.biUnion childrenD_553_i0) := by
  exact envelope_eq_combination childrenD_553_i0 (5, 4) envelope_553_i0
    pivot_mem_553_i0 child_envelope_sub_553_i0 envelope_origin_553_i0
def checked_553_i0 : CheckedCard where
  required := required_553_i0
  envelope := envelope_553_i0
  height := height_553_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_553_i0
def height_553 : ℕ := 14
def childrenH_553 : Fin 5 → ℕ := ![height_107, height_163, height_538, height_552, height_553_i0]
theorem height_exact_553 : height_553 = 1 + Finset.univ.sup childrenH_553 := by decide +kernel
theorem required_origin_553 : ∀ x ∈ required_553,
    (∃ j, x ∈ childrenC_553 j) ∨ ∀ j, x ∈ childrenD_553 j := by decide +kernel
theorem required_exact_553 : required_553 =
    ((Finset.univ.biUnion childrenC_553) ∪ commonEnvelope childrenD_553).erase (7, 6) := by
  exact required_eq_combination childrenC_553 childrenD_553 (7, 6) required_553
    (by decide +kernel) child_required_sub_553 common_sub_553 required_origin_553
theorem envelope_origin_553 : ∀ x ∈ envelope_553,
    x = (7, 6) ∨ ∃ j, x ∈ childrenD_553 j := by decide +kernel
theorem envelope_exact_553 : envelope_553 =
    insert (7, 6) (Finset.univ.biUnion childrenD_553) := by
  exact envelope_eq_combination childrenD_553 (7, 6) envelope_553
    pivot_mem_553 child_envelope_sub_553 envelope_origin_553
def checked_553 : CheckedCard where
  required := required_553
  envelope := envelope_553
  height := height_553
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_553
def height_557_i0 : ℕ := 5
def childrenH_557_i0 : Fin 3 → ℕ := ![height_13, height_28, height_58]
theorem height_exact_557_i0 : height_557_i0 = 1 + Finset.univ.sup childrenH_557_i0 := by decide +kernel
theorem required_origin_557_i0 : ∀ x ∈ required_557_i0,
    (∃ j, x ∈ childrenC_557_i0 j) ∨ ∀ j, x ∈ childrenD_557_i0 j := by decide +kernel
theorem required_exact_557_i0 : required_557_i0 =
    ((Finset.univ.biUnion childrenC_557_i0) ∪ commonEnvelope childrenD_557_i0).erase (4, 7) := by
  exact required_eq_combination childrenC_557_i0 childrenD_557_i0 (4, 7) required_557_i0
    (by decide +kernel) child_required_sub_557_i0 common_sub_557_i0 required_origin_557_i0
theorem envelope_origin_557_i0 : ∀ x ∈ envelope_557_i0,
    x = (4, 7) ∨ ∃ j, x ∈ childrenD_557_i0 j := by decide +kernel
theorem envelope_exact_557_i0 : envelope_557_i0 =
    insert (4, 7) (Finset.univ.biUnion childrenD_557_i0) := by
  exact envelope_eq_combination childrenD_557_i0 (4, 7) envelope_557_i0
    pivot_mem_557_i0 child_envelope_sub_557_i0 envelope_origin_557_i0
def checked_557_i0 : CheckedCard where
  required := required_557_i0
  envelope := envelope_557_i0
  height := height_557_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_557_i0
def height_557_i4 : ℕ := 2
def childrenH_557_i4 : Fin 2 → ℕ := ![height_2, height_5]
theorem height_exact_557_i4 : height_557_i4 = 1 + Finset.univ.sup childrenH_557_i4 := by decide +kernel
theorem required_origin_557_i4 : ∀ x ∈ required_557_i4,
    (∃ j, x ∈ childrenC_557_i4 j) ∨ ∀ j, x ∈ childrenD_557_i4 j := by decide +kernel
theorem required_exact_557_i4 : required_557_i4 =
    ((Finset.univ.biUnion childrenC_557_i4) ∪ commonEnvelope childrenD_557_i4).erase (1, 5) := by
  exact required_eq_combination childrenC_557_i4 childrenD_557_i4 (1, 5) required_557_i4
    (by decide +kernel) child_required_sub_557_i4 common_sub_557_i4 required_origin_557_i4
theorem envelope_origin_557_i4 : ∀ x ∈ envelope_557_i4,
    x = (1, 5) ∨ ∃ j, x ∈ childrenD_557_i4 j := by decide +kernel
theorem envelope_exact_557_i4 : envelope_557_i4 =
    insert (1, 5) (Finset.univ.biUnion childrenD_557_i4) := by
  exact envelope_eq_combination childrenD_557_i4 (1, 5) envelope_557_i4
    pivot_mem_557_i4 child_envelope_sub_557_i4 envelope_origin_557_i4
def checked_557_i4 : CheckedCard where
  required := required_557_i4
  envelope := envelope_557_i4
  height := height_557_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_557_i4
def height_557_i6 : ℕ := 7
def childrenH_557_i6 : Fin 2 → ℕ := ![height_1, height_392]
theorem height_exact_557_i6 : height_557_i6 = 1 + Finset.univ.sup childrenH_557_i6 := by decide +kernel
theorem required_origin_557_i6 : ∀ x ∈ required_557_i6,
    (∃ j, x ∈ childrenC_557_i6 j) ∨ ∀ j, x ∈ childrenD_557_i6 j := by decide +kernel
theorem required_exact_557_i6 : required_557_i6 =
    ((Finset.univ.biUnion childrenC_557_i6) ∪ commonEnvelope childrenD_557_i6).erase (3, 4) := by
  exact required_eq_combination childrenC_557_i6 childrenD_557_i6 (3, 4) required_557_i6
    (by decide +kernel) child_required_sub_557_i6 common_sub_557_i6 required_origin_557_i6
theorem envelope_origin_557_i6 : ∀ x ∈ envelope_557_i6,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_557_i6 j := by decide +kernel
theorem envelope_exact_557_i6 : envelope_557_i6 =
    insert (3, 4) (Finset.univ.biUnion childrenD_557_i6) := by
  exact envelope_eq_combination childrenD_557_i6 (3, 4) envelope_557_i6
    pivot_mem_557_i6 child_envelope_sub_557_i6 envelope_origin_557_i6
def checked_557_i6 : CheckedCard where
  required := required_557_i6
  envelope := envelope_557_i6
  height := height_557_i6
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_557_i6
def height_557_i5 : ℕ := 8
def childrenH_557_i5 : Fin 3 → ℕ := ![height_11, height_41, height_557_i6]
theorem height_exact_557_i5 : height_557_i5 = 1 + Finset.univ.sup childrenH_557_i5 := by decide +kernel
theorem required_origin_557_i5 : ∀ x ∈ required_557_i5,
    (∃ j, x ∈ childrenC_557_i5 j) ∨ ∀ j, x ∈ childrenD_557_i5 j := by decide +kernel
theorem required_exact_557_i5 : required_557_i5 =
    ((Finset.univ.biUnion childrenC_557_i5) ∪ commonEnvelope childrenD_557_i5).erase (3, 3) := by
  exact required_eq_combination childrenC_557_i5 childrenD_557_i5 (3, 3) required_557_i5
    (by decide +kernel) child_required_sub_557_i5 common_sub_557_i5 required_origin_557_i5
theorem envelope_origin_557_i5 : ∀ x ∈ envelope_557_i5,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_557_i5 j := by decide +kernel
theorem envelope_exact_557_i5 : envelope_557_i5 =
    insert (3, 3) (Finset.univ.biUnion childrenD_557_i5) := by
  exact envelope_eq_combination childrenD_557_i5 (3, 3) envelope_557_i5
    pivot_mem_557_i5 child_envelope_sub_557_i5 envelope_origin_557_i5
def checked_557_i5 : CheckedCard where
  required := required_557_i5
  envelope := envelope_557_i5
  height := height_557_i5
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_557_i5
def height_557_i3 : ℕ := 9
def childrenH_557_i3 : Fin 2 → ℕ := ![height_557_i4, height_557_i5]
theorem height_exact_557_i3 : height_557_i3 = 1 + Finset.univ.sup childrenH_557_i3 := by decide +kernel
theorem required_origin_557_i3 : ∀ x ∈ required_557_i3,
    (∃ j, x ∈ childrenC_557_i3 j) ∨ ∀ j, x ∈ childrenD_557_i3 j := by decide +kernel
theorem required_exact_557_i3 : required_557_i3 =
    ((Finset.univ.biUnion childrenC_557_i3) ∪ commonEnvelope childrenD_557_i3).erase (2, 2) := by
  exact required_eq_combination childrenC_557_i3 childrenD_557_i3 (2, 2) required_557_i3
    (by decide +kernel) child_required_sub_557_i3 common_sub_557_i3 required_origin_557_i3
theorem envelope_origin_557_i3 : ∀ x ∈ envelope_557_i3,
    x = (2, 2) ∨ ∃ j, x ∈ childrenD_557_i3 j := by decide +kernel
theorem envelope_exact_557_i3 : envelope_557_i3 =
    insert (2, 2) (Finset.univ.biUnion childrenD_557_i3) := by
  exact envelope_eq_combination childrenD_557_i3 (2, 2) envelope_557_i3
    pivot_mem_557_i3 child_envelope_sub_557_i3 envelope_origin_557_i3
def checked_557_i3 : CheckedCard where
  required := required_557_i3
  envelope := envelope_557_i3
  height := height_557_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_557_i3
def height_557_i2 : ℕ := 10
def childrenH_557_i2 : Fin 3 → ℕ := ![height_42, height_152, height_557_i3]
theorem height_exact_557_i2 : height_557_i2 = 1 + Finset.univ.sup childrenH_557_i2 := by decide +kernel
theorem required_origin_557_i2 : ∀ x ∈ required_557_i2,
    (∃ j, x ∈ childrenC_557_i2 j) ∨ ∀ j, x ∈ childrenD_557_i2 j := by decide +kernel
theorem required_exact_557_i2 : required_557_i2 =
    ((Finset.univ.biUnion childrenC_557_i2) ∪ commonEnvelope childrenD_557_i2).erase (4, 3) := by
  exact required_eq_combination childrenC_557_i2 childrenD_557_i2 (4, 3) required_557_i2
    (by decide +kernel) child_required_sub_557_i2 common_sub_557_i2 required_origin_557_i2
theorem envelope_origin_557_i2 : ∀ x ∈ envelope_557_i2,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_557_i2 j := by decide +kernel
theorem envelope_exact_557_i2 : envelope_557_i2 =
    insert (4, 3) (Finset.univ.biUnion childrenD_557_i2) := by
  exact envelope_eq_combination childrenD_557_i2 (4, 3) envelope_557_i2
    pivot_mem_557_i2 child_envelope_sub_557_i2 envelope_origin_557_i2
def checked_557_i2 : CheckedCard where
  required := required_557_i2
  envelope := envelope_557_i2
  height := height_557_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_557_i2
def height_557_i1 : ℕ := 11
def childrenH_557_i1 : Fin 2 → ℕ := ![height_5, height_557_i2]
theorem height_exact_557_i1 : height_557_i1 = 1 + Finset.univ.sup childrenH_557_i1 := by decide +kernel
theorem required_origin_557_i1 : ∀ x ∈ required_557_i1,
    (∃ j, x ∈ childrenC_557_i1 j) ∨ ∀ j, x ∈ childrenD_557_i1 j := by decide +kernel
theorem required_exact_557_i1 : required_557_i1 =
    ((Finset.univ.biUnion childrenC_557_i1) ∪ commonEnvelope childrenD_557_i1).erase (3, 6) := by
  exact required_eq_combination childrenC_557_i1 childrenD_557_i1 (3, 6) required_557_i1
    (by decide +kernel) child_required_sub_557_i1 common_sub_557_i1 required_origin_557_i1
theorem envelope_origin_557_i1 : ∀ x ∈ envelope_557_i1,
    x = (3, 6) ∨ ∃ j, x ∈ childrenD_557_i1 j := by decide +kernel
theorem envelope_exact_557_i1 : envelope_557_i1 =
    insert (3, 6) (Finset.univ.biUnion childrenD_557_i1) := by
  exact envelope_eq_combination childrenD_557_i1 (3, 6) envelope_557_i1
    pivot_mem_557_i1 child_envelope_sub_557_i1 envelope_origin_557_i1
def checked_557_i1 : CheckedCard where
  required := required_557_i1
  envelope := envelope_557_i1
  height := height_557_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_557_i1
def height_557 : ℕ := 14
def childrenH_557 : Fin 7 → ℕ := ![height_110, height_119, height_430, height_461, height_555, height_557_i0, height_557_i1]
theorem height_exact_557 : height_557 = 1 + Finset.univ.sup childrenH_557 := by decide +kernel
theorem required_origin_557 : ∀ x ∈ required_557,
    (∃ j, x ∈ childrenC_557 j) ∨ ∀ j, x ∈ childrenD_557 j := by decide +kernel
theorem required_exact_557 : required_557 =
    ((Finset.univ.biUnion childrenC_557) ∪ commonEnvelope childrenD_557).erase (4, 6) := by
  exact required_eq_combination childrenC_557 childrenD_557 (4, 6) required_557
    (by decide +kernel) child_required_sub_557 common_sub_557 required_origin_557
theorem envelope_origin_557 : ∀ x ∈ envelope_557,
    x = (4, 6) ∨ ∃ j, x ∈ childrenD_557 j := by decide +kernel
theorem envelope_exact_557 : envelope_557 =
    insert (4, 6) (Finset.univ.biUnion childrenD_557) := by
  exact envelope_eq_combination childrenD_557 (4, 6) envelope_557
    pivot_mem_557 child_envelope_sub_557 envelope_origin_557
def checked_557 : CheckedCard where
  required := required_557
  envelope := envelope_557
  height := height_557
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_557
def height_582_i1 : ℕ := 4
def childrenH_582_i1 : Fin 2 → ℕ := ![height_5, height_160]
theorem height_exact_582_i1 : height_582_i1 = 1 + Finset.univ.sup childrenH_582_i1 := by decide +kernel
theorem required_origin_582_i1 : ∀ x ∈ required_582_i1,
    (∃ j, x ∈ childrenC_582_i1 j) ∨ ∀ j, x ∈ childrenD_582_i1 j := by decide +kernel
theorem required_exact_582_i1 : required_582_i1 =
    ((Finset.univ.biUnion childrenC_582_i1) ∪ commonEnvelope childrenD_582_i1).erase (5, 6) := by
  exact required_eq_combination childrenC_582_i1 childrenD_582_i1 (5, 6) required_582_i1
    (by decide +kernel) child_required_sub_582_i1 common_sub_582_i1 required_origin_582_i1
theorem envelope_origin_582_i1 : ∀ x ∈ envelope_582_i1,
    x = (5, 6) ∨ ∃ j, x ∈ childrenD_582_i1 j := by decide +kernel
theorem envelope_exact_582_i1 : envelope_582_i1 =
    insert (5, 6) (Finset.univ.biUnion childrenD_582_i1) := by
  exact envelope_eq_combination childrenD_582_i1 (5, 6) envelope_582_i1
    pivot_mem_582_i1 child_envelope_sub_582_i1 envelope_origin_582_i1
def checked_582_i1 : CheckedCard where
  required := required_582_i1
  envelope := envelope_582_i1
  height := height_582_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_582_i1
def height_582_i0 : ℕ := 6
def childrenH_582_i0 : Fin 2 → ℕ := ![height_133, height_582_i1]
theorem height_exact_582_i0 : height_582_i0 = 1 + Finset.univ.sup childrenH_582_i0 := by decide +kernel
theorem required_origin_582_i0 : ∀ x ∈ required_582_i0,
    (∃ j, x ∈ childrenC_582_i0 j) ∨ ∀ j, x ∈ childrenD_582_i0 j := by decide +kernel
theorem required_exact_582_i0 : required_582_i0 =
    ((Finset.univ.biUnion childrenC_582_i0) ∪ commonEnvelope childrenD_582_i0).erase (4, 5) := by
  exact required_eq_combination childrenC_582_i0 childrenD_582_i0 (4, 5) required_582_i0
    (by decide +kernel) child_required_sub_582_i0 common_sub_582_i0 required_origin_582_i0
theorem envelope_origin_582_i0 : ∀ x ∈ envelope_582_i0,
    x = (4, 5) ∨ ∃ j, x ∈ childrenD_582_i0 j := by decide +kernel
theorem envelope_exact_582_i0 : envelope_582_i0 =
    insert (4, 5) (Finset.univ.biUnion childrenD_582_i0) := by
  exact envelope_eq_combination childrenD_582_i0 (4, 5) envelope_582_i0
    pivot_mem_582_i0 child_envelope_sub_582_i0 envelope_origin_582_i0
def checked_582_i0 : CheckedCard where
  required := required_582_i0
  envelope := envelope_582_i0
  height := height_582_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_582_i0
def height_582_i2 : ℕ := 5
def childrenH_582_i2 : Fin 4 → ℕ := ![height_12, height_14, height_109, height_424]
theorem height_exact_582_i2 : height_582_i2 = 1 + Finset.univ.sup childrenH_582_i2 := by decide +kernel
theorem required_origin_582_i2 : ∀ x ∈ required_582_i2,
    (∃ j, x ∈ childrenC_582_i2 j) ∨ ∀ j, x ∈ childrenD_582_i2 j := by decide +kernel
theorem required_exact_582_i2 : required_582_i2 =
    ((Finset.univ.biUnion childrenC_582_i2) ∪ commonEnvelope childrenD_582_i2).erase (3, 6) := by
  exact required_eq_combination childrenC_582_i2 childrenD_582_i2 (3, 6) required_582_i2
    (by decide +kernel) child_required_sub_582_i2 common_sub_582_i2 required_origin_582_i2
theorem envelope_origin_582_i2 : ∀ x ∈ envelope_582_i2,
    x = (3, 6) ∨ ∃ j, x ∈ childrenD_582_i2 j := by decide +kernel
theorem envelope_exact_582_i2 : envelope_582_i2 =
    insert (3, 6) (Finset.univ.biUnion childrenD_582_i2) := by
  exact envelope_eq_combination childrenD_582_i2 (3, 6) envelope_582_i2
    pivot_mem_582_i2 child_envelope_sub_582_i2 envelope_origin_582_i2
def checked_582_i2 : CheckedCard where
  required := required_582_i2
  envelope := envelope_582_i2
  height := height_582_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_582_i2
def height_582_i3 : ℕ := 6
def childrenH_582_i3 : Fin 2 → ℕ := ![height_383, height_432]
theorem height_exact_582_i3 : height_582_i3 = 1 + Finset.univ.sup childrenH_582_i3 := by decide +kernel
theorem required_origin_582_i3 : ∀ x ∈ required_582_i3,
    (∃ j, x ∈ childrenC_582_i3 j) ∨ ∀ j, x ∈ childrenD_582_i3 j := by decide +kernel
theorem required_exact_582_i3 : required_582_i3 =
    ((Finset.univ.biUnion childrenC_582_i3) ∪ commonEnvelope childrenD_582_i3).erase (4, 5) := by
  exact required_eq_combination childrenC_582_i3 childrenD_582_i3 (4, 5) required_582_i3
    (by decide +kernel) child_required_sub_582_i3 common_sub_582_i3 required_origin_582_i3
theorem envelope_origin_582_i3 : ∀ x ∈ envelope_582_i3,
    x = (4, 5) ∨ ∃ j, x ∈ childrenD_582_i3 j := by decide +kernel
theorem envelope_exact_582_i3 : envelope_582_i3 =
    insert (4, 5) (Finset.univ.biUnion childrenD_582_i3) := by
  exact envelope_eq_combination childrenD_582_i3 (4, 5) envelope_582_i3
    pivot_mem_582_i3 child_envelope_sub_582_i3 envelope_origin_582_i3
def checked_582_i3 : CheckedCard where
  required := required_582_i3
  envelope := envelope_582_i3
  height := height_582_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_582_i3
def height_582 : ℕ := 14
def childrenH_582 : Fin 6 → ℕ := ![height_184, height_423, height_572, height_582_i0, height_582_i2, height_582_i3]
theorem height_exact_582 : height_582 = 1 + Finset.univ.sup childrenH_582 := by decide +kernel
theorem required_origin_582 : ∀ x ∈ required_582,
    (∃ j, x ∈ childrenC_582 j) ∨ ∀ j, x ∈ childrenD_582 j := by decide +kernel
theorem required_exact_582 : required_582 =
    ((Finset.univ.biUnion childrenC_582) ∪ commonEnvelope childrenD_582).erase (4, 6) := by
  exact required_eq_combination childrenC_582 childrenD_582 (4, 6) required_582
    (by decide +kernel) child_required_sub_582 common_sub_582 required_origin_582
theorem envelope_origin_582 : ∀ x ∈ envelope_582,
    x = (4, 6) ∨ ∃ j, x ∈ childrenD_582 j := by decide +kernel
theorem envelope_exact_582 : envelope_582 =
    insert (4, 6) (Finset.univ.biUnion childrenD_582) := by
  exact envelope_eq_combination childrenD_582 (4, 6) envelope_582
    pivot_mem_582 child_envelope_sub_582 envelope_origin_582
def checked_582 : CheckedCard where
  required := required_582
  envelope := envelope_582
  height := height_582
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_582
end SnakyPrototype.Certificate21

end OAI
