import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height10Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height11Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height11Part06
import OAI.GameTheory.SnakyTwentyOne.Cards.Height12Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height12Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height12Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height12Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height13Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height13Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height13Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height13Part06
import OAI.GameTheory.SnakyTwentyOne.Cards.Height15Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height15Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height16Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height17Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height18Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height18Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height19Part01
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_708_i2 : Finset Cell := ⟨(([(6, 8), (7, 7), (7, 8), (8, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_708_i2 : Finset Cell := ⟨(([(2, 7), (3, 7), (3, 8), (3, 9), (4, 7), (4, 8), (4, 9), (5, 8), (5, 9), (6, 7), (6, 8), (6, 9), (7, 7), (7, 8), (7, 9), (8, 8), (8, 9), (9, 7), (9, 8), (9, 9), (10, 7), (10, 8), (11, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_708_i2 : Fin 3 → Finset Cell := ![(placed21 5 (9, 8) required_7), (placed21 1 (4, 7) required_234), (placed21 5 (9, 7) required_241)]
def childrenD_708_i2 : Fin 3 → Finset Cell := ![(placed21 5 (9, 8) envelope_7), (placed21 1 (4, 7) envelope_234), (placed21 5 (9, 7) envelope_241)]
theorem common_sub_708_i2 : commonEnvelope childrenD_708_i2 ⊆ insert (5, 8) required_708_i2 := by decide +kernel
theorem child_required_sub_708_i2 : ∀ j, childrenC_708_i2 j ⊆ insert (5, 8) required_708_i2 := by decide +kernel
theorem child_envelope_sub_708_i2 : ∀ j, childrenD_708_i2 j ⊆ envelope_708_i2 := by decide +kernel
theorem pivot_mem_708_i2 : (5, 8) ∈ envelope_708_i2 := by decide +kernel
theorem children_work_708_i2 : ∀ j, Template HasSnaky 5 (childrenC_708_i2 j) (childrenD_708_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 5 (9, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_234 1 (4, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_241 5 (9, 7)).mono (by decide +kernel)
theorem row_works_708_i2 : Template HasSnaky 6 required_708_i2 envelope_708_i2 := by
  refine compose HasSnaky 5 childrenC_708_i2 childrenD_708_i2 children_work_708_i2 (5, 8)
    required_708_i2 envelope_708_i2 pivot_mem_708_i2 child_required_sub_708_i2 child_envelope_sub_708_i2 ?_
  intro b hb
  exact common_sub_708_i2 (mem_commonEnvelope childrenD_708_i2 b hb)
def required_708_i4 : Finset Cell := ⟨(([(6, 8), (7, 6), (7, 7), (7, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_708_i4 : Finset Cell := ⟨(([(4, 8), (5, 8), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, 9), (8, 10), (8, 11), (9, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_708_i4 : Fin 3 → Finset Cell := ![(placed21 2 (7, 5) required_7), (placed21 0 (6, 5) required_9), (placed21 5 (9, 6) required_92)]
def childrenD_708_i4 : Fin 3 → Finset Cell := ![(placed21 2 (7, 5) envelope_7), (placed21 0 (6, 5) envelope_9), (placed21 5 (9, 6) envelope_92)]
theorem common_sub_708_i4 : commonEnvelope childrenD_708_i4 ⊆ insert (7, 9) required_708_i4 := by decide +kernel
theorem child_required_sub_708_i4 : ∀ j, childrenC_708_i4 j ⊆ insert (7, 9) required_708_i4 := by decide +kernel
theorem child_envelope_sub_708_i4 : ∀ j, childrenD_708_i4 j ⊆ envelope_708_i4 := by decide +kernel
theorem pivot_mem_708_i4 : (7, 9) ∈ envelope_708_i4 := by decide +kernel
theorem children_work_708_i4 : ∀ j, Template HasSnaky 4 (childrenC_708_i4 j) (childrenD_708_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 2 (7, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_9 0 (6, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_92 5 (9, 6)).mono (by decide +kernel)
theorem row_works_708_i4 : Template HasSnaky 5 required_708_i4 envelope_708_i4 := by
  refine compose HasSnaky 4 childrenC_708_i4 childrenD_708_i4 children_work_708_i4 (7, 9)
    required_708_i4 envelope_708_i4 pivot_mem_708_i4 child_required_sub_708_i4 child_envelope_sub_708_i4 ?_
  intro b hb
  exact common_sub_708_i4 (mem_commonEnvelope childrenD_708_i4 b hb)
def required_708_i3 : Finset Cell := ⟨(([(6, 8), (7, 7), (7, 8), (8, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_708_i3 : Finset Cell := ⟨(([(4, 8), (5, 8), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, 8), (8, 9), (8, 10), (8, 11), (9, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_708_i3 : Fin 3 → Finset Cell := ![(placed21 2 (7, 5) required_44), (placed21 0 (7, 5) required_52), required_708_i4]
def childrenD_708_i3 : Fin 3 → Finset Cell := ![(placed21 2 (7, 5) envelope_44), (placed21 0 (7, 5) envelope_52), envelope_708_i4]
theorem common_sub_708_i3 : commonEnvelope childrenD_708_i3 ⊆ insert (7, 6) required_708_i3 := by decide +kernel
theorem child_required_sub_708_i3 : ∀ j, childrenC_708_i3 j ⊆ insert (7, 6) required_708_i3 := by decide +kernel
theorem child_envelope_sub_708_i3 : ∀ j, childrenD_708_i3 j ⊆ envelope_708_i3 := by decide +kernel
theorem pivot_mem_708_i3 : (7, 6) ∈ envelope_708_i3 := by decide +kernel
theorem children_work_708_i3 : ∀ j, Template HasSnaky 5 (childrenC_708_i3 j) (childrenD_708_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_44 2 (7, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_52 0 (7, 5)).mono (by decide +kernel)
  · exact row_works_708_i4.mono (by decide +kernel)
theorem row_works_708_i3 : Template HasSnaky 6 required_708_i3 envelope_708_i3 := by
  refine compose HasSnaky 5 childrenC_708_i3 childrenD_708_i3 children_work_708_i3 (7, 6)
    required_708_i3 envelope_708_i3 pivot_mem_708_i3 child_required_sub_708_i3 child_envelope_sub_708_i3 ?_
  intro b hb
  exact common_sub_708_i3 (mem_commonEnvelope childrenD_708_i3 b hb)
def required_708_i1 : Finset Cell := ⟨(([(6, 8), (7, 8), (8, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_708_i1 : Finset Cell := ⟨(([(2, 7), (3, 7), (3, 8), (3, 9), (4, 7), (4, 8), (4, 9), (5, 8), (5, 9), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, 8), (8, 9), (8, 10), (8, 11), (9, 7), (9, 8), (9, 9), (10, 7), (10, 8), (11, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_708_i1 : Fin 6 → Finset Cell := ![(placed21 2 (9, 5) required_57), (placed21 2 (9, 5) required_88), (placed21 2 (9, 5) required_111), (placed21 0 (5, 5) required_213), required_708_i2, required_708_i3]
def childrenD_708_i1 : Fin 6 → Finset Cell := ![(placed21 2 (9, 5) envelope_57), (placed21 2 (9, 5) envelope_88), (placed21 2 (9, 5) envelope_111), (placed21 0 (5, 5) envelope_213), envelope_708_i2, envelope_708_i3]
theorem common_sub_708_i1 : commonEnvelope childrenD_708_i1 ⊆ insert (7, 7) required_708_i1 := by decide +kernel
theorem child_required_sub_708_i1 : ∀ j, childrenC_708_i1 j ⊆ insert (7, 7) required_708_i1 := by decide +kernel
theorem child_envelope_sub_708_i1 : ∀ j, childrenD_708_i1 j ⊆ envelope_708_i1 := by decide +kernel
theorem pivot_mem_708_i1 : (7, 7) ∈ envelope_708_i1 := by decide +kernel
theorem children_work_708_i1 : ∀ j, Template HasSnaky 6 (childrenC_708_i1 j) (childrenD_708_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_57 2 (9, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_88 2 (9, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_111 2 (9, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_213 0 (5, 5)).mono (by decide +kernel)
  · exact row_works_708_i2.mono (by decide +kernel)
  · exact row_works_708_i3.mono (by decide +kernel)
theorem row_works_708_i1 : Template HasSnaky 7 required_708_i1 envelope_708_i1 := by
  refine compose HasSnaky 6 childrenC_708_i1 childrenD_708_i1 children_work_708_i1 (7, 7)
    required_708_i1 envelope_708_i1 pivot_mem_708_i1 child_required_sub_708_i1 child_envelope_sub_708_i1 ?_
  intro b hb
  exact common_sub_708_i1 (mem_commonEnvelope childrenD_708_i1 b hb)
def required_708_i5 : Finset Cell := ⟨(([(6, 8), (7, 8), (8, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_708_i5 : Finset Cell := ⟨(([(2, 7), (2, 9), (3, 7), (3, 8), (3, 9), (4, 7), (4, 8), (4, 9), (5, 7), (5, 8), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (8, 8), (8, 9), (9, 7), (9, 8), (9, 9), (10, 7), (10, 8), (11, 7), (11, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_708_i5 : Fin 3 → Finset Cell := ![(placed21 3 (5, 8) required_7), (placed21 5 (11, 7) required_186), (placed21 6 (9, 11) required_292)]
def childrenD_708_i5 : Fin 3 → Finset Cell := ![(placed21 3 (5, 8) envelope_7), (placed21 5 (11, 7) envelope_186), (placed21 6 (9, 11) envelope_292)]
theorem common_sub_708_i5 : commonEnvelope childrenD_708_i5 ⊆ insert (9, 8) required_708_i5 := by decide +kernel
theorem child_required_sub_708_i5 : ∀ j, childrenC_708_i5 j ⊆ insert (9, 8) required_708_i5 := by decide +kernel
theorem child_envelope_sub_708_i5 : ∀ j, childrenD_708_i5 j ⊆ envelope_708_i5 := by decide +kernel
theorem pivot_mem_708_i5 : (9, 8) ∈ envelope_708_i5 := by decide +kernel
theorem children_work_708_i5 : ∀ j, Template HasSnaky 6 (childrenC_708_i5 j) (childrenD_708_i5 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 3 (5, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_186 5 (11, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_292 6 (9, 11)).mono (by decide +kernel)
theorem row_works_708_i5 : Template HasSnaky 7 required_708_i5 envelope_708_i5 := by
  refine compose HasSnaky 6 childrenC_708_i5 childrenD_708_i5 children_work_708_i5 (9, 8)
    required_708_i5 envelope_708_i5 pivot_mem_708_i5 child_required_sub_708_i5 child_envelope_sub_708_i5 ?_
  intro b hb
  exact common_sub_708_i5 (mem_commonEnvelope childrenD_708_i5 b hb)
def required_708_i0 : Finset Cell := ⟨(([(7, 8), (8, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_708_i0 : Finset Cell := ⟨(([(2, 7), (2, 9), (3, 7), (3, 8), (3, 9), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (5, 12), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (7, 12), (8, 8), (8, 9), (8, 10), (8, 11), (9, 7), (9, 8), (9, 9), (10, 7), (10, 8), (11, 7), (11, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_708_i0 : Fin 7 → Finset Cell := ![(placed21 0 (5, 5) required_117), (placed21 2 (9, 6) required_137), (placed21 2 (9, 6) required_181), (placed21 2 (9, 5) required_257), (placed21 2 (9, 5) required_435), required_708_i1, required_708_i5]
def childrenD_708_i0 : Fin 7 → Finset Cell := ![(placed21 0 (5, 5) envelope_117), (placed21 2 (9, 6) envelope_137), (placed21 2 (9, 6) envelope_181), (placed21 2 (9, 5) envelope_257), (placed21 2 (9, 5) envelope_435), envelope_708_i1, envelope_708_i5]
theorem common_sub_708_i0 : commonEnvelope childrenD_708_i0 ⊆ insert (6, 8) required_708_i0 := by decide +kernel
theorem child_required_sub_708_i0 : ∀ j, childrenC_708_i0 j ⊆ insert (6, 8) required_708_i0 := by decide +kernel
theorem child_envelope_sub_708_i0 : ∀ j, childrenD_708_i0 j ⊆ envelope_708_i0 := by decide +kernel
theorem pivot_mem_708_i0 : (6, 8) ∈ envelope_708_i0 := by decide +kernel
theorem children_work_708_i0 : ∀ j, Template HasSnaky 8 (childrenC_708_i0 j) (childrenD_708_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_117 0 (5, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_137 2 (9, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_181 2 (9, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_257 2 (9, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_435 2 (9, 5)).mono (by decide +kernel)
  · exact row_works_708_i1.mono (by decide +kernel)
  · exact row_works_708_i5.mono (by decide +kernel)
theorem row_works_708_i0 : Template HasSnaky 9 required_708_i0 envelope_708_i0 := by
  refine compose HasSnaky 8 childrenC_708_i0 childrenD_708_i0 children_work_708_i0 (6, 8)
    required_708_i0 envelope_708_i0 pivot_mem_708_i0 child_required_sub_708_i0 child_envelope_sub_708_i0 ?_
  intro b hb
  exact common_sub_708_i0 (mem_commonEnvelope childrenD_708_i0 b hb)
def required_708_i6 : Finset Cell := ⟨(([(7, 8), (8, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_708_i6 : Finset Cell := ⟨(([(3, 9), (3, 10), (3, 11), (4, 9), (4, 10), (4, 11), (5, 8), (5, 9), (5, 10), (5, 11), (5, 12), (5, 13), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (6, 12), (6, 13), (6, 14), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (7, 12), (7, 13), (8, 4), (8, 5), (8, 6), (8, 8), (8, 9), (8, 10), (8, 11), (8, 12), (8, 13), (8, 14), (8, 15), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (9, 10), (9, 11), (9, 12), (9, 13), (9, 14), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (10, 9), (10, 10), (10, 11), (10, 12), (10, 13), (10, 14), (10, 15), (11, 7), (11, 8), (11, 9), (11, 10), (11, 11), (12, 7), (12, 9), (12, 10), (12, 11), (12, 12)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_708_i6 : Fin 7 → Finset Cell := ![(placed21 3 (5, 9) required_12), (placed21 5 (11, 6) required_135), (placed21 0 (6, 6) required_181), (placed21 4 (6, 11) required_435), (placed21 4 (5, 11) required_565), (placed21 2 (12, 4) required_687), (placed21 0 (5, 4) required_689)]
def childrenD_708_i6 : Fin 7 → Finset Cell := ![(placed21 3 (5, 9) envelope_12), (placed21 5 (11, 6) envelope_135), (placed21 0 (6, 6) envelope_181), (placed21 4 (6, 11) envelope_435), (placed21 4 (5, 11) envelope_565), (placed21 2 (12, 4) envelope_687), (placed21 0 (5, 4) envelope_689)]
theorem common_sub_708_i6 : commonEnvelope childrenD_708_i6 ⊆ insert (9, 8) required_708_i6 := by decide +kernel
theorem child_required_sub_708_i6 : ∀ j, childrenC_708_i6 j ⊆ insert (9, 8) required_708_i6 := by decide +kernel
theorem child_envelope_sub_708_i6 : ∀ j, childrenD_708_i6 j ⊆ envelope_708_i6 := by decide +kernel
theorem pivot_mem_708_i6 : (9, 8) ∈ envelope_708_i6 := by decide +kernel
theorem children_work_708_i6 : ∀ j, Template HasSnaky 12 (childrenC_708_i6 j) (childrenD_708_i6 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_12 3 (5, 9)).mono (by decide +kernel)
  · exact (placed21_template row_works_135 5 (11, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_181 0 (6, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_435 4 (6, 11)).mono (by decide +kernel)
  · exact (placed21_template row_works_565 4 (5, 11)).mono (by decide +kernel)
  · exact (placed21_template row_works_687 2 (12, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_689 0 (5, 4)).mono (by decide +kernel)
theorem row_works_708_i6 : Template HasSnaky 13 required_708_i6 envelope_708_i6 := by
  refine compose HasSnaky 12 childrenC_708_i6 childrenD_708_i6 children_work_708_i6 (9, 8)
    required_708_i6 envelope_708_i6 pivot_mem_708_i6 child_required_sub_708_i6 child_envelope_sub_708_i6 ?_
  intro b hb
  exact common_sub_708_i6 (mem_commonEnvelope childrenD_708_i6 b hb)
def required_708_i7 : Finset Cell := ⟨(([(7, 8), (8, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_708_i7 : Finset Cell := ⟨(([(2, 4), (2, 6), (2, 7), (2, 9), (2, 10), (2, 12), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (4, 13), (4, 14), (4, 15), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (5, 12), (5, 13), (5, 14), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (6, 12), (6, 13), (6, 14), (6, 15), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (7, 12), (7, 13), (7, 14), (8, 3), (8, 4), (8, 5), (8, 6), (8, 8), (8, 10), (8, 11), (8, 12), (8, 13), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (9, 10), (9, 11), (9, 12), (9, 13), (9, 14), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (10, 9), (10, 10), (10, 11), (10, 12), (10, 13), (10, 14), (10, 15), (11, 2), (11, 3), (11, 4), (11, 5), (11, 6), (11, 7), (11, 8), (11, 9), (11, 10), (11, 11), (11, 12), (11, 13), (11, 14), (12, 1), (12, 2), (12, 3), (12, 4), (12, 5), (12, 6), (12, 7), (12, 8), (12, 9), (12, 10), (12, 11), (12, 12), (12, 13), (12, 14), (12, 15), (13, 4), (13, 5), (13, 6), (13, 7), (13, 8), (13, 9), (13, 10), (13, 11), (13, 12), (14, 4), (14, 6), (14, 7), (14, 9), (14, 10), (14, 12)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_708_i7 : Fin 6 → Finset Cell := ![(placed21 1 (5, 7) required_12), (placed21 3 (5, 9) required_12), (placed21 5 (11, 7) required_12), (placed21 7 (11, 9) required_12), (placed21 0 (5, 1) required_490), (placed21 2 (11, 1) required_490)]
def childrenD_708_i7 : Fin 6 → Finset Cell := ![(placed21 1 (5, 7) envelope_12), (placed21 3 (5, 9) envelope_12), (placed21 5 (11, 7) envelope_12), (placed21 7 (11, 9) envelope_12), (placed21 0 (5, 1) envelope_490), (placed21 2 (11, 1) envelope_490)]
theorem common_sub_708_i7 : commonEnvelope childrenD_708_i7 ⊆ insert (9, 8) required_708_i7 := by decide +kernel
theorem child_required_sub_708_i7 : ∀ j, childrenC_708_i7 j ⊆ insert (9, 8) required_708_i7 := by decide +kernel
theorem child_envelope_sub_708_i7 : ∀ j, childrenD_708_i7 j ⊆ envelope_708_i7 := by decide +kernel
theorem pivot_mem_708_i7 : (9, 8) ∈ envelope_708_i7 := by decide +kernel
theorem children_work_708_i7 : ∀ j, Template HasSnaky 13 (childrenC_708_i7 j) (childrenD_708_i7 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_12 1 (5, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_12 3 (5, 9)).mono (by decide +kernel)
  · exact (placed21_template row_works_12 5 (11, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_12 7 (11, 9)).mono (by decide +kernel)
  · exact (placed21_template row_works_490 0 (5, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_490 2 (11, 1)).mono (by decide +kernel)
theorem row_works_708_i7 : Template HasSnaky 14 required_708_i7 envelope_708_i7 := by
  refine compose HasSnaky 13 childrenC_708_i7 childrenD_708_i7 children_work_708_i7 (9, 8)
    required_708_i7 envelope_708_i7 pivot_mem_708_i7 child_required_sub_708_i7 child_envelope_sub_708_i7 ?_
  intro b hb
  exact common_sub_708_i7 (mem_commonEnvelope childrenD_708_i7 b hb)
def required_708 : Finset Cell := ⟨(([(8, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_708 : Finset Cell := ⟨(([(0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 11), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (1, 14), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (2, 13), (2, 14), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (3, 13), (3, 14), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (4, 13), (4, 14), (4, 15), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (5, 12), (5, 13), (5, 14), (5, 15), (5, 16), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (6, 12), (6, 13), (6, 14), (6, 15), (6, 16), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (7, 12), (7, 13), (7, 14), (7, 15), (7, 16), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 8), (8, 9), (8, 10), (8, 11), (8, 12), (8, 13), (8, 14), (8, 15), (8, 16), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (9, 10), (9, 11), (9, 12), (9, 13), (9, 14), (9, 15), (9, 16), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (10, 9), (10, 10), (10, 11), (10, 12), (10, 13), (10, 14), (10, 15), (10, 16), (11, 1), (11, 2), (11, 3), (11, 4), (11, 5), (11, 6), (11, 7), (11, 8), (11, 9), (11, 10), (11, 11), (11, 12), (11, 13), (11, 14), (11, 15), (11, 16), (12, 1), (12, 2), (12, 3), (12, 4), (12, 5), (12, 6), (12, 7), (12, 8), (12, 9), (12, 10), (12, 11), (12, 12), (12, 13), (12, 14), (12, 15), (13, 2), (13, 3), (13, 4), (13, 5), (13, 6), (13, 7), (13, 8), (13, 9), (13, 10), (13, 11), (13, 12), (13, 13), (13, 14), (13, 15), (14, 4), (14, 5), (14, 6), (14, 7), (14, 8), (14, 9), (14, 10), (14, 11), (14, 12), (14, 13), (14, 15), (15, 5), (15, 6), (15, 7), (15, 8), (15, 9), (15, 10), (15, 11), (16, 6), (16, 8), (16, 10)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_708 : Fin 16 → Finset Cell := ![(placed21 5 (12, 7) required_459), (placed21 5 (11, 6) required_475), (placed21 3 (4, 10) required_587), (placed21 1 (4, 7) required_603), (placed21 0 (5, 5) required_605), (placed21 6 (11, 13) required_650), (placed21 0 (1, 1) required_684), required_708_i0, required_708_i6, (placed21 7 (13, 13) required_694), (placed21 0 (5, 3) required_695), (placed21 5 (13, 3) required_696), (placed21 1 (3, 4) required_698), (placed21 2 (13, 1) required_701), required_708_i7, (placed21 2 (12, 3) required_707)]
def childrenD_708 : Fin 16 → Finset Cell := ![(placed21 5 (12, 7) envelope_459), (placed21 5 (11, 6) envelope_475), (placed21 3 (4, 10) envelope_587), (placed21 1 (4, 7) envelope_603), (placed21 0 (5, 5) envelope_605), (placed21 6 (11, 13) envelope_650), (placed21 0 (1, 1) envelope_684), envelope_708_i0, envelope_708_i6, (placed21 7 (13, 13) envelope_694), (placed21 0 (5, 3) envelope_695), (placed21 5 (13, 3) envelope_696), (placed21 1 (3, 4) envelope_698), (placed21 2 (13, 1) envelope_701), envelope_708_i7, (placed21 2 (12, 3) envelope_707)]
theorem common_sub_708 : commonEnvelope childrenD_708 ⊆ insert (7, 8) required_708 := by decide +kernel
theorem child_required_sub_708 : ∀ j, childrenC_708 j ⊆ insert (7, 8) required_708 := by decide +kernel
theorem child_envelope_sub_708 : ∀ j, childrenD_708 j ⊆ envelope_708 := by decide +kernel
theorem pivot_mem_708 : (7, 8) ∈ envelope_708 := by decide +kernel
theorem children_work_708 : ∀ j, Template HasSnaky 19 (childrenC_708 j) (childrenD_708 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_459 5 (12, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_475 5 (11, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_587 3 (4, 10)).mono (by decide +kernel)
  · exact (placed21_template row_works_603 1 (4, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_605 0 (5, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_650 6 (11, 13)).mono (by decide +kernel)
  · exact (placed21_template row_works_684 0 (1, 1)).mono (by decide +kernel)
  · exact row_works_708_i0.mono (by decide +kernel)
  · exact row_works_708_i6.mono (by decide +kernel)
  · exact (placed21_template row_works_694 7 (13, 13)).mono (by decide +kernel)
  · exact (placed21_template row_works_695 0 (5, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_696 5 (13, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_698 1 (3, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_701 2 (13, 1)).mono (by decide +kernel)
  · exact row_works_708_i7.mono (by decide +kernel)
  · exact (placed21_template row_works_707 2 (12, 3)).mono (by decide +kernel)
theorem row_works_708 : Template HasSnaky 20 required_708 envelope_708 := by
  refine compose HasSnaky 19 childrenC_708 childrenD_708 children_work_708 (7, 8)
    required_708 envelope_708 pivot_mem_708 child_required_sub_708 child_envelope_sub_708 ?_
  intro b hb
  exact common_sub_708 (mem_commonEnvelope childrenD_708 b hb)
def required_725 : Finset Cell := ⟨(([(7, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_725 : Finset Cell := ⟨(([(0, 3), (0, 4), (0, 5), (0, 6), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 11), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 10), (6, 11), (6, 12), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (7, 12), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (8, 11), (8, 12), (8, 13), (8, 14), (8, 15), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (9, 10), (9, 11), (9, 12), (9, 13), (9, 14), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (10, 9), (10, 10), (10, 11), (10, 12), (10, 13), (10, 14), (11, 0), (11, 1), (11, 2), (11, 3), (11, 4), (11, 5), (11, 6), (11, 7), (11, 8), (11, 9), (11, 10), (11, 11), (11, 12), (11, 13), (12, 2), (12, 3), (12, 4), (12, 5), (12, 6), (12, 7), (12, 8), (12, 9), (12, 10), (12, 11), (12, 12), (13, 2), (13, 3), (13, 4), (13, 5), (13, 6), (13, 7), (13, 8), (13, 9), (13, 10), (13, 11), (13, 12), (14, 2), (14, 3), (14, 4), (14, 5), (14, 6), (14, 7), (14, 8), (14, 9), (14, 10), (14, 12), (15, 6), (15, 7), (15, 8), (15, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_725 : Fin 16 → Finset Cell := ![(placed21 4 (6, 12) required_459), (placed21 7 (11, 9) required_579), (placed21 6 (11, 12) required_581), (placed21 4 (4, 11) required_654), (placed21 0 (3, 3) required_661), (placed21 6 (10, 12) required_677), (placed21 7 (12, 11) required_682), (placed21 4 (2, 13) required_694), (placed21 0 (2, 2) required_696), (placed21 6 (11, 12) required_698), (placed21 0 (2, 2) required_709), (placed21 0 (4, 3) required_710), (placed21 3 (2, 12) required_715), (placed21 7 (13, 12) required_717), (placed21 0 (2, 2) required_718), (placed21 6 (12, 15) required_724)]
def childrenD_725 : Fin 16 → Finset Cell := ![(placed21 4 (6, 12) envelope_459), (placed21 7 (11, 9) envelope_579), (placed21 6 (11, 12) envelope_581), (placed21 4 (4, 11) envelope_654), (placed21 0 (3, 3) envelope_661), (placed21 6 (10, 12) envelope_677), (placed21 7 (12, 11) envelope_682), (placed21 4 (2, 13) envelope_694), (placed21 0 (2, 2) envelope_696), (placed21 6 (11, 12) envelope_698), (placed21 0 (2, 2) envelope_709), (placed21 0 (4, 3) envelope_710), (placed21 3 (2, 12) envelope_715), (placed21 7 (13, 12) envelope_717), (placed21 0 (2, 2) envelope_718), (placed21 6 (12, 15) envelope_724)]
theorem common_sub_725 : commonEnvelope childrenD_725 ⊆ insert (7, 8) required_725 := by decide +kernel
theorem child_required_sub_725 : ∀ j, childrenC_725 j ⊆ insert (7, 8) required_725 := by decide +kernel
theorem child_envelope_sub_725 : ∀ j, childrenD_725 j ⊆ envelope_725 := by decide +kernel
theorem pivot_mem_725 : (7, 8) ∈ envelope_725 := by decide +kernel
theorem children_work_725 : ∀ j, Template HasSnaky 19 (childrenC_725 j) (childrenD_725 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_459 4 (6, 12)).mono (by decide +kernel)
  · exact (placed21_template row_works_579 7 (11, 9)).mono (by decide +kernel)
  · exact (placed21_template row_works_581 6 (11, 12)).mono (by decide +kernel)
  · exact (placed21_template row_works_654 4 (4, 11)).mono (by decide +kernel)
  · exact (placed21_template row_works_661 0 (3, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_677 6 (10, 12)).mono (by decide +kernel)
  · exact (placed21_template row_works_682 7 (12, 11)).mono (by decide +kernel)
  · exact (placed21_template row_works_694 4 (2, 13)).mono (by decide +kernel)
  · exact (placed21_template row_works_696 0 (2, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_698 6 (11, 12)).mono (by decide +kernel)
  · exact (placed21_template row_works_709 0 (2, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_710 0 (4, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_715 3 (2, 12)).mono (by decide +kernel)
  · exact (placed21_template row_works_717 7 (13, 12)).mono (by decide +kernel)
  · exact (placed21_template row_works_718 0 (2, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_724 6 (12, 15)).mono (by decide +kernel)
theorem row_works_725 : Template HasSnaky 20 required_725 envelope_725 := by
  refine compose HasSnaky 19 childrenC_725 childrenD_725 children_work_725 (7, 8)
    required_725 envelope_725 pivot_mem_725 child_required_sub_725 child_envelope_sub_725 ?_
  intro b hb
  exact common_sub_725 (mem_commonEnvelope childrenD_725 b hb)
def required_726 : Finset Cell := ⟨(([(7, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_726 : Finset Cell := ⟨(([(0, 8), (1, 8), (1, 9), (1, 10), (2, 8), (2, 9), (2, 10), (2, 11), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (3, 13), (3, 14), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (4, 13), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (5, 12), (5, 13), (5, 14), (6, 3), (6, 4), (6, 5), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (6, 12), (6, 13), (6, 14), (6, 15), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (7, 12), (7, 13), (7, 14), (7, 15), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (8, 11), (8, 12), (8, 13), (8, 14), (8, 15), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (9, 10), (9, 11), (9, 12), (9, 13), (9, 14), (9, 15), (10, 0), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (10, 9), (10, 10), (10, 11), (10, 12), (10, 13), (10, 14), (11, 0), (11, 1), (11, 2), (11, 3), (11, 4), (11, 5), (11, 6), (11, 7), (11, 8), (11, 9), (11, 10), (11, 11), (11, 12), (11, 13), (11, 14), (12, 0), (12, 1), (12, 2), (12, 3), (12, 4), (12, 5), (12, 6), (12, 7), (12, 8), (12, 9), (12, 10), (12, 11), (12, 12), (12, 13), (12, 14), (13, 3), (13, 4), (13, 5), (13, 6), (13, 7), (13, 8), (13, 9), (13, 10), (13, 11), (13, 12), (13, 13), (13, 14), (14, 3), (14, 4), (14, 5), (14, 6), (14, 8), (14, 9), (14, 10), (14, 11), (15, 6), (15, 9), (15, 11)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_726 : Fin 16 → Finset Cell := ![(placed21 1 (3, 6) required_459), (placed21 4 (6, 11) required_579), (placed21 1 (3, 3) required_581), (placed21 1 (4, 4) required_654), (placed21 5 (12, 3) required_661), (placed21 3 (3, 10) required_677), (placed21 4 (4, 12) required_682), (placed21 1 (2, 2) required_694), (placed21 5 (13, 2) required_696), (placed21 3 (3, 11) required_698), (placed21 5 (13, 2) required_709), (placed21 5 (12, 4) required_710), (placed21 0 (3, 2) required_715), (placed21 4 (3, 13) required_717), (placed21 5 (13, 2) required_718), (placed21 5 (15, 2) required_724)]
def childrenD_726 : Fin 16 → Finset Cell := ![(placed21 1 (3, 6) envelope_459), (placed21 4 (6, 11) envelope_579), (placed21 1 (3, 3) envelope_581), (placed21 1 (4, 4) envelope_654), (placed21 5 (12, 3) envelope_661), (placed21 3 (3, 10) envelope_677), (placed21 4 (4, 12) envelope_682), (placed21 1 (2, 2) envelope_694), (placed21 5 (13, 2) envelope_696), (placed21 3 (3, 11) envelope_698), (placed21 5 (13, 2) envelope_709), (placed21 5 (12, 4) envelope_710), (placed21 0 (3, 2) envelope_715), (placed21 4 (3, 13) envelope_717), (placed21 5 (13, 2) envelope_718), (placed21 5 (15, 2) envelope_724)]
theorem common_sub_726 : commonEnvelope childrenD_726 ⊆ insert (8, 7) required_726 := by decide +kernel
theorem child_required_sub_726 : ∀ j, childrenC_726 j ⊆ insert (8, 7) required_726 := by decide +kernel
theorem child_envelope_sub_726 : ∀ j, childrenD_726 j ⊆ envelope_726 := by decide +kernel
theorem pivot_mem_726 : (8, 7) ∈ envelope_726 := by decide +kernel
theorem children_work_726 : ∀ j, Template HasSnaky 19 (childrenC_726 j) (childrenD_726 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_459 1 (3, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_579 4 (6, 11)).mono (by decide +kernel)
  · exact (placed21_template row_works_581 1 (3, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_654 1 (4, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_661 5 (12, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_677 3 (3, 10)).mono (by decide +kernel)
  · exact (placed21_template row_works_682 4 (4, 12)).mono (by decide +kernel)
  · exact (placed21_template row_works_694 1 (2, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_696 5 (13, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_698 3 (3, 11)).mono (by decide +kernel)
  · exact (placed21_template row_works_709 5 (13, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_710 5 (12, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_715 0 (3, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_717 4 (3, 13)).mono (by decide +kernel)
  · exact (placed21_template row_works_718 5 (13, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_724 5 (15, 2)).mono (by decide +kernel)
theorem row_works_726 : Template HasSnaky 20 required_726 envelope_726 := by
  refine compose HasSnaky 19 childrenC_726 childrenD_726 children_work_726 (8, 7)
    required_726 envelope_726 pivot_mem_726 child_required_sub_726 child_envelope_sub_726 ?_
  intro b hb
  exact common_sub_726 (mem_commonEnvelope childrenD_726 b hb)
def height_708_i2 : ℕ := 6
def childrenH_708_i2 : Fin 3 → ℕ := ![height_7, height_234, height_241]
theorem height_exact_708_i2 : height_708_i2 = 1 + Finset.univ.sup childrenH_708_i2 := by decide +kernel
theorem required_origin_708_i2 : ∀ x ∈ required_708_i2,
    (∃ j, x ∈ childrenC_708_i2 j) ∨ ∀ j, x ∈ childrenD_708_i2 j := by decide +kernel
theorem required_exact_708_i2 : required_708_i2 =
    ((Finset.univ.biUnion childrenC_708_i2) ∪ commonEnvelope childrenD_708_i2).erase (5, 8) := by
  exact required_eq_combination childrenC_708_i2 childrenD_708_i2 (5, 8) required_708_i2
    (by decide +kernel) child_required_sub_708_i2 common_sub_708_i2 required_origin_708_i2
theorem envelope_origin_708_i2 : ∀ x ∈ envelope_708_i2,
    x = (5, 8) ∨ ∃ j, x ∈ childrenD_708_i2 j := by decide +kernel
theorem envelope_exact_708_i2 : envelope_708_i2 =
    insert (5, 8) (Finset.univ.biUnion childrenD_708_i2) := by
  exact envelope_eq_combination childrenD_708_i2 (5, 8) envelope_708_i2
    pivot_mem_708_i2 child_envelope_sub_708_i2 envelope_origin_708_i2
def checked_708_i2 : CheckedCard where
  required := required_708_i2
  envelope := envelope_708_i2
  height := height_708_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_708_i2
def height_708_i4 : ℕ := 5
def childrenH_708_i4 : Fin 3 → ℕ := ![height_7, height_9, height_92]
theorem height_exact_708_i4 : height_708_i4 = 1 + Finset.univ.sup childrenH_708_i4 := by decide +kernel
theorem required_origin_708_i4 : ∀ x ∈ required_708_i4,
    (∃ j, x ∈ childrenC_708_i4 j) ∨ ∀ j, x ∈ childrenD_708_i4 j := by decide +kernel
theorem required_exact_708_i4 : required_708_i4 =
    ((Finset.univ.biUnion childrenC_708_i4) ∪ commonEnvelope childrenD_708_i4).erase (7, 9) := by
  exact required_eq_combination childrenC_708_i4 childrenD_708_i4 (7, 9) required_708_i4
    (by decide +kernel) child_required_sub_708_i4 common_sub_708_i4 required_origin_708_i4
theorem envelope_origin_708_i4 : ∀ x ∈ envelope_708_i4,
    x = (7, 9) ∨ ∃ j, x ∈ childrenD_708_i4 j := by decide +kernel
theorem envelope_exact_708_i4 : envelope_708_i4 =
    insert (7, 9) (Finset.univ.biUnion childrenD_708_i4) := by
  exact envelope_eq_combination childrenD_708_i4 (7, 9) envelope_708_i4
    pivot_mem_708_i4 child_envelope_sub_708_i4 envelope_origin_708_i4
def checked_708_i4 : CheckedCard where
  required := required_708_i4
  envelope := envelope_708_i4
  height := height_708_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_708_i4
def height_708_i3 : ℕ := 6
def childrenH_708_i3 : Fin 3 → ℕ := ![height_44, height_52, height_708_i4]
theorem height_exact_708_i3 : height_708_i3 = 1 + Finset.univ.sup childrenH_708_i3 := by decide +kernel
theorem required_origin_708_i3 : ∀ x ∈ required_708_i3,
    (∃ j, x ∈ childrenC_708_i3 j) ∨ ∀ j, x ∈ childrenD_708_i3 j := by decide +kernel
theorem required_exact_708_i3 : required_708_i3 =
    ((Finset.univ.biUnion childrenC_708_i3) ∪ commonEnvelope childrenD_708_i3).erase (7, 6) := by
  exact required_eq_combination childrenC_708_i3 childrenD_708_i3 (7, 6) required_708_i3
    (by decide +kernel) child_required_sub_708_i3 common_sub_708_i3 required_origin_708_i3
theorem envelope_origin_708_i3 : ∀ x ∈ envelope_708_i3,
    x = (7, 6) ∨ ∃ j, x ∈ childrenD_708_i3 j := by decide +kernel
theorem envelope_exact_708_i3 : envelope_708_i3 =
    insert (7, 6) (Finset.univ.biUnion childrenD_708_i3) := by
  exact envelope_eq_combination childrenD_708_i3 (7, 6) envelope_708_i3
    pivot_mem_708_i3 child_envelope_sub_708_i3 envelope_origin_708_i3
def checked_708_i3 : CheckedCard where
  required := required_708_i3
  envelope := envelope_708_i3
  height := height_708_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_708_i3
def height_708_i1 : ℕ := 7
def childrenH_708_i1 : Fin 6 → ℕ := ![height_57, height_88, height_111, height_213, height_708_i2, height_708_i3]
theorem height_exact_708_i1 : height_708_i1 = 1 + Finset.univ.sup childrenH_708_i1 := by decide +kernel
theorem required_origin_708_i1 : ∀ x ∈ required_708_i1,
    (∃ j, x ∈ childrenC_708_i1 j) ∨ ∀ j, x ∈ childrenD_708_i1 j := by decide +kernel
theorem required_exact_708_i1 : required_708_i1 =
    ((Finset.univ.biUnion childrenC_708_i1) ∪ commonEnvelope childrenD_708_i1).erase (7, 7) := by
  exact required_eq_combination childrenC_708_i1 childrenD_708_i1 (7, 7) required_708_i1
    (by decide +kernel) child_required_sub_708_i1 common_sub_708_i1 required_origin_708_i1
theorem envelope_origin_708_i1 : ∀ x ∈ envelope_708_i1,
    x = (7, 7) ∨ ∃ j, x ∈ childrenD_708_i1 j := by decide +kernel
theorem envelope_exact_708_i1 : envelope_708_i1 =
    insert (7, 7) (Finset.univ.biUnion childrenD_708_i1) := by
  exact envelope_eq_combination childrenD_708_i1 (7, 7) envelope_708_i1
    pivot_mem_708_i1 child_envelope_sub_708_i1 envelope_origin_708_i1
def checked_708_i1 : CheckedCard where
  required := required_708_i1
  envelope := envelope_708_i1
  height := height_708_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_708_i1
def height_708_i5 : ℕ := 7
def childrenH_708_i5 : Fin 3 → ℕ := ![height_7, height_186, height_292]
theorem height_exact_708_i5 : height_708_i5 = 1 + Finset.univ.sup childrenH_708_i5 := by decide +kernel
theorem required_origin_708_i5 : ∀ x ∈ required_708_i5,
    (∃ j, x ∈ childrenC_708_i5 j) ∨ ∀ j, x ∈ childrenD_708_i5 j := by decide +kernel
theorem required_exact_708_i5 : required_708_i5 =
    ((Finset.univ.biUnion childrenC_708_i5) ∪ commonEnvelope childrenD_708_i5).erase (9, 8) := by
  exact required_eq_combination childrenC_708_i5 childrenD_708_i5 (9, 8) required_708_i5
    (by decide +kernel) child_required_sub_708_i5 common_sub_708_i5 required_origin_708_i5
theorem envelope_origin_708_i5 : ∀ x ∈ envelope_708_i5,
    x = (9, 8) ∨ ∃ j, x ∈ childrenD_708_i5 j := by decide +kernel
theorem envelope_exact_708_i5 : envelope_708_i5 =
    insert (9, 8) (Finset.univ.biUnion childrenD_708_i5) := by
  exact envelope_eq_combination childrenD_708_i5 (9, 8) envelope_708_i5
    pivot_mem_708_i5 child_envelope_sub_708_i5 envelope_origin_708_i5
def checked_708_i5 : CheckedCard where
  required := required_708_i5
  envelope := envelope_708_i5
  height := height_708_i5
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_708_i5
def height_708_i0 : ℕ := 9
def childrenH_708_i0 : Fin 7 → ℕ := ![height_117, height_137, height_181, height_257, height_435, height_708_i1, height_708_i5]
theorem height_exact_708_i0 : height_708_i0 = 1 + Finset.univ.sup childrenH_708_i0 := by decide +kernel
theorem required_origin_708_i0 : ∀ x ∈ required_708_i0,
    (∃ j, x ∈ childrenC_708_i0 j) ∨ ∀ j, x ∈ childrenD_708_i0 j := by decide +kernel
theorem required_exact_708_i0 : required_708_i0 =
    ((Finset.univ.biUnion childrenC_708_i0) ∪ commonEnvelope childrenD_708_i0).erase (6, 8) := by
  exact required_eq_combination childrenC_708_i0 childrenD_708_i0 (6, 8) required_708_i0
    (by decide +kernel) child_required_sub_708_i0 common_sub_708_i0 required_origin_708_i0
theorem envelope_origin_708_i0 : ∀ x ∈ envelope_708_i0,
    x = (6, 8) ∨ ∃ j, x ∈ childrenD_708_i0 j := by decide +kernel
theorem envelope_exact_708_i0 : envelope_708_i0 =
    insert (6, 8) (Finset.univ.biUnion childrenD_708_i0) := by
  exact envelope_eq_combination childrenD_708_i0 (6, 8) envelope_708_i0
    pivot_mem_708_i0 child_envelope_sub_708_i0 envelope_origin_708_i0
def checked_708_i0 : CheckedCard where
  required := required_708_i0
  envelope := envelope_708_i0
  height := height_708_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_708_i0
def height_708_i6 : ℕ := 13
def childrenH_708_i6 : Fin 7 → ℕ := ![height_12, height_135, height_181, height_435, height_565, height_687, height_689]
theorem height_exact_708_i6 : height_708_i6 = 1 + Finset.univ.sup childrenH_708_i6 := by decide +kernel
theorem required_origin_708_i6 : ∀ x ∈ required_708_i6,
    (∃ j, x ∈ childrenC_708_i6 j) ∨ ∀ j, x ∈ childrenD_708_i6 j := by decide +kernel
theorem required_exact_708_i6 : required_708_i6 =
    ((Finset.univ.biUnion childrenC_708_i6) ∪ commonEnvelope childrenD_708_i6).erase (9, 8) := by
  exact required_eq_combination childrenC_708_i6 childrenD_708_i6 (9, 8) required_708_i6
    (by decide +kernel) child_required_sub_708_i6 common_sub_708_i6 required_origin_708_i6
theorem envelope_origin_708_i6 : ∀ x ∈ envelope_708_i6,
    x = (9, 8) ∨ ∃ j, x ∈ childrenD_708_i6 j := by decide +kernel
theorem envelope_exact_708_i6 : envelope_708_i6 =
    insert (9, 8) (Finset.univ.biUnion childrenD_708_i6) := by
  exact envelope_eq_combination childrenD_708_i6 (9, 8) envelope_708_i6
    pivot_mem_708_i6 child_envelope_sub_708_i6 envelope_origin_708_i6
def checked_708_i6 : CheckedCard where
  required := required_708_i6
  envelope := envelope_708_i6
  height := height_708_i6
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_708_i6
def height_708_i7 : ℕ := 14
def childrenH_708_i7 : Fin 6 → ℕ := ![height_12, height_12, height_12, height_12, height_490, height_490]
theorem height_exact_708_i7 : height_708_i7 = 1 + Finset.univ.sup childrenH_708_i7 := by decide +kernel
theorem required_origin_708_i7 : ∀ x ∈ required_708_i7,
    (∃ j, x ∈ childrenC_708_i7 j) ∨ ∀ j, x ∈ childrenD_708_i7 j := by decide +kernel
theorem required_exact_708_i7 : required_708_i7 =
    ((Finset.univ.biUnion childrenC_708_i7) ∪ commonEnvelope childrenD_708_i7).erase (9, 8) := by
  exact required_eq_combination childrenC_708_i7 childrenD_708_i7 (9, 8) required_708_i7
    (by decide +kernel) child_required_sub_708_i7 common_sub_708_i7 required_origin_708_i7
theorem envelope_origin_708_i7 : ∀ x ∈ envelope_708_i7,
    x = (9, 8) ∨ ∃ j, x ∈ childrenD_708_i7 j := by decide +kernel
theorem envelope_exact_708_i7 : envelope_708_i7 =
    insert (9, 8) (Finset.univ.biUnion childrenD_708_i7) := by
  exact envelope_eq_combination childrenD_708_i7 (9, 8) envelope_708_i7
    pivot_mem_708_i7 child_envelope_sub_708_i7 envelope_origin_708_i7
def checked_708_i7 : CheckedCard where
  required := required_708_i7
  envelope := envelope_708_i7
  height := height_708_i7
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_708_i7
def height_708 : ℕ := 20
def childrenH_708 : Fin 16 → ℕ := ![height_459, height_475, height_587, height_603, height_605, height_650, height_684, height_708_i0, height_708_i6, height_694, height_695, height_696, height_698, height_701, height_708_i7, height_707]
theorem height_exact_708 : height_708 = 1 + Finset.univ.sup childrenH_708 := by decide +kernel
theorem required_origin_708 : ∀ x ∈ required_708,
    (∃ j, x ∈ childrenC_708 j) ∨ ∀ j, x ∈ childrenD_708 j := by decide +kernel
theorem required_exact_708 : required_708 =
    ((Finset.univ.biUnion childrenC_708) ∪ commonEnvelope childrenD_708).erase (7, 8) := by
  exact required_eq_combination childrenC_708 childrenD_708 (7, 8) required_708
    (by decide +kernel) child_required_sub_708 common_sub_708 required_origin_708
theorem envelope_origin_708 : ∀ x ∈ envelope_708,
    x = (7, 8) ∨ ∃ j, x ∈ childrenD_708 j := by decide +kernel
theorem envelope_exact_708 : envelope_708 =
    insert (7, 8) (Finset.univ.biUnion childrenD_708) := by
  exact envelope_eq_combination childrenD_708 (7, 8) envelope_708
    pivot_mem_708 child_envelope_sub_708 envelope_origin_708
def checked_708 : CheckedCard where
  required := required_708
  envelope := envelope_708
  height := height_708
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_708
def height_725 : ℕ := 20
def childrenH_725 : Fin 16 → ℕ := ![height_459, height_579, height_581, height_654, height_661, height_677, height_682, height_694, height_696, height_698, height_709, height_710, height_715, height_717, height_718, height_724]
theorem height_exact_725 : height_725 = 1 + Finset.univ.sup childrenH_725 := by decide +kernel
theorem required_origin_725 : ∀ x ∈ required_725,
    (∃ j, x ∈ childrenC_725 j) ∨ ∀ j, x ∈ childrenD_725 j := by decide +kernel
theorem required_exact_725 : required_725 =
    ((Finset.univ.biUnion childrenC_725) ∪ commonEnvelope childrenD_725).erase (7, 8) := by
  exact required_eq_combination childrenC_725 childrenD_725 (7, 8) required_725
    (by decide +kernel) child_required_sub_725 common_sub_725 required_origin_725
theorem envelope_origin_725 : ∀ x ∈ envelope_725,
    x = (7, 8) ∨ ∃ j, x ∈ childrenD_725 j := by decide +kernel
theorem envelope_exact_725 : envelope_725 =
    insert (7, 8) (Finset.univ.biUnion childrenD_725) := by
  exact envelope_eq_combination childrenD_725 (7, 8) envelope_725
    pivot_mem_725 child_envelope_sub_725 envelope_origin_725
def checked_725 : CheckedCard where
  required := required_725
  envelope := envelope_725
  height := height_725
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_725
def height_726 : ℕ := 20
def childrenH_726 : Fin 16 → ℕ := ![height_459, height_579, height_581, height_654, height_661, height_677, height_682, height_694, height_696, height_698, height_709, height_710, height_715, height_717, height_718, height_724]
theorem height_exact_726 : height_726 = 1 + Finset.univ.sup childrenH_726 := by decide +kernel
theorem required_origin_726 : ∀ x ∈ required_726,
    (∃ j, x ∈ childrenC_726 j) ∨ ∀ j, x ∈ childrenD_726 j := by decide +kernel
theorem required_exact_726 : required_726 =
    ((Finset.univ.biUnion childrenC_726) ∪ commonEnvelope childrenD_726).erase (8, 7) := by
  exact required_eq_combination childrenC_726 childrenD_726 (8, 7) required_726
    (by decide +kernel) child_required_sub_726 common_sub_726 required_origin_726
theorem envelope_origin_726 : ∀ x ∈ envelope_726,
    x = (8, 7) ∨ ∃ j, x ∈ childrenD_726 j := by decide +kernel
theorem envelope_exact_726 : envelope_726 =
    insert (8, 7) (Finset.univ.biUnion childrenD_726) := by
  exact envelope_eq_combination childrenD_726 (8, 7) envelope_726
    pivot_mem_726 child_envelope_sub_726 envelope_origin_726
def checked_726 : CheckedCard where
  required := required_726
  envelope := envelope_726
  height := height_726
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_726
end SnakyPrototype.Certificate21

end OAI
