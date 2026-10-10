import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part06
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part07
import OAI.GameTheory.SnakyTwentyOne.Cards.Height10Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height10Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height11Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height12Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height12Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height13Part03
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_598_i2 : Finset Cell := ⟨(([(3, 5), (3, 6), (4, 5), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_598_i2 : Finset Cell := ⟨(([(2, 5), (2, 6), (3, 5), (3, 6), (4, 5), (5, 5), (5, 6), (5, 7), (5, 8), (6, 3), (6, 4), (6, 5), (6, 6), (7, 4), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_598_i2 : Fin 2 → Finset Cell := ![(placed21 2 (6, 5) required_5), (placed21 2 (7, 3) required_133)]
def childrenD_598_i2 : Fin 2 → Finset Cell := ![(placed21 2 (6, 5) envelope_5), (placed21 2 (7, 3) envelope_133)]
theorem common_sub_598_i2 : commonEnvelope childrenD_598_i2 ⊆ insert (5, 5) required_598_i2 := by decide +kernel
theorem child_required_sub_598_i2 : ∀ j, childrenC_598_i2 j ⊆ insert (5, 5) required_598_i2 := by decide +kernel
theorem child_envelope_sub_598_i2 : ∀ j, childrenD_598_i2 j ⊆ envelope_598_i2 := by decide +kernel
theorem pivot_mem_598_i2 : (5, 5) ∈ envelope_598_i2 := by decide +kernel
theorem children_work_598_i2 : ∀ j, Template HasSnaky 5 (childrenC_598_i2 j) (childrenD_598_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 2 (6, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_133 2 (7, 3)).mono (by decide +kernel)
theorem row_works_598_i2 : Template HasSnaky 6 required_598_i2 envelope_598_i2 := by
  refine compose HasSnaky 5 childrenC_598_i2 childrenD_598_i2 children_work_598_i2 (5, 5)
    required_598_i2 envelope_598_i2 pivot_mem_598_i2 child_required_sub_598_i2 child_envelope_sub_598_i2 ?_
  intro b hb
  exact common_sub_598_i2 (mem_commonEnvelope childrenD_598_i2 b hb)
def required_598_i1 : Finset Cell := ⟨(([(3, 5), (3, 6), (3, 7), (4, 4), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_598_i1 : Finset Cell := ⟨(([(2, 5), (2, 6), (3, 5), (3, 6), (3, 7), (3, 8), (4, 4), (4, 5), (5, 5), (5, 6), (5, 7), (5, 8), (6, 3), (6, 4), (6, 5), (6, 6), (7, 4), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_598_i1 : Fin 2 → Finset Cell := ![(placed21 3 (3, 8) required_0), required_598_i2]
def childrenD_598_i1 : Fin 2 → Finset Cell := ![(placed21 3 (3, 8) envelope_0), envelope_598_i2]
theorem common_sub_598_i1 : commonEnvelope childrenD_598_i1 ⊆ insert (4, 5) required_598_i1 := by decide +kernel
theorem child_required_sub_598_i1 : ∀ j, childrenC_598_i1 j ⊆ insert (4, 5) required_598_i1 := by decide +kernel
theorem child_envelope_sub_598_i1 : ∀ j, childrenD_598_i1 j ⊆ envelope_598_i1 := by decide +kernel
theorem pivot_mem_598_i1 : (4, 5) ∈ envelope_598_i1 := by decide +kernel
theorem children_work_598_i1 : ∀ j, Template HasSnaky 6 (childrenC_598_i1 j) (childrenD_598_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 3 (3, 8)).mono (by decide +kernel)
  · exact row_works_598_i2.mono (by decide +kernel)
theorem row_works_598_i1 : Template HasSnaky 7 required_598_i1 envelope_598_i1 := by
  refine compose HasSnaky 6 childrenC_598_i1 childrenD_598_i1 children_work_598_i1 (4, 5)
    required_598_i1 envelope_598_i1 pivot_mem_598_i1 child_required_sub_598_i1 child_envelope_sub_598_i1 ?_
  intro b hb
  exact common_sub_598_i1 (mem_commonEnvelope childrenD_598_i1 b hb)
def required_598_i0 : Finset Cell := ⟨(([(3, 4), (3, 5), (3, 7), (4, 4), (4, 7), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_598_i0 : Finset Cell := ⟨(([(2, 5), (2, 6), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 4), (4, 5), (4, 7), (4, 8), (5, 5), (5, 6), (5, 7), (5, 8), (6, 3), (6, 4), (6, 5), (6, 6), (7, 4), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_598_i0 : Fin 2 → Finset Cell := ![(placed21 1 (3, 4) required_5), required_598_i1]
def childrenD_598_i0 : Fin 2 → Finset Cell := ![(placed21 1 (3, 4) envelope_5), envelope_598_i1]
theorem common_sub_598_i0 : commonEnvelope childrenD_598_i0 ⊆ insert (3, 6) required_598_i0 := by decide +kernel
theorem child_required_sub_598_i0 : ∀ j, childrenC_598_i0 j ⊆ insert (3, 6) required_598_i0 := by decide +kernel
theorem child_envelope_sub_598_i0 : ∀ j, childrenD_598_i0 j ⊆ envelope_598_i0 := by decide +kernel
theorem pivot_mem_598_i0 : (3, 6) ∈ envelope_598_i0 := by decide +kernel
theorem children_work_598_i0 : ∀ j, Template HasSnaky 7 (childrenC_598_i0 j) (childrenD_598_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 1 (3, 4)).mono (by decide +kernel)
  · exact row_works_598_i1.mono (by decide +kernel)
theorem row_works_598_i0 : Template HasSnaky 8 required_598_i0 envelope_598_i0 := by
  refine compose HasSnaky 7 childrenC_598_i0 childrenD_598_i0 children_work_598_i0 (3, 6)
    required_598_i0 envelope_598_i0 pivot_mem_598_i0 child_required_sub_598_i0 child_envelope_sub_598_i0 ?_
  intro b hb
  exact common_sub_598_i0 (mem_commonEnvelope childrenD_598_i0 b hb)
def required_598_i5 : Finset Cell := ⟨(([(3, 5), (3, 6), (4, 5), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_598_i5 : Finset Cell := ⟨(([(2, 5), (2, 6), (3, 5), (3, 6), (4, 5), (5, 2), (5, 3), (5, 4), (5, 5), (6, 4), (6, 5), (6, 6), (6, 7), (7, 4), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_598_i5 : Fin 2 → Finset Cell := ![(placed21 2 (6, 5) required_5), (placed21 6 (7, 7) required_133)]
def childrenD_598_i5 : Fin 2 → Finset Cell := ![(placed21 2 (6, 5) envelope_5), (placed21 6 (7, 7) envelope_133)]
theorem common_sub_598_i5 : commonEnvelope childrenD_598_i5 ⊆ insert (5, 5) required_598_i5 := by decide +kernel
theorem child_required_sub_598_i5 : ∀ j, childrenC_598_i5 j ⊆ insert (5, 5) required_598_i5 := by decide +kernel
theorem child_envelope_sub_598_i5 : ∀ j, childrenD_598_i5 j ⊆ envelope_598_i5 := by decide +kernel
theorem pivot_mem_598_i5 : (5, 5) ∈ envelope_598_i5 := by decide +kernel
theorem children_work_598_i5 : ∀ j, Template HasSnaky 5 (childrenC_598_i5 j) (childrenD_598_i5 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 2 (6, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_133 6 (7, 7)).mono (by decide +kernel)
theorem row_works_598_i5 : Template HasSnaky 6 required_598_i5 envelope_598_i5 := by
  refine compose HasSnaky 5 childrenC_598_i5 childrenD_598_i5 children_work_598_i5 (5, 5)
    required_598_i5 envelope_598_i5 pivot_mem_598_i5 child_required_sub_598_i5 child_envelope_sub_598_i5 ?_
  intro b hb
  exact common_sub_598_i5 (mem_commonEnvelope childrenD_598_i5 b hb)
def required_598_i4 : Finset Cell := ⟨(([(3, 5), (3, 6), (3, 7), (4, 4), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_598_i4 : Finset Cell := ⟨(([(2, 5), (2, 6), (3, 5), (3, 6), (3, 7), (3, 8), (4, 4), (4, 5), (5, 2), (5, 3), (5, 4), (5, 5), (6, 4), (6, 5), (6, 6), (6, 7), (7, 4), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_598_i4 : Fin 2 → Finset Cell := ![(placed21 3 (3, 8) required_0), required_598_i5]
def childrenD_598_i4 : Fin 2 → Finset Cell := ![(placed21 3 (3, 8) envelope_0), envelope_598_i5]
theorem common_sub_598_i4 : commonEnvelope childrenD_598_i4 ⊆ insert (4, 5) required_598_i4 := by decide +kernel
theorem child_required_sub_598_i4 : ∀ j, childrenC_598_i4 j ⊆ insert (4, 5) required_598_i4 := by decide +kernel
theorem child_envelope_sub_598_i4 : ∀ j, childrenD_598_i4 j ⊆ envelope_598_i4 := by decide +kernel
theorem pivot_mem_598_i4 : (4, 5) ∈ envelope_598_i4 := by decide +kernel
theorem children_work_598_i4 : ∀ j, Template HasSnaky 6 (childrenC_598_i4 j) (childrenD_598_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 3 (3, 8)).mono (by decide +kernel)
  · exact row_works_598_i5.mono (by decide +kernel)
theorem row_works_598_i4 : Template HasSnaky 7 required_598_i4 envelope_598_i4 := by
  refine compose HasSnaky 6 childrenC_598_i4 childrenD_598_i4 children_work_598_i4 (4, 5)
    required_598_i4 envelope_598_i4 pivot_mem_598_i4 child_required_sub_598_i4 child_envelope_sub_598_i4 ?_
  intro b hb
  exact common_sub_598_i4 (mem_commonEnvelope childrenD_598_i4 b hb)
def required_598_i3 : Finset Cell := ⟨(([(3, 4), (3, 5), (3, 7), (4, 4), (4, 7), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_598_i3 : Finset Cell := ⟨(([(2, 5), (2, 6), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 4), (4, 5), (4, 7), (4, 8), (5, 2), (5, 3), (5, 4), (5, 5), (6, 4), (6, 5), (6, 6), (6, 7), (7, 4), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_598_i3 : Fin 2 → Finset Cell := ![(placed21 1 (3, 4) required_5), required_598_i4]
def childrenD_598_i3 : Fin 2 → Finset Cell := ![(placed21 1 (3, 4) envelope_5), envelope_598_i4]
theorem common_sub_598_i3 : commonEnvelope childrenD_598_i3 ⊆ insert (3, 6) required_598_i3 := by decide +kernel
theorem child_required_sub_598_i3 : ∀ j, childrenC_598_i3 j ⊆ insert (3, 6) required_598_i3 := by decide +kernel
theorem child_envelope_sub_598_i3 : ∀ j, childrenD_598_i3 j ⊆ envelope_598_i3 := by decide +kernel
theorem pivot_mem_598_i3 : (3, 6) ∈ envelope_598_i3 := by decide +kernel
theorem children_work_598_i3 : ∀ j, Template HasSnaky 7 (childrenC_598_i3 j) (childrenD_598_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 1 (3, 4)).mono (by decide +kernel)
  · exact row_works_598_i4.mono (by decide +kernel)
theorem row_works_598_i3 : Template HasSnaky 8 required_598_i3 envelope_598_i3 := by
  refine compose HasSnaky 7 childrenC_598_i3 childrenD_598_i3 children_work_598_i3 (3, 6)
    required_598_i3 envelope_598_i3 pivot_mem_598_i3 child_required_sub_598_i3 child_envelope_sub_598_i3 ?_
  intro b hb
  exact common_sub_598_i3 (mem_commonEnvelope childrenD_598_i3 b hb)
def required_598_i8 : Finset Cell := ⟨(([(3, 4), (3, 5), (3, 6), (4, 4), (4, 5), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_598_i8 : Finset Cell := ⟨(([(2, 5), (2, 6), (3, 4), (3, 5), (3, 6), (4, 4), (4, 5), (5, 4), (5, 5), (5, 6), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (7, 3), (7, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_598_i8 : Fin 2 → Finset Cell := ![(placed21 2 (6, 5) required_5), (placed21 3 (2, 6) required_413)]
def childrenD_598_i8 : Fin 2 → Finset Cell := ![(placed21 2 (6, 5) envelope_5), (placed21 3 (2, 6) envelope_413)]
theorem common_sub_598_i8 : commonEnvelope childrenD_598_i8 ⊆ insert (5, 5) required_598_i8 := by decide +kernel
theorem child_required_sub_598_i8 : ∀ j, childrenC_598_i8 j ⊆ insert (5, 5) required_598_i8 := by decide +kernel
theorem child_envelope_sub_598_i8 : ∀ j, childrenD_598_i8 j ⊆ envelope_598_i8 := by decide +kernel
theorem pivot_mem_598_i8 : (5, 5) ∈ envelope_598_i8 := by decide +kernel
theorem children_work_598_i8 : ∀ j, Template HasSnaky 5 (childrenC_598_i8 j) (childrenD_598_i8 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 2 (6, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_413 3 (2, 6)).mono (by decide +kernel)
theorem row_works_598_i8 : Template HasSnaky 6 required_598_i8 envelope_598_i8 := by
  refine compose HasSnaky 5 childrenC_598_i8 childrenD_598_i8 children_work_598_i8 (5, 5)
    required_598_i8 envelope_598_i8 pivot_mem_598_i8 child_required_sub_598_i8 child_envelope_sub_598_i8 ?_
  intro b hb
  exact common_sub_598_i8 (mem_commonEnvelope childrenD_598_i8 b hb)
def required_598_i7 : Finset Cell := ⟨(([(3, 4), (3, 5), (3, 6), (3, 7), (4, 4), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_598_i7 : Finset Cell := ⟨(([(2, 5), (2, 6), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 4), (4, 5), (5, 4), (5, 5), (5, 6), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (7, 3), (7, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_598_i7 : Fin 2 → Finset Cell := ![(placed21 3 (3, 8) required_0), required_598_i8]
def childrenD_598_i7 : Fin 2 → Finset Cell := ![(placed21 3 (3, 8) envelope_0), envelope_598_i8]
theorem common_sub_598_i7 : commonEnvelope childrenD_598_i7 ⊆ insert (4, 5) required_598_i7 := by decide +kernel
theorem child_required_sub_598_i7 : ∀ j, childrenC_598_i7 j ⊆ insert (4, 5) required_598_i7 := by decide +kernel
theorem child_envelope_sub_598_i7 : ∀ j, childrenD_598_i7 j ⊆ envelope_598_i7 := by decide +kernel
theorem pivot_mem_598_i7 : (4, 5) ∈ envelope_598_i7 := by decide +kernel
theorem children_work_598_i7 : ∀ j, Template HasSnaky 6 (childrenC_598_i7 j) (childrenD_598_i7 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 3 (3, 8)).mono (by decide +kernel)
  · exact row_works_598_i8.mono (by decide +kernel)
theorem row_works_598_i7 : Template HasSnaky 7 required_598_i7 envelope_598_i7 := by
  refine compose HasSnaky 6 childrenC_598_i7 childrenD_598_i7 children_work_598_i7 (4, 5)
    required_598_i7 envelope_598_i7 pivot_mem_598_i7 child_required_sub_598_i7 child_envelope_sub_598_i7 ?_
  intro b hb
  exact common_sub_598_i7 (mem_commonEnvelope childrenD_598_i7 b hb)
def required_598_i6 : Finset Cell := ⟨(([(3, 4), (3, 5), (3, 7), (4, 4), (4, 7), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_598_i6 : Finset Cell := ⟨(([(2, 5), (2, 6), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 4), (4, 5), (4, 7), (4, 8), (5, 4), (5, 5), (5, 6), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (7, 3), (7, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_598_i6 : Fin 2 → Finset Cell := ![(placed21 1 (3, 4) required_5), required_598_i7]
def childrenD_598_i6 : Fin 2 → Finset Cell := ![(placed21 1 (3, 4) envelope_5), envelope_598_i7]
theorem common_sub_598_i6 : commonEnvelope childrenD_598_i6 ⊆ insert (3, 6) required_598_i6 := by decide +kernel
theorem child_required_sub_598_i6 : ∀ j, childrenC_598_i6 j ⊆ insert (3, 6) required_598_i6 := by decide +kernel
theorem child_envelope_sub_598_i6 : ∀ j, childrenD_598_i6 j ⊆ envelope_598_i6 := by decide +kernel
theorem pivot_mem_598_i6 : (3, 6) ∈ envelope_598_i6 := by decide +kernel
theorem children_work_598_i6 : ∀ j, Template HasSnaky 7 (childrenC_598_i6 j) (childrenD_598_i6 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 1 (3, 4)).mono (by decide +kernel)
  · exact row_works_598_i7.mono (by decide +kernel)
theorem row_works_598_i6 : Template HasSnaky 8 required_598_i6 envelope_598_i6 := by
  refine compose HasSnaky 7 childrenC_598_i6 childrenD_598_i6 children_work_598_i6 (3, 6)
    required_598_i6 envelope_598_i6 pivot_mem_598_i6 child_required_sub_598_i6 child_envelope_sub_598_i6 ?_
  intro b hb
  exact common_sub_598_i6 (mem_commonEnvelope childrenD_598_i6 b hb)
def required_598 : Finset Cell := ⟨(([(3, 4), (3, 7), (4, 4), (4, 7), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_598 : Finset Cell := ⟨(([(0, 5), (1, 5), (1, 9), (2, 1), (2, 2), (2, 3), (2, 5), (2, 6), (2, 8), (2, 9), (2, 10), (2, 11), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (4, 2), (4, 4), (4, 5), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (7, 12), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 9), (10, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_598 : Fin 7 → Finset Cell := ![required_598_i0, required_598_i3, (placed21 1 (2, 4) required_584), (placed21 4 (2, 10) required_591), (placed21 2 (8, 1) required_594), required_598_i6, (placed21 0 (1, 2) required_597)]
def childrenD_598 : Fin 7 → Finset Cell := ![envelope_598_i0, envelope_598_i3, (placed21 1 (2, 4) envelope_584), (placed21 4 (2, 10) envelope_591), (placed21 2 (8, 1) envelope_594), envelope_598_i6, (placed21 0 (1, 2) envelope_597)]
theorem common_sub_598 : commonEnvelope childrenD_598 ⊆ insert (3, 5) required_598 := by decide +kernel
theorem child_required_sub_598 : ∀ j, childrenC_598 j ⊆ insert (3, 5) required_598 := by decide +kernel
theorem child_envelope_sub_598 : ∀ j, childrenD_598 j ⊆ envelope_598 := by decide +kernel
theorem pivot_mem_598 : (3, 5) ∈ envelope_598 := by decide +kernel
theorem children_work_598 : ∀ j, Template HasSnaky 13 (childrenC_598 j) (childrenD_598 j) := by
  intro j
  fin_cases j
  · exact row_works_598_i0.mono (by decide +kernel)
  · exact row_works_598_i3.mono (by decide +kernel)
  · exact (placed21_template row_works_584 1 (2, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_591 4 (2, 10)).mono (by decide +kernel)
  · exact (placed21_template row_works_594 2 (8, 1)).mono (by decide +kernel)
  · exact row_works_598_i6.mono (by decide +kernel)
  · exact (placed21_template row_works_597 0 (1, 2)).mono (by decide +kernel)
theorem row_works_598 : Template HasSnaky 14 required_598 envelope_598 := by
  refine compose HasSnaky 13 childrenC_598 childrenD_598 children_work_598 (3, 5)
    required_598 envelope_598 pivot_mem_598 child_required_sub_598 child_envelope_sub_598 ?_
  intro b hb
  exact common_sub_598 (mem_commonEnvelope childrenD_598 b hb)
def required_636_i1 : Finset Cell := ⟨(([(1, 5), (3, 4), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_636_i1 : Finset Cell := ⟨(([(0, 5), (1, 5), (2, 3), (2, 5), (3, 2), (3, 3), (3, 4), (3, 5), (3, 7), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (8, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_636_i1 : Fin 3 → Finset Cell := ![(placed21 7 (5, 5) required_22), (placed21 6 (5, 7) required_108), (placed21 0 (2, 1) required_512)]
def childrenD_636_i1 : Fin 3 → Finset Cell := ![(placed21 7 (5, 5) envelope_22), (placed21 6 (5, 7) envelope_108), (placed21 0 (2, 1) envelope_512)]
theorem common_sub_636_i1 : commonEnvelope childrenD_636_i1 ⊆ insert (3, 5) required_636_i1 := by decide +kernel
theorem child_required_sub_636_i1 : ∀ j, childrenC_636_i1 j ⊆ insert (3, 5) required_636_i1 := by decide +kernel
theorem child_envelope_sub_636_i1 : ∀ j, childrenD_636_i1 j ⊆ envelope_636_i1 := by decide +kernel
theorem pivot_mem_636_i1 : (3, 5) ∈ envelope_636_i1 := by decide +kernel
theorem children_work_636_i1 : ∀ j, Template HasSnaky 9 (childrenC_636_i1 j) (childrenD_636_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_22 7 (5, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_108 6 (5, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_512 0 (2, 1)).mono (by decide +kernel)
theorem row_works_636_i1 : Template HasSnaky 10 required_636_i1 envelope_636_i1 := by
  refine compose HasSnaky 9 childrenC_636_i1 childrenD_636_i1 children_work_636_i1 (3, 5)
    required_636_i1 envelope_636_i1 pivot_mem_636_i1 child_required_sub_636_i1 child_envelope_sub_636_i1 ?_
  intro b hb
  exact common_sub_636_i1 (mem_commonEnvelope childrenD_636_i1 b hb)
def required_636_i2 : Finset Cell := ⟨(([(3, 4), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_636_i2 : Finset Cell := ⟨(([(1, 5), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 5), (6, 6), (6, 7), (7, 5), (7, 6), (7, 7), (8, 5), (8, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_636_i2 : Fin 4 → Finset Cell := ![(placed21 0 (3, 3) required_10), (placed21 6 (4, 7) required_44), (placed21 0 (3, 3) required_63), (placed21 3 (1, 7) required_117)]
def childrenD_636_i2 : Fin 4 → Finset Cell := ![(placed21 0 (3, 3) envelope_10), (placed21 6 (4, 7) envelope_44), (placed21 0 (3, 3) envelope_63), (placed21 3 (1, 7) envelope_117)]
theorem common_sub_636_i2 : commonEnvelope childrenD_636_i2 ⊆ insert (4, 6) required_636_i2 := by decide +kernel
theorem child_required_sub_636_i2 : ∀ j, childrenC_636_i2 j ⊆ insert (4, 6) required_636_i2 := by decide +kernel
theorem child_envelope_sub_636_i2 : ∀ j, childrenD_636_i2 j ⊆ envelope_636_i2 := by decide +kernel
theorem pivot_mem_636_i2 : (4, 6) ∈ envelope_636_i2 := by decide +kernel
theorem children_work_636_i2 : ∀ j, Template HasSnaky 7 (childrenC_636_i2 j) (childrenD_636_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_10 0 (3, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_44 6 (4, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_63 0 (3, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_117 3 (1, 7)).mono (by decide +kernel)
theorem row_works_636_i2 : Template HasSnaky 8 required_636_i2 envelope_636_i2 := by
  refine compose HasSnaky 7 childrenC_636_i2 childrenD_636_i2 children_work_636_i2 (4, 6)
    required_636_i2 envelope_636_i2 pivot_mem_636_i2 child_required_sub_636_i2 child_envelope_sub_636_i2 ?_
  intro b hb
  exact common_sub_636_i2 (mem_commonEnvelope childrenD_636_i2 b hb)
def required_636_i5 : Finset Cell := ⟨(([(3, 4), (3, 5), (4, 4), (4, 5), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_636_i5 : Finset Cell := ⟨(([(2, 6), (3, 4), (3, 5), (3, 6), (3, 7), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 1), (6, 2), (6, 3), (6, 5), (6, 6), (6, 7), (6, 8), (7, 3), (7, 5), (7, 6), (8, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_636_i5 : Fin 3 → Finset Cell := ![(placed21 0 (3, 1) required_85), (placed21 0 (3, 2) required_164), (placed21 4 (2, 7) required_262)]
def childrenD_636_i5 : Fin 3 → Finset Cell := ![(placed21 0 (3, 1) envelope_85), (placed21 0 (3, 2) envelope_164), (placed21 4 (2, 7) envelope_262)]
theorem common_sub_636_i5 : commonEnvelope childrenD_636_i5 ⊆ insert (5, 5) required_636_i5 := by decide +kernel
theorem child_required_sub_636_i5 : ∀ j, childrenC_636_i5 j ⊆ insert (5, 5) required_636_i5 := by decide +kernel
theorem child_envelope_sub_636_i5 : ∀ j, childrenD_636_i5 j ⊆ envelope_636_i5 := by decide +kernel
theorem pivot_mem_636_i5 : (5, 5) ∈ envelope_636_i5 := by decide +kernel
theorem children_work_636_i5 : ∀ j, Template HasSnaky 6 (childrenC_636_i5 j) (childrenD_636_i5 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_85 0 (3, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_164 0 (3, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_262 4 (2, 7)).mono (by decide +kernel)
theorem row_works_636_i5 : Template HasSnaky 7 required_636_i5 envelope_636_i5 := by
  refine compose HasSnaky 6 childrenC_636_i5 childrenD_636_i5 children_work_636_i5 (5, 5)
    required_636_i5 envelope_636_i5 pivot_mem_636_i5 child_required_sub_636_i5 child_envelope_sub_636_i5 ?_
  intro b hb
  exact common_sub_636_i5 (mem_commonEnvelope childrenD_636_i5 b hb)
def required_636_i4 : Finset Cell := ⟨(([(1, 5), (3, 4), (4, 4), (4, 5), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_636_i4 : Finset Cell := ⟨(([(1, 5), (2, 5), (2, 6), (3, 4), (3, 5), (3, 6), (3, 7), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 1), (6, 2), (6, 3), (6, 5), (6, 6), (6, 7), (6, 8), (7, 3), (7, 5), (7, 6), (8, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_636_i4 : Fin 2 → Finset Cell := ![(placed21 4 (1, 5) required_1), required_636_i5]
def childrenD_636_i4 : Fin 2 → Finset Cell := ![(placed21 4 (1, 5) envelope_1), envelope_636_i5]
theorem common_sub_636_i4 : commonEnvelope childrenD_636_i4 ⊆ insert (3, 5) required_636_i4 := by decide +kernel
theorem child_required_sub_636_i4 : ∀ j, childrenC_636_i4 j ⊆ insert (3, 5) required_636_i4 := by decide +kernel
theorem child_envelope_sub_636_i4 : ∀ j, childrenD_636_i4 j ⊆ envelope_636_i4 := by decide +kernel
theorem pivot_mem_636_i4 : (3, 5) ∈ envelope_636_i4 := by decide +kernel
theorem children_work_636_i4 : ∀ j, Template HasSnaky 7 (childrenC_636_i4 j) (childrenD_636_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_1 4 (1, 5)).mono (by decide +kernel)
  · exact row_works_636_i5.mono (by decide +kernel)
theorem row_works_636_i4 : Template HasSnaky 8 required_636_i4 envelope_636_i4 := by
  refine compose HasSnaky 7 childrenC_636_i4 childrenD_636_i4 children_work_636_i4 (3, 5)
    required_636_i4 envelope_636_i4 pivot_mem_636_i4 child_required_sub_636_i4 child_envelope_sub_636_i4 ?_
  intro b hb
  exact common_sub_636_i4 (mem_commonEnvelope childrenD_636_i4 b hb)
def required_636_i6 : Finset Cell := ⟨(([(3, 4), (4, 4), (4, 5), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_636_i6 : Finset Cell := ⟨(([(2, 3), (2, 5), (2, 6), (2, 7), (2, 8), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 4), (6, 3), (6, 4), (7, 3), (7, 4), (8, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_636_i6 : Fin 3 → Finset Cell := ![(placed21 3 (2, 4) required_7), (placed21 1 (2, 4) required_11), (placed21 2 (6, 1) required_331)]
def childrenD_636_i6 : Fin 3 → Finset Cell := ![(placed21 3 (2, 4) envelope_7), (placed21 1 (2, 4) envelope_11), (placed21 2 (6, 1) envelope_331)]
theorem common_sub_636_i6 : commonEnvelope childrenD_636_i6 ⊆ insert (6, 4) required_636_i6 := by decide +kernel
theorem child_required_sub_636_i6 : ∀ j, childrenC_636_i6 j ⊆ insert (6, 4) required_636_i6 := by decide +kernel
theorem child_envelope_sub_636_i6 : ∀ j, childrenD_636_i6 j ⊆ envelope_636_i6 := by decide +kernel
theorem pivot_mem_636_i6 : (6, 4) ∈ envelope_636_i6 := by decide +kernel
theorem children_work_636_i6 : ∀ j, Template HasSnaky 6 (childrenC_636_i6 j) (childrenD_636_i6 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 3 (2, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_11 1 (2, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_331 2 (6, 1)).mono (by decide +kernel)
theorem row_works_636_i6 : Template HasSnaky 7 required_636_i6 envelope_636_i6 := by
  refine compose HasSnaky 6 childrenC_636_i6 childrenD_636_i6 children_work_636_i6 (6, 4)
    required_636_i6 envelope_636_i6 pivot_mem_636_i6 child_required_sub_636_i6 child_envelope_sub_636_i6 ?_
  intro b hb
  exact common_sub_636_i6 (mem_commonEnvelope childrenD_636_i6 b hb)
def required_636_i3 : Finset Cell := ⟨(([(1, 5), (3, 4), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_636_i3 : Finset Cell := ⟨(([(1, 5), (2, 3), (2, 5), (2, 6), (2, 7), (2, 8), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (8, 3), (8, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_636_i3 : Fin 5 → Finset Cell := ![(placed21 0 (2, 1) required_332), (placed21 4 (2, 6) required_474), (placed21 0 (2, 2) required_522), required_636_i4, required_636_i6]
def childrenD_636_i3 : Fin 5 → Finset Cell := ![(placed21 0 (2, 1) envelope_332), (placed21 4 (2, 6) envelope_474), (placed21 0 (2, 2) envelope_522), envelope_636_i4, envelope_636_i6]
theorem common_sub_636_i3 : commonEnvelope childrenD_636_i3 ⊆ insert (5, 4) required_636_i3 := by decide +kernel
theorem child_required_sub_636_i3 : ∀ j, childrenC_636_i3 j ⊆ insert (5, 4) required_636_i3 := by decide +kernel
theorem child_envelope_sub_636_i3 : ∀ j, childrenD_636_i3 j ⊆ envelope_636_i3 := by decide +kernel
theorem pivot_mem_636_i3 : (5, 4) ∈ envelope_636_i3 := by decide +kernel
theorem children_work_636_i3 : ∀ j, Template HasSnaky 9 (childrenC_636_i3 j) (childrenD_636_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_332 0 (2, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_474 4 (2, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_522 0 (2, 2)).mono (by decide +kernel)
  · exact row_works_636_i4.mono (by decide +kernel)
  · exact row_works_636_i6.mono (by decide +kernel)
theorem row_works_636_i3 : Template HasSnaky 10 required_636_i3 envelope_636_i3 := by
  refine compose HasSnaky 9 childrenC_636_i3 childrenD_636_i3 children_work_636_i3 (5, 4)
    required_636_i3 envelope_636_i3 pivot_mem_636_i3 child_required_sub_636_i3 child_envelope_sub_636_i3 ?_
  intro b hb
  exact common_sub_636_i3 (mem_commonEnvelope childrenD_636_i3 b hb)
def required_636_i0 : Finset Cell := ⟨(([(1, 5), (3, 4), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_636_i0 : Finset Cell := ⟨(([(0, 5), (1, 5), (1, 7), (2, 3), (2, 5), (2, 6), (2, 7), (2, 8), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_636_i0 : Fin 9 → Finset Cell := ![(placed21 4 (2, 8) required_399), (placed21 0 (3, 1) required_408), (placed21 4 (2, 8) required_475), (placed21 1 (1, 2) required_509), (placed21 0 (2, 1) required_587), required_636_i1, (placed21 4 (2, 9) required_635), required_636_i2, required_636_i3]
def childrenD_636_i0 : Fin 9 → Finset Cell := ![(placed21 4 (2, 8) envelope_399), (placed21 0 (3, 1) envelope_408), (placed21 4 (2, 8) envelope_475), (placed21 1 (1, 2) envelope_509), (placed21 0 (2, 1) envelope_587), envelope_636_i1, (placed21 4 (2, 9) envelope_635), envelope_636_i2, envelope_636_i3]
theorem common_sub_636_i0 : commonEnvelope childrenD_636_i0 ⊆ insert (4, 5) required_636_i0 := by decide +kernel
theorem child_required_sub_636_i0 : ∀ j, childrenC_636_i0 j ⊆ insert (4, 5) required_636_i0 := by decide +kernel
theorem child_envelope_sub_636_i0 : ∀ j, childrenD_636_i0 j ⊆ envelope_636_i0 := by decide +kernel
theorem pivot_mem_636_i0 : (4, 5) ∈ envelope_636_i0 := by decide +kernel
theorem children_work_636_i0 : ∀ j, Template HasSnaky 12 (childrenC_636_i0 j) (childrenD_636_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_399 4 (2, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_408 0 (3, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_475 4 (2, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_509 1 (1, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_587 0 (2, 1)).mono (by decide +kernel)
  · exact row_works_636_i1.mono (by decide +kernel)
  · exact (placed21_template row_works_635 4 (2, 9)).mono (by decide +kernel)
  · exact row_works_636_i2.mono (by decide +kernel)
  · exact row_works_636_i3.mono (by decide +kernel)
theorem row_works_636_i0 : Template HasSnaky 13 required_636_i0 envelope_636_i0 := by
  refine compose HasSnaky 12 childrenC_636_i0 childrenD_636_i0 children_work_636_i0 (4, 5)
    required_636_i0 envelope_636_i0 pivot_mem_636_i0 child_required_sub_636_i0 child_envelope_sub_636_i0 ?_
  intro b hb
  exact common_sub_636_i0 (mem_commonEnvelope childrenD_636_i0 b hb)
def required_636_i7 : Finset Cell := ⟨(([(3, 4), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_636_i7 : Finset Cell := ⟨(([(0, 3), (1, 3), (1, 4), (2, 3), (2, 4), (3, 3), (3, 4), (3, 5), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (8, 3), (8, 4), (8, 5), (8, 6), (9, 3), (9, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_636_i7 : Fin 6 → Finset Cell := ![(placed21 0 (2, 1) required_118), (placed21 1 (1, 2) required_188), (placed21 3 (1, 6) required_188), (placed21 1 (1, 3) required_192), (placed21 1 (1, 3) required_193), (placed21 5 (8, 2) required_396)]
def childrenD_636_i7 : Fin 6 → Finset Cell := ![(placed21 0 (2, 1) envelope_118), (placed21 1 (1, 2) envelope_188), (placed21 3 (1, 6) envelope_188), (placed21 1 (1, 3) envelope_192), (placed21 1 (1, 3) envelope_193), (placed21 5 (8, 2) envelope_396)]
theorem common_sub_636_i7 : commonEnvelope childrenD_636_i7 ⊆ insert (5, 4) required_636_i7 := by decide +kernel
theorem child_required_sub_636_i7 : ∀ j, childrenC_636_i7 j ⊆ insert (5, 4) required_636_i7 := by decide +kernel
theorem child_envelope_sub_636_i7 : ∀ j, childrenD_636_i7 j ⊆ envelope_636_i7 := by decide +kernel
theorem pivot_mem_636_i7 : (5, 4) ∈ envelope_636_i7 := by decide +kernel
theorem children_work_636_i7 : ∀ j, Template HasSnaky 9 (childrenC_636_i7 j) (childrenD_636_i7 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_118 0 (2, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_188 1 (1, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_188 3 (1, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_192 1 (1, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_193 1 (1, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_396 5 (8, 2)).mono (by decide +kernel)
theorem row_works_636_i7 : Template HasSnaky 10 required_636_i7 envelope_636_i7 := by
  refine compose HasSnaky 9 childrenC_636_i7 childrenD_636_i7 children_work_636_i7 (5, 4)
    required_636_i7 envelope_636_i7 pivot_mem_636_i7 child_required_sub_636_i7 child_envelope_sub_636_i7 ?_
  intro b hb
  exact common_sub_636_i7 (mem_commonEnvelope childrenD_636_i7 b hb)
def required_636 : Finset Cell := ⟨(([(1, 4), (1, 5), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_636 : Finset Cell := ⟨(([(0, 3), (0, 5), (1, 3), (1, 4), (1, 5), (1, 7), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (9, 3), (9, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_636 : Fin 4 → Finset Cell := ![(placed21 3 (0, 5) required_125), (placed21 5 (5, 3) required_454), required_636_i0, required_636_i7]
def childrenD_636 : Fin 4 → Finset Cell := ![(placed21 3 (0, 5) envelope_125), (placed21 5 (5, 3) envelope_454), envelope_636_i0, envelope_636_i7]
theorem common_sub_636 : commonEnvelope childrenD_636 ⊆ insert (3, 4) required_636 := by decide +kernel
theorem child_required_sub_636 : ∀ j, childrenC_636 j ⊆ insert (3, 4) required_636 := by decide +kernel
theorem child_envelope_sub_636 : ∀ j, childrenD_636 j ⊆ envelope_636 := by decide +kernel
theorem pivot_mem_636 : (3, 4) ∈ envelope_636 := by decide +kernel
theorem children_work_636 : ∀ j, Template HasSnaky 13 (childrenC_636 j) (childrenD_636 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_125 3 (0, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_454 5 (5, 3)).mono (by decide +kernel)
  · exact row_works_636_i0.mono (by decide +kernel)
  · exact row_works_636_i7.mono (by decide +kernel)
theorem row_works_636 : Template HasSnaky 14 required_636 envelope_636 := by
  refine compose HasSnaky 13 childrenC_636 childrenD_636 children_work_636 (3, 4)
    required_636 envelope_636 pivot_mem_636 child_required_sub_636 child_envelope_sub_636 ?_
  intro b hb
  exact common_sub_636 (mem_commonEnvelope childrenD_636 b hb)
def required_644_i1 : Finset Cell := ⟨(([(4, 4), (4, 5), (6, 4), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_644_i1 : Finset Cell := ⟨(([(1, 4), (1, 6), (2, 1), (2, 3), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 1), (4, 2), (4, 4), (4, 5), (5, 0), (5, 1), (5, 2), (5, 3), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 6), (7, 7), (7, 8), (7, 9), (8, 1), (8, 2), (8, 3), (8, 6), (9, 1), (9, 2), (9, 3), (9, 6), (10, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_644_i1 : Fin 3 → Finset Cell := ![(placed21 5 (7, 4) required_10), (placed21 0 (3, 1) required_317), (placed21 4 (2, 8) required_640)]
def childrenD_644_i1 : Fin 3 → Finset Cell := ![(placed21 5 (7, 4) envelope_10), (placed21 0 (3, 1) envelope_317), (placed21 4 (2, 8) envelope_640)]
theorem common_sub_644_i1 : commonEnvelope childrenD_644_i1 ⊆ insert (5, 5) required_644_i1 := by decide +kernel
theorem child_required_sub_644_i1 : ∀ j, childrenC_644_i1 j ⊆ insert (5, 5) required_644_i1 := by decide +kernel
theorem child_envelope_sub_644_i1 : ∀ j, childrenD_644_i1 j ⊆ envelope_644_i1 := by decide +kernel
theorem pivot_mem_644_i1 : (5, 5) ∈ envelope_644_i1 := by decide +kernel
theorem children_work_644_i1 : ∀ j, Template HasSnaky 9 (childrenC_644_i1 j) (childrenD_644_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_10 5 (7, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_317 0 (3, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_640 4 (2, 8)).mono (by decide +kernel)
theorem row_works_644_i1 : Template HasSnaky 10 required_644_i1 envelope_644_i1 := by
  refine compose HasSnaky 9 childrenC_644_i1 childrenD_644_i1 children_work_644_i1 (5, 5)
    required_644_i1 envelope_644_i1 pivot_mem_644_i1 child_required_sub_644_i1 child_envelope_sub_644_i1 ?_
  intro b hb
  exact common_sub_644_i1 (mem_commonEnvelope childrenD_644_i1 b hb)
def required_644_i0 : Finset Cell := ⟨(([(4, 4), (4, 5), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_644_i0 : Finset Cell := ⟨(([(1, 4), (1, 6), (2, 1), (2, 3), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 1), (4, 2), (4, 4), (4, 5), (4, 6), (5, 0), (5, 1), (5, 2), (5, 3), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (10, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_644_i0 : Fin 6 → Finset Cell := ![(placed21 1 (1, 4) required_104), (placed21 1 (1, 4) required_359), (placed21 0 (1, 1) required_452), (placed21 4 (3, 8) required_476), (placed21 0 (3, 1) required_479), required_644_i1]
def childrenD_644_i0 : Fin 6 → Finset Cell := ![(placed21 1 (1, 4) envelope_104), (placed21 1 (1, 4) envelope_359), (placed21 0 (1, 1) envelope_452), (placed21 4 (3, 8) envelope_476), (placed21 0 (3, 1) envelope_479), envelope_644_i1]
theorem common_sub_644_i0 : commonEnvelope childrenD_644_i0 ⊆ insert (6, 5) required_644_i0 := by decide +kernel
theorem child_required_sub_644_i0 : ∀ j, childrenC_644_i0 j ⊆ insert (6, 5) required_644_i0 := by decide +kernel
theorem child_envelope_sub_644_i0 : ∀ j, childrenD_644_i0 j ⊆ envelope_644_i0 := by decide +kernel
theorem pivot_mem_644_i0 : (6, 5) ∈ envelope_644_i0 := by decide +kernel
theorem children_work_644_i0 : ∀ j, Template HasSnaky 10 (childrenC_644_i0 j) (childrenD_644_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_104 1 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_359 1 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_452 0 (1, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_476 4 (3, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_479 0 (3, 1)).mono (by decide +kernel)
  · exact row_works_644_i1.mono (by decide +kernel)
theorem row_works_644_i0 : Template HasSnaky 11 required_644_i0 envelope_644_i0 := by
  refine compose HasSnaky 10 childrenC_644_i0 childrenD_644_i0 children_work_644_i0 (6, 5)
    required_644_i0 envelope_644_i0 pivot_mem_644_i0 child_required_sub_644_i0 child_envelope_sub_644_i0 ?_
  intro b hb
  exact common_sub_644_i0 (mem_commonEnvelope childrenD_644_i0 b hb)
def required_644 : Finset Cell := ⟨(([(4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_644 : Finset Cell := ⟨(([(0, 5), (1, 3), (1, 4), (1, 5), (1, 6), (2, 1), (2, 3), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 1), (4, 2), (4, 4), (4, 5), (4, 6), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (10, 1), (10, 3), (10, 4), (10, 5), (11, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_644 : Fin 9 → Finset Cell := ![(placed21 6 (7, 7) required_120), (placed21 3 (1, 6) required_338), (placed21 3 (1, 7) required_437), (placed21 3 (0, 6) required_611), (placed21 1 (1, 3) required_613), (placed21 0 (1, 0) required_634), required_644_i0, (placed21 0 (3, 0) required_642), (placed21 0 (3, 0) required_643)]
def childrenD_644 : Fin 9 → Finset Cell := ![(placed21 6 (7, 7) envelope_120), (placed21 3 (1, 6) envelope_338), (placed21 3 (1, 7) envelope_437), (placed21 3 (0, 6) envelope_611), (placed21 1 (1, 3) envelope_613), (placed21 0 (1, 0) envelope_634), envelope_644_i0, (placed21 0 (3, 0) envelope_642), (placed21 0 (3, 0) envelope_643)]
theorem common_sub_644 : commonEnvelope childrenD_644 ⊆ insert (6, 4) required_644 := by decide +kernel
theorem child_required_sub_644 : ∀ j, childrenC_644 j ⊆ insert (6, 4) required_644 := by decide +kernel
theorem child_envelope_sub_644 : ∀ j, childrenD_644 j ⊆ envelope_644 := by decide +kernel
theorem pivot_mem_644 : (6, 4) ∈ envelope_644 := by decide +kernel
theorem children_work_644 : ∀ j, Template HasSnaky 13 (childrenC_644 j) (childrenD_644 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_120 6 (7, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_338 3 (1, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_437 3 (1, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_611 3 (0, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_613 1 (1, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_634 0 (1, 0)).mono (by decide +kernel)
  · exact row_works_644_i0.mono (by decide +kernel)
  · exact (placed21_template row_works_642 0 (3, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_643 0 (3, 0)).mono (by decide +kernel)
theorem row_works_644 : Template HasSnaky 14 required_644 envelope_644 := by
  refine compose HasSnaky 13 childrenC_644 childrenD_644 children_work_644 (6, 4)
    required_644 envelope_644 pivot_mem_644 child_required_sub_644 child_envelope_sub_644 ?_
  intro b hb
  exact common_sub_644 (mem_commonEnvelope childrenD_644 b hb)
def height_598_i2 : ℕ := 6
def childrenH_598_i2 : Fin 2 → ℕ := ![height_5, height_133]
theorem height_exact_598_i2 : height_598_i2 = 1 + Finset.univ.sup childrenH_598_i2 := by decide +kernel
theorem required_origin_598_i2 : ∀ x ∈ required_598_i2,
    (∃ j, x ∈ childrenC_598_i2 j) ∨ ∀ j, x ∈ childrenD_598_i2 j := by decide +kernel
theorem required_exact_598_i2 : required_598_i2 =
    ((Finset.univ.biUnion childrenC_598_i2) ∪ commonEnvelope childrenD_598_i2).erase (5, 5) := by
  exact required_eq_combination childrenC_598_i2 childrenD_598_i2 (5, 5) required_598_i2
    (by decide +kernel) child_required_sub_598_i2 common_sub_598_i2 required_origin_598_i2
theorem envelope_origin_598_i2 : ∀ x ∈ envelope_598_i2,
    x = (5, 5) ∨ ∃ j, x ∈ childrenD_598_i2 j := by decide +kernel
theorem envelope_exact_598_i2 : envelope_598_i2 =
    insert (5, 5) (Finset.univ.biUnion childrenD_598_i2) := by
  exact envelope_eq_combination childrenD_598_i2 (5, 5) envelope_598_i2
    pivot_mem_598_i2 child_envelope_sub_598_i2 envelope_origin_598_i2
def checked_598_i2 : CheckedCard where
  required := required_598_i2
  envelope := envelope_598_i2
  height := height_598_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_598_i2
def height_598_i1 : ℕ := 7
def childrenH_598_i1 : Fin 2 → ℕ := ![height_0, height_598_i2]
theorem height_exact_598_i1 : height_598_i1 = 1 + Finset.univ.sup childrenH_598_i1 := by decide +kernel
theorem required_origin_598_i1 : ∀ x ∈ required_598_i1,
    (∃ j, x ∈ childrenC_598_i1 j) ∨ ∀ j, x ∈ childrenD_598_i1 j := by decide +kernel
theorem required_exact_598_i1 : required_598_i1 =
    ((Finset.univ.biUnion childrenC_598_i1) ∪ commonEnvelope childrenD_598_i1).erase (4, 5) := by
  exact required_eq_combination childrenC_598_i1 childrenD_598_i1 (4, 5) required_598_i1
    (by decide +kernel) child_required_sub_598_i1 common_sub_598_i1 required_origin_598_i1
theorem envelope_origin_598_i1 : ∀ x ∈ envelope_598_i1,
    x = (4, 5) ∨ ∃ j, x ∈ childrenD_598_i1 j := by decide +kernel
theorem envelope_exact_598_i1 : envelope_598_i1 =
    insert (4, 5) (Finset.univ.biUnion childrenD_598_i1) := by
  exact envelope_eq_combination childrenD_598_i1 (4, 5) envelope_598_i1
    pivot_mem_598_i1 child_envelope_sub_598_i1 envelope_origin_598_i1
def checked_598_i1 : CheckedCard where
  required := required_598_i1
  envelope := envelope_598_i1
  height := height_598_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_598_i1
def height_598_i0 : ℕ := 8
def childrenH_598_i0 : Fin 2 → ℕ := ![height_5, height_598_i1]
theorem height_exact_598_i0 : height_598_i0 = 1 + Finset.univ.sup childrenH_598_i0 := by decide +kernel
theorem required_origin_598_i0 : ∀ x ∈ required_598_i0,
    (∃ j, x ∈ childrenC_598_i0 j) ∨ ∀ j, x ∈ childrenD_598_i0 j := by decide +kernel
theorem required_exact_598_i0 : required_598_i0 =
    ((Finset.univ.biUnion childrenC_598_i0) ∪ commonEnvelope childrenD_598_i0).erase (3, 6) := by
  exact required_eq_combination childrenC_598_i0 childrenD_598_i0 (3, 6) required_598_i0
    (by decide +kernel) child_required_sub_598_i0 common_sub_598_i0 required_origin_598_i0
theorem envelope_origin_598_i0 : ∀ x ∈ envelope_598_i0,
    x = (3, 6) ∨ ∃ j, x ∈ childrenD_598_i0 j := by decide +kernel
theorem envelope_exact_598_i0 : envelope_598_i0 =
    insert (3, 6) (Finset.univ.biUnion childrenD_598_i0) := by
  exact envelope_eq_combination childrenD_598_i0 (3, 6) envelope_598_i0
    pivot_mem_598_i0 child_envelope_sub_598_i0 envelope_origin_598_i0
def checked_598_i0 : CheckedCard where
  required := required_598_i0
  envelope := envelope_598_i0
  height := height_598_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_598_i0
def height_598_i5 : ℕ := 6
def childrenH_598_i5 : Fin 2 → ℕ := ![height_5, height_133]
theorem height_exact_598_i5 : height_598_i5 = 1 + Finset.univ.sup childrenH_598_i5 := by decide +kernel
theorem required_origin_598_i5 : ∀ x ∈ required_598_i5,
    (∃ j, x ∈ childrenC_598_i5 j) ∨ ∀ j, x ∈ childrenD_598_i5 j := by decide +kernel
theorem required_exact_598_i5 : required_598_i5 =
    ((Finset.univ.biUnion childrenC_598_i5) ∪ commonEnvelope childrenD_598_i5).erase (5, 5) := by
  exact required_eq_combination childrenC_598_i5 childrenD_598_i5 (5, 5) required_598_i5
    (by decide +kernel) child_required_sub_598_i5 common_sub_598_i5 required_origin_598_i5
theorem envelope_origin_598_i5 : ∀ x ∈ envelope_598_i5,
    x = (5, 5) ∨ ∃ j, x ∈ childrenD_598_i5 j := by decide +kernel
theorem envelope_exact_598_i5 : envelope_598_i5 =
    insert (5, 5) (Finset.univ.biUnion childrenD_598_i5) := by
  exact envelope_eq_combination childrenD_598_i5 (5, 5) envelope_598_i5
    pivot_mem_598_i5 child_envelope_sub_598_i5 envelope_origin_598_i5
def checked_598_i5 : CheckedCard where
  required := required_598_i5
  envelope := envelope_598_i5
  height := height_598_i5
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_598_i5
def height_598_i4 : ℕ := 7
def childrenH_598_i4 : Fin 2 → ℕ := ![height_0, height_598_i5]
theorem height_exact_598_i4 : height_598_i4 = 1 + Finset.univ.sup childrenH_598_i4 := by decide +kernel
theorem required_origin_598_i4 : ∀ x ∈ required_598_i4,
    (∃ j, x ∈ childrenC_598_i4 j) ∨ ∀ j, x ∈ childrenD_598_i4 j := by decide +kernel
theorem required_exact_598_i4 : required_598_i4 =
    ((Finset.univ.biUnion childrenC_598_i4) ∪ commonEnvelope childrenD_598_i4).erase (4, 5) := by
  exact required_eq_combination childrenC_598_i4 childrenD_598_i4 (4, 5) required_598_i4
    (by decide +kernel) child_required_sub_598_i4 common_sub_598_i4 required_origin_598_i4
theorem envelope_origin_598_i4 : ∀ x ∈ envelope_598_i4,
    x = (4, 5) ∨ ∃ j, x ∈ childrenD_598_i4 j := by decide +kernel
theorem envelope_exact_598_i4 : envelope_598_i4 =
    insert (4, 5) (Finset.univ.biUnion childrenD_598_i4) := by
  exact envelope_eq_combination childrenD_598_i4 (4, 5) envelope_598_i4
    pivot_mem_598_i4 child_envelope_sub_598_i4 envelope_origin_598_i4
def checked_598_i4 : CheckedCard where
  required := required_598_i4
  envelope := envelope_598_i4
  height := height_598_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_598_i4
def height_598_i3 : ℕ := 8
def childrenH_598_i3 : Fin 2 → ℕ := ![height_5, height_598_i4]
theorem height_exact_598_i3 : height_598_i3 = 1 + Finset.univ.sup childrenH_598_i3 := by decide +kernel
theorem required_origin_598_i3 : ∀ x ∈ required_598_i3,
    (∃ j, x ∈ childrenC_598_i3 j) ∨ ∀ j, x ∈ childrenD_598_i3 j := by decide +kernel
theorem required_exact_598_i3 : required_598_i3 =
    ((Finset.univ.biUnion childrenC_598_i3) ∪ commonEnvelope childrenD_598_i3).erase (3, 6) := by
  exact required_eq_combination childrenC_598_i3 childrenD_598_i3 (3, 6) required_598_i3
    (by decide +kernel) child_required_sub_598_i3 common_sub_598_i3 required_origin_598_i3
theorem envelope_origin_598_i3 : ∀ x ∈ envelope_598_i3,
    x = (3, 6) ∨ ∃ j, x ∈ childrenD_598_i3 j := by decide +kernel
theorem envelope_exact_598_i3 : envelope_598_i3 =
    insert (3, 6) (Finset.univ.biUnion childrenD_598_i3) := by
  exact envelope_eq_combination childrenD_598_i3 (3, 6) envelope_598_i3
    pivot_mem_598_i3 child_envelope_sub_598_i3 envelope_origin_598_i3
def checked_598_i3 : CheckedCard where
  required := required_598_i3
  envelope := envelope_598_i3
  height := height_598_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_598_i3
def height_598_i8 : ℕ := 6
def childrenH_598_i8 : Fin 2 → ℕ := ![height_5, height_413]
theorem height_exact_598_i8 : height_598_i8 = 1 + Finset.univ.sup childrenH_598_i8 := by decide +kernel
theorem required_origin_598_i8 : ∀ x ∈ required_598_i8,
    (∃ j, x ∈ childrenC_598_i8 j) ∨ ∀ j, x ∈ childrenD_598_i8 j := by decide +kernel
theorem required_exact_598_i8 : required_598_i8 =
    ((Finset.univ.biUnion childrenC_598_i8) ∪ commonEnvelope childrenD_598_i8).erase (5, 5) := by
  exact required_eq_combination childrenC_598_i8 childrenD_598_i8 (5, 5) required_598_i8
    (by decide +kernel) child_required_sub_598_i8 common_sub_598_i8 required_origin_598_i8
theorem envelope_origin_598_i8 : ∀ x ∈ envelope_598_i8,
    x = (5, 5) ∨ ∃ j, x ∈ childrenD_598_i8 j := by decide +kernel
theorem envelope_exact_598_i8 : envelope_598_i8 =
    insert (5, 5) (Finset.univ.biUnion childrenD_598_i8) := by
  exact envelope_eq_combination childrenD_598_i8 (5, 5) envelope_598_i8
    pivot_mem_598_i8 child_envelope_sub_598_i8 envelope_origin_598_i8
def checked_598_i8 : CheckedCard where
  required := required_598_i8
  envelope := envelope_598_i8
  height := height_598_i8
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_598_i8
def height_598_i7 : ℕ := 7
def childrenH_598_i7 : Fin 2 → ℕ := ![height_0, height_598_i8]
theorem height_exact_598_i7 : height_598_i7 = 1 + Finset.univ.sup childrenH_598_i7 := by decide +kernel
theorem required_origin_598_i7 : ∀ x ∈ required_598_i7,
    (∃ j, x ∈ childrenC_598_i7 j) ∨ ∀ j, x ∈ childrenD_598_i7 j := by decide +kernel
theorem required_exact_598_i7 : required_598_i7 =
    ((Finset.univ.biUnion childrenC_598_i7) ∪ commonEnvelope childrenD_598_i7).erase (4, 5) := by
  exact required_eq_combination childrenC_598_i7 childrenD_598_i7 (4, 5) required_598_i7
    (by decide +kernel) child_required_sub_598_i7 common_sub_598_i7 required_origin_598_i7
theorem envelope_origin_598_i7 : ∀ x ∈ envelope_598_i7,
    x = (4, 5) ∨ ∃ j, x ∈ childrenD_598_i7 j := by decide +kernel
theorem envelope_exact_598_i7 : envelope_598_i7 =
    insert (4, 5) (Finset.univ.biUnion childrenD_598_i7) := by
  exact envelope_eq_combination childrenD_598_i7 (4, 5) envelope_598_i7
    pivot_mem_598_i7 child_envelope_sub_598_i7 envelope_origin_598_i7
def checked_598_i7 : CheckedCard where
  required := required_598_i7
  envelope := envelope_598_i7
  height := height_598_i7
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_598_i7
def height_598_i6 : ℕ := 8
def childrenH_598_i6 : Fin 2 → ℕ := ![height_5, height_598_i7]
theorem height_exact_598_i6 : height_598_i6 = 1 + Finset.univ.sup childrenH_598_i6 := by decide +kernel
theorem required_origin_598_i6 : ∀ x ∈ required_598_i6,
    (∃ j, x ∈ childrenC_598_i6 j) ∨ ∀ j, x ∈ childrenD_598_i6 j := by decide +kernel
theorem required_exact_598_i6 : required_598_i6 =
    ((Finset.univ.biUnion childrenC_598_i6) ∪ commonEnvelope childrenD_598_i6).erase (3, 6) := by
  exact required_eq_combination childrenC_598_i6 childrenD_598_i6 (3, 6) required_598_i6
    (by decide +kernel) child_required_sub_598_i6 common_sub_598_i6 required_origin_598_i6
theorem envelope_origin_598_i6 : ∀ x ∈ envelope_598_i6,
    x = (3, 6) ∨ ∃ j, x ∈ childrenD_598_i6 j := by decide +kernel
theorem envelope_exact_598_i6 : envelope_598_i6 =
    insert (3, 6) (Finset.univ.biUnion childrenD_598_i6) := by
  exact envelope_eq_combination childrenD_598_i6 (3, 6) envelope_598_i6
    pivot_mem_598_i6 child_envelope_sub_598_i6 envelope_origin_598_i6
def checked_598_i6 : CheckedCard where
  required := required_598_i6
  envelope := envelope_598_i6
  height := height_598_i6
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_598_i6
def height_598 : ℕ := 14
def childrenH_598 : Fin 7 → ℕ := ![height_598_i0, height_598_i3, height_584, height_591, height_594, height_598_i6, height_597]
theorem height_exact_598 : height_598 = 1 + Finset.univ.sup childrenH_598 := by decide +kernel
theorem required_origin_598 : ∀ x ∈ required_598,
    (∃ j, x ∈ childrenC_598 j) ∨ ∀ j, x ∈ childrenD_598 j := by decide +kernel
theorem required_exact_598 : required_598 =
    ((Finset.univ.biUnion childrenC_598) ∪ commonEnvelope childrenD_598).erase (3, 5) := by
  exact required_eq_combination childrenC_598 childrenD_598 (3, 5) required_598
    (by decide +kernel) child_required_sub_598 common_sub_598 required_origin_598
theorem envelope_origin_598 : ∀ x ∈ envelope_598,
    x = (3, 5) ∨ ∃ j, x ∈ childrenD_598 j := by decide +kernel
theorem envelope_exact_598 : envelope_598 =
    insert (3, 5) (Finset.univ.biUnion childrenD_598) := by
  exact envelope_eq_combination childrenD_598 (3, 5) envelope_598
    pivot_mem_598 child_envelope_sub_598 envelope_origin_598
def checked_598 : CheckedCard where
  required := required_598
  envelope := envelope_598
  height := height_598
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_598
def height_636_i1 : ℕ := 10
def childrenH_636_i1 : Fin 3 → ℕ := ![height_22, height_108, height_512]
theorem height_exact_636_i1 : height_636_i1 = 1 + Finset.univ.sup childrenH_636_i1 := by decide +kernel
theorem required_origin_636_i1 : ∀ x ∈ required_636_i1,
    (∃ j, x ∈ childrenC_636_i1 j) ∨ ∀ j, x ∈ childrenD_636_i1 j := by decide +kernel
theorem required_exact_636_i1 : required_636_i1 =
    ((Finset.univ.biUnion childrenC_636_i1) ∪ commonEnvelope childrenD_636_i1).erase (3, 5) := by
  exact required_eq_combination childrenC_636_i1 childrenD_636_i1 (3, 5) required_636_i1
    (by decide +kernel) child_required_sub_636_i1 common_sub_636_i1 required_origin_636_i1
theorem envelope_origin_636_i1 : ∀ x ∈ envelope_636_i1,
    x = (3, 5) ∨ ∃ j, x ∈ childrenD_636_i1 j := by decide +kernel
theorem envelope_exact_636_i1 : envelope_636_i1 =
    insert (3, 5) (Finset.univ.biUnion childrenD_636_i1) := by
  exact envelope_eq_combination childrenD_636_i1 (3, 5) envelope_636_i1
    pivot_mem_636_i1 child_envelope_sub_636_i1 envelope_origin_636_i1
def checked_636_i1 : CheckedCard where
  required := required_636_i1
  envelope := envelope_636_i1
  height := height_636_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_636_i1
def height_636_i2 : ℕ := 8
def childrenH_636_i2 : Fin 4 → ℕ := ![height_10, height_44, height_63, height_117]
theorem height_exact_636_i2 : height_636_i2 = 1 + Finset.univ.sup childrenH_636_i2 := by decide +kernel
theorem required_origin_636_i2 : ∀ x ∈ required_636_i2,
    (∃ j, x ∈ childrenC_636_i2 j) ∨ ∀ j, x ∈ childrenD_636_i2 j := by decide +kernel
theorem required_exact_636_i2 : required_636_i2 =
    ((Finset.univ.biUnion childrenC_636_i2) ∪ commonEnvelope childrenD_636_i2).erase (4, 6) := by
  exact required_eq_combination childrenC_636_i2 childrenD_636_i2 (4, 6) required_636_i2
    (by decide +kernel) child_required_sub_636_i2 common_sub_636_i2 required_origin_636_i2
theorem envelope_origin_636_i2 : ∀ x ∈ envelope_636_i2,
    x = (4, 6) ∨ ∃ j, x ∈ childrenD_636_i2 j := by decide +kernel
theorem envelope_exact_636_i2 : envelope_636_i2 =
    insert (4, 6) (Finset.univ.biUnion childrenD_636_i2) := by
  exact envelope_eq_combination childrenD_636_i2 (4, 6) envelope_636_i2
    pivot_mem_636_i2 child_envelope_sub_636_i2 envelope_origin_636_i2
def checked_636_i2 : CheckedCard where
  required := required_636_i2
  envelope := envelope_636_i2
  height := height_636_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_636_i2
def height_636_i5 : ℕ := 7
def childrenH_636_i5 : Fin 3 → ℕ := ![height_85, height_164, height_262]
theorem height_exact_636_i5 : height_636_i5 = 1 + Finset.univ.sup childrenH_636_i5 := by decide +kernel
theorem required_origin_636_i5 : ∀ x ∈ required_636_i5,
    (∃ j, x ∈ childrenC_636_i5 j) ∨ ∀ j, x ∈ childrenD_636_i5 j := by decide +kernel
theorem required_exact_636_i5 : required_636_i5 =
    ((Finset.univ.biUnion childrenC_636_i5) ∪ commonEnvelope childrenD_636_i5).erase (5, 5) := by
  exact required_eq_combination childrenC_636_i5 childrenD_636_i5 (5, 5) required_636_i5
    (by decide +kernel) child_required_sub_636_i5 common_sub_636_i5 required_origin_636_i5
theorem envelope_origin_636_i5 : ∀ x ∈ envelope_636_i5,
    x = (5, 5) ∨ ∃ j, x ∈ childrenD_636_i5 j := by decide +kernel
theorem envelope_exact_636_i5 : envelope_636_i5 =
    insert (5, 5) (Finset.univ.biUnion childrenD_636_i5) := by
  exact envelope_eq_combination childrenD_636_i5 (5, 5) envelope_636_i5
    pivot_mem_636_i5 child_envelope_sub_636_i5 envelope_origin_636_i5
def checked_636_i5 : CheckedCard where
  required := required_636_i5
  envelope := envelope_636_i5
  height := height_636_i5
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_636_i5
def height_636_i4 : ℕ := 8
def childrenH_636_i4 : Fin 2 → ℕ := ![height_1, height_636_i5]
theorem height_exact_636_i4 : height_636_i4 = 1 + Finset.univ.sup childrenH_636_i4 := by decide +kernel
theorem required_origin_636_i4 : ∀ x ∈ required_636_i4,
    (∃ j, x ∈ childrenC_636_i4 j) ∨ ∀ j, x ∈ childrenD_636_i4 j := by decide +kernel
theorem required_exact_636_i4 : required_636_i4 =
    ((Finset.univ.biUnion childrenC_636_i4) ∪ commonEnvelope childrenD_636_i4).erase (3, 5) := by
  exact required_eq_combination childrenC_636_i4 childrenD_636_i4 (3, 5) required_636_i4
    (by decide +kernel) child_required_sub_636_i4 common_sub_636_i4 required_origin_636_i4
theorem envelope_origin_636_i4 : ∀ x ∈ envelope_636_i4,
    x = (3, 5) ∨ ∃ j, x ∈ childrenD_636_i4 j := by decide +kernel
theorem envelope_exact_636_i4 : envelope_636_i4 =
    insert (3, 5) (Finset.univ.biUnion childrenD_636_i4) := by
  exact envelope_eq_combination childrenD_636_i4 (3, 5) envelope_636_i4
    pivot_mem_636_i4 child_envelope_sub_636_i4 envelope_origin_636_i4
def checked_636_i4 : CheckedCard where
  required := required_636_i4
  envelope := envelope_636_i4
  height := height_636_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_636_i4
def height_636_i6 : ℕ := 7
def childrenH_636_i6 : Fin 3 → ℕ := ![height_7, height_11, height_331]
theorem height_exact_636_i6 : height_636_i6 = 1 + Finset.univ.sup childrenH_636_i6 := by decide +kernel
theorem required_origin_636_i6 : ∀ x ∈ required_636_i6,
    (∃ j, x ∈ childrenC_636_i6 j) ∨ ∀ j, x ∈ childrenD_636_i6 j := by decide +kernel
theorem required_exact_636_i6 : required_636_i6 =
    ((Finset.univ.biUnion childrenC_636_i6) ∪ commonEnvelope childrenD_636_i6).erase (6, 4) := by
  exact required_eq_combination childrenC_636_i6 childrenD_636_i6 (6, 4) required_636_i6
    (by decide +kernel) child_required_sub_636_i6 common_sub_636_i6 required_origin_636_i6
theorem envelope_origin_636_i6 : ∀ x ∈ envelope_636_i6,
    x = (6, 4) ∨ ∃ j, x ∈ childrenD_636_i6 j := by decide +kernel
theorem envelope_exact_636_i6 : envelope_636_i6 =
    insert (6, 4) (Finset.univ.biUnion childrenD_636_i6) := by
  exact envelope_eq_combination childrenD_636_i6 (6, 4) envelope_636_i6
    pivot_mem_636_i6 child_envelope_sub_636_i6 envelope_origin_636_i6
def checked_636_i6 : CheckedCard where
  required := required_636_i6
  envelope := envelope_636_i6
  height := height_636_i6
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_636_i6
def height_636_i3 : ℕ := 10
def childrenH_636_i3 : Fin 5 → ℕ := ![height_332, height_474, height_522, height_636_i4, height_636_i6]
theorem height_exact_636_i3 : height_636_i3 = 1 + Finset.univ.sup childrenH_636_i3 := by decide +kernel
theorem required_origin_636_i3 : ∀ x ∈ required_636_i3,
    (∃ j, x ∈ childrenC_636_i3 j) ∨ ∀ j, x ∈ childrenD_636_i3 j := by decide +kernel
theorem required_exact_636_i3 : required_636_i3 =
    ((Finset.univ.biUnion childrenC_636_i3) ∪ commonEnvelope childrenD_636_i3).erase (5, 4) := by
  exact required_eq_combination childrenC_636_i3 childrenD_636_i3 (5, 4) required_636_i3
    (by decide +kernel) child_required_sub_636_i3 common_sub_636_i3 required_origin_636_i3
theorem envelope_origin_636_i3 : ∀ x ∈ envelope_636_i3,
    x = (5, 4) ∨ ∃ j, x ∈ childrenD_636_i3 j := by decide +kernel
theorem envelope_exact_636_i3 : envelope_636_i3 =
    insert (5, 4) (Finset.univ.biUnion childrenD_636_i3) := by
  exact envelope_eq_combination childrenD_636_i3 (5, 4) envelope_636_i3
    pivot_mem_636_i3 child_envelope_sub_636_i3 envelope_origin_636_i3
def checked_636_i3 : CheckedCard where
  required := required_636_i3
  envelope := envelope_636_i3
  height := height_636_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_636_i3
def height_636_i0 : ℕ := 13
def childrenH_636_i0 : Fin 9 → ℕ := ![height_399, height_408, height_475, height_509, height_587, height_636_i1, height_635, height_636_i2, height_636_i3]
theorem height_exact_636_i0 : height_636_i0 = 1 + Finset.univ.sup childrenH_636_i0 := by decide +kernel
theorem required_origin_636_i0 : ∀ x ∈ required_636_i0,
    (∃ j, x ∈ childrenC_636_i0 j) ∨ ∀ j, x ∈ childrenD_636_i0 j := by decide +kernel
theorem required_exact_636_i0 : required_636_i0 =
    ((Finset.univ.biUnion childrenC_636_i0) ∪ commonEnvelope childrenD_636_i0).erase (4, 5) := by
  exact required_eq_combination childrenC_636_i0 childrenD_636_i0 (4, 5) required_636_i0
    (by decide +kernel) child_required_sub_636_i0 common_sub_636_i0 required_origin_636_i0
theorem envelope_origin_636_i0 : ∀ x ∈ envelope_636_i0,
    x = (4, 5) ∨ ∃ j, x ∈ childrenD_636_i0 j := by decide +kernel
theorem envelope_exact_636_i0 : envelope_636_i0 =
    insert (4, 5) (Finset.univ.biUnion childrenD_636_i0) := by
  exact envelope_eq_combination childrenD_636_i0 (4, 5) envelope_636_i0
    pivot_mem_636_i0 child_envelope_sub_636_i0 envelope_origin_636_i0
def checked_636_i0 : CheckedCard where
  required := required_636_i0
  envelope := envelope_636_i0
  height := height_636_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_636_i0
def height_636_i7 : ℕ := 10
def childrenH_636_i7 : Fin 6 → ℕ := ![height_118, height_188, height_188, height_192, height_193, height_396]
theorem height_exact_636_i7 : height_636_i7 = 1 + Finset.univ.sup childrenH_636_i7 := by decide +kernel
theorem required_origin_636_i7 : ∀ x ∈ required_636_i7,
    (∃ j, x ∈ childrenC_636_i7 j) ∨ ∀ j, x ∈ childrenD_636_i7 j := by decide +kernel
theorem required_exact_636_i7 : required_636_i7 =
    ((Finset.univ.biUnion childrenC_636_i7) ∪ commonEnvelope childrenD_636_i7).erase (5, 4) := by
  exact required_eq_combination childrenC_636_i7 childrenD_636_i7 (5, 4) required_636_i7
    (by decide +kernel) child_required_sub_636_i7 common_sub_636_i7 required_origin_636_i7
theorem envelope_origin_636_i7 : ∀ x ∈ envelope_636_i7,
    x = (5, 4) ∨ ∃ j, x ∈ childrenD_636_i7 j := by decide +kernel
theorem envelope_exact_636_i7 : envelope_636_i7 =
    insert (5, 4) (Finset.univ.biUnion childrenD_636_i7) := by
  exact envelope_eq_combination childrenD_636_i7 (5, 4) envelope_636_i7
    pivot_mem_636_i7 child_envelope_sub_636_i7 envelope_origin_636_i7
def checked_636_i7 : CheckedCard where
  required := required_636_i7
  envelope := envelope_636_i7
  height := height_636_i7
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_636_i7
def height_636 : ℕ := 14
def childrenH_636 : Fin 4 → ℕ := ![height_125, height_454, height_636_i0, height_636_i7]
theorem height_exact_636 : height_636 = 1 + Finset.univ.sup childrenH_636 := by decide +kernel
theorem required_origin_636 : ∀ x ∈ required_636,
    (∃ j, x ∈ childrenC_636 j) ∨ ∀ j, x ∈ childrenD_636 j := by decide +kernel
theorem required_exact_636 : required_636 =
    ((Finset.univ.biUnion childrenC_636) ∪ commonEnvelope childrenD_636).erase (3, 4) := by
  exact required_eq_combination childrenC_636 childrenD_636 (3, 4) required_636
    (by decide +kernel) child_required_sub_636 common_sub_636 required_origin_636
theorem envelope_origin_636 : ∀ x ∈ envelope_636,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_636 j := by decide +kernel
theorem envelope_exact_636 : envelope_636 =
    insert (3, 4) (Finset.univ.biUnion childrenD_636) := by
  exact envelope_eq_combination childrenD_636 (3, 4) envelope_636
    pivot_mem_636 child_envelope_sub_636 envelope_origin_636
def checked_636 : CheckedCard where
  required := required_636
  envelope := envelope_636
  height := height_636
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_636
def height_644_i1 : ℕ := 10
def childrenH_644_i1 : Fin 3 → ℕ := ![height_10, height_317, height_640]
theorem height_exact_644_i1 : height_644_i1 = 1 + Finset.univ.sup childrenH_644_i1 := by decide +kernel
theorem required_origin_644_i1 : ∀ x ∈ required_644_i1,
    (∃ j, x ∈ childrenC_644_i1 j) ∨ ∀ j, x ∈ childrenD_644_i1 j := by decide +kernel
theorem required_exact_644_i1 : required_644_i1 =
    ((Finset.univ.biUnion childrenC_644_i1) ∪ commonEnvelope childrenD_644_i1).erase (5, 5) := by
  exact required_eq_combination childrenC_644_i1 childrenD_644_i1 (5, 5) required_644_i1
    (by decide +kernel) child_required_sub_644_i1 common_sub_644_i1 required_origin_644_i1
theorem envelope_origin_644_i1 : ∀ x ∈ envelope_644_i1,
    x = (5, 5) ∨ ∃ j, x ∈ childrenD_644_i1 j := by decide +kernel
theorem envelope_exact_644_i1 : envelope_644_i1 =
    insert (5, 5) (Finset.univ.biUnion childrenD_644_i1) := by
  exact envelope_eq_combination childrenD_644_i1 (5, 5) envelope_644_i1
    pivot_mem_644_i1 child_envelope_sub_644_i1 envelope_origin_644_i1
def checked_644_i1 : CheckedCard where
  required := required_644_i1
  envelope := envelope_644_i1
  height := height_644_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_644_i1
def height_644_i0 : ℕ := 11
def childrenH_644_i0 : Fin 6 → ℕ := ![height_104, height_359, height_452, height_476, height_479, height_644_i1]
theorem height_exact_644_i0 : height_644_i0 = 1 + Finset.univ.sup childrenH_644_i0 := by decide +kernel
theorem required_origin_644_i0 : ∀ x ∈ required_644_i0,
    (∃ j, x ∈ childrenC_644_i0 j) ∨ ∀ j, x ∈ childrenD_644_i0 j := by decide +kernel
theorem required_exact_644_i0 : required_644_i0 =
    ((Finset.univ.biUnion childrenC_644_i0) ∪ commonEnvelope childrenD_644_i0).erase (6, 5) := by
  exact required_eq_combination childrenC_644_i0 childrenD_644_i0 (6, 5) required_644_i0
    (by decide +kernel) child_required_sub_644_i0 common_sub_644_i0 required_origin_644_i0
theorem envelope_origin_644_i0 : ∀ x ∈ envelope_644_i0,
    x = (6, 5) ∨ ∃ j, x ∈ childrenD_644_i0 j := by decide +kernel
theorem envelope_exact_644_i0 : envelope_644_i0 =
    insert (6, 5) (Finset.univ.biUnion childrenD_644_i0) := by
  exact envelope_eq_combination childrenD_644_i0 (6, 5) envelope_644_i0
    pivot_mem_644_i0 child_envelope_sub_644_i0 envelope_origin_644_i0
def checked_644_i0 : CheckedCard where
  required := required_644_i0
  envelope := envelope_644_i0
  height := height_644_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_644_i0
def height_644 : ℕ := 14
def childrenH_644 : Fin 9 → ℕ := ![height_120, height_338, height_437, height_611, height_613, height_634, height_644_i0, height_642, height_643]
theorem height_exact_644 : height_644 = 1 + Finset.univ.sup childrenH_644 := by decide +kernel
theorem required_origin_644 : ∀ x ∈ required_644,
    (∃ j, x ∈ childrenC_644 j) ∨ ∀ j, x ∈ childrenD_644 j := by decide +kernel
theorem required_exact_644 : required_644 =
    ((Finset.univ.biUnion childrenC_644) ∪ commonEnvelope childrenD_644).erase (6, 4) := by
  exact required_eq_combination childrenC_644 childrenD_644 (6, 4) required_644
    (by decide +kernel) child_required_sub_644 common_sub_644 required_origin_644
theorem envelope_origin_644 : ∀ x ∈ envelope_644,
    x = (6, 4) ∨ ∃ j, x ∈ childrenD_644 j := by decide +kernel
theorem envelope_exact_644 : envelope_644 =
    insert (6, 4) (Finset.univ.biUnion childrenD_644) := by
  exact envelope_eq_combination childrenD_644 (6, 4) envelope_644
    pivot_mem_644 child_envelope_sub_644 envelope_origin_644
def checked_644 : CheckedCard where
  required := required_644
  envelope := envelope_644
  height := height_644
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_644
end SnakyPrototype.Certificate21

end OAI
