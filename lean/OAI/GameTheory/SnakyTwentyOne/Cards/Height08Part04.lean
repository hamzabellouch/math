import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part06
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part04
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_559_i0 : Finset Cell := ⟨(([(3, 1), (3, 2), (3, 3), (4, 1), (5, 1), (6, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_559_i0 : Finset Cell := ⟨(([(3, 1), (3, 2), (3, 3), (3, 4), (4, 0), (4, 1), (5, 0), (5, 1), (6, 1), (6, 2), (7, 0), (7, 1), (7, 2), (8, 0), (8, 1), (8, 2), (9, 0)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_559_i0 : Fin 2 → Finset Cell := ![(placed21 3 (3, 4) required_0), (placed21 1 (3, 0) required_17)]
def childrenD_559_i0 : Fin 2 → Finset Cell := ![(placed21 3 (3, 4) envelope_0), (placed21 1 (3, 0) envelope_17)]
theorem common_sub_559_i0 : commonEnvelope childrenD_559_i0 ⊆ insert (4, 0) required_559_i0 := by decide +kernel
theorem child_required_sub_559_i0 : ∀ j, childrenC_559_i0 j ⊆ insert (4, 0) required_559_i0 := by decide +kernel
theorem child_envelope_sub_559_i0 : ∀ j, childrenD_559_i0 j ⊆ envelope_559_i0 := by decide +kernel
theorem pivot_mem_559_i0 : (4, 0) ∈ envelope_559_i0 := by decide +kernel
theorem children_work_559_i0 : ∀ j, Template HasSnaky 4 (childrenC_559_i0 j) (childrenD_559_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 3 (3, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_17 1 (3, 0)).mono (by decide +kernel)
theorem row_works_559_i0 : Template HasSnaky 5 required_559_i0 envelope_559_i0 := by
  refine compose HasSnaky 4 childrenC_559_i0 childrenD_559_i0 children_work_559_i0 (4, 0)
    required_559_i0 envelope_559_i0 pivot_mem_559_i0 child_required_sub_559_i0 child_envelope_sub_559_i0 ?_
  intro b hb
  exact common_sub_559_i0 (mem_commonEnvelope childrenD_559_i0 b hb)
def required_559_i6 : Finset Cell := ⟨(([(0, 2), (1, 2), (2, 3), (3, 3), (3, 4), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_559_i6 : Finset Cell := ⟨(([(0, 2), (0, 3), (1, 2), (1, 3), (2, 3), (3, 3), (3, 4), (4, 3), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_559_i6 : Fin 2 → Finset Cell := ![(placed21 6 (4, 3) required_0), (placed21 0 (0, 3) required_0)]
def childrenD_559_i6 : Fin 2 → Finset Cell := ![(placed21 6 (4, 3) envelope_0), (placed21 0 (0, 3) envelope_0)]
theorem common_sub_559_i6 : commonEnvelope childrenD_559_i6 ⊆ insert (1, 3) required_559_i6 := by decide +kernel
theorem child_required_sub_559_i6 : ∀ j, childrenC_559_i6 j ⊆ insert (1, 3) required_559_i6 := by decide +kernel
theorem child_envelope_sub_559_i6 : ∀ j, childrenD_559_i6 j ⊆ envelope_559_i6 := by decide +kernel
theorem pivot_mem_559_i6 : (1, 3) ∈ envelope_559_i6 := by decide +kernel
theorem children_work_559_i6 : ∀ j, Template HasSnaky 1 (childrenC_559_i6 j) (childrenD_559_i6 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 6 (4, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_0 0 (0, 3)).mono (by decide +kernel)
theorem row_works_559_i6 : Template HasSnaky 2 required_559_i6 envelope_559_i6 := by
  refine compose HasSnaky 1 childrenC_559_i6 childrenD_559_i6 children_work_559_i6 (1, 3)
    required_559_i6 envelope_559_i6 pivot_mem_559_i6 child_required_sub_559_i6 child_envelope_sub_559_i6 ?_
  intro b hb
  exact common_sub_559_i6 (mem_commonEnvelope childrenD_559_i6 b hb)
def required_559_i5 : Finset Cell := ⟨(([(0, 2), (1, 2), (3, 3), (3, 4), (4, 4), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_559_i5 : Finset Cell := ⟨(([(0, 2), (0, 3), (1, 2), (1, 3), (2, 3), (3, 3), (3, 4), (4, 3), (4, 4), (5, 4), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_559_i5 : Fin 2 → Finset Cell := ![(placed21 6 (6, 4) required_1), required_559_i6]
def childrenD_559_i5 : Fin 2 → Finset Cell := ![(placed21 6 (6, 4) envelope_1), envelope_559_i6]
theorem common_sub_559_i5 : commonEnvelope childrenD_559_i5 ⊆ insert (2, 3) required_559_i5 := by decide +kernel
theorem child_required_sub_559_i5 : ∀ j, childrenC_559_i5 j ⊆ insert (2, 3) required_559_i5 := by decide +kernel
theorem child_envelope_sub_559_i5 : ∀ j, childrenD_559_i5 j ⊆ envelope_559_i5 := by decide +kernel
theorem pivot_mem_559_i5 : (2, 3) ∈ envelope_559_i5 := by decide +kernel
theorem children_work_559_i5 : ∀ j, Template HasSnaky 2 (childrenC_559_i5 j) (childrenD_559_i5 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_1 6 (6, 4)).mono (by decide +kernel)
  · exact row_works_559_i6.mono (by decide +kernel)
theorem row_works_559_i5 : Template HasSnaky 3 required_559_i5 envelope_559_i5 := by
  refine compose HasSnaky 2 childrenC_559_i5 childrenD_559_i5 children_work_559_i5 (2, 3)
    required_559_i5 envelope_559_i5 pivot_mem_559_i5 child_required_sub_559_i5 child_envelope_sub_559_i5 ?_
  intro b hb
  exact common_sub_559_i5 (mem_commonEnvelope childrenD_559_i5 b hb)
def required_559_i4 : Finset Cell := ⟨(([(0, 2), (1, 2), (3, 1), (3, 2), (3, 3), (3, 4), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_559_i4 : Finset Cell := ⟨(([(0, 2), (0, 3), (1, 2), (1, 3), (2, 3), (3, 1), (3, 2), (3, 3), (3, 4), (4, 3), (4, 4), (4, 5), (5, 4), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_559_i4 : Fin 2 → Finset Cell := ![(placed21 1 (3, 1) required_5), required_559_i5]
def childrenD_559_i4 : Fin 2 → Finset Cell := ![(placed21 1 (3, 1) envelope_5), envelope_559_i5]
theorem common_sub_559_i4 : commonEnvelope childrenD_559_i4 ⊆ insert (4, 4) required_559_i4 := by decide +kernel
theorem child_required_sub_559_i4 : ∀ j, childrenC_559_i4 j ⊆ insert (4, 4) required_559_i4 := by decide +kernel
theorem child_envelope_sub_559_i4 : ∀ j, childrenD_559_i4 j ⊆ envelope_559_i4 := by decide +kernel
theorem pivot_mem_559_i4 : (4, 4) ∈ envelope_559_i4 := by decide +kernel
theorem children_work_559_i4 : ∀ j, Template HasSnaky 3 (childrenC_559_i4 j) (childrenD_559_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 1 (3, 1)).mono (by decide +kernel)
  · exact row_works_559_i5.mono (by decide +kernel)
theorem row_works_559_i4 : Template HasSnaky 4 required_559_i4 envelope_559_i4 := by
  refine compose HasSnaky 3 childrenC_559_i4 childrenD_559_i4 children_work_559_i4 (4, 4)
    required_559_i4 envelope_559_i4 pivot_mem_559_i4 child_required_sub_559_i4 child_envelope_sub_559_i4 ?_
  intro b hb
  exact common_sub_559_i4 (mem_commonEnvelope childrenD_559_i4 b hb)
def required_559_i3 : Finset Cell := ⟨(([(0, 2), (1, 2), (3, 1), (3, 2), (3, 3), (3, 4), (4, 1), (5, 0), (5, 1), (6, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_559_i3 : Finset Cell := ⟨(([(0, 2), (0, 3), (1, 2), (1, 3), (2, 3), (3, 1), (3, 2), (3, 3), (3, 4), (4, 1), (4, 3), (4, 4), (4, 5), (5, 0), (5, 1), (5, 4), (6, 1), (6, 2), (6, 3), (6, 4), (7, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_559_i3 : Fin 2 → Finset Cell := ![(placed21 0 (3, 0) required_35), required_559_i4]
def childrenD_559_i3 : Fin 2 → Finset Cell := ![(placed21 0 (3, 0) envelope_35), envelope_559_i4]
theorem common_sub_559_i3 : commonEnvelope childrenD_559_i3 ⊆ insert (6, 4) required_559_i3 := by decide +kernel
theorem child_required_sub_559_i3 : ∀ j, childrenC_559_i3 j ⊆ insert (6, 4) required_559_i3 := by decide +kernel
theorem child_envelope_sub_559_i3 : ∀ j, childrenD_559_i3 j ⊆ envelope_559_i3 := by decide +kernel
theorem pivot_mem_559_i3 : (6, 4) ∈ envelope_559_i3 := by decide +kernel
theorem children_work_559_i3 : ∀ j, Template HasSnaky 4 (childrenC_559_i3 j) (childrenD_559_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_35 0 (3, 0)).mono (by decide +kernel)
  · exact row_works_559_i4.mono (by decide +kernel)
theorem row_works_559_i3 : Template HasSnaky 5 required_559_i3 envelope_559_i3 := by
  refine compose HasSnaky 4 childrenC_559_i3 childrenD_559_i3 children_work_559_i3 (6, 4)
    required_559_i3 envelope_559_i3 pivot_mem_559_i3 child_required_sub_559_i3 child_envelope_sub_559_i3 ?_
  intro b hb
  exact common_sub_559_i3 (mem_commonEnvelope childrenD_559_i3 b hb)
def required_559_i2 : Finset Cell := ⟨(([(0, 2), (1, 2), (3, 1), (3, 2), (3, 3), (3, 4), (4, 1), (5, 1), (6, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_559_i2 : Finset Cell := ⟨(([(0, 2), (0, 3), (1, 2), (1, 3), (2, 0), (2, 1), (2, 3), (3, 1), (3, 2), (3, 3), (3, 4), (4, 1), (4, 3), (4, 4), (4, 5), (5, 0), (5, 1), (5, 4), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (7, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_559_i2 : Fin 2 → Finset Cell := ![(placed21 5 (6, 0) required_244), required_559_i3]
def childrenD_559_i2 : Fin 2 → Finset Cell := ![(placed21 5 (6, 0) envelope_244), envelope_559_i3]
theorem common_sub_559_i2 : commonEnvelope childrenD_559_i2 ⊆ insert (5, 0) required_559_i2 := by decide +kernel
theorem child_required_sub_559_i2 : ∀ j, childrenC_559_i2 j ⊆ insert (5, 0) required_559_i2 := by decide +kernel
theorem child_envelope_sub_559_i2 : ∀ j, childrenD_559_i2 j ⊆ envelope_559_i2 := by decide +kernel
theorem pivot_mem_559_i2 : (5, 0) ∈ envelope_559_i2 := by decide +kernel
theorem children_work_559_i2 : ∀ j, Template HasSnaky 5 (childrenC_559_i2 j) (childrenD_559_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_244 5 (6, 0)).mono (by decide +kernel)
  · exact row_works_559_i3.mono (by decide +kernel)
theorem row_works_559_i2 : Template HasSnaky 6 required_559_i2 envelope_559_i2 := by
  refine compose HasSnaky 5 childrenC_559_i2 childrenD_559_i2 children_work_559_i2 (5, 0)
    required_559_i2 envelope_559_i2 pivot_mem_559_i2 child_required_sub_559_i2 child_envelope_sub_559_i2 ?_
  intro b hb
  exact common_sub_559_i2 (mem_commonEnvelope childrenD_559_i2 b hb)
def required_559_i1 : Finset Cell := ⟨(([(0, 2), (1, 2), (3, 1), (3, 2), (3, 3), (4, 1), (5, 1), (6, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_559_i1 : Finset Cell := ⟨(([(0, 2), (0, 3), (1, 2), (1, 3), (2, 0), (2, 1), (2, 3), (3, 1), (3, 2), (3, 3), (3, 4), (4, 0), (4, 1), (4, 3), (4, 4), (4, 5), (5, 0), (5, 1), (5, 4), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (7, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_559_i1 : Fin 2 → Finset Cell := ![(placed21 3 (3, 4) required_5), required_559_i2]
def childrenD_559_i1 : Fin 2 → Finset Cell := ![(placed21 3 (3, 4) envelope_5), envelope_559_i2]
theorem common_sub_559_i1 : commonEnvelope childrenD_559_i1 ⊆ insert (3, 4) required_559_i1 := by decide +kernel
theorem child_required_sub_559_i1 : ∀ j, childrenC_559_i1 j ⊆ insert (3, 4) required_559_i1 := by decide +kernel
theorem child_envelope_sub_559_i1 : ∀ j, childrenD_559_i1 j ⊆ envelope_559_i1 := by decide +kernel
theorem pivot_mem_559_i1 : (3, 4) ∈ envelope_559_i1 := by decide +kernel
theorem children_work_559_i1 : ∀ j, Template HasSnaky 6 (childrenC_559_i1 j) (childrenD_559_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 3 (3, 4)).mono (by decide +kernel)
  · exact row_works_559_i2.mono (by decide +kernel)
theorem row_works_559_i1 : Template HasSnaky 7 required_559_i1 envelope_559_i1 := by
  refine compose HasSnaky 6 childrenC_559_i1 childrenD_559_i1 children_work_559_i1 (3, 4)
    required_559_i1 envelope_559_i1 pivot_mem_559_i1 child_required_sub_559_i1 child_envelope_sub_559_i1 ?_
  intro b hb
  exact common_sub_559_i1 (mem_commonEnvelope childrenD_559_i1 b hb)
def required_559 : Finset Cell := ⟨(([(0, 2), (1, 2), (3, 1), (3, 2), (3, 3), (4, 1), (5, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_559 : Finset Cell := ⟨(([(0, 2), (0, 3), (1, 0), (1, 2), (1, 3), (2, 0), (2, 1), (2, 3), (3, 1), (3, 2), (3, 3), (3, 4), (4, 0), (4, 1), (4, 3), (4, 4), (4, 5), (5, 0), (5, 1), (5, 4), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (7, 0), (7, 1), (7, 2), (8, 0), (8, 1), (8, 2), (9, 0)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_559 : Fin 4 → Finset Cell := ![(placed21 4 (3, 2) required_8), (placed21 5 (7, 0) required_236), required_559_i0, required_559_i1]
def childrenD_559 : Fin 4 → Finset Cell := ![(placed21 4 (3, 2) envelope_8), (placed21 5 (7, 0) envelope_236), envelope_559_i0, envelope_559_i1]
theorem common_sub_559 : commonEnvelope childrenD_559 ⊆ insert (6, 1) required_559 := by decide +kernel
theorem child_required_sub_559 : ∀ j, childrenC_559 j ⊆ insert (6, 1) required_559 := by decide +kernel
theorem child_envelope_sub_559 : ∀ j, childrenD_559 j ⊆ envelope_559 := by decide +kernel
theorem pivot_mem_559 : (6, 1) ∈ envelope_559 := by decide +kernel
theorem children_work_559 : ∀ j, Template HasSnaky 7 (childrenC_559 j) (childrenD_559 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_8 4 (3, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_236 5 (7, 0)).mono (by decide +kernel)
  · exact row_works_559_i0.mono (by decide +kernel)
  · exact row_works_559_i1.mono (by decide +kernel)
theorem row_works_559 : Template HasSnaky 8 required_559 envelope_559 := by
  refine compose HasSnaky 7 childrenC_559 childrenD_559 children_work_559 (6, 1)
    required_559 envelope_559 pivot_mem_559 child_required_sub_559 child_envelope_sub_559 ?_
  intro b hb
  exact common_sub_559 (mem_commonEnvelope childrenD_559 b hb)
def required_566 : Finset Cell := ⟨(([(3, 3), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_566 : Finset Cell := ⟨(([(0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (7, 2), (7, 4), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_566 : Fin 6 → Finset Cell := ![(placed21 1 (0, 2) required_116), (placed21 3 (0, 6) required_116), (placed21 1 (0, 2) required_172), (placed21 3 (0, 6) required_172), (placed21 0 (1, 1) required_182), (placed21 5 (6, 1) required_565)]
def childrenD_566 : Fin 6 → Finset Cell := ![(placed21 1 (0, 2) envelope_116), (placed21 3 (0, 6) envelope_116), (placed21 1 (0, 2) envelope_172), (placed21 3 (0, 6) envelope_172), (placed21 0 (1, 1) envelope_182), (placed21 5 (6, 1) envelope_565)]
theorem common_sub_566 : commonEnvelope childrenD_566 ⊆ insert (3, 5) required_566 := by decide +kernel
theorem child_required_sub_566 : ∀ j, childrenC_566 j ⊆ insert (3, 5) required_566 := by decide +kernel
theorem child_envelope_sub_566 : ∀ j, childrenD_566 j ⊆ envelope_566 := by decide +kernel
theorem pivot_mem_566 : (3, 5) ∈ envelope_566 := by decide +kernel
theorem children_work_566 : ∀ j, Template HasSnaky 7 (childrenC_566 j) (childrenD_566 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_116 1 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_116 3 (0, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_172 1 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_172 3 (0, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_182 0 (1, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_565 5 (6, 1)).mono (by decide +kernel)
theorem row_works_566 : Template HasSnaky 8 required_566 envelope_566 := by
  refine compose HasSnaky 7 childrenC_566 childrenD_566 children_work_566 (3, 5)
    required_566 envelope_566 pivot_mem_566 child_required_sub_566 child_envelope_sub_566 ?_
  intro b hb
  exact common_sub_566 (mem_commonEnvelope childrenD_566 b hb)
def required_604_i0 : Finset Cell := ⟨(([(0, 3), (1, 3), (2, 3), (3, 2), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_604_i0 : Finset Cell := ⟨(([(0, 3), (1, 3), (1, 4), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 4), (4, 5), (4, 6), (4, 7), (5, 5), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_604_i0 : Fin 2 → Finset Cell := ![(placed21 0 (0, 3) required_5), (placed21 0 (1, 0) required_267)]
def childrenD_604_i0 : Fin 2 → Finset Cell := ![(placed21 0 (0, 3) envelope_5), (placed21 0 (1, 0) envelope_267)]
theorem common_sub_604_i0 : commonEnvelope childrenD_604_i0 ⊆ insert (3, 4) required_604_i0 := by decide +kernel
theorem child_required_sub_604_i0 : ∀ j, childrenC_604_i0 j ⊆ insert (3, 4) required_604_i0 := by decide +kernel
theorem child_envelope_sub_604_i0 : ∀ j, childrenD_604_i0 j ⊆ envelope_604_i0 := by decide +kernel
theorem pivot_mem_604_i0 : (3, 4) ∈ envelope_604_i0 := by decide +kernel
theorem children_work_604_i0 : ∀ j, Template HasSnaky 6 (childrenC_604_i0 j) (childrenD_604_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 0 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_267 0 (1, 0)).mono (by decide +kernel)
theorem row_works_604_i0 : Template HasSnaky 7 required_604_i0 envelope_604_i0 := by
  refine compose HasSnaky 6 childrenC_604_i0 childrenD_604_i0 children_work_604_i0 (3, 4)
    required_604_i0 envelope_604_i0 pivot_mem_604_i0 child_required_sub_604_i0 child_envelope_sub_604_i0 ?_
  intro b hb
  exact common_sub_604_i0 (mem_commonEnvelope childrenD_604_i0 b hb)
def required_604 : Finset Cell := ⟨(([(0, 3), (1, 3), (2, 3), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_604 : Finset Cell := ⟨(([(0, 3), (1, 3), (1, 4), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 2), (4, 4), (4, 5), (4, 6), (4, 7), (5, 5), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_604 : Fin 2 → Finset Cell := ![(placed21 4 (0, 3) required_5), required_604_i0]
def childrenD_604 : Fin 2 → Finset Cell := ![(placed21 4 (0, 3) envelope_5), envelope_604_i0]
theorem common_sub_604 : commonEnvelope childrenD_604 ⊆ insert (3, 2) required_604 := by decide +kernel
theorem child_required_sub_604 : ∀ j, childrenC_604 j ⊆ insert (3, 2) required_604 := by decide +kernel
theorem child_envelope_sub_604 : ∀ j, childrenD_604 j ⊆ envelope_604 := by decide +kernel
theorem pivot_mem_604 : (3, 2) ∈ envelope_604 := by decide +kernel
theorem children_work_604 : ∀ j, Template HasSnaky 7 (childrenC_604 j) (childrenD_604 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 4 (0, 3)).mono (by decide +kernel)
  · exact row_works_604_i0.mono (by decide +kernel)
theorem row_works_604 : Template HasSnaky 8 required_604 envelope_604 := by
  refine compose HasSnaky 7 childrenC_604 childrenD_604 children_work_604 (3, 2)
    required_604 envelope_604 pivot_mem_604 child_required_sub_604 child_envelope_sub_604 ?_
  intro b hb
  exact common_sub_604 (mem_commonEnvelope childrenD_604 b hb)
def required_607_i0 : Finset Cell := ⟨(([(1, 4), (4, 3), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_607_i0 : Finset Cell := ⟨(([(1, 4), (1, 5), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 5), (3, 6), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 0), (5, 1), (5, 2), (5, 4), (5, 5), (5, 6), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_607_i0 : Fin 2 → Finset Cell := ![(placed21 3 (3, 5) required_8), (placed21 5 (6, 2) required_383)]
def childrenD_607_i0 : Fin 2 → Finset Cell := ![(placed21 3 (3, 5) envelope_8), (placed21 5 (6, 2) envelope_383)]
theorem common_sub_607_i0 : commonEnvelope childrenD_607_i0 ⊆ insert (4, 2) required_607_i0 := by decide +kernel
theorem child_required_sub_607_i0 : ∀ j, childrenC_607_i0 j ⊆ insert (4, 2) required_607_i0 := by decide +kernel
theorem child_envelope_sub_607_i0 : ∀ j, childrenD_607_i0 j ⊆ envelope_607_i0 := by decide +kernel
theorem pivot_mem_607_i0 : (4, 2) ∈ envelope_607_i0 := by decide +kernel
theorem children_work_607_i0 : ∀ j, Template HasSnaky 5 (childrenC_607_i0 j) (childrenD_607_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_8 3 (3, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_383 5 (6, 2)).mono (by decide +kernel)
theorem row_works_607_i0 : Template HasSnaky 6 required_607_i0 envelope_607_i0 := by
  refine compose HasSnaky 5 childrenC_607_i0 childrenD_607_i0 children_work_607_i0 (4, 2)
    required_607_i0 envelope_607_i0 pivot_mem_607_i0 child_required_sub_607_i0 child_envelope_sub_607_i0 ?_
  intro b hb
  exact common_sub_607_i0 (mem_commonEnvelope childrenD_607_i0 b hb)
def required_607_i3 : Finset Cell := ⟨(([(1, 2), (1, 4), (1, 5), (4, 3), (4, 4), (4, 5), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_607_i3 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 4), (2, 5), (2, 6), (3, 5), (4, 3), (4, 4), (4, 5), (4, 6), (5, 6), (5, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_607_i3 : Fin 2 → Finset Cell := ![(placed21 5 (5, 3) required_25), (placed21 6 (2, 6) required_42)]
def childrenD_607_i3 : Fin 2 → Finset Cell := ![(placed21 5 (5, 3) envelope_25), (placed21 6 (2, 6) envelope_42)]
theorem common_sub_607_i3 : commonEnvelope childrenD_607_i3 ⊆ insert (2, 5) required_607_i3 := by decide +kernel
theorem child_required_sub_607_i3 : ∀ j, childrenC_607_i3 j ⊆ insert (2, 5) required_607_i3 := by decide +kernel
theorem child_envelope_sub_607_i3 : ∀ j, childrenD_607_i3 j ⊆ envelope_607_i3 := by decide +kernel
theorem pivot_mem_607_i3 : (2, 5) ∈ envelope_607_i3 := by decide +kernel
theorem children_work_607_i3 : ∀ j, Template HasSnaky 4 (childrenC_607_i3 j) (childrenD_607_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_25 5 (5, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_42 6 (2, 6)).mono (by decide +kernel)
theorem row_works_607_i3 : Template HasSnaky 5 required_607_i3 envelope_607_i3 := by
  refine compose HasSnaky 4 childrenC_607_i3 childrenD_607_i3 children_work_607_i3 (2, 5)
    required_607_i3 envelope_607_i3 pivot_mem_607_i3 child_required_sub_607_i3 child_envelope_sub_607_i3 ?_
  intro b hb
  exact common_sub_607_i3 (mem_commonEnvelope childrenD_607_i3 b hb)
def required_607_i2 : Finset Cell := ⟨(([(1, 4), (1, 5), (4, 3), (4, 4), (4, 5), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_607_i2 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 2), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 5), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 0), (5, 1), (5, 2), (5, 6), (5, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_607_i2 : Fin 2 → Finset Cell := ![(placed21 7 (5, 6) required_352), required_607_i3]
def childrenD_607_i2 : Fin 2 → Finset Cell := ![(placed21 7 (5, 6) envelope_352), envelope_607_i3]
theorem common_sub_607_i2 : commonEnvelope childrenD_607_i2 ⊆ insert (1, 2) required_607_i2 := by decide +kernel
theorem child_required_sub_607_i2 : ∀ j, childrenC_607_i2 j ⊆ insert (1, 2) required_607_i2 := by decide +kernel
theorem child_envelope_sub_607_i2 : ∀ j, childrenD_607_i2 j ⊆ envelope_607_i2 := by decide +kernel
theorem pivot_mem_607_i2 : (1, 2) ∈ envelope_607_i2 := by decide +kernel
theorem children_work_607_i2 : ∀ j, Template HasSnaky 5 (childrenC_607_i2 j) (childrenD_607_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_352 7 (5, 6)).mono (by decide +kernel)
  · exact row_works_607_i3.mono (by decide +kernel)
theorem row_works_607_i2 : Template HasSnaky 6 required_607_i2 envelope_607_i2 := by
  refine compose HasSnaky 5 childrenC_607_i2 childrenD_607_i2 children_work_607_i2 (1, 2)
    required_607_i2 envelope_607_i2 pivot_mem_607_i2 child_required_sub_607_i2 child_envelope_sub_607_i2 ?_
  intro b hb
  exact common_sub_607_i2 (mem_commonEnvelope childrenD_607_i2 b hb)
def required_607_i1 : Finset Cell := ⟨(([(1, 4), (1, 5), (4, 3), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_607_i1 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 2), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 5), (3, 6), (3, 7), (3, 8), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 0), (5, 1), (5, 2), (5, 6), (5, 7), (5, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_607_i1 : Fin 3 → Finset Cell := ![(placed21 6 (4, 7) required_7), (placed21 5 (5, 3) required_8), required_607_i2]
def childrenD_607_i1 : Fin 3 → Finset Cell := ![(placed21 6 (4, 7) envelope_7), (placed21 5 (5, 3) envelope_8), envelope_607_i2]
theorem common_sub_607_i1 : commonEnvelope childrenD_607_i1 ⊆ insert (4, 6) required_607_i1 := by decide +kernel
theorem child_required_sub_607_i1 : ∀ j, childrenC_607_i1 j ⊆ insert (4, 6) required_607_i1 := by decide +kernel
theorem child_envelope_sub_607_i1 : ∀ j, childrenD_607_i1 j ⊆ envelope_607_i1 := by decide +kernel
theorem pivot_mem_607_i1 : (4, 6) ∈ envelope_607_i1 := by decide +kernel
theorem children_work_607_i1 : ∀ j, Template HasSnaky 6 (childrenC_607_i1 j) (childrenD_607_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 6 (4, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_8 5 (5, 3)).mono (by decide +kernel)
  · exact row_works_607_i2.mono (by decide +kernel)
theorem row_works_607_i1 : Template HasSnaky 7 required_607_i1 envelope_607_i1 := by
  refine compose HasSnaky 6 childrenC_607_i1 childrenD_607_i1 children_work_607_i1 (4, 6)
    required_607_i1 envelope_607_i1 pivot_mem_607_i1 child_required_sub_607_i1 child_envelope_sub_607_i1 ?_
  intro b hb
  exact common_sub_607_i1 (mem_commonEnvelope childrenD_607_i1 b hb)
def required_607_i4 : Finset Cell := ⟨(([(1, 4), (1, 5), (4, 3), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_607_i4 : Finset Cell := ⟨(([(0, 5), (1, 2), (1, 3), (1, 4), (1, 5), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_607_i4 : Fin 4 → Finset Cell := ![(placed21 5 (5, 3) required_197), (placed21 0 (1, 2) required_363), (placed21 5 (5, 3) required_371), (placed21 2 (5, 2) required_606)]
def childrenD_607_i4 : Fin 4 → Finset Cell := ![(placed21 5 (5, 3) envelope_197), (placed21 0 (1, 2) envelope_363), (placed21 5 (5, 3) envelope_371), (placed21 2 (5, 2) envelope_606)]
theorem common_sub_607_i4 : commonEnvelope childrenD_607_i4 ⊆ insert (4, 6) required_607_i4 := by decide +kernel
theorem child_required_sub_607_i4 : ∀ j, childrenC_607_i4 j ⊆ insert (4, 6) required_607_i4 := by decide +kernel
theorem child_envelope_sub_607_i4 : ∀ j, childrenD_607_i4 j ⊆ envelope_607_i4 := by decide +kernel
theorem pivot_mem_607_i4 : (4, 6) ∈ envelope_607_i4 := by decide +kernel
theorem children_work_607_i4 : ∀ j, Template HasSnaky 6 (childrenC_607_i4 j) (childrenD_607_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_197 5 (5, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_363 0 (1, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_371 5 (5, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_606 2 (5, 2)).mono (by decide +kernel)
theorem row_works_607_i4 : Template HasSnaky 7 required_607_i4 envelope_607_i4 := by
  refine compose HasSnaky 6 childrenC_607_i4 childrenD_607_i4 children_work_607_i4 (4, 6)
    required_607_i4 envelope_607_i4 pivot_mem_607_i4 child_required_sub_607_i4 child_envelope_sub_607_i4 ?_
  intro b hb
  exact common_sub_607_i4 (mem_commonEnvelope childrenD_607_i4 b hb)
def required_607 : Finset Cell := ⟨(([(1, 4), (1, 5), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_607 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 5), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 2), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 0), (3, 1), (3, 2), (3, 3), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 0), (5, 1), (5, 2), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_607 : Fin 5 → Finset Cell := ![(placed21 6 (5, 7) required_13), (placed21 4 (1, 7) required_211), required_607_i0, required_607_i1, required_607_i4]
def childrenD_607 : Fin 5 → Finset Cell := ![(placed21 6 (5, 7) envelope_13), (placed21 4 (1, 7) envelope_211), envelope_607_i0, envelope_607_i1, envelope_607_i4]
theorem common_sub_607 : commonEnvelope childrenD_607 ⊆ insert (4, 3) required_607 := by decide +kernel
theorem child_required_sub_607 : ∀ j, childrenC_607 j ⊆ insert (4, 3) required_607 := by decide +kernel
theorem child_envelope_sub_607 : ∀ j, childrenD_607 j ⊆ envelope_607 := by decide +kernel
theorem pivot_mem_607 : (4, 3) ∈ envelope_607 := by decide +kernel
theorem children_work_607 : ∀ j, Template HasSnaky 7 (childrenC_607 j) (childrenD_607 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_13 6 (5, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_211 4 (1, 7)).mono (by decide +kernel)
  · exact row_works_607_i0.mono (by decide +kernel)
  · exact row_works_607_i1.mono (by decide +kernel)
  · exact row_works_607_i4.mono (by decide +kernel)
theorem row_works_607 : Template HasSnaky 8 required_607 envelope_607 := by
  refine compose HasSnaky 7 childrenC_607 childrenD_607 children_work_607 (4, 3)
    required_607 envelope_607 pivot_mem_607 child_required_sub_607 child_envelope_sub_607 ?_
  intro b hb
  exact common_sub_607 (mem_commonEnvelope childrenD_607 b hb)
def required_619_i0 : Finset Cell := ⟨(([(1, 3), (2, 3), (3, 3), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_619_i0 : Finset Cell := ⟨(([(0, 4), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 0), (2, 1), (2, 2), (2, 3), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, 2), (5, 3), (6, 2), (6, 3), (6, 4), (7, 2), (7, 3), (7, 4), (8, 2), (8, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_619_i0 : Fin 2 → Finset Cell := ![(placed21 2 (4, 0) required_56), (placed21 0 (1, 0) required_253)]
def childrenD_619_i0 : Fin 2 → Finset Cell := ![(placed21 2 (4, 0) envelope_56), (placed21 0 (1, 0) envelope_253)]
theorem common_sub_619_i0 : commonEnvelope childrenD_619_i0 ⊆ insert (2, 2) required_619_i0 := by decide +kernel
theorem child_required_sub_619_i0 : ∀ j, childrenC_619_i0 j ⊆ insert (2, 2) required_619_i0 := by decide +kernel
theorem child_envelope_sub_619_i0 : ∀ j, childrenD_619_i0 j ⊆ envelope_619_i0 := by decide +kernel
theorem pivot_mem_619_i0 : (2, 2) ∈ envelope_619_i0 := by decide +kernel
theorem children_work_619_i0 : ∀ j, Template HasSnaky 6 (childrenC_619_i0 j) (childrenD_619_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_56 2 (4, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_253 0 (1, 0)).mono (by decide +kernel)
theorem row_works_619_i0 : Template HasSnaky 7 required_619_i0 envelope_619_i0 := by
  refine compose HasSnaky 6 childrenC_619_i0 childrenD_619_i0 children_work_619_i0 (2, 2)
    required_619_i0 envelope_619_i0 pivot_mem_619_i0 child_required_sub_619_i0 child_envelope_sub_619_i0 ?_
  intro b hb
  exact common_sub_619_i0 (mem_commonEnvelope childrenD_619_i0 b hb)
def required_619 : Finset Cell := ⟨(([(1, 3), (2, 3), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_619 : Finset Cell := ⟨(([(0, 4), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 0), (2, 1), (2, 2), (2, 3), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 2), (6, 3), (6, 4), (7, 2), (7, 3), (7, 4), (8, 2), (8, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_619 : Fin 6 → Finset Cell := ![(placed21 0 (1, 2) required_8), (placed21 0 (1, 2) required_26), (placed21 0 (1, 2) required_49), (placed21 0 (1, 0) required_115), (placed21 0 (1, 0) required_292), required_619_i0]
def childrenD_619 : Fin 6 → Finset Cell := ![(placed21 0 (1, 2) envelope_8), (placed21 0 (1, 2) envelope_26), (placed21 0 (1, 2) envelope_49), (placed21 0 (1, 0) envelope_115), (placed21 0 (1, 0) envelope_292), envelope_619_i0]
theorem common_sub_619 : commonEnvelope childrenD_619 ⊆ insert (4, 3) required_619 := by decide +kernel
theorem child_required_sub_619 : ∀ j, childrenC_619 j ⊆ insert (4, 3) required_619 := by decide +kernel
theorem child_envelope_sub_619 : ∀ j, childrenD_619 j ⊆ envelope_619 := by decide +kernel
theorem pivot_mem_619 : (4, 3) ∈ envelope_619 := by decide +kernel
theorem children_work_619 : ∀ j, Template HasSnaky 7 (childrenC_619 j) (childrenD_619 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_8 0 (1, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_26 0 (1, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_49 0 (1, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_115 0 (1, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_292 0 (1, 0)).mono (by decide +kernel)
  · exact row_works_619_i0.mono (by decide +kernel)
theorem row_works_619 : Template HasSnaky 8 required_619 envelope_619 := by
  refine compose HasSnaky 7 childrenC_619 childrenD_619 children_work_619 (4, 3)
    required_619 envelope_619 pivot_mem_619 child_required_sub_619 child_envelope_sub_619 ?_
  intro b hb
  exact common_sub_619 (mem_commonEnvelope childrenD_619 b hb)
def required_651_i0 : Finset Cell := ⟨(([(3, 3), (3, 4), (3, 6), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_651_i0 : Finset Cell := ⟨(([(0, 3), (0, 6), (1, 3), (1, 6), (2, 2), (2, 3), (2, 5), (2, 6), (2, 7), (3, 3), (3, 4), (3, 5), (3, 6), (4, 3), (4, 4), (4, 5), (5, 4), (5, 5), (6, 4), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_651_i0 : Fin 2 → Finset Cell := ![(placed21 5 (6, 3) required_55), (placed21 7 (6, 6) required_56)]
def childrenD_651_i0 : Fin 2 → Finset Cell := ![(placed21 5 (6, 3) envelope_55), (placed21 7 (6, 6) envelope_56)]
theorem common_sub_651_i0 : commonEnvelope childrenD_651_i0 ⊆ insert (3, 5) required_651_i0 := by decide +kernel
theorem child_required_sub_651_i0 : ∀ j, childrenC_651_i0 j ⊆ insert (3, 5) required_651_i0 := by decide +kernel
theorem child_envelope_sub_651_i0 : ∀ j, childrenD_651_i0 j ⊆ envelope_651_i0 := by decide +kernel
theorem pivot_mem_651_i0 : (3, 5) ∈ envelope_651_i0 := by decide +kernel
theorem children_work_651_i0 : ∀ j, Template HasSnaky 4 (childrenC_651_i0 j) (childrenD_651_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_55 5 (6, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_56 7 (6, 6)).mono (by decide +kernel)
theorem row_works_651_i0 : Template HasSnaky 5 required_651_i0 envelope_651_i0 := by
  refine compose HasSnaky 4 childrenC_651_i0 childrenD_651_i0 children_work_651_i0 (3, 5)
    required_651_i0 envelope_651_i0 pivot_mem_651_i0 child_required_sub_651_i0 child_envelope_sub_651_i0 ?_
  intro b hb
  exact common_sub_651_i0 (mem_commonEnvelope childrenD_651_i0 b hb)
def required_651_i1 : Finset Cell := ⟨(([(3, 3), (3, 4), (3, 6), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_651_i1 : Finset Cell := ⟨(([(0, 6), (1, 6), (2, 6), (2, 7), (2, 8), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_651_i1 : Fin 3 → Finset Cell := ![(placed21 2 (4, 3) required_20), (placed21 0 (3, 3) required_29), (placed21 5 (5, 3) required_46)]
def childrenD_651_i1 : Fin 3 → Finset Cell := ![(placed21 2 (4, 3) envelope_20), (placed21 0 (3, 3) envelope_29), (placed21 5 (5, 3) envelope_46)]
theorem common_sub_651_i1 : commonEnvelope childrenD_651_i1 ⊆ insert (3, 5) required_651_i1 := by decide +kernel
theorem child_required_sub_651_i1 : ∀ j, childrenC_651_i1 j ⊆ insert (3, 5) required_651_i1 := by decide +kernel
theorem child_envelope_sub_651_i1 : ∀ j, childrenD_651_i1 j ⊆ envelope_651_i1 := by decide +kernel
theorem pivot_mem_651_i1 : (3, 5) ∈ envelope_651_i1 := by decide +kernel
theorem children_work_651_i1 : ∀ j, Template HasSnaky 4 (childrenC_651_i1 j) (childrenD_651_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_20 2 (4, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_29 0 (3, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_46 5 (5, 3)).mono (by decide +kernel)
theorem row_works_651_i1 : Template HasSnaky 5 required_651_i1 envelope_651_i1 := by
  refine compose HasSnaky 4 childrenC_651_i1 childrenD_651_i1 children_work_651_i1 (3, 5)
    required_651_i1 envelope_651_i1 pivot_mem_651_i1 child_required_sub_651_i1 child_envelope_sub_651_i1 ?_
  intro b hb
  exact common_sub_651_i1 (mem_commonEnvelope childrenD_651_i1 b hb)
def required_651_i2 : Finset Cell := ⟨(([(3, 3), (3, 4), (3, 6), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_651_i2 : Finset Cell := ⟨(([(0, 2), (0, 3), (1, 2), (1, 3), (2, 2), (2, 3), (3, 3), (3, 4), (3, 6), (3, 7), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (6, 2), (6, 3), (6, 4), (7, 2), (7, 3), (7, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_651_i2 : Fin 2 → Finset Cell := ![(placed21 7 (7, 5) required_85), (placed21 2 (4, 3) required_94)]
def childrenD_651_i2 : Fin 2 → Finset Cell := ![(placed21 7 (7, 5) envelope_85), (placed21 2 (4, 3) envelope_94)]
theorem common_sub_651_i2 : commonEnvelope childrenD_651_i2 ⊆ insert (4, 3) required_651_i2 := by decide +kernel
theorem child_required_sub_651_i2 : ∀ j, childrenC_651_i2 j ⊆ insert (4, 3) required_651_i2 := by decide +kernel
theorem child_envelope_sub_651_i2 : ∀ j, childrenD_651_i2 j ⊆ envelope_651_i2 := by decide +kernel
theorem pivot_mem_651_i2 : (4, 3) ∈ envelope_651_i2 := by decide +kernel
theorem children_work_651_i2 : ∀ j, Template HasSnaky 6 (childrenC_651_i2 j) (childrenD_651_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_85 7 (7, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_94 2 (4, 3)).mono (by decide +kernel)
theorem row_works_651_i2 : Template HasSnaky 7 required_651_i2 envelope_651_i2 := by
  refine compose HasSnaky 6 childrenC_651_i2 childrenD_651_i2 children_work_651_i2 (4, 3)
    required_651_i2 envelope_651_i2 pivot_mem_651_i2 child_required_sub_651_i2 child_envelope_sub_651_i2 ?_
  intro b hb
  exact common_sub_651_i2 (mem_commonEnvelope childrenD_651_i2 b hb)
def required_651 : Finset Cell := ⟨(([(3, 3), (3, 4), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_651 : Finset Cell := ⟨(([(0, 2), (0, 3), (0, 6), (1, 2), (1, 3), (1, 6), (2, 2), (2, 3), (2, 5), (2, 6), (2, 7), (2, 8), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (6, 2), (6, 3), (6, 4), (6, 5), (7, 2), (7, 3), (7, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_651 : Fin 3 → Finset Cell := ![required_651_i0, required_651_i1, required_651_i2]
def childrenD_651 : Fin 3 → Finset Cell := ![envelope_651_i0, envelope_651_i1, envelope_651_i2]
theorem common_sub_651 : commonEnvelope childrenD_651 ⊆ insert (3, 6) required_651 := by decide +kernel
theorem child_required_sub_651 : ∀ j, childrenC_651 j ⊆ insert (3, 6) required_651 := by decide +kernel
theorem child_envelope_sub_651 : ∀ j, childrenD_651 j ⊆ envelope_651 := by decide +kernel
theorem pivot_mem_651 : (3, 6) ∈ envelope_651 := by decide +kernel
theorem children_work_651 : ∀ j, Template HasSnaky 7 (childrenC_651 j) (childrenD_651 j) := by
  intro j
  fin_cases j
  · exact row_works_651_i0.mono (by decide +kernel)
  · exact row_works_651_i1.mono (by decide +kernel)
  · exact row_works_651_i2.mono (by decide +kernel)
theorem row_works_651 : Template HasSnaky 8 required_651 envelope_651 := by
  refine compose HasSnaky 7 childrenC_651 childrenD_651 children_work_651 (3, 6)
    required_651 envelope_651 pivot_mem_651 child_required_sub_651 child_envelope_sub_651 ?_
  intro b hb
  exact common_sub_651 (mem_commonEnvelope childrenD_651 b hb)
def height_559_i0 : ℕ := 5
def childrenH_559_i0 : Fin 2 → ℕ := ![height_0, height_17]
theorem height_exact_559_i0 : height_559_i0 = 1 + Finset.univ.sup childrenH_559_i0 := by decide +kernel
theorem required_origin_559_i0 : ∀ x ∈ required_559_i0,
    (∃ j, x ∈ childrenC_559_i0 j) ∨ ∀ j, x ∈ childrenD_559_i0 j := by decide +kernel
theorem required_exact_559_i0 : required_559_i0 =
    ((Finset.univ.biUnion childrenC_559_i0) ∪ commonEnvelope childrenD_559_i0).erase (4, 0) := by
  exact required_eq_combination childrenC_559_i0 childrenD_559_i0 (4, 0) required_559_i0
    (by decide +kernel) child_required_sub_559_i0 common_sub_559_i0 required_origin_559_i0
theorem envelope_origin_559_i0 : ∀ x ∈ envelope_559_i0,
    x = (4, 0) ∨ ∃ j, x ∈ childrenD_559_i0 j := by decide +kernel
theorem envelope_exact_559_i0 : envelope_559_i0 =
    insert (4, 0) (Finset.univ.biUnion childrenD_559_i0) := by
  exact envelope_eq_combination childrenD_559_i0 (4, 0) envelope_559_i0
    pivot_mem_559_i0 child_envelope_sub_559_i0 envelope_origin_559_i0
def checked_559_i0 : CheckedCard where
  required := required_559_i0
  envelope := envelope_559_i0
  height := height_559_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_559_i0
def height_559_i6 : ℕ := 2
def childrenH_559_i6 : Fin 2 → ℕ := ![height_0, height_0]
theorem height_exact_559_i6 : height_559_i6 = 1 + Finset.univ.sup childrenH_559_i6 := by decide +kernel
theorem required_origin_559_i6 : ∀ x ∈ required_559_i6,
    (∃ j, x ∈ childrenC_559_i6 j) ∨ ∀ j, x ∈ childrenD_559_i6 j := by decide +kernel
theorem required_exact_559_i6 : required_559_i6 =
    ((Finset.univ.biUnion childrenC_559_i6) ∪ commonEnvelope childrenD_559_i6).erase (1, 3) := by
  exact required_eq_combination childrenC_559_i6 childrenD_559_i6 (1, 3) required_559_i6
    (by decide +kernel) child_required_sub_559_i6 common_sub_559_i6 required_origin_559_i6
theorem envelope_origin_559_i6 : ∀ x ∈ envelope_559_i6,
    x = (1, 3) ∨ ∃ j, x ∈ childrenD_559_i6 j := by decide +kernel
theorem envelope_exact_559_i6 : envelope_559_i6 =
    insert (1, 3) (Finset.univ.biUnion childrenD_559_i6) := by
  exact envelope_eq_combination childrenD_559_i6 (1, 3) envelope_559_i6
    pivot_mem_559_i6 child_envelope_sub_559_i6 envelope_origin_559_i6
def checked_559_i6 : CheckedCard where
  required := required_559_i6
  envelope := envelope_559_i6
  height := height_559_i6
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_559_i6
def height_559_i5 : ℕ := 3
def childrenH_559_i5 : Fin 2 → ℕ := ![height_1, height_559_i6]
theorem height_exact_559_i5 : height_559_i5 = 1 + Finset.univ.sup childrenH_559_i5 := by decide +kernel
theorem required_origin_559_i5 : ∀ x ∈ required_559_i5,
    (∃ j, x ∈ childrenC_559_i5 j) ∨ ∀ j, x ∈ childrenD_559_i5 j := by decide +kernel
theorem required_exact_559_i5 : required_559_i5 =
    ((Finset.univ.biUnion childrenC_559_i5) ∪ commonEnvelope childrenD_559_i5).erase (2, 3) := by
  exact required_eq_combination childrenC_559_i5 childrenD_559_i5 (2, 3) required_559_i5
    (by decide +kernel) child_required_sub_559_i5 common_sub_559_i5 required_origin_559_i5
theorem envelope_origin_559_i5 : ∀ x ∈ envelope_559_i5,
    x = (2, 3) ∨ ∃ j, x ∈ childrenD_559_i5 j := by decide +kernel
theorem envelope_exact_559_i5 : envelope_559_i5 =
    insert (2, 3) (Finset.univ.biUnion childrenD_559_i5) := by
  exact envelope_eq_combination childrenD_559_i5 (2, 3) envelope_559_i5
    pivot_mem_559_i5 child_envelope_sub_559_i5 envelope_origin_559_i5
def checked_559_i5 : CheckedCard where
  required := required_559_i5
  envelope := envelope_559_i5
  height := height_559_i5
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_559_i5
def height_559_i4 : ℕ := 4
def childrenH_559_i4 : Fin 2 → ℕ := ![height_5, height_559_i5]
theorem height_exact_559_i4 : height_559_i4 = 1 + Finset.univ.sup childrenH_559_i4 := by decide +kernel
theorem required_origin_559_i4 : ∀ x ∈ required_559_i4,
    (∃ j, x ∈ childrenC_559_i4 j) ∨ ∀ j, x ∈ childrenD_559_i4 j := by decide +kernel
theorem required_exact_559_i4 : required_559_i4 =
    ((Finset.univ.biUnion childrenC_559_i4) ∪ commonEnvelope childrenD_559_i4).erase (4, 4) := by
  exact required_eq_combination childrenC_559_i4 childrenD_559_i4 (4, 4) required_559_i4
    (by decide +kernel) child_required_sub_559_i4 common_sub_559_i4 required_origin_559_i4
theorem envelope_origin_559_i4 : ∀ x ∈ envelope_559_i4,
    x = (4, 4) ∨ ∃ j, x ∈ childrenD_559_i4 j := by decide +kernel
theorem envelope_exact_559_i4 : envelope_559_i4 =
    insert (4, 4) (Finset.univ.biUnion childrenD_559_i4) := by
  exact envelope_eq_combination childrenD_559_i4 (4, 4) envelope_559_i4
    pivot_mem_559_i4 child_envelope_sub_559_i4 envelope_origin_559_i4
def checked_559_i4 : CheckedCard where
  required := required_559_i4
  envelope := envelope_559_i4
  height := height_559_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_559_i4
def height_559_i3 : ℕ := 5
def childrenH_559_i3 : Fin 2 → ℕ := ![height_35, height_559_i4]
theorem height_exact_559_i3 : height_559_i3 = 1 + Finset.univ.sup childrenH_559_i3 := by decide +kernel
theorem required_origin_559_i3 : ∀ x ∈ required_559_i3,
    (∃ j, x ∈ childrenC_559_i3 j) ∨ ∀ j, x ∈ childrenD_559_i3 j := by decide +kernel
theorem required_exact_559_i3 : required_559_i3 =
    ((Finset.univ.biUnion childrenC_559_i3) ∪ commonEnvelope childrenD_559_i3).erase (6, 4) := by
  exact required_eq_combination childrenC_559_i3 childrenD_559_i3 (6, 4) required_559_i3
    (by decide +kernel) child_required_sub_559_i3 common_sub_559_i3 required_origin_559_i3
theorem envelope_origin_559_i3 : ∀ x ∈ envelope_559_i3,
    x = (6, 4) ∨ ∃ j, x ∈ childrenD_559_i3 j := by decide +kernel
theorem envelope_exact_559_i3 : envelope_559_i3 =
    insert (6, 4) (Finset.univ.biUnion childrenD_559_i3) := by
  exact envelope_eq_combination childrenD_559_i3 (6, 4) envelope_559_i3
    pivot_mem_559_i3 child_envelope_sub_559_i3 envelope_origin_559_i3
def checked_559_i3 : CheckedCard where
  required := required_559_i3
  envelope := envelope_559_i3
  height := height_559_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_559_i3
def height_559_i2 : ℕ := 6
def childrenH_559_i2 : Fin 2 → ℕ := ![height_244, height_559_i3]
theorem height_exact_559_i2 : height_559_i2 = 1 + Finset.univ.sup childrenH_559_i2 := by decide +kernel
theorem required_origin_559_i2 : ∀ x ∈ required_559_i2,
    (∃ j, x ∈ childrenC_559_i2 j) ∨ ∀ j, x ∈ childrenD_559_i2 j := by decide +kernel
theorem required_exact_559_i2 : required_559_i2 =
    ((Finset.univ.biUnion childrenC_559_i2) ∪ commonEnvelope childrenD_559_i2).erase (5, 0) := by
  exact required_eq_combination childrenC_559_i2 childrenD_559_i2 (5, 0) required_559_i2
    (by decide +kernel) child_required_sub_559_i2 common_sub_559_i2 required_origin_559_i2
theorem envelope_origin_559_i2 : ∀ x ∈ envelope_559_i2,
    x = (5, 0) ∨ ∃ j, x ∈ childrenD_559_i2 j := by decide +kernel
theorem envelope_exact_559_i2 : envelope_559_i2 =
    insert (5, 0) (Finset.univ.biUnion childrenD_559_i2) := by
  exact envelope_eq_combination childrenD_559_i2 (5, 0) envelope_559_i2
    pivot_mem_559_i2 child_envelope_sub_559_i2 envelope_origin_559_i2
def checked_559_i2 : CheckedCard where
  required := required_559_i2
  envelope := envelope_559_i2
  height := height_559_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_559_i2
def height_559_i1 : ℕ := 7
def childrenH_559_i1 : Fin 2 → ℕ := ![height_5, height_559_i2]
theorem height_exact_559_i1 : height_559_i1 = 1 + Finset.univ.sup childrenH_559_i1 := by decide +kernel
theorem required_origin_559_i1 : ∀ x ∈ required_559_i1,
    (∃ j, x ∈ childrenC_559_i1 j) ∨ ∀ j, x ∈ childrenD_559_i1 j := by decide +kernel
theorem required_exact_559_i1 : required_559_i1 =
    ((Finset.univ.biUnion childrenC_559_i1) ∪ commonEnvelope childrenD_559_i1).erase (3, 4) := by
  exact required_eq_combination childrenC_559_i1 childrenD_559_i1 (3, 4) required_559_i1
    (by decide +kernel) child_required_sub_559_i1 common_sub_559_i1 required_origin_559_i1
theorem envelope_origin_559_i1 : ∀ x ∈ envelope_559_i1,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_559_i1 j := by decide +kernel
theorem envelope_exact_559_i1 : envelope_559_i1 =
    insert (3, 4) (Finset.univ.biUnion childrenD_559_i1) := by
  exact envelope_eq_combination childrenD_559_i1 (3, 4) envelope_559_i1
    pivot_mem_559_i1 child_envelope_sub_559_i1 envelope_origin_559_i1
def checked_559_i1 : CheckedCard where
  required := required_559_i1
  envelope := envelope_559_i1
  height := height_559_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_559_i1
def height_559 : ℕ := 8
def childrenH_559 : Fin 4 → ℕ := ![height_8, height_236, height_559_i0, height_559_i1]
theorem height_exact_559 : height_559 = 1 + Finset.univ.sup childrenH_559 := by decide +kernel
theorem required_origin_559 : ∀ x ∈ required_559,
    (∃ j, x ∈ childrenC_559 j) ∨ ∀ j, x ∈ childrenD_559 j := by decide +kernel
theorem required_exact_559 : required_559 =
    ((Finset.univ.biUnion childrenC_559) ∪ commonEnvelope childrenD_559).erase (6, 1) := by
  exact required_eq_combination childrenC_559 childrenD_559 (6, 1) required_559
    (by decide +kernel) child_required_sub_559 common_sub_559 required_origin_559
theorem envelope_origin_559 : ∀ x ∈ envelope_559,
    x = (6, 1) ∨ ∃ j, x ∈ childrenD_559 j := by decide +kernel
theorem envelope_exact_559 : envelope_559 =
    insert (6, 1) (Finset.univ.biUnion childrenD_559) := by
  exact envelope_eq_combination childrenD_559 (6, 1) envelope_559
    pivot_mem_559 child_envelope_sub_559 envelope_origin_559
def checked_559 : CheckedCard where
  required := required_559
  envelope := envelope_559
  height := height_559
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_559
def height_566 : ℕ := 8
def childrenH_566 : Fin 6 → ℕ := ![height_116, height_116, height_172, height_172, height_182, height_565]
theorem height_exact_566 : height_566 = 1 + Finset.univ.sup childrenH_566 := by decide +kernel
theorem required_origin_566 : ∀ x ∈ required_566,
    (∃ j, x ∈ childrenC_566 j) ∨ ∀ j, x ∈ childrenD_566 j := by decide +kernel
theorem required_exact_566 : required_566 =
    ((Finset.univ.biUnion childrenC_566) ∪ commonEnvelope childrenD_566).erase (3, 5) := by
  exact required_eq_combination childrenC_566 childrenD_566 (3, 5) required_566
    (by decide +kernel) child_required_sub_566 common_sub_566 required_origin_566
theorem envelope_origin_566 : ∀ x ∈ envelope_566,
    x = (3, 5) ∨ ∃ j, x ∈ childrenD_566 j := by decide +kernel
theorem envelope_exact_566 : envelope_566 =
    insert (3, 5) (Finset.univ.biUnion childrenD_566) := by
  exact envelope_eq_combination childrenD_566 (3, 5) envelope_566
    pivot_mem_566 child_envelope_sub_566 envelope_origin_566
def checked_566 : CheckedCard where
  required := required_566
  envelope := envelope_566
  height := height_566
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_566
def height_604_i0 : ℕ := 7
def childrenH_604_i0 : Fin 2 → ℕ := ![height_5, height_267]
theorem height_exact_604_i0 : height_604_i0 = 1 + Finset.univ.sup childrenH_604_i0 := by decide +kernel
theorem required_origin_604_i0 : ∀ x ∈ required_604_i0,
    (∃ j, x ∈ childrenC_604_i0 j) ∨ ∀ j, x ∈ childrenD_604_i0 j := by decide +kernel
theorem required_exact_604_i0 : required_604_i0 =
    ((Finset.univ.biUnion childrenC_604_i0) ∪ commonEnvelope childrenD_604_i0).erase (3, 4) := by
  exact required_eq_combination childrenC_604_i0 childrenD_604_i0 (3, 4) required_604_i0
    (by decide +kernel) child_required_sub_604_i0 common_sub_604_i0 required_origin_604_i0
theorem envelope_origin_604_i0 : ∀ x ∈ envelope_604_i0,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_604_i0 j := by decide +kernel
theorem envelope_exact_604_i0 : envelope_604_i0 =
    insert (3, 4) (Finset.univ.biUnion childrenD_604_i0) := by
  exact envelope_eq_combination childrenD_604_i0 (3, 4) envelope_604_i0
    pivot_mem_604_i0 child_envelope_sub_604_i0 envelope_origin_604_i0
def checked_604_i0 : CheckedCard where
  required := required_604_i0
  envelope := envelope_604_i0
  height := height_604_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_604_i0
def height_604 : ℕ := 8
def childrenH_604 : Fin 2 → ℕ := ![height_5, height_604_i0]
theorem height_exact_604 : height_604 = 1 + Finset.univ.sup childrenH_604 := by decide +kernel
theorem required_origin_604 : ∀ x ∈ required_604,
    (∃ j, x ∈ childrenC_604 j) ∨ ∀ j, x ∈ childrenD_604 j := by decide +kernel
theorem required_exact_604 : required_604 =
    ((Finset.univ.biUnion childrenC_604) ∪ commonEnvelope childrenD_604).erase (3, 2) := by
  exact required_eq_combination childrenC_604 childrenD_604 (3, 2) required_604
    (by decide +kernel) child_required_sub_604 common_sub_604 required_origin_604
theorem envelope_origin_604 : ∀ x ∈ envelope_604,
    x = (3, 2) ∨ ∃ j, x ∈ childrenD_604 j := by decide +kernel
theorem envelope_exact_604 : envelope_604 =
    insert (3, 2) (Finset.univ.biUnion childrenD_604) := by
  exact envelope_eq_combination childrenD_604 (3, 2) envelope_604
    pivot_mem_604 child_envelope_sub_604 envelope_origin_604
def checked_604 : CheckedCard where
  required := required_604
  envelope := envelope_604
  height := height_604
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_604
def height_607_i0 : ℕ := 6
def childrenH_607_i0 : Fin 2 → ℕ := ![height_8, height_383]
theorem height_exact_607_i0 : height_607_i0 = 1 + Finset.univ.sup childrenH_607_i0 := by decide +kernel
theorem required_origin_607_i0 : ∀ x ∈ required_607_i0,
    (∃ j, x ∈ childrenC_607_i0 j) ∨ ∀ j, x ∈ childrenD_607_i0 j := by decide +kernel
theorem required_exact_607_i0 : required_607_i0 =
    ((Finset.univ.biUnion childrenC_607_i0) ∪ commonEnvelope childrenD_607_i0).erase (4, 2) := by
  exact required_eq_combination childrenC_607_i0 childrenD_607_i0 (4, 2) required_607_i0
    (by decide +kernel) child_required_sub_607_i0 common_sub_607_i0 required_origin_607_i0
theorem envelope_origin_607_i0 : ∀ x ∈ envelope_607_i0,
    x = (4, 2) ∨ ∃ j, x ∈ childrenD_607_i0 j := by decide +kernel
theorem envelope_exact_607_i0 : envelope_607_i0 =
    insert (4, 2) (Finset.univ.biUnion childrenD_607_i0) := by
  exact envelope_eq_combination childrenD_607_i0 (4, 2) envelope_607_i0
    pivot_mem_607_i0 child_envelope_sub_607_i0 envelope_origin_607_i0
def checked_607_i0 : CheckedCard where
  required := required_607_i0
  envelope := envelope_607_i0
  height := height_607_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_607_i0
def height_607_i3 : ℕ := 5
def childrenH_607_i3 : Fin 2 → ℕ := ![height_25, height_42]
theorem height_exact_607_i3 : height_607_i3 = 1 + Finset.univ.sup childrenH_607_i3 := by decide +kernel
theorem required_origin_607_i3 : ∀ x ∈ required_607_i3,
    (∃ j, x ∈ childrenC_607_i3 j) ∨ ∀ j, x ∈ childrenD_607_i3 j := by decide +kernel
theorem required_exact_607_i3 : required_607_i3 =
    ((Finset.univ.biUnion childrenC_607_i3) ∪ commonEnvelope childrenD_607_i3).erase (2, 5) := by
  exact required_eq_combination childrenC_607_i3 childrenD_607_i3 (2, 5) required_607_i3
    (by decide +kernel) child_required_sub_607_i3 common_sub_607_i3 required_origin_607_i3
theorem envelope_origin_607_i3 : ∀ x ∈ envelope_607_i3,
    x = (2, 5) ∨ ∃ j, x ∈ childrenD_607_i3 j := by decide +kernel
theorem envelope_exact_607_i3 : envelope_607_i3 =
    insert (2, 5) (Finset.univ.biUnion childrenD_607_i3) := by
  exact envelope_eq_combination childrenD_607_i3 (2, 5) envelope_607_i3
    pivot_mem_607_i3 child_envelope_sub_607_i3 envelope_origin_607_i3
def checked_607_i3 : CheckedCard where
  required := required_607_i3
  envelope := envelope_607_i3
  height := height_607_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_607_i3
def height_607_i2 : ℕ := 6
def childrenH_607_i2 : Fin 2 → ℕ := ![height_352, height_607_i3]
theorem height_exact_607_i2 : height_607_i2 = 1 + Finset.univ.sup childrenH_607_i2 := by decide +kernel
theorem required_origin_607_i2 : ∀ x ∈ required_607_i2,
    (∃ j, x ∈ childrenC_607_i2 j) ∨ ∀ j, x ∈ childrenD_607_i2 j := by decide +kernel
theorem required_exact_607_i2 : required_607_i2 =
    ((Finset.univ.biUnion childrenC_607_i2) ∪ commonEnvelope childrenD_607_i2).erase (1, 2) := by
  exact required_eq_combination childrenC_607_i2 childrenD_607_i2 (1, 2) required_607_i2
    (by decide +kernel) child_required_sub_607_i2 common_sub_607_i2 required_origin_607_i2
theorem envelope_origin_607_i2 : ∀ x ∈ envelope_607_i2,
    x = (1, 2) ∨ ∃ j, x ∈ childrenD_607_i2 j := by decide +kernel
theorem envelope_exact_607_i2 : envelope_607_i2 =
    insert (1, 2) (Finset.univ.biUnion childrenD_607_i2) := by
  exact envelope_eq_combination childrenD_607_i2 (1, 2) envelope_607_i2
    pivot_mem_607_i2 child_envelope_sub_607_i2 envelope_origin_607_i2
def checked_607_i2 : CheckedCard where
  required := required_607_i2
  envelope := envelope_607_i2
  height := height_607_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_607_i2
def height_607_i1 : ℕ := 7
def childrenH_607_i1 : Fin 3 → ℕ := ![height_7, height_8, height_607_i2]
theorem height_exact_607_i1 : height_607_i1 = 1 + Finset.univ.sup childrenH_607_i1 := by decide +kernel
theorem required_origin_607_i1 : ∀ x ∈ required_607_i1,
    (∃ j, x ∈ childrenC_607_i1 j) ∨ ∀ j, x ∈ childrenD_607_i1 j := by decide +kernel
theorem required_exact_607_i1 : required_607_i1 =
    ((Finset.univ.biUnion childrenC_607_i1) ∪ commonEnvelope childrenD_607_i1).erase (4, 6) := by
  exact required_eq_combination childrenC_607_i1 childrenD_607_i1 (4, 6) required_607_i1
    (by decide +kernel) child_required_sub_607_i1 common_sub_607_i1 required_origin_607_i1
theorem envelope_origin_607_i1 : ∀ x ∈ envelope_607_i1,
    x = (4, 6) ∨ ∃ j, x ∈ childrenD_607_i1 j := by decide +kernel
theorem envelope_exact_607_i1 : envelope_607_i1 =
    insert (4, 6) (Finset.univ.biUnion childrenD_607_i1) := by
  exact envelope_eq_combination childrenD_607_i1 (4, 6) envelope_607_i1
    pivot_mem_607_i1 child_envelope_sub_607_i1 envelope_origin_607_i1
def checked_607_i1 : CheckedCard where
  required := required_607_i1
  envelope := envelope_607_i1
  height := height_607_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_607_i1
def height_607_i4 : ℕ := 7
def childrenH_607_i4 : Fin 4 → ℕ := ![height_197, height_363, height_371, height_606]
theorem height_exact_607_i4 : height_607_i4 = 1 + Finset.univ.sup childrenH_607_i4 := by decide +kernel
theorem required_origin_607_i4 : ∀ x ∈ required_607_i4,
    (∃ j, x ∈ childrenC_607_i4 j) ∨ ∀ j, x ∈ childrenD_607_i4 j := by decide +kernel
theorem required_exact_607_i4 : required_607_i4 =
    ((Finset.univ.biUnion childrenC_607_i4) ∪ commonEnvelope childrenD_607_i4).erase (4, 6) := by
  exact required_eq_combination childrenC_607_i4 childrenD_607_i4 (4, 6) required_607_i4
    (by decide +kernel) child_required_sub_607_i4 common_sub_607_i4 required_origin_607_i4
theorem envelope_origin_607_i4 : ∀ x ∈ envelope_607_i4,
    x = (4, 6) ∨ ∃ j, x ∈ childrenD_607_i4 j := by decide +kernel
theorem envelope_exact_607_i4 : envelope_607_i4 =
    insert (4, 6) (Finset.univ.biUnion childrenD_607_i4) := by
  exact envelope_eq_combination childrenD_607_i4 (4, 6) envelope_607_i4
    pivot_mem_607_i4 child_envelope_sub_607_i4 envelope_origin_607_i4
def checked_607_i4 : CheckedCard where
  required := required_607_i4
  envelope := envelope_607_i4
  height := height_607_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_607_i4
def height_607 : ℕ := 8
def childrenH_607 : Fin 5 → ℕ := ![height_13, height_211, height_607_i0, height_607_i1, height_607_i4]
theorem height_exact_607 : height_607 = 1 + Finset.univ.sup childrenH_607 := by decide +kernel
theorem required_origin_607 : ∀ x ∈ required_607,
    (∃ j, x ∈ childrenC_607 j) ∨ ∀ j, x ∈ childrenD_607 j := by decide +kernel
theorem required_exact_607 : required_607 =
    ((Finset.univ.biUnion childrenC_607) ∪ commonEnvelope childrenD_607).erase (4, 3) := by
  exact required_eq_combination childrenC_607 childrenD_607 (4, 3) required_607
    (by decide +kernel) child_required_sub_607 common_sub_607 required_origin_607
theorem envelope_origin_607 : ∀ x ∈ envelope_607,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_607 j := by decide +kernel
theorem envelope_exact_607 : envelope_607 =
    insert (4, 3) (Finset.univ.biUnion childrenD_607) := by
  exact envelope_eq_combination childrenD_607 (4, 3) envelope_607
    pivot_mem_607 child_envelope_sub_607 envelope_origin_607
def checked_607 : CheckedCard where
  required := required_607
  envelope := envelope_607
  height := height_607
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_607
def height_619_i0 : ℕ := 7
def childrenH_619_i0 : Fin 2 → ℕ := ![height_56, height_253]
theorem height_exact_619_i0 : height_619_i0 = 1 + Finset.univ.sup childrenH_619_i0 := by decide +kernel
theorem required_origin_619_i0 : ∀ x ∈ required_619_i0,
    (∃ j, x ∈ childrenC_619_i0 j) ∨ ∀ j, x ∈ childrenD_619_i0 j := by decide +kernel
theorem required_exact_619_i0 : required_619_i0 =
    ((Finset.univ.biUnion childrenC_619_i0) ∪ commonEnvelope childrenD_619_i0).erase (2, 2) := by
  exact required_eq_combination childrenC_619_i0 childrenD_619_i0 (2, 2) required_619_i0
    (by decide +kernel) child_required_sub_619_i0 common_sub_619_i0 required_origin_619_i0
theorem envelope_origin_619_i0 : ∀ x ∈ envelope_619_i0,
    x = (2, 2) ∨ ∃ j, x ∈ childrenD_619_i0 j := by decide +kernel
theorem envelope_exact_619_i0 : envelope_619_i0 =
    insert (2, 2) (Finset.univ.biUnion childrenD_619_i0) := by
  exact envelope_eq_combination childrenD_619_i0 (2, 2) envelope_619_i0
    pivot_mem_619_i0 child_envelope_sub_619_i0 envelope_origin_619_i0
def checked_619_i0 : CheckedCard where
  required := required_619_i0
  envelope := envelope_619_i0
  height := height_619_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_619_i0
def height_619 : ℕ := 8
def childrenH_619 : Fin 6 → ℕ := ![height_8, height_26, height_49, height_115, height_292, height_619_i0]
theorem height_exact_619 : height_619 = 1 + Finset.univ.sup childrenH_619 := by decide +kernel
theorem required_origin_619 : ∀ x ∈ required_619,
    (∃ j, x ∈ childrenC_619 j) ∨ ∀ j, x ∈ childrenD_619 j := by decide +kernel
theorem required_exact_619 : required_619 =
    ((Finset.univ.biUnion childrenC_619) ∪ commonEnvelope childrenD_619).erase (4, 3) := by
  exact required_eq_combination childrenC_619 childrenD_619 (4, 3) required_619
    (by decide +kernel) child_required_sub_619 common_sub_619 required_origin_619
theorem envelope_origin_619 : ∀ x ∈ envelope_619,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_619 j := by decide +kernel
theorem envelope_exact_619 : envelope_619 =
    insert (4, 3) (Finset.univ.biUnion childrenD_619) := by
  exact envelope_eq_combination childrenD_619 (4, 3) envelope_619
    pivot_mem_619 child_envelope_sub_619 envelope_origin_619
def checked_619 : CheckedCard where
  required := required_619
  envelope := envelope_619
  height := height_619
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_619
def height_651_i0 : ℕ := 5
def childrenH_651_i0 : Fin 2 → ℕ := ![height_55, height_56]
theorem height_exact_651_i0 : height_651_i0 = 1 + Finset.univ.sup childrenH_651_i0 := by decide +kernel
theorem required_origin_651_i0 : ∀ x ∈ required_651_i0,
    (∃ j, x ∈ childrenC_651_i0 j) ∨ ∀ j, x ∈ childrenD_651_i0 j := by decide +kernel
theorem required_exact_651_i0 : required_651_i0 =
    ((Finset.univ.biUnion childrenC_651_i0) ∪ commonEnvelope childrenD_651_i0).erase (3, 5) := by
  exact required_eq_combination childrenC_651_i0 childrenD_651_i0 (3, 5) required_651_i0
    (by decide +kernel) child_required_sub_651_i0 common_sub_651_i0 required_origin_651_i0
theorem envelope_origin_651_i0 : ∀ x ∈ envelope_651_i0,
    x = (3, 5) ∨ ∃ j, x ∈ childrenD_651_i0 j := by decide +kernel
theorem envelope_exact_651_i0 : envelope_651_i0 =
    insert (3, 5) (Finset.univ.biUnion childrenD_651_i0) := by
  exact envelope_eq_combination childrenD_651_i0 (3, 5) envelope_651_i0
    pivot_mem_651_i0 child_envelope_sub_651_i0 envelope_origin_651_i0
def checked_651_i0 : CheckedCard where
  required := required_651_i0
  envelope := envelope_651_i0
  height := height_651_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_651_i0
def height_651_i1 : ℕ := 5
def childrenH_651_i1 : Fin 3 → ℕ := ![height_20, height_29, height_46]
theorem height_exact_651_i1 : height_651_i1 = 1 + Finset.univ.sup childrenH_651_i1 := by decide +kernel
theorem required_origin_651_i1 : ∀ x ∈ required_651_i1,
    (∃ j, x ∈ childrenC_651_i1 j) ∨ ∀ j, x ∈ childrenD_651_i1 j := by decide +kernel
theorem required_exact_651_i1 : required_651_i1 =
    ((Finset.univ.biUnion childrenC_651_i1) ∪ commonEnvelope childrenD_651_i1).erase (3, 5) := by
  exact required_eq_combination childrenC_651_i1 childrenD_651_i1 (3, 5) required_651_i1
    (by decide +kernel) child_required_sub_651_i1 common_sub_651_i1 required_origin_651_i1
theorem envelope_origin_651_i1 : ∀ x ∈ envelope_651_i1,
    x = (3, 5) ∨ ∃ j, x ∈ childrenD_651_i1 j := by decide +kernel
theorem envelope_exact_651_i1 : envelope_651_i1 =
    insert (3, 5) (Finset.univ.biUnion childrenD_651_i1) := by
  exact envelope_eq_combination childrenD_651_i1 (3, 5) envelope_651_i1
    pivot_mem_651_i1 child_envelope_sub_651_i1 envelope_origin_651_i1
def checked_651_i1 : CheckedCard where
  required := required_651_i1
  envelope := envelope_651_i1
  height := height_651_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_651_i1
def height_651_i2 : ℕ := 7
def childrenH_651_i2 : Fin 2 → ℕ := ![height_85, height_94]
theorem height_exact_651_i2 : height_651_i2 = 1 + Finset.univ.sup childrenH_651_i2 := by decide +kernel
theorem required_origin_651_i2 : ∀ x ∈ required_651_i2,
    (∃ j, x ∈ childrenC_651_i2 j) ∨ ∀ j, x ∈ childrenD_651_i2 j := by decide +kernel
theorem required_exact_651_i2 : required_651_i2 =
    ((Finset.univ.biUnion childrenC_651_i2) ∪ commonEnvelope childrenD_651_i2).erase (4, 3) := by
  exact required_eq_combination childrenC_651_i2 childrenD_651_i2 (4, 3) required_651_i2
    (by decide +kernel) child_required_sub_651_i2 common_sub_651_i2 required_origin_651_i2
theorem envelope_origin_651_i2 : ∀ x ∈ envelope_651_i2,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_651_i2 j := by decide +kernel
theorem envelope_exact_651_i2 : envelope_651_i2 =
    insert (4, 3) (Finset.univ.biUnion childrenD_651_i2) := by
  exact envelope_eq_combination childrenD_651_i2 (4, 3) envelope_651_i2
    pivot_mem_651_i2 child_envelope_sub_651_i2 envelope_origin_651_i2
def checked_651_i2 : CheckedCard where
  required := required_651_i2
  envelope := envelope_651_i2
  height := height_651_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_651_i2
def height_651 : ℕ := 8
def childrenH_651 : Fin 3 → ℕ := ![height_651_i0, height_651_i1, height_651_i2]
theorem height_exact_651 : height_651 = 1 + Finset.univ.sup childrenH_651 := by decide +kernel
theorem required_origin_651 : ∀ x ∈ required_651,
    (∃ j, x ∈ childrenC_651 j) ∨ ∀ j, x ∈ childrenD_651 j := by decide +kernel
theorem required_exact_651 : required_651 =
    ((Finset.univ.biUnion childrenC_651) ∪ commonEnvelope childrenD_651).erase (3, 6) := by
  exact required_eq_combination childrenC_651 childrenD_651 (3, 6) required_651
    (by decide +kernel) child_required_sub_651 common_sub_651 required_origin_651
theorem envelope_origin_651 : ∀ x ∈ envelope_651,
    x = (3, 6) ∨ ∃ j, x ∈ childrenD_651 j := by decide +kernel
theorem envelope_exact_651 : envelope_651 =
    insert (3, 6) (Finset.univ.biUnion childrenD_651) := by
  exact envelope_eq_combination childrenD_651 (3, 6) envelope_651
    pivot_mem_651 child_envelope_sub_651 envelope_origin_651
def checked_651 : CheckedCard where
  required := required_651
  envelope := envelope_651
  height := height_651
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_651
end SnakyPrototype.Certificate21

end OAI
