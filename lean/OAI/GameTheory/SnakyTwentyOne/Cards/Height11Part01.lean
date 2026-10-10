import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height10Part01
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_427_i6 : Finset Cell := ⟨(([(0, 4), (1, 2), (1, 3), (1, 4), (2, 1), (2, 4), (3, 1), (4, 1), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_427_i6 : Finset Cell := ⟨(([(0, 4), (1, 2), (1, 3), (1, 4), (2, 1), (2, 2), (2, 3), (2, 4), (3, 1), (3, 3), (3, 4), (4, 1), (4, 2), (4, 3), (4, 4), (5, 0), (5, 1), (6, 0)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_427_i6 : Fin 2 → Finset Cell := ![(placed21 3 (0, 4) required_70), (placed21 0 (1, 0) required_226)]
def childrenD_427_i6 : Fin 2 → Finset Cell := ![(placed21 3 (0, 4) envelope_70), (placed21 0 (1, 0) envelope_226)]
theorem common_sub_427_i6 : commonEnvelope childrenD_427_i6 ⊆ insert (4, 3) required_427_i6 := by decide +kernel
theorem child_required_sub_427_i6 : ∀ j, childrenC_427_i6 j ⊆ insert (4, 3) required_427_i6 := by decide +kernel
theorem child_envelope_sub_427_i6 : ∀ j, childrenD_427_i6 j ⊆ envelope_427_i6 := by decide +kernel
theorem pivot_mem_427_i6 : (4, 3) ∈ envelope_427_i6 := by decide +kernel
theorem children_work_427_i6 : ∀ j, Template HasSnaky 3 (childrenC_427_i6 j) (childrenD_427_i6 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_70 3 (0, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_226 0 (1, 0)).mono (by decide +kernel)
theorem row_works_427_i6 : Template HasSnaky 4 required_427_i6 envelope_427_i6 := by
  refine compose HasSnaky 3 childrenC_427_i6 childrenD_427_i6 children_work_427_i6 (4, 3)
    required_427_i6 envelope_427_i6 pivot_mem_427_i6 child_required_sub_427_i6 child_envelope_sub_427_i6 ?_
  intro b hb
  exact common_sub_427_i6 (mem_commonEnvelope childrenD_427_i6 b hb)
def required_427_i5 : Finset Cell := ⟨(([(0, 4), (1, 1), (1, 2), (1, 3), (1, 4), (2, 1), (2, 4), (3, 1), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_427_i5 : Finset Cell := ⟨(([(0, 4), (1, 1), (1, 2), (1, 3), (1, 4), (2, 1), (2, 2), (2, 3), (2, 4), (3, 1), (3, 3), (3, 4), (4, 1), (4, 2), (4, 3), (4, 4), (5, 0), (5, 1), (5, 2), (6, 0)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_427_i5 : Fin 2 → Finset Cell := ![(placed21 0 (1, 1) required_5), required_427_i6]
def childrenD_427_i5 : Fin 2 → Finset Cell := ![(placed21 0 (1, 1) envelope_5), envelope_427_i6]
theorem common_sub_427_i5 : commonEnvelope childrenD_427_i5 ⊆ insert (4, 1) required_427_i5 := by decide +kernel
theorem child_required_sub_427_i5 : ∀ j, childrenC_427_i5 j ⊆ insert (4, 1) required_427_i5 := by decide +kernel
theorem child_envelope_sub_427_i5 : ∀ j, childrenD_427_i5 j ⊆ envelope_427_i5 := by decide +kernel
theorem pivot_mem_427_i5 : (4, 1) ∈ envelope_427_i5 := by decide +kernel
theorem children_work_427_i5 : ∀ j, Template HasSnaky 4 (childrenC_427_i5 j) (childrenD_427_i5 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 0 (1, 1)).mono (by decide +kernel)
  · exact row_works_427_i6.mono (by decide +kernel)
theorem row_works_427_i5 : Template HasSnaky 5 required_427_i5 envelope_427_i5 := by
  refine compose HasSnaky 4 childrenC_427_i5 childrenD_427_i5 children_work_427_i5 (4, 1)
    required_427_i5 envelope_427_i5 pivot_mem_427_i5 child_required_sub_427_i5 child_envelope_sub_427_i5 ?_
  intro b hb
  exact common_sub_427_i5 (mem_commonEnvelope childrenD_427_i5 b hb)
def required_427_i4 : Finset Cell := ⟨(([(0, 1), (0, 4), (1, 1), (1, 2), (1, 3), (1, 4), (2, 1), (2, 4), (3, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_427_i4 : Finset Cell := ⟨(([(0, 1), (0, 4), (1, 1), (1, 2), (1, 3), (1, 4), (2, 1), (2, 2), (2, 3), (2, 4), (3, 1), (3, 2), (3, 3), (3, 4), (4, 1), (4, 2), (4, 3), (4, 4), (5, 0), (5, 1), (5, 2), (6, 0)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_427_i4 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) required_4), required_427_i5]
def childrenD_427_i4 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) envelope_4), envelope_427_i5]
theorem common_sub_427_i4 : commonEnvelope childrenD_427_i4 ⊆ insert (4, 2) required_427_i4 := by decide +kernel
theorem child_required_sub_427_i4 : ∀ j, childrenC_427_i4 j ⊆ insert (4, 2) required_427_i4 := by decide +kernel
theorem child_envelope_sub_427_i4 : ∀ j, childrenD_427_i4 j ⊆ envelope_427_i4 := by decide +kernel
theorem pivot_mem_427_i4 : (4, 2) ∈ envelope_427_i4 := by decide +kernel
theorem children_work_427_i4 : ∀ j, Template HasSnaky 5 (childrenC_427_i4 j) (childrenD_427_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_4 0 (0, 1)).mono (by decide +kernel)
  · exact row_works_427_i5.mono (by decide +kernel)
theorem row_works_427_i4 : Template HasSnaky 6 required_427_i4 envelope_427_i4 := by
  refine compose HasSnaky 5 childrenC_427_i4 childrenD_427_i4 children_work_427_i4 (4, 2)
    required_427_i4 envelope_427_i4 pivot_mem_427_i4 child_required_sub_427_i4 child_envelope_sub_427_i4 ?_
  intro b hb
  exact common_sub_427_i4 (mem_commonEnvelope childrenD_427_i4 b hb)
def required_427_i9 : Finset Cell := ⟨(([(0, 4), (1, 3), (1, 4), (2, 3), (2, 4), (3, 0), (3, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_427_i9 : Finset Cell := ⟨(([(0, 4), (1, 3), (1, 4), (2, 3), (2, 4), (3, 0), (3, 1), (3, 2), (3, 3), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_427_i9 : Fin 2 → Finset Cell := ![(placed21 2 (4, 3) required_0), (placed21 5 (3, 0) required_2)]
def childrenD_427_i9 : Fin 2 → Finset Cell := ![(placed21 2 (4, 3) envelope_0), (placed21 5 (3, 0) envelope_2)]
theorem common_sub_427_i9 : commonEnvelope childrenD_427_i9 ⊆ insert (3, 3) required_427_i9 := by decide +kernel
theorem child_required_sub_427_i9 : ∀ j, childrenC_427_i9 j ⊆ insert (3, 3) required_427_i9 := by decide +kernel
theorem child_envelope_sub_427_i9 : ∀ j, childrenD_427_i9 j ⊆ envelope_427_i9 := by decide +kernel
theorem pivot_mem_427_i9 : (3, 3) ∈ envelope_427_i9 := by decide +kernel
theorem children_work_427_i9 : ∀ j, Template HasSnaky 1 (childrenC_427_i9 j) (childrenD_427_i9 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 2 (4, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_2 5 (3, 0)).mono (by decide +kernel)
theorem row_works_427_i9 : Template HasSnaky 2 required_427_i9 envelope_427_i9 := by
  refine compose HasSnaky 1 childrenC_427_i9 childrenD_427_i9 children_work_427_i9 (3, 3)
    required_427_i9 envelope_427_i9 pivot_mem_427_i9 child_required_sub_427_i9 child_envelope_sub_427_i9 ?_
  intro b hb
  exact common_sub_427_i9 (mem_commonEnvelope childrenD_427_i9 b hb)
def required_427_i8 : Finset Cell := ⟨(([(0, 4), (1, 3), (1, 4), (2, 1), (2, 4), (3, 0), (3, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_427_i8 : Finset Cell := ⟨(([(0, 4), (1, 3), (1, 4), (2, 1), (2, 2), (2, 3), (2, 4), (3, 0), (3, 1), (3, 2), (3, 3), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_427_i8 : Fin 2 → Finset Cell := ![(placed21 3 (2, 4) required_2), required_427_i9]
def childrenD_427_i8 : Fin 2 → Finset Cell := ![(placed21 3 (2, 4) envelope_2), envelope_427_i9]
theorem common_sub_427_i8 : commonEnvelope childrenD_427_i8 ⊆ insert (2, 3) required_427_i8 := by decide +kernel
theorem child_required_sub_427_i8 : ∀ j, childrenC_427_i8 j ⊆ insert (2, 3) required_427_i8 := by decide +kernel
theorem child_envelope_sub_427_i8 : ∀ j, childrenD_427_i8 j ⊆ envelope_427_i8 := by decide +kernel
theorem pivot_mem_427_i8 : (2, 3) ∈ envelope_427_i8 := by decide +kernel
theorem children_work_427_i8 : ∀ j, Template HasSnaky 2 (childrenC_427_i8 j) (childrenD_427_i8 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_2 3 (2, 4)).mono (by decide +kernel)
  · exact row_works_427_i9.mono (by decide +kernel)
theorem row_works_427_i8 : Template HasSnaky 3 required_427_i8 envelope_427_i8 := by
  refine compose HasSnaky 2 childrenC_427_i8 childrenD_427_i8 children_work_427_i8 (2, 3)
    required_427_i8 envelope_427_i8 pivot_mem_427_i8 child_required_sub_427_i8 child_envelope_sub_427_i8 ?_
  intro b hb
  exact common_sub_427_i8 (mem_commonEnvelope childrenD_427_i8 b hb)
def required_427_i7 : Finset Cell := ⟨(([(0, 4), (1, 1), (1, 3), (1, 4), (2, 1), (2, 4), (3, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_427_i7 : Finset Cell := ⟨(([(0, 1), (0, 4), (1, 1), (1, 3), (1, 4), (2, 1), (2, 2), (2, 3), (2, 4), (3, 0), (3, 1), (3, 2), (3, 3), (4, 0), (4, 1), (4, 3), (5, 0), (6, 0)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_427_i7 : Fin 2 → Finset Cell := ![(placed21 3 (0, 1) required_52), required_427_i8]
def childrenD_427_i7 : Fin 2 → Finset Cell := ![(placed21 3 (0, 1) envelope_52), envelope_427_i8]
theorem common_sub_427_i7 : commonEnvelope childrenD_427_i7 ⊆ insert (3, 0) required_427_i7 := by decide +kernel
theorem child_required_sub_427_i7 : ∀ j, childrenC_427_i7 j ⊆ insert (3, 0) required_427_i7 := by decide +kernel
theorem child_envelope_sub_427_i7 : ∀ j, childrenD_427_i7 j ⊆ envelope_427_i7 := by decide +kernel
theorem pivot_mem_427_i7 : (3, 0) ∈ envelope_427_i7 := by decide +kernel
theorem children_work_427_i7 : ∀ j, Template HasSnaky 3 (childrenC_427_i7 j) (childrenD_427_i7 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_52 3 (0, 1)).mono (by decide +kernel)
  · exact row_works_427_i8.mono (by decide +kernel)
theorem row_works_427_i7 : Template HasSnaky 4 required_427_i7 envelope_427_i7 := by
  refine compose HasSnaky 3 childrenC_427_i7 childrenD_427_i7 children_work_427_i7 (3, 0)
    required_427_i7 envelope_427_i7 pivot_mem_427_i7 child_required_sub_427_i7 child_envelope_sub_427_i7 ?_
  intro b hb
  exact common_sub_427_i7 (mem_commonEnvelope childrenD_427_i7 b hb)
def required_427_i3 : Finset Cell := ⟨(([(0, 1), (0, 4), (1, 1), (1, 2), (1, 3), (1, 4), (2, 1), (2, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_427_i3 : Finset Cell := ⟨(([(0, 1), (0, 4), (1, 1), (1, 2), (1, 3), (1, 4), (2, 1), (2, 2), (2, 3), (2, 4), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, 0), (5, 1), (5, 2), (6, 0), (6, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_427_i3 : Fin 4 → Finset Cell := ![(placed21 3 (0, 2) required_17), (placed21 3 (0, 4) required_357), required_427_i4, required_427_i7]
def childrenD_427_i3 : Fin 4 → Finset Cell := ![(placed21 3 (0, 2) envelope_17), (placed21 3 (0, 4) envelope_357), envelope_427_i4, envelope_427_i7]
theorem common_sub_427_i3 : commonEnvelope childrenD_427_i3 ⊆ insert (3, 1) required_427_i3 := by decide +kernel
theorem child_required_sub_427_i3 : ∀ j, childrenC_427_i3 j ⊆ insert (3, 1) required_427_i3 := by decide +kernel
theorem child_envelope_sub_427_i3 : ∀ j, childrenD_427_i3 j ⊆ envelope_427_i3 := by decide +kernel
theorem pivot_mem_427_i3 : (3, 1) ∈ envelope_427_i3 := by decide +kernel
theorem children_work_427_i3 : ∀ j, Template HasSnaky 6 (childrenC_427_i3 j) (childrenD_427_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_17 3 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_357 3 (0, 4)).mono (by decide +kernel)
  · exact row_works_427_i4.mono (by decide +kernel)
  · exact row_works_427_i7.mono (by decide +kernel)
theorem row_works_427_i3 : Template HasSnaky 7 required_427_i3 envelope_427_i3 := by
  refine compose HasSnaky 6 childrenC_427_i3 childrenD_427_i3 children_work_427_i3 (3, 1)
    required_427_i3 envelope_427_i3 pivot_mem_427_i3 child_required_sub_427_i3 child_envelope_sub_427_i3 ?_
  intro b hb
  exact common_sub_427_i3 (mem_commonEnvelope childrenD_427_i3 b hb)
def required_427_i2 : Finset Cell := ⟨(([(0, 4), (1, 1), (1, 2), (1, 3), (1, 4), (2, 1), (2, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_427_i2 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 4), (1, 1), (1, 2), (1, 3), (1, 4), (2, 1), (2, 2), (2, 3), (2, 4), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, 0), (5, 1), (5, 2), (6, 0), (6, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_427_i2 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) required_5), required_427_i3]
def childrenD_427_i2 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) envelope_5), envelope_427_i3]
theorem common_sub_427_i2 : commonEnvelope childrenD_427_i2 ⊆ insert (0, 1) required_427_i2 := by decide +kernel
theorem child_required_sub_427_i2 : ∀ j, childrenC_427_i2 j ⊆ insert (0, 1) required_427_i2 := by decide +kernel
theorem child_envelope_sub_427_i2 : ∀ j, childrenD_427_i2 j ⊆ envelope_427_i2 := by decide +kernel
theorem pivot_mem_427_i2 : (0, 1) ∈ envelope_427_i2 := by decide +kernel
theorem children_work_427_i2 : ∀ j, Template HasSnaky 7 (childrenC_427_i2 j) (childrenD_427_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 7 (1, 4)).mono (by decide +kernel)
  · exact row_works_427_i3.mono (by decide +kernel)
theorem row_works_427_i2 : Template HasSnaky 8 required_427_i2 envelope_427_i2 := by
  refine compose HasSnaky 7 childrenC_427_i2 childrenD_427_i2 children_work_427_i2 (0, 1)
    required_427_i2 envelope_427_i2 pivot_mem_427_i2 child_required_sub_427_i2 child_envelope_sub_427_i2 ?_
  intro b hb
  exact common_sub_427_i2 (mem_commonEnvelope childrenD_427_i2 b hb)
def required_427_i1 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 3), (1, 4), (2, 1), (2, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_427_i1 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 4), (0, 5), (1, 1), (1, 2), (1, 3), (1, 4), (2, 1), (2, 2), (2, 3), (2, 4), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, 0), (5, 1), (5, 2), (6, 0), (6, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_427_i1 : Fin 2 → Finset Cell := ![(placed21 5 (1, 1) required_5), required_427_i2]
def childrenD_427_i1 : Fin 2 → Finset Cell := ![(placed21 5 (1, 1) envelope_5), envelope_427_i2]
theorem common_sub_427_i1 : commonEnvelope childrenD_427_i1 ⊆ insert (0, 4) required_427_i1 := by decide +kernel
theorem child_required_sub_427_i1 : ∀ j, childrenC_427_i1 j ⊆ insert (0, 4) required_427_i1 := by decide +kernel
theorem child_envelope_sub_427_i1 : ∀ j, childrenD_427_i1 j ⊆ envelope_427_i1 := by decide +kernel
theorem pivot_mem_427_i1 : (0, 4) ∈ envelope_427_i1 := by decide +kernel
theorem children_work_427_i1 : ∀ j, Template HasSnaky 8 (childrenC_427_i1 j) (childrenD_427_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 5 (1, 1)).mono (by decide +kernel)
  · exact row_works_427_i2.mono (by decide +kernel)
theorem row_works_427_i1 : Template HasSnaky 9 required_427_i1 envelope_427_i1 := by
  refine compose HasSnaky 8 childrenC_427_i1 childrenD_427_i1 children_work_427_i1 (0, 4)
    required_427_i1 envelope_427_i1 pivot_mem_427_i1 child_required_sub_427_i1 child_envelope_sub_427_i1 ?_
  intro b hb
  exact common_sub_427_i1 (mem_commonEnvelope childrenD_427_i1 b hb)
def required_427_i0 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 3), (1, 4), (2, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_427_i0 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 4), (0, 5), (1, 1), (1, 2), (1, 3), (1, 4), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, 0), (5, 1), (5, 2), (6, 0), (6, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_427_i0 : Fin 2 → Finset Cell := ![(placed21 1 (1, 1) required_5), required_427_i1]
def childrenD_427_i0 : Fin 2 → Finset Cell := ![(placed21 1 (1, 1) envelope_5), envelope_427_i1]
theorem common_sub_427_i0 : commonEnvelope childrenD_427_i0 ⊆ insert (2, 4) required_427_i0 := by decide +kernel
theorem child_required_sub_427_i0 : ∀ j, childrenC_427_i0 j ⊆ insert (2, 4) required_427_i0 := by decide +kernel
theorem child_envelope_sub_427_i0 : ∀ j, childrenD_427_i0 j ⊆ envelope_427_i0 := by decide +kernel
theorem pivot_mem_427_i0 : (2, 4) ∈ envelope_427_i0 := by decide +kernel
theorem children_work_427_i0 : ∀ j, Template HasSnaky 9 (childrenC_427_i0 j) (childrenD_427_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 1 (1, 1)).mono (by decide +kernel)
  · exact row_works_427_i1.mono (by decide +kernel)
theorem row_works_427_i0 : Template HasSnaky 10 required_427_i0 envelope_427_i0 := by
  refine compose HasSnaky 9 childrenC_427_i0 childrenD_427_i0 children_work_427_i0 (2, 4)
    required_427_i0 envelope_427_i0 pivot_mem_427_i0 child_required_sub_427_i0 child_envelope_sub_427_i0 ?_
  intro b hb
  exact common_sub_427_i0 (mem_commonEnvelope childrenD_427_i0 b hb)
def required_427 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 3), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_427 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 4), (0, 5), (1, 1), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, 0), (5, 1), (5, 2), (6, 0), (6, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_427 : Fin 2 → Finset Cell := ![(placed21 3 (1, 4) required_5), required_427_i0]
def childrenD_427 : Fin 2 → Finset Cell := ![(placed21 3 (1, 4) envelope_5), envelope_427_i0]
theorem common_sub_427 : commonEnvelope childrenD_427 ⊆ insert (2, 1) required_427 := by decide +kernel
theorem child_required_sub_427 : ∀ j, childrenC_427 j ⊆ insert (2, 1) required_427 := by decide +kernel
theorem child_envelope_sub_427 : ∀ j, childrenD_427 j ⊆ envelope_427 := by decide +kernel
theorem pivot_mem_427 : (2, 1) ∈ envelope_427 := by decide +kernel
theorem children_work_427 : ∀ j, Template HasSnaky 10 (childrenC_427 j) (childrenD_427 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 3 (1, 4)).mono (by decide +kernel)
  · exact row_works_427_i0.mono (by decide +kernel)
theorem row_works_427 : Template HasSnaky 11 required_427 envelope_427 := by
  refine compose HasSnaky 10 childrenC_427 childrenD_427 children_work_427 (2, 1)
    required_427 envelope_427 pivot_mem_427 child_required_sub_427 child_envelope_sub_427 ?_
  intro b hb
  exact common_sub_427 (mem_commonEnvelope childrenD_427 b hb)
def required_463_i0 : Finset Cell := ⟨(([(1, 2), (1, 3), (1, 4), (1, 5), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_463_i0 : Finset Cell := ⟨(([(0, 6), (0, 7), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 5), (2, 6), (2, 7), (3, 5), (3, 6), (3, 7), (4, 5), (4, 6), (4, 7), (5, 5), (5, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_463_i0 : Fin 2 → Finset Cell := ![(placed21 1 (1, 2) required_4), (placed21 1 (0, 3) required_348)]
def childrenD_463_i0 : Fin 2 → Finset Cell := ![(placed21 1 (1, 2) envelope_4), (placed21 1 (0, 3) envelope_348)]
theorem common_sub_463_i0 : commonEnvelope childrenD_463_i0 ⊆ insert (2, 6) required_463_i0 := by decide +kernel
theorem child_required_sub_463_i0 : ∀ j, childrenC_463_i0 j ⊆ insert (2, 6) required_463_i0 := by decide +kernel
theorem child_envelope_sub_463_i0 : ∀ j, childrenD_463_i0 j ⊆ envelope_463_i0 := by decide +kernel
theorem pivot_mem_463_i0 : (2, 6) ∈ envelope_463_i0 := by decide +kernel
theorem children_work_463_i0 : ∀ j, Template HasSnaky 6 (childrenC_463_i0 j) (childrenD_463_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_4 1 (1, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_348 1 (0, 3)).mono (by decide +kernel)
theorem row_works_463_i0 : Template HasSnaky 7 required_463_i0 envelope_463_i0 := by
  refine compose HasSnaky 6 childrenC_463_i0 childrenD_463_i0 children_work_463_i0 (2, 6)
    required_463_i0 envelope_463_i0 pivot_mem_463_i0 child_required_sub_463_i0 child_envelope_sub_463_i0 ?_
  intro b hb
  exact common_sub_463_i0 (mem_commonEnvelope childrenD_463_i0 b hb)
def required_463 : Finset Cell := ⟨(([(1, 2), (1, 3), (1, 4), (1, 5), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_463 : Finset Cell := ⟨(([(0, 4), (0, 6), (0, 7), (0, 8), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 5), (2, 6), (2, 7), (3, 0), (3, 1), (3, 2), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, 4), (7, 5), (7, 6), (7, 7), (8, 4), (8, 5), (8, 6), (8, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_463 : Fin 5 → Finset Cell := ![(placed21 1 (0, 2) required_147), (placed21 1 (0, 2) required_167), required_463_i0, required_353, (placed21 4 (3, 8) required_460)]
def childrenD_463 : Fin 5 → Finset Cell := ![(placed21 1 (0, 2) envelope_147), (placed21 1 (0, 2) envelope_167), envelope_463_i0, envelope_353, (placed21 4 (3, 8) envelope_460)]
theorem common_sub_463 : commonEnvelope childrenD_463 ⊆ insert (4, 5) required_463 := by decide +kernel
theorem child_required_sub_463 : ∀ j, childrenC_463 j ⊆ insert (4, 5) required_463 := by decide +kernel
theorem child_envelope_sub_463 : ∀ j, childrenD_463 j ⊆ envelope_463 := by decide +kernel
theorem pivot_mem_463 : (4, 5) ∈ envelope_463 := by decide +kernel
theorem children_work_463 : ∀ j, Template HasSnaky 10 (childrenC_463 j) (childrenD_463 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_147 1 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_167 1 (0, 2)).mono (by decide +kernel)
  · exact row_works_463_i0.mono (by decide +kernel)
  · exact row_works_353.mono (by decide +kernel)
  · exact (placed21_template row_works_460 4 (3, 8)).mono (by decide +kernel)
theorem row_works_463 : Template HasSnaky 11 required_463 envelope_463 := by
  refine compose HasSnaky 10 childrenC_463 childrenD_463 children_work_463 (4, 5)
    required_463 envelope_463 pivot_mem_463 child_required_sub_463 child_envelope_sub_463 ?_
  intro b hb
  exact common_sub_463 (mem_commonEnvelope childrenD_463 b hb)
def required_467 : Finset Cell := ⟨(([(1, 4), (1, 5), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_467 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 5), (0, 6), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 7), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 1), (3, 2), (3, 3), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, 1), (5, 2), (5, 3), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, 5), (7, 6), (7, 7), (7, 8), (8, 5), (8, 6), (8, 7), (8, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_467 : Fin 4 → Finset Cell := ![(placed21 6 (5, 8) required_31), (placed21 1 (1, 4) required_398), (placed21 6 (5, 7) required_444), (placed21 6 (5, 7) required_466)]
def childrenD_467 : Fin 4 → Finset Cell := ![(placed21 6 (5, 8) envelope_31), (placed21 1 (1, 4) envelope_398), (placed21 6 (5, 7) envelope_444), (placed21 6 (5, 7) envelope_466)]
theorem common_sub_467 : commonEnvelope childrenD_467 ⊆ insert (4, 6) required_467 := by decide +kernel
theorem child_required_sub_467 : ∀ j, childrenC_467 j ⊆ insert (4, 6) required_467 := by decide +kernel
theorem child_envelope_sub_467 : ∀ j, childrenD_467 j ⊆ envelope_467 := by decide +kernel
theorem pivot_mem_467 : (4, 6) ∈ envelope_467 := by decide +kernel
theorem children_work_467 : ∀ j, Template HasSnaky 10 (childrenC_467 j) (childrenD_467 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_31 6 (5, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_398 1 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_444 6 (5, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_466 6 (5, 7)).mono (by decide +kernel)
theorem row_works_467 : Template HasSnaky 11 required_467 envelope_467 := by
  refine compose HasSnaky 10 childrenC_467 childrenD_467 children_work_467 (4, 6)
    required_467 envelope_467 pivot_mem_467 child_required_sub_467 child_envelope_sub_467 ?_
  intro b hb
  exact common_sub_467 (mem_commonEnvelope childrenD_467 b hb)
def required_468_i1 : Finset Cell := ⟨(([(1, 3), (1, 5), (3, 4), (3, 5), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_468_i1 : Finset Cell := ⟨(([(0, 3), (0, 5), (1, 3), (1, 5), (2, 0), (2, 1), (2, 2), (2, 3), (2, 5), (2, 6), (2, 7), (2, 8), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 0), (4, 1), (4, 2), (4, 4), (4, 6), (4, 7), (4, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_468_i1 : Fin 4 → Finset Cell := ![(placed21 6 (4, 6) required_71), (placed21 2 (4, 2) required_71), (placed21 6 (4, 6) required_73), (placed21 2 (4, 2) required_73)]
def childrenD_468_i1 : Fin 4 → Finset Cell := ![(placed21 6 (4, 6) envelope_71), (placed21 2 (4, 2) envelope_71), (placed21 6 (4, 6) envelope_73), (placed21 2 (4, 2) envelope_73)]
theorem common_sub_468_i1 : commonEnvelope childrenD_468_i1 ⊆ insert (3, 3) required_468_i1 := by decide +kernel
theorem child_required_sub_468_i1 : ∀ j, childrenC_468_i1 j ⊆ insert (3, 3) required_468_i1 := by decide +kernel
theorem child_envelope_sub_468_i1 : ∀ j, childrenD_468_i1 j ⊆ envelope_468_i1 := by decide +kernel
theorem pivot_mem_468_i1 : (3, 3) ∈ envelope_468_i1 := by decide +kernel
theorem children_work_468_i1 : ∀ j, Template HasSnaky 5 (childrenC_468_i1 j) (childrenD_468_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_71 6 (4, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_71 2 (4, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_73 6 (4, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_73 2 (4, 2)).mono (by decide +kernel)
theorem row_works_468_i1 : Template HasSnaky 6 required_468_i1 envelope_468_i1 := by
  refine compose HasSnaky 5 childrenC_468_i1 childrenD_468_i1 children_work_468_i1 (3, 3)
    required_468_i1 envelope_468_i1 pivot_mem_468_i1 child_required_sub_468_i1 child_envelope_sub_468_i1 ?_
  intro b hb
  exact common_sub_468_i1 (mem_commonEnvelope childrenD_468_i1 b hb)
def required_468_i3 : Finset Cell := ⟨(([(3, 3), (3, 4), (3, 5), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_468_i3 : Finset Cell := ⟨(([(2, 6), (2, 7), (2, 8), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 5), (5, 6), (5, 7), (5, 8), (6, 5), (6, 6), (6, 7), (7, 5), (7, 6), (7, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_468_i3 : Fin 5 → Finset Cell := ![(placed21 1 (2, 3) required_8), (placed21 2 (4, 3) required_17), (placed21 2 (4, 1) required_75), (placed21 0 (3, 1) required_266), (placed21 0 (2, 2) required_447)]
def childrenD_468_i3 : Fin 5 → Finset Cell := ![(placed21 1 (2, 3) envelope_8), (placed21 2 (4, 3) envelope_17), (placed21 2 (4, 1) envelope_75), (placed21 0 (3, 1) envelope_266), (placed21 0 (2, 2) envelope_447)]
theorem common_sub_468_i3 : commonEnvelope childrenD_468_i3 ⊆ insert (3, 6) required_468_i3 := by decide +kernel
theorem child_required_sub_468_i3 : ∀ j, childrenC_468_i3 j ⊆ insert (3, 6) required_468_i3 := by decide +kernel
theorem child_envelope_sub_468_i3 : ∀ j, childrenD_468_i3 j ⊆ envelope_468_i3 := by decide +kernel
theorem pivot_mem_468_i3 : (3, 6) ∈ envelope_468_i3 := by decide +kernel
theorem children_work_468_i3 : ∀ j, Template HasSnaky 7 (childrenC_468_i3 j) (childrenD_468_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_8 1 (2, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_17 2 (4, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_75 2 (4, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_266 0 (3, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_447 0 (2, 2)).mono (by decide +kernel)
theorem row_works_468_i3 : Template HasSnaky 8 required_468_i3 envelope_468_i3 := by
  refine compose HasSnaky 7 childrenC_468_i3 childrenD_468_i3 children_work_468_i3 (3, 6)
    required_468_i3 envelope_468_i3 pivot_mem_468_i3 child_required_sub_468_i3 child_envelope_sub_468_i3 ?_
  intro b hb
  exact common_sub_468_i3 (mem_commonEnvelope childrenD_468_i3 b hb)
def required_468_i2 : Finset Cell := ⟨(([(1, 3), (3, 4), (3, 5), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_468_i2 : Finset Cell := ⟨(([(0, 3), (1, 3), (2, 0), (2, 1), (2, 2), (2, 3), (2, 6), (2, 7), (2, 8), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 1), (4, 2), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 2), (5, 5), (5, 6), (5, 7), (5, 8), (6, 5), (6, 6), (6, 7), (7, 5), (7, 6), (7, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_468_i2 : Fin 4 → Finset Cell := ![(placed21 2 (4, 2) required_71), (placed21 6 (4, 6) required_73), (placed21 6 (5, 6) required_426), required_468_i3]
def childrenD_468_i2 : Fin 4 → Finset Cell := ![(placed21 2 (4, 2) envelope_71), (placed21 6 (4, 6) envelope_73), (placed21 6 (5, 6) envelope_426), envelope_468_i3]
theorem common_sub_468_i2 : commonEnvelope childrenD_468_i2 ⊆ insert (3, 3) required_468_i2 := by decide +kernel
theorem child_required_sub_468_i2 : ∀ j, childrenC_468_i2 j ⊆ insert (3, 3) required_468_i2 := by decide +kernel
theorem child_envelope_sub_468_i2 : ∀ j, childrenD_468_i2 j ⊆ envelope_468_i2 := by decide +kernel
theorem pivot_mem_468_i2 : (3, 3) ∈ envelope_468_i2 := by decide +kernel
theorem children_work_468_i2 : ∀ j, Template HasSnaky 8 (childrenC_468_i2 j) (childrenD_468_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_71 2 (4, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_73 6 (4, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_426 6 (5, 6)).mono (by decide +kernel)
  · exact row_works_468_i3.mono (by decide +kernel)
theorem row_works_468_i2 : Template HasSnaky 9 required_468_i2 envelope_468_i2 := by
  refine compose HasSnaky 8 childrenC_468_i2 childrenD_468_i2 children_work_468_i2 (3, 3)
    required_468_i2 envelope_468_i2 pivot_mem_468_i2 child_required_sub_468_i2 child_envelope_sub_468_i2 ?_
  intro b hb
  exact common_sub_468_i2 (mem_commonEnvelope childrenD_468_i2 b hb)
def required_468_i0 : Finset Cell := ⟨(([(1, 3), (1, 5), (3, 4), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_468_i0 : Finset Cell := ⟨(([(0, 3), (0, 5), (1, 3), (1, 5), (2, 0), (2, 1), (2, 2), (2, 3), (2, 5), (2, 6), (2, 7), (2, 8), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 0), (4, 1), (4, 2), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 2), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 4), (6, 5), (6, 6), (6, 7), (7, 5), (7, 6), (7, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_468_i0 : Fin 3 → Finset Cell := ![(placed21 3 (0, 5) required_54), required_468_i1, required_468_i2]
def childrenD_468_i0 : Fin 3 → Finset Cell := ![(placed21 3 (0, 5) envelope_54), envelope_468_i1, envelope_468_i2]
theorem common_sub_468_i0 : commonEnvelope childrenD_468_i0 ⊆ insert (3, 5) required_468_i0 := by decide +kernel
theorem child_required_sub_468_i0 : ∀ j, childrenC_468_i0 j ⊆ insert (3, 5) required_468_i0 := by decide +kernel
theorem child_envelope_sub_468_i0 : ∀ j, childrenD_468_i0 j ⊆ envelope_468_i0 := by decide +kernel
theorem pivot_mem_468_i0 : (3, 5) ∈ envelope_468_i0 := by decide +kernel
theorem children_work_468_i0 : ∀ j, Template HasSnaky 9 (childrenC_468_i0 j) (childrenD_468_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_54 3 (0, 5)).mono (by decide +kernel)
  · exact row_works_468_i1.mono (by decide +kernel)
  · exact row_works_468_i2.mono (by decide +kernel)
theorem row_works_468_i0 : Template HasSnaky 10 required_468_i0 envelope_468_i0 := by
  refine compose HasSnaky 9 childrenC_468_i0 childrenD_468_i0 children_work_468_i0 (3, 5)
    required_468_i0 envelope_468_i0 pivot_mem_468_i0 child_required_sub_468_i0 child_envelope_sub_468_i0 ?_
  intro b hb
  exact common_sub_468_i0 (mem_commonEnvelope childrenD_468_i0 b hb)
def required_468 : Finset Cell := ⟨(([(1, 3), (1, 4), (1, 5), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_468 : Finset Cell := ⟨(([(0, 3), (0, 5), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 0), (4, 1), (4, 2), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 2), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 4), (6, 5), (6, 6), (6, 7), (7, 5), (7, 6), (7, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_468 : Fin 4 → Finset Cell := ![(placed21 1 (0, 3) required_28), (placed21 1 (0, 3) required_126), (placed21 3 (0, 5) required_126), required_468_i0]
def childrenD_468 : Fin 4 → Finset Cell := ![(placed21 1 (0, 3) envelope_28), (placed21 1 (0, 3) envelope_126), (placed21 3 (0, 5) envelope_126), envelope_468_i0]
theorem common_sub_468 : commonEnvelope childrenD_468 ⊆ insert (3, 4) required_468 := by decide +kernel
theorem child_required_sub_468 : ∀ j, childrenC_468 j ⊆ insert (3, 4) required_468 := by decide +kernel
theorem child_envelope_sub_468 : ∀ j, childrenD_468 j ⊆ envelope_468 := by decide +kernel
theorem pivot_mem_468 : (3, 4) ∈ envelope_468 := by decide +kernel
theorem children_work_468 : ∀ j, Template HasSnaky 10 (childrenC_468 j) (childrenD_468 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_28 1 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_126 1 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_126 3 (0, 5)).mono (by decide +kernel)
  · exact row_works_468_i0.mono (by decide +kernel)
theorem row_works_468 : Template HasSnaky 11 required_468 envelope_468 := by
  refine compose HasSnaky 10 childrenC_468 childrenD_468 children_work_468 (3, 4)
    required_468 envelope_468 pivot_mem_468 child_required_sub_468 child_envelope_sub_468 ?_
  intro b hb
  exact common_sub_468 (mem_commonEnvelope childrenD_468 b hb)
def height_427_i6 : ℕ := 4
def childrenH_427_i6 : Fin 2 → ℕ := ![height_70, height_226]
theorem height_exact_427_i6 : height_427_i6 = 1 + Finset.univ.sup childrenH_427_i6 := by decide +kernel
theorem required_origin_427_i6 : ∀ x ∈ required_427_i6,
    (∃ j, x ∈ childrenC_427_i6 j) ∨ ∀ j, x ∈ childrenD_427_i6 j := by decide +kernel
theorem required_exact_427_i6 : required_427_i6 =
    ((Finset.univ.biUnion childrenC_427_i6) ∪ commonEnvelope childrenD_427_i6).erase (4, 3) := by
  exact required_eq_combination childrenC_427_i6 childrenD_427_i6 (4, 3) required_427_i6
    (by decide +kernel) child_required_sub_427_i6 common_sub_427_i6 required_origin_427_i6
theorem envelope_origin_427_i6 : ∀ x ∈ envelope_427_i6,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_427_i6 j := by decide +kernel
theorem envelope_exact_427_i6 : envelope_427_i6 =
    insert (4, 3) (Finset.univ.biUnion childrenD_427_i6) := by
  exact envelope_eq_combination childrenD_427_i6 (4, 3) envelope_427_i6
    pivot_mem_427_i6 child_envelope_sub_427_i6 envelope_origin_427_i6
def checked_427_i6 : CheckedCard where
  required := required_427_i6
  envelope := envelope_427_i6
  height := height_427_i6
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_427_i6
def height_427_i5 : ℕ := 5
def childrenH_427_i5 : Fin 2 → ℕ := ![height_5, height_427_i6]
theorem height_exact_427_i5 : height_427_i5 = 1 + Finset.univ.sup childrenH_427_i5 := by decide +kernel
theorem required_origin_427_i5 : ∀ x ∈ required_427_i5,
    (∃ j, x ∈ childrenC_427_i5 j) ∨ ∀ j, x ∈ childrenD_427_i5 j := by decide +kernel
theorem required_exact_427_i5 : required_427_i5 =
    ((Finset.univ.biUnion childrenC_427_i5) ∪ commonEnvelope childrenD_427_i5).erase (4, 1) := by
  exact required_eq_combination childrenC_427_i5 childrenD_427_i5 (4, 1) required_427_i5
    (by decide +kernel) child_required_sub_427_i5 common_sub_427_i5 required_origin_427_i5
theorem envelope_origin_427_i5 : ∀ x ∈ envelope_427_i5,
    x = (4, 1) ∨ ∃ j, x ∈ childrenD_427_i5 j := by decide +kernel
theorem envelope_exact_427_i5 : envelope_427_i5 =
    insert (4, 1) (Finset.univ.biUnion childrenD_427_i5) := by
  exact envelope_eq_combination childrenD_427_i5 (4, 1) envelope_427_i5
    pivot_mem_427_i5 child_envelope_sub_427_i5 envelope_origin_427_i5
def checked_427_i5 : CheckedCard where
  required := required_427_i5
  envelope := envelope_427_i5
  height := height_427_i5
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_427_i5
def height_427_i4 : ℕ := 6
def childrenH_427_i4 : Fin 2 → ℕ := ![height_4, height_427_i5]
theorem height_exact_427_i4 : height_427_i4 = 1 + Finset.univ.sup childrenH_427_i4 := by decide +kernel
theorem required_origin_427_i4 : ∀ x ∈ required_427_i4,
    (∃ j, x ∈ childrenC_427_i4 j) ∨ ∀ j, x ∈ childrenD_427_i4 j := by decide +kernel
theorem required_exact_427_i4 : required_427_i4 =
    ((Finset.univ.biUnion childrenC_427_i4) ∪ commonEnvelope childrenD_427_i4).erase (4, 2) := by
  exact required_eq_combination childrenC_427_i4 childrenD_427_i4 (4, 2) required_427_i4
    (by decide +kernel) child_required_sub_427_i4 common_sub_427_i4 required_origin_427_i4
theorem envelope_origin_427_i4 : ∀ x ∈ envelope_427_i4,
    x = (4, 2) ∨ ∃ j, x ∈ childrenD_427_i4 j := by decide +kernel
theorem envelope_exact_427_i4 : envelope_427_i4 =
    insert (4, 2) (Finset.univ.biUnion childrenD_427_i4) := by
  exact envelope_eq_combination childrenD_427_i4 (4, 2) envelope_427_i4
    pivot_mem_427_i4 child_envelope_sub_427_i4 envelope_origin_427_i4
def checked_427_i4 : CheckedCard where
  required := required_427_i4
  envelope := envelope_427_i4
  height := height_427_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_427_i4
def height_427_i9 : ℕ := 2
def childrenH_427_i9 : Fin 2 → ℕ := ![height_0, height_2]
theorem height_exact_427_i9 : height_427_i9 = 1 + Finset.univ.sup childrenH_427_i9 := by decide +kernel
theorem required_origin_427_i9 : ∀ x ∈ required_427_i9,
    (∃ j, x ∈ childrenC_427_i9 j) ∨ ∀ j, x ∈ childrenD_427_i9 j := by decide +kernel
theorem required_exact_427_i9 : required_427_i9 =
    ((Finset.univ.biUnion childrenC_427_i9) ∪ commonEnvelope childrenD_427_i9).erase (3, 3) := by
  exact required_eq_combination childrenC_427_i9 childrenD_427_i9 (3, 3) required_427_i9
    (by decide +kernel) child_required_sub_427_i9 common_sub_427_i9 required_origin_427_i9
theorem envelope_origin_427_i9 : ∀ x ∈ envelope_427_i9,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_427_i9 j := by decide +kernel
theorem envelope_exact_427_i9 : envelope_427_i9 =
    insert (3, 3) (Finset.univ.biUnion childrenD_427_i9) := by
  exact envelope_eq_combination childrenD_427_i9 (3, 3) envelope_427_i9
    pivot_mem_427_i9 child_envelope_sub_427_i9 envelope_origin_427_i9
def checked_427_i9 : CheckedCard where
  required := required_427_i9
  envelope := envelope_427_i9
  height := height_427_i9
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_427_i9
def height_427_i8 : ℕ := 3
def childrenH_427_i8 : Fin 2 → ℕ := ![height_2, height_427_i9]
theorem height_exact_427_i8 : height_427_i8 = 1 + Finset.univ.sup childrenH_427_i8 := by decide +kernel
theorem required_origin_427_i8 : ∀ x ∈ required_427_i8,
    (∃ j, x ∈ childrenC_427_i8 j) ∨ ∀ j, x ∈ childrenD_427_i8 j := by decide +kernel
theorem required_exact_427_i8 : required_427_i8 =
    ((Finset.univ.biUnion childrenC_427_i8) ∪ commonEnvelope childrenD_427_i8).erase (2, 3) := by
  exact required_eq_combination childrenC_427_i8 childrenD_427_i8 (2, 3) required_427_i8
    (by decide +kernel) child_required_sub_427_i8 common_sub_427_i8 required_origin_427_i8
theorem envelope_origin_427_i8 : ∀ x ∈ envelope_427_i8,
    x = (2, 3) ∨ ∃ j, x ∈ childrenD_427_i8 j := by decide +kernel
theorem envelope_exact_427_i8 : envelope_427_i8 =
    insert (2, 3) (Finset.univ.biUnion childrenD_427_i8) := by
  exact envelope_eq_combination childrenD_427_i8 (2, 3) envelope_427_i8
    pivot_mem_427_i8 child_envelope_sub_427_i8 envelope_origin_427_i8
def checked_427_i8 : CheckedCard where
  required := required_427_i8
  envelope := envelope_427_i8
  height := height_427_i8
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_427_i8
def height_427_i7 : ℕ := 4
def childrenH_427_i7 : Fin 2 → ℕ := ![height_52, height_427_i8]
theorem height_exact_427_i7 : height_427_i7 = 1 + Finset.univ.sup childrenH_427_i7 := by decide +kernel
theorem required_origin_427_i7 : ∀ x ∈ required_427_i7,
    (∃ j, x ∈ childrenC_427_i7 j) ∨ ∀ j, x ∈ childrenD_427_i7 j := by decide +kernel
theorem required_exact_427_i7 : required_427_i7 =
    ((Finset.univ.biUnion childrenC_427_i7) ∪ commonEnvelope childrenD_427_i7).erase (3, 0) := by
  exact required_eq_combination childrenC_427_i7 childrenD_427_i7 (3, 0) required_427_i7
    (by decide +kernel) child_required_sub_427_i7 common_sub_427_i7 required_origin_427_i7
theorem envelope_origin_427_i7 : ∀ x ∈ envelope_427_i7,
    x = (3, 0) ∨ ∃ j, x ∈ childrenD_427_i7 j := by decide +kernel
theorem envelope_exact_427_i7 : envelope_427_i7 =
    insert (3, 0) (Finset.univ.biUnion childrenD_427_i7) := by
  exact envelope_eq_combination childrenD_427_i7 (3, 0) envelope_427_i7
    pivot_mem_427_i7 child_envelope_sub_427_i7 envelope_origin_427_i7
def checked_427_i7 : CheckedCard where
  required := required_427_i7
  envelope := envelope_427_i7
  height := height_427_i7
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_427_i7
def height_427_i3 : ℕ := 7
def childrenH_427_i3 : Fin 4 → ℕ := ![height_17, height_357, height_427_i4, height_427_i7]
theorem height_exact_427_i3 : height_427_i3 = 1 + Finset.univ.sup childrenH_427_i3 := by decide +kernel
theorem required_origin_427_i3 : ∀ x ∈ required_427_i3,
    (∃ j, x ∈ childrenC_427_i3 j) ∨ ∀ j, x ∈ childrenD_427_i3 j := by decide +kernel
theorem required_exact_427_i3 : required_427_i3 =
    ((Finset.univ.biUnion childrenC_427_i3) ∪ commonEnvelope childrenD_427_i3).erase (3, 1) := by
  exact required_eq_combination childrenC_427_i3 childrenD_427_i3 (3, 1) required_427_i3
    (by decide +kernel) child_required_sub_427_i3 common_sub_427_i3 required_origin_427_i3
theorem envelope_origin_427_i3 : ∀ x ∈ envelope_427_i3,
    x = (3, 1) ∨ ∃ j, x ∈ childrenD_427_i3 j := by decide +kernel
theorem envelope_exact_427_i3 : envelope_427_i3 =
    insert (3, 1) (Finset.univ.biUnion childrenD_427_i3) := by
  exact envelope_eq_combination childrenD_427_i3 (3, 1) envelope_427_i3
    pivot_mem_427_i3 child_envelope_sub_427_i3 envelope_origin_427_i3
def checked_427_i3 : CheckedCard where
  required := required_427_i3
  envelope := envelope_427_i3
  height := height_427_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_427_i3
def height_427_i2 : ℕ := 8
def childrenH_427_i2 : Fin 2 → ℕ := ![height_5, height_427_i3]
theorem height_exact_427_i2 : height_427_i2 = 1 + Finset.univ.sup childrenH_427_i2 := by decide +kernel
theorem required_origin_427_i2 : ∀ x ∈ required_427_i2,
    (∃ j, x ∈ childrenC_427_i2 j) ∨ ∀ j, x ∈ childrenD_427_i2 j := by decide +kernel
theorem required_exact_427_i2 : required_427_i2 =
    ((Finset.univ.biUnion childrenC_427_i2) ∪ commonEnvelope childrenD_427_i2).erase (0, 1) := by
  exact required_eq_combination childrenC_427_i2 childrenD_427_i2 (0, 1) required_427_i2
    (by decide +kernel) child_required_sub_427_i2 common_sub_427_i2 required_origin_427_i2
theorem envelope_origin_427_i2 : ∀ x ∈ envelope_427_i2,
    x = (0, 1) ∨ ∃ j, x ∈ childrenD_427_i2 j := by decide +kernel
theorem envelope_exact_427_i2 : envelope_427_i2 =
    insert (0, 1) (Finset.univ.biUnion childrenD_427_i2) := by
  exact envelope_eq_combination childrenD_427_i2 (0, 1) envelope_427_i2
    pivot_mem_427_i2 child_envelope_sub_427_i2 envelope_origin_427_i2
def checked_427_i2 : CheckedCard where
  required := required_427_i2
  envelope := envelope_427_i2
  height := height_427_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_427_i2
def height_427_i1 : ℕ := 9
def childrenH_427_i1 : Fin 2 → ℕ := ![height_5, height_427_i2]
theorem height_exact_427_i1 : height_427_i1 = 1 + Finset.univ.sup childrenH_427_i1 := by decide +kernel
theorem required_origin_427_i1 : ∀ x ∈ required_427_i1,
    (∃ j, x ∈ childrenC_427_i1 j) ∨ ∀ j, x ∈ childrenD_427_i1 j := by decide +kernel
theorem required_exact_427_i1 : required_427_i1 =
    ((Finset.univ.biUnion childrenC_427_i1) ∪ commonEnvelope childrenD_427_i1).erase (0, 4) := by
  exact required_eq_combination childrenC_427_i1 childrenD_427_i1 (0, 4) required_427_i1
    (by decide +kernel) child_required_sub_427_i1 common_sub_427_i1 required_origin_427_i1
theorem envelope_origin_427_i1 : ∀ x ∈ envelope_427_i1,
    x = (0, 4) ∨ ∃ j, x ∈ childrenD_427_i1 j := by decide +kernel
theorem envelope_exact_427_i1 : envelope_427_i1 =
    insert (0, 4) (Finset.univ.biUnion childrenD_427_i1) := by
  exact envelope_eq_combination childrenD_427_i1 (0, 4) envelope_427_i1
    pivot_mem_427_i1 child_envelope_sub_427_i1 envelope_origin_427_i1
def checked_427_i1 : CheckedCard where
  required := required_427_i1
  envelope := envelope_427_i1
  height := height_427_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_427_i1
def height_427_i0 : ℕ := 10
def childrenH_427_i0 : Fin 2 → ℕ := ![height_5, height_427_i1]
theorem height_exact_427_i0 : height_427_i0 = 1 + Finset.univ.sup childrenH_427_i0 := by decide +kernel
theorem required_origin_427_i0 : ∀ x ∈ required_427_i0,
    (∃ j, x ∈ childrenC_427_i0 j) ∨ ∀ j, x ∈ childrenD_427_i0 j := by decide +kernel
theorem required_exact_427_i0 : required_427_i0 =
    ((Finset.univ.biUnion childrenC_427_i0) ∪ commonEnvelope childrenD_427_i0).erase (2, 4) := by
  exact required_eq_combination childrenC_427_i0 childrenD_427_i0 (2, 4) required_427_i0
    (by decide +kernel) child_required_sub_427_i0 common_sub_427_i0 required_origin_427_i0
theorem envelope_origin_427_i0 : ∀ x ∈ envelope_427_i0,
    x = (2, 4) ∨ ∃ j, x ∈ childrenD_427_i0 j := by decide +kernel
theorem envelope_exact_427_i0 : envelope_427_i0 =
    insert (2, 4) (Finset.univ.biUnion childrenD_427_i0) := by
  exact envelope_eq_combination childrenD_427_i0 (2, 4) envelope_427_i0
    pivot_mem_427_i0 child_envelope_sub_427_i0 envelope_origin_427_i0
def checked_427_i0 : CheckedCard where
  required := required_427_i0
  envelope := envelope_427_i0
  height := height_427_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_427_i0
def height_427 : ℕ := 11
def childrenH_427 : Fin 2 → ℕ := ![height_5, height_427_i0]
theorem height_exact_427 : height_427 = 1 + Finset.univ.sup childrenH_427 := by decide +kernel
theorem required_origin_427 : ∀ x ∈ required_427,
    (∃ j, x ∈ childrenC_427 j) ∨ ∀ j, x ∈ childrenD_427 j := by decide +kernel
theorem required_exact_427 : required_427 =
    ((Finset.univ.biUnion childrenC_427) ∪ commonEnvelope childrenD_427).erase (2, 1) := by
  exact required_eq_combination childrenC_427 childrenD_427 (2, 1) required_427
    (by decide +kernel) child_required_sub_427 common_sub_427 required_origin_427
theorem envelope_origin_427 : ∀ x ∈ envelope_427,
    x = (2, 1) ∨ ∃ j, x ∈ childrenD_427 j := by decide +kernel
theorem envelope_exact_427 : envelope_427 =
    insert (2, 1) (Finset.univ.biUnion childrenD_427) := by
  exact envelope_eq_combination childrenD_427 (2, 1) envelope_427
    pivot_mem_427 child_envelope_sub_427 envelope_origin_427
def checked_427 : CheckedCard where
  required := required_427
  envelope := envelope_427
  height := height_427
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_427
def height_463_i0 : ℕ := 7
def childrenH_463_i0 : Fin 2 → ℕ := ![height_4, height_348]
theorem height_exact_463_i0 : height_463_i0 = 1 + Finset.univ.sup childrenH_463_i0 := by decide +kernel
theorem required_origin_463_i0 : ∀ x ∈ required_463_i0,
    (∃ j, x ∈ childrenC_463_i0 j) ∨ ∀ j, x ∈ childrenD_463_i0 j := by decide +kernel
theorem required_exact_463_i0 : required_463_i0 =
    ((Finset.univ.biUnion childrenC_463_i0) ∪ commonEnvelope childrenD_463_i0).erase (2, 6) := by
  exact required_eq_combination childrenC_463_i0 childrenD_463_i0 (2, 6) required_463_i0
    (by decide +kernel) child_required_sub_463_i0 common_sub_463_i0 required_origin_463_i0
theorem envelope_origin_463_i0 : ∀ x ∈ envelope_463_i0,
    x = (2, 6) ∨ ∃ j, x ∈ childrenD_463_i0 j := by decide +kernel
theorem envelope_exact_463_i0 : envelope_463_i0 =
    insert (2, 6) (Finset.univ.biUnion childrenD_463_i0) := by
  exact envelope_eq_combination childrenD_463_i0 (2, 6) envelope_463_i0
    pivot_mem_463_i0 child_envelope_sub_463_i0 envelope_origin_463_i0
def checked_463_i0 : CheckedCard where
  required := required_463_i0
  envelope := envelope_463_i0
  height := height_463_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_463_i0
def height_463 : ℕ := 11
def childrenH_463 : Fin 5 → ℕ := ![height_147, height_167, height_463_i0, height_353, height_460]
theorem height_exact_463 : height_463 = 1 + Finset.univ.sup childrenH_463 := by decide +kernel
theorem required_origin_463 : ∀ x ∈ required_463,
    (∃ j, x ∈ childrenC_463 j) ∨ ∀ j, x ∈ childrenD_463 j := by decide +kernel
theorem required_exact_463 : required_463 =
    ((Finset.univ.biUnion childrenC_463) ∪ commonEnvelope childrenD_463).erase (4, 5) := by
  exact required_eq_combination childrenC_463 childrenD_463 (4, 5) required_463
    (by decide +kernel) child_required_sub_463 common_sub_463 required_origin_463
theorem envelope_origin_463 : ∀ x ∈ envelope_463,
    x = (4, 5) ∨ ∃ j, x ∈ childrenD_463 j := by decide +kernel
theorem envelope_exact_463 : envelope_463 =
    insert (4, 5) (Finset.univ.biUnion childrenD_463) := by
  exact envelope_eq_combination childrenD_463 (4, 5) envelope_463
    pivot_mem_463 child_envelope_sub_463 envelope_origin_463
def checked_463 : CheckedCard where
  required := required_463
  envelope := envelope_463
  height := height_463
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_463
def height_467 : ℕ := 11
def childrenH_467 : Fin 4 → ℕ := ![height_31, height_398, height_444, height_466]
theorem height_exact_467 : height_467 = 1 + Finset.univ.sup childrenH_467 := by decide +kernel
theorem required_origin_467 : ∀ x ∈ required_467,
    (∃ j, x ∈ childrenC_467 j) ∨ ∀ j, x ∈ childrenD_467 j := by decide +kernel
theorem required_exact_467 : required_467 =
    ((Finset.univ.biUnion childrenC_467) ∪ commonEnvelope childrenD_467).erase (4, 6) := by
  exact required_eq_combination childrenC_467 childrenD_467 (4, 6) required_467
    (by decide +kernel) child_required_sub_467 common_sub_467 required_origin_467
theorem envelope_origin_467 : ∀ x ∈ envelope_467,
    x = (4, 6) ∨ ∃ j, x ∈ childrenD_467 j := by decide +kernel
theorem envelope_exact_467 : envelope_467 =
    insert (4, 6) (Finset.univ.biUnion childrenD_467) := by
  exact envelope_eq_combination childrenD_467 (4, 6) envelope_467
    pivot_mem_467 child_envelope_sub_467 envelope_origin_467
def checked_467 : CheckedCard where
  required := required_467
  envelope := envelope_467
  height := height_467
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_467
def height_468_i1 : ℕ := 6
def childrenH_468_i1 : Fin 4 → ℕ := ![height_71, height_71, height_73, height_73]
theorem height_exact_468_i1 : height_468_i1 = 1 + Finset.univ.sup childrenH_468_i1 := by decide +kernel
theorem required_origin_468_i1 : ∀ x ∈ required_468_i1,
    (∃ j, x ∈ childrenC_468_i1 j) ∨ ∀ j, x ∈ childrenD_468_i1 j := by decide +kernel
theorem required_exact_468_i1 : required_468_i1 =
    ((Finset.univ.biUnion childrenC_468_i1) ∪ commonEnvelope childrenD_468_i1).erase (3, 3) := by
  exact required_eq_combination childrenC_468_i1 childrenD_468_i1 (3, 3) required_468_i1
    (by decide +kernel) child_required_sub_468_i1 common_sub_468_i1 required_origin_468_i1
theorem envelope_origin_468_i1 : ∀ x ∈ envelope_468_i1,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_468_i1 j := by decide +kernel
theorem envelope_exact_468_i1 : envelope_468_i1 =
    insert (3, 3) (Finset.univ.biUnion childrenD_468_i1) := by
  exact envelope_eq_combination childrenD_468_i1 (3, 3) envelope_468_i1
    pivot_mem_468_i1 child_envelope_sub_468_i1 envelope_origin_468_i1
def checked_468_i1 : CheckedCard where
  required := required_468_i1
  envelope := envelope_468_i1
  height := height_468_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_468_i1
def height_468_i3 : ℕ := 8
def childrenH_468_i3 : Fin 5 → ℕ := ![height_8, height_17, height_75, height_266, height_447]
theorem height_exact_468_i3 : height_468_i3 = 1 + Finset.univ.sup childrenH_468_i3 := by decide +kernel
theorem required_origin_468_i3 : ∀ x ∈ required_468_i3,
    (∃ j, x ∈ childrenC_468_i3 j) ∨ ∀ j, x ∈ childrenD_468_i3 j := by decide +kernel
theorem required_exact_468_i3 : required_468_i3 =
    ((Finset.univ.biUnion childrenC_468_i3) ∪ commonEnvelope childrenD_468_i3).erase (3, 6) := by
  exact required_eq_combination childrenC_468_i3 childrenD_468_i3 (3, 6) required_468_i3
    (by decide +kernel) child_required_sub_468_i3 common_sub_468_i3 required_origin_468_i3
theorem envelope_origin_468_i3 : ∀ x ∈ envelope_468_i3,
    x = (3, 6) ∨ ∃ j, x ∈ childrenD_468_i3 j := by decide +kernel
theorem envelope_exact_468_i3 : envelope_468_i3 =
    insert (3, 6) (Finset.univ.biUnion childrenD_468_i3) := by
  exact envelope_eq_combination childrenD_468_i3 (3, 6) envelope_468_i3
    pivot_mem_468_i3 child_envelope_sub_468_i3 envelope_origin_468_i3
def checked_468_i3 : CheckedCard where
  required := required_468_i3
  envelope := envelope_468_i3
  height := height_468_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_468_i3
def height_468_i2 : ℕ := 9
def childrenH_468_i2 : Fin 4 → ℕ := ![height_71, height_73, height_426, height_468_i3]
theorem height_exact_468_i2 : height_468_i2 = 1 + Finset.univ.sup childrenH_468_i2 := by decide +kernel
theorem required_origin_468_i2 : ∀ x ∈ required_468_i2,
    (∃ j, x ∈ childrenC_468_i2 j) ∨ ∀ j, x ∈ childrenD_468_i2 j := by decide +kernel
theorem required_exact_468_i2 : required_468_i2 =
    ((Finset.univ.biUnion childrenC_468_i2) ∪ commonEnvelope childrenD_468_i2).erase (3, 3) := by
  exact required_eq_combination childrenC_468_i2 childrenD_468_i2 (3, 3) required_468_i2
    (by decide +kernel) child_required_sub_468_i2 common_sub_468_i2 required_origin_468_i2
theorem envelope_origin_468_i2 : ∀ x ∈ envelope_468_i2,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_468_i2 j := by decide +kernel
theorem envelope_exact_468_i2 : envelope_468_i2 =
    insert (3, 3) (Finset.univ.biUnion childrenD_468_i2) := by
  exact envelope_eq_combination childrenD_468_i2 (3, 3) envelope_468_i2
    pivot_mem_468_i2 child_envelope_sub_468_i2 envelope_origin_468_i2
def checked_468_i2 : CheckedCard where
  required := required_468_i2
  envelope := envelope_468_i2
  height := height_468_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_468_i2
def height_468_i0 : ℕ := 10
def childrenH_468_i0 : Fin 3 → ℕ := ![height_54, height_468_i1, height_468_i2]
theorem height_exact_468_i0 : height_468_i0 = 1 + Finset.univ.sup childrenH_468_i0 := by decide +kernel
theorem required_origin_468_i0 : ∀ x ∈ required_468_i0,
    (∃ j, x ∈ childrenC_468_i0 j) ∨ ∀ j, x ∈ childrenD_468_i0 j := by decide +kernel
theorem required_exact_468_i0 : required_468_i0 =
    ((Finset.univ.biUnion childrenC_468_i0) ∪ commonEnvelope childrenD_468_i0).erase (3, 5) := by
  exact required_eq_combination childrenC_468_i0 childrenD_468_i0 (3, 5) required_468_i0
    (by decide +kernel) child_required_sub_468_i0 common_sub_468_i0 required_origin_468_i0
theorem envelope_origin_468_i0 : ∀ x ∈ envelope_468_i0,
    x = (3, 5) ∨ ∃ j, x ∈ childrenD_468_i0 j := by decide +kernel
theorem envelope_exact_468_i0 : envelope_468_i0 =
    insert (3, 5) (Finset.univ.biUnion childrenD_468_i0) := by
  exact envelope_eq_combination childrenD_468_i0 (3, 5) envelope_468_i0
    pivot_mem_468_i0 child_envelope_sub_468_i0 envelope_origin_468_i0
def checked_468_i0 : CheckedCard where
  required := required_468_i0
  envelope := envelope_468_i0
  height := height_468_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_468_i0
def height_468 : ℕ := 11
def childrenH_468 : Fin 4 → ℕ := ![height_28, height_126, height_126, height_468_i0]
theorem height_exact_468 : height_468 = 1 + Finset.univ.sup childrenH_468 := by decide +kernel
theorem required_origin_468 : ∀ x ∈ required_468,
    (∃ j, x ∈ childrenC_468 j) ∨ ∀ j, x ∈ childrenD_468 j := by decide +kernel
theorem required_exact_468 : required_468 =
    ((Finset.univ.biUnion childrenC_468) ∪ commonEnvelope childrenD_468).erase (3, 4) := by
  exact required_eq_combination childrenC_468 childrenD_468 (3, 4) required_468
    (by decide +kernel) child_required_sub_468 common_sub_468 required_origin_468
theorem envelope_origin_468 : ∀ x ∈ envelope_468,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_468 j := by decide +kernel
theorem envelope_exact_468 : envelope_468 =
    insert (3, 4) (Finset.univ.biUnion childrenD_468) := by
  exact envelope_eq_combination childrenD_468 (3, 4) envelope_468
    pivot_mem_468 child_envelope_sub_468 envelope_origin_468
def checked_468 : CheckedCard where
  required := required_468
  envelope := envelope_468
  height := height_468
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_468
end SnakyPrototype.Certificate21

end OAI
