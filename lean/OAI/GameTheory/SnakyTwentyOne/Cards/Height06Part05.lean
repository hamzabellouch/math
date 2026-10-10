import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part06
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_439_i1 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 2), (3, 2), (3, 3), (3, 4), (3, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_439_i1 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 2), (2, 2), (3, 2), (3, 3), (3, 4), (3, 5), (4, 1), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_439_i1 : Fin 2 → Finset Cell := ![(placed21 6 (4, 2) required_2), (placed21 3 (3, 5) required_5)]
def childrenD_439_i1 : Fin 2 → Finset Cell := ![(placed21 6 (4, 2) envelope_2), (placed21 3 (3, 5) envelope_5)]
theorem common_sub_439_i1 : commonEnvelope childrenD_439_i1 ⊆ insert (4, 2) required_439_i1 := by decide +kernel
theorem child_required_sub_439_i1 : ∀ j, childrenC_439_i1 j ⊆ insert (4, 2) required_439_i1 := by decide +kernel
theorem child_envelope_sub_439_i1 : ∀ j, childrenD_439_i1 j ⊆ envelope_439_i1 := by decide +kernel
theorem pivot_mem_439_i1 : (4, 2) ∈ envelope_439_i1 := by decide +kernel
theorem children_work_439_i1 : ∀ j, Template HasSnaky 1 (childrenC_439_i1 j) (childrenD_439_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_2 6 (4, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_5 3 (3, 5)).mono (by decide +kernel)
theorem row_works_439_i1 : Template HasSnaky 2 required_439_i1 envelope_439_i1 := by
  refine compose HasSnaky 1 childrenC_439_i1 childrenD_439_i1 children_work_439_i1 (4, 2)
    required_439_i1 envelope_439_i1 pivot_mem_439_i1 child_required_sub_439_i1 child_envelope_sub_439_i1 ?_
  intro b hb
  exact common_sub_439_i1 (mem_commonEnvelope childrenD_439_i1 b hb)
def required_439_i4 : Finset Cell := ⟨(([(1, 1), (1, 2), (2, 1), (3, 1), (3, 2), (3, 3), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_439_i4 : Finset Cell := ⟨(([(0, 2), (1, 1), (1, 2), (2, 1), (3, 1), (3, 2), (3, 3), (3, 4), (4, 0), (4, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_439_i4 : Fin 2 → Finset Cell := ![(placed21 3 (3, 4) required_5), (placed21 2 (4, 1) required_5)]
def childrenD_439_i4 : Fin 2 → Finset Cell := ![(placed21 3 (3, 4) envelope_5), (placed21 2 (4, 1) envelope_5)]
theorem common_sub_439_i4 : commonEnvelope childrenD_439_i4 ⊆ insert (4, 1) required_439_i4 := by decide +kernel
theorem child_required_sub_439_i4 : ∀ j, childrenC_439_i4 j ⊆ insert (4, 1) required_439_i4 := by decide +kernel
theorem child_envelope_sub_439_i4 : ∀ j, childrenD_439_i4 j ⊆ envelope_439_i4 := by decide +kernel
theorem pivot_mem_439_i4 : (4, 1) ∈ envelope_439_i4 := by decide +kernel
theorem children_work_439_i4 : ∀ j, Template HasSnaky 1 (childrenC_439_i4 j) (childrenD_439_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 3 (3, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_5 2 (4, 1)).mono (by decide +kernel)
theorem row_works_439_i4 : Template HasSnaky 2 required_439_i4 envelope_439_i4 := by
  refine compose HasSnaky 1 childrenC_439_i4 childrenD_439_i4 children_work_439_i4 (4, 1)
    required_439_i4 envelope_439_i4 pivot_mem_439_i4 child_required_sub_439_i4 child_envelope_sub_439_i4 ?_
  intro b hb
  exact common_sub_439_i4 (mem_commonEnvelope childrenD_439_i4 b hb)
def required_439_i3 : Finset Cell := ⟨(([(1, 1), (1, 2), (2, 1), (3, 2), (3, 3), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_439_i3 : Finset Cell := ⟨(([(0, 2), (1, 1), (1, 2), (2, 0), (2, 1), (3, 1), (3, 2), (3, 3), (3, 4), (4, 0), (4, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_439_i3 : Fin 2 → Finset Cell := ![(placed21 7 (3, 4) required_5), required_439_i4]
def childrenD_439_i3 : Fin 2 → Finset Cell := ![(placed21 7 (3, 4) envelope_5), envelope_439_i4]
theorem common_sub_439_i3 : commonEnvelope childrenD_439_i3 ⊆ insert (3, 1) required_439_i3 := by decide +kernel
theorem child_required_sub_439_i3 : ∀ j, childrenC_439_i3 j ⊆ insert (3, 1) required_439_i3 := by decide +kernel
theorem child_envelope_sub_439_i3 : ∀ j, childrenD_439_i3 j ⊆ envelope_439_i3 := by decide +kernel
theorem pivot_mem_439_i3 : (3, 1) ∈ envelope_439_i3 := by decide +kernel
theorem children_work_439_i3 : ∀ j, Template HasSnaky 2 (childrenC_439_i3 j) (childrenD_439_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 7 (3, 4)).mono (by decide +kernel)
  · exact row_works_439_i4.mono (by decide +kernel)
theorem row_works_439_i3 : Template HasSnaky 3 required_439_i3 envelope_439_i3 := by
  refine compose HasSnaky 2 childrenC_439_i3 childrenD_439_i3 children_work_439_i3 (3, 1)
    required_439_i3 envelope_439_i3 pivot_mem_439_i3 child_required_sub_439_i3 child_envelope_sub_439_i3 ?_
  intro b hb
  exact common_sub_439_i3 (mem_commonEnvelope childrenD_439_i3 b hb)
def required_439_i2 : Finset Cell := ⟨(([(1, 1), (1, 2), (3, 2), (3, 3), (3, 4), (3, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_439_i2 : Finset Cell := ⟨(([(0, 2), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_439_i2 : Fin 2 → Finset Cell := ![(placed21 7 (3, 5) required_4), required_439_i3]
def childrenD_439_i2 : Fin 2 → Finset Cell := ![(placed21 7 (3, 5) envelope_4), envelope_439_i3]
theorem common_sub_439_i2 : commonEnvelope childrenD_439_i2 ⊆ insert (2, 1) required_439_i2 := by decide +kernel
theorem child_required_sub_439_i2 : ∀ j, childrenC_439_i2 j ⊆ insert (2, 1) required_439_i2 := by decide +kernel
theorem child_envelope_sub_439_i2 : ∀ j, childrenD_439_i2 j ⊆ envelope_439_i2 := by decide +kernel
theorem pivot_mem_439_i2 : (2, 1) ∈ envelope_439_i2 := by decide +kernel
theorem children_work_439_i2 : ∀ j, Template HasSnaky 3 (childrenC_439_i2 j) (childrenD_439_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_4 7 (3, 5)).mono (by decide +kernel)
  · exact row_works_439_i3.mono (by decide +kernel)
theorem row_works_439_i2 : Template HasSnaky 4 required_439_i2 envelope_439_i2 := by
  refine compose HasSnaky 3 childrenC_439_i2 childrenD_439_i2 children_work_439_i2 (2, 1)
    required_439_i2 envelope_439_i2 pivot_mem_439_i2 child_required_sub_439_i2 child_envelope_sub_439_i2 ?_
  intro b hb
  exact common_sub_439_i2 (mem_commonEnvelope childrenD_439_i2 b hb)
def required_439_i0 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 2), (3, 3), (3, 4), (3, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_439_i0 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_439_i0 : Fin 4 → Finset Cell := ![(placed21 7 (4, 5) required_251), (placed21 7 (4, 5) required_432), required_439_i1, required_439_i2]
def childrenD_439_i0 : Fin 4 → Finset Cell := ![(placed21 7 (4, 5) envelope_251), (placed21 7 (4, 5) envelope_432), envelope_439_i1, envelope_439_i2]
theorem common_sub_439_i0 : commonEnvelope childrenD_439_i0 ⊆ insert (3, 2) required_439_i0 := by decide +kernel
theorem child_required_sub_439_i0 : ∀ j, childrenC_439_i0 j ⊆ insert (3, 2) required_439_i0 := by decide +kernel
theorem child_envelope_sub_439_i0 : ∀ j, childrenD_439_i0 j ⊆ envelope_439_i0 := by decide +kernel
theorem pivot_mem_439_i0 : (3, 2) ∈ envelope_439_i0 := by decide +kernel
theorem children_work_439_i0 : ∀ j, Template HasSnaky 4 (childrenC_439_i0 j) (childrenD_439_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_251 7 (4, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_432 7 (4, 5)).mono (by decide +kernel)
  · exact row_works_439_i1.mono (by decide +kernel)
  · exact row_works_439_i2.mono (by decide +kernel)
theorem row_works_439_i0 : Template HasSnaky 5 required_439_i0 envelope_439_i0 := by
  refine compose HasSnaky 4 childrenC_439_i0 childrenD_439_i0 children_work_439_i0 (3, 2)
    required_439_i0 envelope_439_i0 pivot_mem_439_i0 child_required_sub_439_i0 child_envelope_sub_439_i0 ?_
  intro b hb
  exact common_sub_439_i0 (mem_commonEnvelope childrenD_439_i0 b hb)
def required_439 : Finset Cell := ⟨(([(0, 1), (0, 4), (1, 1), (1, 2), (1, 4), (2, 4), (3, 4), (3, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_439 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 4), (1, 1), (1, 2), (1, 4), (2, 0), (2, 1), (2, 2), (2, 4), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 2), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_439 : Fin 2 → Finset Cell := ![(placed21 4 (0, 4) required_5), required_439_i0]
def childrenD_439 : Fin 2 → Finset Cell := ![(placed21 4 (0, 4) envelope_5), envelope_439_i0]
theorem common_sub_439 : commonEnvelope childrenD_439 ⊆ insert (3, 3) required_439 := by decide +kernel
theorem child_required_sub_439 : ∀ j, childrenC_439 j ⊆ insert (3, 3) required_439 := by decide +kernel
theorem child_envelope_sub_439 : ∀ j, childrenD_439 j ⊆ envelope_439 := by decide +kernel
theorem pivot_mem_439 : (3, 3) ∈ envelope_439 := by decide +kernel
theorem children_work_439 : ∀ j, Template HasSnaky 5 (childrenC_439 j) (childrenD_439 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 4 (0, 4)).mono (by decide +kernel)
  · exact row_works_439_i0.mono (by decide +kernel)
theorem row_works_439 : Template HasSnaky 6 required_439 envelope_439 := by
  refine compose HasSnaky 5 childrenC_439 childrenD_439 children_work_439 (3, 3)
    required_439 envelope_439 pivot_mem_439 child_required_sub_439 child_envelope_sub_439 ?_
  intro b hb
  exact common_sub_439 (mem_commonEnvelope childrenD_439 b hb)
def required_465_i3 : Finset Cell := ⟨(([(0, 4), (1, 4), (2, 4), (4, 3), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_465_i3 : Finset Cell := ⟨(([(0, 4), (1, 4), (2, 4), (3, 3), (3, 4), (3, 5), (4, 3), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_465_i3 : Fin 2 → Finset Cell := ![(placed21 4 (0, 4) required_4), (placed21 0 (0, 4) required_4)]
def childrenD_465_i3 : Fin 2 → Finset Cell := ![(placed21 4 (0, 4) envelope_4), (placed21 0 (0, 4) envelope_4)]
theorem common_sub_465_i3 : commonEnvelope childrenD_465_i3 ⊆ insert (3, 4) required_465_i3 := by decide +kernel
theorem child_required_sub_465_i3 : ∀ j, childrenC_465_i3 j ⊆ insert (3, 4) required_465_i3 := by decide +kernel
theorem child_envelope_sub_465_i3 : ∀ j, childrenD_465_i3 j ⊆ envelope_465_i3 := by decide +kernel
theorem pivot_mem_465_i3 : (3, 4) ∈ envelope_465_i3 := by decide +kernel
theorem children_work_465_i3 : ∀ j, Template HasSnaky 1 (childrenC_465_i3 j) (childrenD_465_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_4 4 (0, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_4 0 (0, 4)).mono (by decide +kernel)
theorem row_works_465_i3 : Template HasSnaky 2 required_465_i3 envelope_465_i3 := by
  refine compose HasSnaky 1 childrenC_465_i3 childrenD_465_i3 children_work_465_i3 (3, 4)
    required_465_i3 envelope_465_i3 pivot_mem_465_i3 child_required_sub_465_i3 child_envelope_sub_465_i3 ?_
  intro b hb
  exact common_sub_465_i3 (mem_commonEnvelope childrenD_465_i3 b hb)
def required_465_i2 : Finset Cell := ⟨(([(0, 4), (1, 1), (1, 2), (1, 3), (1, 4), (4, 3), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_465_i2 : Finset Cell := ⟨(([(0, 4), (1, 1), (1, 2), (1, 3), (1, 4), (2, 4), (2, 5), (3, 3), (3, 4), (3, 5), (4, 3), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_465_i2 : Fin 2 → Finset Cell := ![(placed21 1 (1, 1) required_5), required_465_i3]
def childrenD_465_i2 : Fin 2 → Finset Cell := ![(placed21 1 (1, 1) envelope_5), envelope_465_i3]
theorem common_sub_465_i2 : commonEnvelope childrenD_465_i2 ⊆ insert (2, 4) required_465_i2 := by decide +kernel
theorem child_required_sub_465_i2 : ∀ j, childrenC_465_i2 j ⊆ insert (2, 4) required_465_i2 := by decide +kernel
theorem child_envelope_sub_465_i2 : ∀ j, childrenD_465_i2 j ⊆ envelope_465_i2 := by decide +kernel
theorem pivot_mem_465_i2 : (2, 4) ∈ envelope_465_i2 := by decide +kernel
theorem children_work_465_i2 : ∀ j, Template HasSnaky 2 (childrenC_465_i2 j) (childrenD_465_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 1 (1, 1)).mono (by decide +kernel)
  · exact row_works_465_i3.mono (by decide +kernel)
theorem row_works_465_i2 : Template HasSnaky 3 required_465_i2 envelope_465_i2 := by
  refine compose HasSnaky 2 childrenC_465_i2 childrenD_465_i2 children_work_465_i2 (2, 4)
    required_465_i2 envelope_465_i2 pivot_mem_465_i2 child_required_sub_465_i2 child_envelope_sub_465_i2 ?_
  intro b hb
  exact common_sub_465_i2 (mem_commonEnvelope childrenD_465_i2 b hb)
def required_465_i1 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 3), (1, 4), (4, 3), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_465_i1 : Finset Cell := ⟨(([(0, 4), (0, 5), (1, 1), (1, 2), (1, 3), (1, 4), (2, 4), (2, 5), (3, 3), (3, 4), (3, 5), (4, 3), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_465_i1 : Fin 2 → Finset Cell := ![(placed21 5 (1, 1) required_5), required_465_i2]
def childrenD_465_i1 : Fin 2 → Finset Cell := ![(placed21 5 (1, 1) envelope_5), envelope_465_i2]
theorem common_sub_465_i1 : commonEnvelope childrenD_465_i1 ⊆ insert (0, 4) required_465_i1 := by decide +kernel
theorem child_required_sub_465_i1 : ∀ j, childrenC_465_i1 j ⊆ insert (0, 4) required_465_i1 := by decide +kernel
theorem child_envelope_sub_465_i1 : ∀ j, childrenD_465_i1 j ⊆ envelope_465_i1 := by decide +kernel
theorem pivot_mem_465_i1 : (0, 4) ∈ envelope_465_i1 := by decide +kernel
theorem children_work_465_i1 : ∀ j, Template HasSnaky 3 (childrenC_465_i1 j) (childrenD_465_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 5 (1, 1)).mono (by decide +kernel)
  · exact row_works_465_i2.mono (by decide +kernel)
theorem row_works_465_i1 : Template HasSnaky 4 required_465_i1 envelope_465_i1 := by
  refine compose HasSnaky 3 childrenC_465_i1 childrenD_465_i1 children_work_465_i1 (0, 4)
    required_465_i1 envelope_465_i1 pivot_mem_465_i1 child_required_sub_465_i1 child_envelope_sub_465_i1 ?_
  intro b hb
  exact common_sub_465_i1 (mem_commonEnvelope childrenD_465_i1 b hb)
def required_465_i0 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 3), (1, 4), (3, 2), (4, 2), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_465_i0 : Finset Cell := ⟨(([(0, 4), (0, 5), (1, 1), (1, 2), (1, 3), (1, 4), (2, 4), (2, 5), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 5), (5, 6), (5, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_465_i0 : Fin 3 → Finset Cell := ![(placed21 0 (3, 1) required_39), (placed21 0 (3, 1) required_42), required_465_i1]
def childrenD_465_i0 : Fin 3 → Finset Cell := ![(placed21 0 (3, 1) envelope_39), (placed21 0 (3, 1) envelope_42), envelope_465_i1]
theorem common_sub_465_i0 : commonEnvelope childrenD_465_i0 ⊆ insert (4, 5) required_465_i0 := by decide +kernel
theorem child_required_sub_465_i0 : ∀ j, childrenC_465_i0 j ⊆ insert (4, 5) required_465_i0 := by decide +kernel
theorem child_envelope_sub_465_i0 : ∀ j, childrenD_465_i0 j ⊆ envelope_465_i0 := by decide +kernel
theorem pivot_mem_465_i0 : (4, 5) ∈ envelope_465_i0 := by decide +kernel
theorem children_work_465_i0 : ∀ j, Template HasSnaky 4 (childrenC_465_i0 j) (childrenD_465_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_39 0 (3, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_42 0 (3, 1)).mono (by decide +kernel)
  · exact row_works_465_i1.mono (by decide +kernel)
theorem row_works_465_i0 : Template HasSnaky 5 required_465_i0 envelope_465_i0 := by
  refine compose HasSnaky 4 childrenC_465_i0 childrenD_465_i0 children_work_465_i0 (4, 5)
    required_465_i0 envelope_465_i0 pivot_mem_465_i0 child_required_sub_465_i0 child_envelope_sub_465_i0 ?_
  intro b hb
  exact common_sub_465_i0 (mem_commonEnvelope childrenD_465_i0 b hb)
def required_465 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 3), (1, 4), (4, 2), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_465 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 4), (0, 5), (1, 1), (1, 2), (1, 3), (1, 4), (2, 2), (2, 4), (2, 5), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 5), (5, 6), (5, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_465 : Fin 2 → Finset Cell := ![(placed21 3 (0, 4) required_25), required_465_i0]
def childrenD_465 : Fin 2 → Finset Cell := ![(placed21 3 (0, 4) envelope_25), envelope_465_i0]
theorem common_sub_465 : commonEnvelope childrenD_465 ⊆ insert (3, 2) required_465 := by decide +kernel
theorem child_required_sub_465 : ∀ j, childrenC_465 j ⊆ insert (3, 2) required_465 := by decide +kernel
theorem child_envelope_sub_465 : ∀ j, childrenD_465 j ⊆ envelope_465 := by decide +kernel
theorem pivot_mem_465 : (3, 2) ∈ envelope_465 := by decide +kernel
theorem children_work_465 : ∀ j, Template HasSnaky 5 (childrenC_465 j) (childrenD_465 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_25 3 (0, 4)).mono (by decide +kernel)
  · exact row_works_465_i0.mono (by decide +kernel)
theorem row_works_465 : Template HasSnaky 6 required_465 envelope_465 := by
  refine compose HasSnaky 5 childrenC_465 childrenD_465 children_work_465 (3, 2)
    required_465 envelope_465 pivot_mem_465 child_required_sub_465 child_envelope_sub_465 ?_
  intro b hb
  exact common_sub_465 (mem_commonEnvelope childrenD_465 b hb)
def required_471_i0 : Finset Cell := ⟨(([(0, 3), (2, 2), (3, 1), (3, 2), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_471_i0 : Finset Cell := ⟨(([(0, 3), (1, 3), (1, 4), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_471_i0 : Fin 2 → Finset Cell := ![(placed21 2 (3, 0) required_11), (placed21 5 (4, 1) required_354)]
def childrenD_471_i0 : Fin 2 → Finset Cell := ![(placed21 2 (3, 0) envelope_11), (placed21 5 (4, 1) envelope_354)]
theorem common_sub_471_i0 : commonEnvelope childrenD_471_i0 ⊆ insert (3, 4) required_471_i0 := by decide +kernel
theorem child_required_sub_471_i0 : ∀ j, childrenC_471_i0 j ⊆ insert (3, 4) required_471_i0 := by decide +kernel
theorem child_envelope_sub_471_i0 : ∀ j, childrenD_471_i0 j ⊆ envelope_471_i0 := by decide +kernel
theorem pivot_mem_471_i0 : (3, 4) ∈ envelope_471_i0 := by decide +kernel
theorem children_work_471_i0 : ∀ j, Template HasSnaky 4 (childrenC_471_i0 j) (childrenD_471_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_11 2 (3, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_354 5 (4, 1)).mono (by decide +kernel)
theorem row_works_471_i0 : Template HasSnaky 5 required_471_i0 envelope_471_i0 := by
  refine compose HasSnaky 4 childrenC_471_i0 childrenD_471_i0 children_work_471_i0 (3, 4)
    required_471_i0 envelope_471_i0 pivot_mem_471_i0 child_required_sub_471_i0 child_envelope_sub_471_i0 ?_
  intro b hb
  exact common_sub_471_i0 (mem_commonEnvelope childrenD_471_i0 b hb)
def required_471 : Finset Cell := ⟨(([(0, 2), (0, 3), (1, 2), (2, 2), (3, 1), (3, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_471 : Finset Cell := ⟨(([(0, 2), (0, 3), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 3), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_471 : Fin 2 → Finset Cell := ![(placed21 0 (0, 2) required_5), required_471_i0]
def childrenD_471 : Fin 2 → Finset Cell := ![(placed21 0 (0, 2) envelope_5), envelope_471_i0]
theorem common_sub_471 : commonEnvelope childrenD_471 ⊆ insert (3, 3) required_471 := by decide +kernel
theorem child_required_sub_471 : ∀ j, childrenC_471 j ⊆ insert (3, 3) required_471 := by decide +kernel
theorem child_envelope_sub_471 : ∀ j, childrenD_471 j ⊆ envelope_471 := by decide +kernel
theorem pivot_mem_471 : (3, 3) ∈ envelope_471 := by decide +kernel
theorem children_work_471 : ∀ j, Template HasSnaky 5 (childrenC_471 j) (childrenD_471 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 0 (0, 2)).mono (by decide +kernel)
  · exact row_works_471_i0.mono (by decide +kernel)
theorem row_works_471 : Template HasSnaky 6 required_471 envelope_471 := by
  refine compose HasSnaky 5 childrenC_471 childrenD_471 children_work_471 (3, 3)
    required_471 envelope_471 pivot_mem_471 child_required_sub_471 child_envelope_sub_471 ?_
  intro b hb
  exact common_sub_471 (mem_commonEnvelope childrenD_471 b hb)
def required_486_i2 : Finset Cell := ⟨(([(0, 1), (1, 2), (1, 3), (2, 3), (3, 2), (3, 3), (4, 2), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_486_i2 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 4), (1, 1), (1, 2), (1, 3), (1, 4), (2, 2), (2, 3), (3, 2), (3, 3), (4, 2), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_486_i2 : Fin 2 → Finset Cell := ![(placed21 2 (4, 3) required_5), (placed21 3 (0, 4) required_156)]
def childrenD_486_i2 : Fin 2 → Finset Cell := ![(placed21 2 (4, 3) envelope_5), (placed21 3 (0, 4) envelope_156)]
theorem common_sub_486_i2 : commonEnvelope childrenD_486_i2 ⊆ insert (1, 4) required_486_i2 := by decide +kernel
theorem child_required_sub_486_i2 : ∀ j, childrenC_486_i2 j ⊆ insert (1, 4) required_486_i2 := by decide +kernel
theorem child_envelope_sub_486_i2 : ∀ j, childrenD_486_i2 j ⊆ envelope_486_i2 := by decide +kernel
theorem pivot_mem_486_i2 : (1, 4) ∈ envelope_486_i2 := by decide +kernel
theorem children_work_486_i2 : ∀ j, Template HasSnaky 2 (childrenC_486_i2 j) (childrenD_486_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 2 (4, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_156 3 (0, 4)).mono (by decide +kernel)
theorem row_works_486_i2 : Template HasSnaky 3 required_486_i2 envelope_486_i2 := by
  refine compose HasSnaky 2 childrenC_486_i2 childrenD_486_i2 children_work_486_i2 (1, 4)
    required_486_i2 envelope_486_i2 pivot_mem_486_i2 child_required_sub_486_i2 child_envelope_sub_486_i2 ?_
  intro b hb
  exact common_sub_486_i2 (mem_commonEnvelope childrenD_486_i2 b hb)
def required_486_i1 : Finset Cell := ⟨(([(0, 1), (1, 2), (1, 3), (2, 3), (3, 2), (3, 3), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_486_i1 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 4), (1, 1), (1, 2), (1, 3), (1, 4), (2, 2), (2, 3), (3, 2), (3, 3), (4, 2), (4, 3), (5, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_486_i1 : Fin 2 → Finset Cell := ![(placed21 4 (1, 3) required_5), required_486_i2]
def childrenD_486_i1 : Fin 2 → Finset Cell := ![(placed21 4 (1, 3) envelope_5), envelope_486_i2]
theorem common_sub_486_i1 : commonEnvelope childrenD_486_i1 ⊆ insert (4, 2) required_486_i1 := by decide +kernel
theorem child_required_sub_486_i1 : ∀ j, childrenC_486_i1 j ⊆ insert (4, 2) required_486_i1 := by decide +kernel
theorem child_envelope_sub_486_i1 : ∀ j, childrenD_486_i1 j ⊆ envelope_486_i1 := by decide +kernel
theorem pivot_mem_486_i1 : (4, 2) ∈ envelope_486_i1 := by decide +kernel
theorem children_work_486_i1 : ∀ j, Template HasSnaky 3 (childrenC_486_i1 j) (childrenD_486_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 4 (1, 3)).mono (by decide +kernel)
  · exact row_works_486_i2.mono (by decide +kernel)
theorem row_works_486_i1 : Template HasSnaky 4 required_486_i1 envelope_486_i1 := by
  refine compose HasSnaky 3 childrenC_486_i1 childrenD_486_i1 children_work_486_i1 (4, 2)
    required_486_i1 envelope_486_i1 pivot_mem_486_i1 child_required_sub_486_i1 child_envelope_sub_486_i1 ?_
  intro b hb
  exact common_sub_486_i1 (mem_commonEnvelope childrenD_486_i1 b hb)
def required_486_i0 : Finset Cell := ⟨(([(0, 1), (1, 3), (2, 3), (3, 2), (3, 3), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_486_i0 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 4), (1, 1), (1, 2), (1, 3), (1, 4), (2, 2), (2, 3), (3, 2), (3, 3), (4, 2), (4, 3), (5, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_486_i0 : Fin 2 → Finset Cell := ![(placed21 6 (4, 3) required_5), required_486_i1]
def childrenD_486_i0 : Fin 2 → Finset Cell := ![(placed21 6 (4, 3) envelope_5), envelope_486_i1]
theorem common_sub_486_i0 : commonEnvelope childrenD_486_i0 ⊆ insert (1, 2) required_486_i0 := by decide +kernel
theorem child_required_sub_486_i0 : ∀ j, childrenC_486_i0 j ⊆ insert (1, 2) required_486_i0 := by decide +kernel
theorem child_envelope_sub_486_i0 : ∀ j, childrenD_486_i0 j ⊆ envelope_486_i0 := by decide +kernel
theorem pivot_mem_486_i0 : (1, 2) ∈ envelope_486_i0 := by decide +kernel
theorem children_work_486_i0 : ∀ j, Template HasSnaky 4 (childrenC_486_i0 j) (childrenD_486_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 6 (4, 3)).mono (by decide +kernel)
  · exact row_works_486_i1.mono (by decide +kernel)
theorem row_works_486_i0 : Template HasSnaky 5 required_486_i0 envelope_486_i0 := by
  refine compose HasSnaky 4 childrenC_486_i0 childrenD_486_i0 children_work_486_i0 (1, 2)
    required_486_i0 envelope_486_i0 pivot_mem_486_i0 child_required_sub_486_i0 child_envelope_sub_486_i0 ?_
  intro b hb
  exact common_sub_486_i0 (mem_commonEnvelope childrenD_486_i0 b hb)
def required_486 : Finset Cell := ⟨(([(0, 1), (1, 3), (2, 3), (3, 2), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_486 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 4), (1, 1), (1, 2), (1, 3), (1, 4), (2, 2), (2, 3), (3, 2), (3, 3), (4, 2), (4, 3), (5, 2), (5, 3), (5, 4), (6, 2), (6, 3), (6, 4), (7, 2), (7, 3), (7, 4), (8, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_486 : Fin 4 → Finset Cell := ![(placed21 1 (0, 2) required_19), (placed21 1 (0, 2) required_84), (placed21 0 (1, 2) required_314), required_486_i0]
def childrenD_486 : Fin 4 → Finset Cell := ![(placed21 1 (0, 2) envelope_19), (placed21 1 (0, 2) envelope_84), (placed21 0 (1, 2) envelope_314), envelope_486_i0]
theorem common_sub_486 : commonEnvelope childrenD_486 ⊆ insert (4, 3) required_486 := by decide +kernel
theorem child_required_sub_486 : ∀ j, childrenC_486 j ⊆ insert (4, 3) required_486 := by decide +kernel
theorem child_envelope_sub_486 : ∀ j, childrenD_486 j ⊆ envelope_486 := by decide +kernel
theorem pivot_mem_486 : (4, 3) ∈ envelope_486 := by decide +kernel
theorem children_work_486 : ∀ j, Template HasSnaky 5 (childrenC_486 j) (childrenD_486 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_19 1 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_84 1 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_314 0 (1, 2)).mono (by decide +kernel)
  · exact row_works_486_i0.mono (by decide +kernel)
theorem row_works_486 : Template HasSnaky 6 required_486 envelope_486 := by
  refine compose HasSnaky 5 childrenC_486 childrenD_486 children_work_486 (4, 3)
    required_486 envelope_486 pivot_mem_486 child_required_sub_486 child_envelope_sub_486 ?_
  intro b hb
  exact common_sub_486 (mem_commonEnvelope childrenD_486 b hb)
def required_493 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 4), (3, 1), (3, 2), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_493 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 3), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 3), (2, 5), (2, 6), (2, 7), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_493 : Fin 3 → Finset Cell := ![required_87, (placed21 5 (4, 1) required_197), required_492]
def childrenD_493 : Fin 3 → Finset Cell := ![envelope_87, (placed21 5 (4, 1) envelope_197), envelope_492]
theorem common_sub_493 : commonEnvelope childrenD_493 ⊆ insert (3, 3) required_493 := by decide +kernel
theorem child_required_sub_493 : ∀ j, childrenC_493 j ⊆ insert (3, 3) required_493 := by decide +kernel
theorem child_envelope_sub_493 : ∀ j, childrenD_493 j ⊆ envelope_493 := by decide +kernel
theorem pivot_mem_493 : (3, 3) ∈ envelope_493 := by decide +kernel
theorem children_work_493 : ∀ j, Template HasSnaky 5 (childrenC_493 j) (childrenD_493 j) := by
  intro j
  fin_cases j
  · exact row_works_87.mono (by decide +kernel)
  · exact (placed21_template row_works_197 5 (4, 1)).mono (by decide +kernel)
  · exact row_works_492.mono (by decide +kernel)
theorem row_works_493 : Template HasSnaky 6 required_493 envelope_493 := by
  refine compose HasSnaky 5 childrenC_493 childrenD_493 children_work_493 (3, 3)
    required_493 envelope_493 pivot_mem_493 child_required_sub_493 child_envelope_sub_493 ?_
  intro b hb
  exact common_sub_493 (mem_commonEnvelope childrenD_493 b hb)
def required_498 : Finset Cell := ⟨(([(1, 1), (1, 2), (3, 4), (4, 1), (4, 2), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_498 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 1), (1, 2), (1, 3), (2, 1), (2, 3), (2, 4), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 3), (5, 4), (5, 5), (6, 3), (6, 4), (6, 5), (7, 3), (7, 4), (7, 5), (8, 3), (8, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_498 : Fin 2 → Finset Cell := ![(placed21 1 (1, 1) required_114), (placed21 2 (4, 0) required_496)]
def childrenD_498 : Fin 2 → Finset Cell := ![(placed21 1 (1, 1) envelope_114), (placed21 2 (4, 0) envelope_496)]
theorem common_sub_498 : commonEnvelope childrenD_498 ⊆ insert (4, 3) required_498 := by decide +kernel
theorem child_required_sub_498 : ∀ j, childrenC_498 j ⊆ insert (4, 3) required_498 := by decide +kernel
theorem child_envelope_sub_498 : ∀ j, childrenD_498 j ⊆ envelope_498 := by decide +kernel
theorem pivot_mem_498 : (4, 3) ∈ envelope_498 := by decide +kernel
theorem children_work_498 : ∀ j, Template HasSnaky 5 (childrenC_498 j) (childrenD_498 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_114 1 (1, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_496 2 (4, 0)).mono (by decide +kernel)
theorem row_works_498 : Template HasSnaky 6 required_498 envelope_498 := by
  refine compose HasSnaky 5 childrenC_498 childrenD_498 children_work_498 (4, 3)
    required_498 envelope_498 pivot_mem_498 child_required_sub_498 child_envelope_sub_498 ?_
  intro b hb
  exact common_sub_498 (mem_commonEnvelope childrenD_498 b hb)
def required_503 : Finset Cell := ⟨(([(1, 3), (3, 2), (3, 3), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_503 : Finset Cell := ⟨(([(0, 3), (0, 4), (1, 3), (1, 4), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 0), (3, 1), (3, 2), (3, 3), (4, 2), (4, 3), (4, 4), (4, 5), (5, 3), (5, 4), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_503 : Fin 2 → Finset Cell := ![(placed21 4 (0, 3) required_0), required_502]
def childrenD_503 : Fin 2 → Finset Cell := ![(placed21 4 (0, 3) envelope_0), envelope_502]
theorem common_sub_503 : commonEnvelope childrenD_503 ⊆ insert (2, 3) required_503 := by decide +kernel
theorem child_required_sub_503 : ∀ j, childrenC_503 j ⊆ insert (2, 3) required_503 := by decide +kernel
theorem child_envelope_sub_503 : ∀ j, childrenD_503 j ⊆ envelope_503 := by decide +kernel
theorem pivot_mem_503 : (2, 3) ∈ envelope_503 := by decide +kernel
theorem children_work_503 : ∀ j, Template HasSnaky 5 (childrenC_503 j) (childrenD_503 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 4 (0, 3)).mono (by decide +kernel)
  · exact row_works_502.mono (by decide +kernel)
theorem row_works_503 : Template HasSnaky 6 required_503 envelope_503 := by
  refine compose HasSnaky 5 childrenC_503 childrenD_503 children_work_503 (2, 3)
    required_503 envelope_503 pivot_mem_503 child_required_sub_503 child_envelope_sub_503 ?_
  intro b hb
  exact common_sub_503 (mem_commonEnvelope childrenD_503 b hb)
def required_516_i0 : Finset Cell := ⟨(([(0, 2), (1, 2), (3, 1), (3, 2), (3, 3), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_516_i0 : Finset Cell := ⟨(([(0, 2), (1, 2), (1, 3), (2, 3), (2, 4), (3, 0), (3, 1), (3, 2), (3, 3), (4, 3), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_516_i0 : Fin 2 → Finset Cell := ![(placed21 6 (4, 3) required_3), (placed21 6 (4, 4) required_83)]
def childrenD_516_i0 : Fin 2 → Finset Cell := ![(placed21 6 (4, 3) envelope_3), (placed21 6 (4, 4) envelope_83)]
theorem common_sub_516_i0 : commonEnvelope childrenD_516_i0 ⊆ insert (2, 3) required_516_i0 := by decide +kernel
theorem child_required_sub_516_i0 : ∀ j, childrenC_516_i0 j ⊆ insert (2, 3) required_516_i0 := by decide +kernel
theorem child_envelope_sub_516_i0 : ∀ j, childrenD_516_i0 j ⊆ envelope_516_i0 := by decide +kernel
theorem pivot_mem_516_i0 : (2, 3) ∈ envelope_516_i0 := by decide +kernel
theorem children_work_516_i0 : ∀ j, Template HasSnaky 2 (childrenC_516_i0 j) (childrenD_516_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_3 6 (4, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_83 6 (4, 4)).mono (by decide +kernel)
theorem row_works_516_i0 : Template HasSnaky 3 required_516_i0 envelope_516_i0 := by
  refine compose HasSnaky 2 childrenC_516_i0 childrenD_516_i0 children_work_516_i0 (2, 3)
    required_516_i0 envelope_516_i0 pivot_mem_516_i0 child_required_sub_516_i0 child_envelope_sub_516_i0 ?_
  intro b hb
  exact common_sub_516_i0 (mem_commonEnvelope childrenD_516_i0 b hb)
def required_516 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 1), (1, 2), (3, 1), (3, 2), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_516 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 4), (0, 5), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 3), (4, 4), (4, 5), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_516 : Fin 3 → Finset Cell := ![(placed21 0 (3, 0) required_52), required_516_i0, (placed21 1 (0, 1) required_515)]
def childrenD_516 : Fin 3 → Finset Cell := ![(placed21 0 (3, 0) envelope_52), envelope_516_i0, (placed21 1 (0, 1) envelope_515)]
theorem common_sub_516 : commonEnvelope childrenD_516 ⊆ insert (4, 3) required_516 := by decide +kernel
theorem child_required_sub_516 : ∀ j, childrenC_516 j ⊆ insert (4, 3) required_516 := by decide +kernel
theorem child_envelope_sub_516 : ∀ j, childrenD_516 j ⊆ envelope_516 := by decide +kernel
theorem pivot_mem_516 : (4, 3) ∈ envelope_516 := by decide +kernel
theorem children_work_516 : ∀ j, Template HasSnaky 5 (childrenC_516 j) (childrenD_516 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_52 0 (3, 0)).mono (by decide +kernel)
  · exact row_works_516_i0.mono (by decide +kernel)
  · exact (placed21_template row_works_515 1 (0, 1)).mono (by decide +kernel)
theorem row_works_516 : Template HasSnaky 6 required_516 envelope_516 := by
  refine compose HasSnaky 5 childrenC_516 childrenD_516 children_work_516 (4, 3)
    required_516 envelope_516 pivot_mem_516 child_required_sub_516 child_envelope_sub_516 ?_
  intro b hb
  exact common_sub_516 (mem_commonEnvelope childrenD_516 b hb)
def height_439_i1 : ℕ := 2
def childrenH_439_i1 : Fin 2 → ℕ := ![height_2, height_5]
theorem height_exact_439_i1 : height_439_i1 = 1 + Finset.univ.sup childrenH_439_i1 := by decide +kernel
theorem required_origin_439_i1 : ∀ x ∈ required_439_i1,
    (∃ j, x ∈ childrenC_439_i1 j) ∨ ∀ j, x ∈ childrenD_439_i1 j := by decide +kernel
theorem required_exact_439_i1 : required_439_i1 =
    ((Finset.univ.biUnion childrenC_439_i1) ∪ commonEnvelope childrenD_439_i1).erase (4, 2) := by
  exact required_eq_combination childrenC_439_i1 childrenD_439_i1 (4, 2) required_439_i1
    (by decide +kernel) child_required_sub_439_i1 common_sub_439_i1 required_origin_439_i1
theorem envelope_origin_439_i1 : ∀ x ∈ envelope_439_i1,
    x = (4, 2) ∨ ∃ j, x ∈ childrenD_439_i1 j := by decide +kernel
theorem envelope_exact_439_i1 : envelope_439_i1 =
    insert (4, 2) (Finset.univ.biUnion childrenD_439_i1) := by
  exact envelope_eq_combination childrenD_439_i1 (4, 2) envelope_439_i1
    pivot_mem_439_i1 child_envelope_sub_439_i1 envelope_origin_439_i1
def checked_439_i1 : CheckedCard where
  required := required_439_i1
  envelope := envelope_439_i1
  height := height_439_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_439_i1
def height_439_i4 : ℕ := 2
def childrenH_439_i4 : Fin 2 → ℕ := ![height_5, height_5]
theorem height_exact_439_i4 : height_439_i4 = 1 + Finset.univ.sup childrenH_439_i4 := by decide +kernel
theorem required_origin_439_i4 : ∀ x ∈ required_439_i4,
    (∃ j, x ∈ childrenC_439_i4 j) ∨ ∀ j, x ∈ childrenD_439_i4 j := by decide +kernel
theorem required_exact_439_i4 : required_439_i4 =
    ((Finset.univ.biUnion childrenC_439_i4) ∪ commonEnvelope childrenD_439_i4).erase (4, 1) := by
  exact required_eq_combination childrenC_439_i4 childrenD_439_i4 (4, 1) required_439_i4
    (by decide +kernel) child_required_sub_439_i4 common_sub_439_i4 required_origin_439_i4
theorem envelope_origin_439_i4 : ∀ x ∈ envelope_439_i4,
    x = (4, 1) ∨ ∃ j, x ∈ childrenD_439_i4 j := by decide +kernel
theorem envelope_exact_439_i4 : envelope_439_i4 =
    insert (4, 1) (Finset.univ.biUnion childrenD_439_i4) := by
  exact envelope_eq_combination childrenD_439_i4 (4, 1) envelope_439_i4
    pivot_mem_439_i4 child_envelope_sub_439_i4 envelope_origin_439_i4
def checked_439_i4 : CheckedCard where
  required := required_439_i4
  envelope := envelope_439_i4
  height := height_439_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_439_i4
def height_439_i3 : ℕ := 3
def childrenH_439_i3 : Fin 2 → ℕ := ![height_5, height_439_i4]
theorem height_exact_439_i3 : height_439_i3 = 1 + Finset.univ.sup childrenH_439_i3 := by decide +kernel
theorem required_origin_439_i3 : ∀ x ∈ required_439_i3,
    (∃ j, x ∈ childrenC_439_i3 j) ∨ ∀ j, x ∈ childrenD_439_i3 j := by decide +kernel
theorem required_exact_439_i3 : required_439_i3 =
    ((Finset.univ.biUnion childrenC_439_i3) ∪ commonEnvelope childrenD_439_i3).erase (3, 1) := by
  exact required_eq_combination childrenC_439_i3 childrenD_439_i3 (3, 1) required_439_i3
    (by decide +kernel) child_required_sub_439_i3 common_sub_439_i3 required_origin_439_i3
theorem envelope_origin_439_i3 : ∀ x ∈ envelope_439_i3,
    x = (3, 1) ∨ ∃ j, x ∈ childrenD_439_i3 j := by decide +kernel
theorem envelope_exact_439_i3 : envelope_439_i3 =
    insert (3, 1) (Finset.univ.biUnion childrenD_439_i3) := by
  exact envelope_eq_combination childrenD_439_i3 (3, 1) envelope_439_i3
    pivot_mem_439_i3 child_envelope_sub_439_i3 envelope_origin_439_i3
def checked_439_i3 : CheckedCard where
  required := required_439_i3
  envelope := envelope_439_i3
  height := height_439_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_439_i3
def height_439_i2 : ℕ := 4
def childrenH_439_i2 : Fin 2 → ℕ := ![height_4, height_439_i3]
theorem height_exact_439_i2 : height_439_i2 = 1 + Finset.univ.sup childrenH_439_i2 := by decide +kernel
theorem required_origin_439_i2 : ∀ x ∈ required_439_i2,
    (∃ j, x ∈ childrenC_439_i2 j) ∨ ∀ j, x ∈ childrenD_439_i2 j := by decide +kernel
theorem required_exact_439_i2 : required_439_i2 =
    ((Finset.univ.biUnion childrenC_439_i2) ∪ commonEnvelope childrenD_439_i2).erase (2, 1) := by
  exact required_eq_combination childrenC_439_i2 childrenD_439_i2 (2, 1) required_439_i2
    (by decide +kernel) child_required_sub_439_i2 common_sub_439_i2 required_origin_439_i2
theorem envelope_origin_439_i2 : ∀ x ∈ envelope_439_i2,
    x = (2, 1) ∨ ∃ j, x ∈ childrenD_439_i2 j := by decide +kernel
theorem envelope_exact_439_i2 : envelope_439_i2 =
    insert (2, 1) (Finset.univ.biUnion childrenD_439_i2) := by
  exact envelope_eq_combination childrenD_439_i2 (2, 1) envelope_439_i2
    pivot_mem_439_i2 child_envelope_sub_439_i2 envelope_origin_439_i2
def checked_439_i2 : CheckedCard where
  required := required_439_i2
  envelope := envelope_439_i2
  height := height_439_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_439_i2
def height_439_i0 : ℕ := 5
def childrenH_439_i0 : Fin 4 → ℕ := ![height_251, height_432, height_439_i1, height_439_i2]
theorem height_exact_439_i0 : height_439_i0 = 1 + Finset.univ.sup childrenH_439_i0 := by decide +kernel
theorem required_origin_439_i0 : ∀ x ∈ required_439_i0,
    (∃ j, x ∈ childrenC_439_i0 j) ∨ ∀ j, x ∈ childrenD_439_i0 j := by decide +kernel
theorem required_exact_439_i0 : required_439_i0 =
    ((Finset.univ.biUnion childrenC_439_i0) ∪ commonEnvelope childrenD_439_i0).erase (3, 2) := by
  exact required_eq_combination childrenC_439_i0 childrenD_439_i0 (3, 2) required_439_i0
    (by decide +kernel) child_required_sub_439_i0 common_sub_439_i0 required_origin_439_i0
theorem envelope_origin_439_i0 : ∀ x ∈ envelope_439_i0,
    x = (3, 2) ∨ ∃ j, x ∈ childrenD_439_i0 j := by decide +kernel
theorem envelope_exact_439_i0 : envelope_439_i0 =
    insert (3, 2) (Finset.univ.biUnion childrenD_439_i0) := by
  exact envelope_eq_combination childrenD_439_i0 (3, 2) envelope_439_i0
    pivot_mem_439_i0 child_envelope_sub_439_i0 envelope_origin_439_i0
def checked_439_i0 : CheckedCard where
  required := required_439_i0
  envelope := envelope_439_i0
  height := height_439_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_439_i0
def height_439 : ℕ := 6
def childrenH_439 : Fin 2 → ℕ := ![height_5, height_439_i0]
theorem height_exact_439 : height_439 = 1 + Finset.univ.sup childrenH_439 := by decide +kernel
theorem required_origin_439 : ∀ x ∈ required_439,
    (∃ j, x ∈ childrenC_439 j) ∨ ∀ j, x ∈ childrenD_439 j := by decide +kernel
theorem required_exact_439 : required_439 =
    ((Finset.univ.biUnion childrenC_439) ∪ commonEnvelope childrenD_439).erase (3, 3) := by
  exact required_eq_combination childrenC_439 childrenD_439 (3, 3) required_439
    (by decide +kernel) child_required_sub_439 common_sub_439 required_origin_439
theorem envelope_origin_439 : ∀ x ∈ envelope_439,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_439 j := by decide +kernel
theorem envelope_exact_439 : envelope_439 =
    insert (3, 3) (Finset.univ.biUnion childrenD_439) := by
  exact envelope_eq_combination childrenD_439 (3, 3) envelope_439
    pivot_mem_439 child_envelope_sub_439 envelope_origin_439
def checked_439 : CheckedCard where
  required := required_439
  envelope := envelope_439
  height := height_439
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_439
def height_465_i3 : ℕ := 2
def childrenH_465_i3 : Fin 2 → ℕ := ![height_4, height_4]
theorem height_exact_465_i3 : height_465_i3 = 1 + Finset.univ.sup childrenH_465_i3 := by decide +kernel
theorem required_origin_465_i3 : ∀ x ∈ required_465_i3,
    (∃ j, x ∈ childrenC_465_i3 j) ∨ ∀ j, x ∈ childrenD_465_i3 j := by decide +kernel
theorem required_exact_465_i3 : required_465_i3 =
    ((Finset.univ.biUnion childrenC_465_i3) ∪ commonEnvelope childrenD_465_i3).erase (3, 4) := by
  exact required_eq_combination childrenC_465_i3 childrenD_465_i3 (3, 4) required_465_i3
    (by decide +kernel) child_required_sub_465_i3 common_sub_465_i3 required_origin_465_i3
theorem envelope_origin_465_i3 : ∀ x ∈ envelope_465_i3,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_465_i3 j := by decide +kernel
theorem envelope_exact_465_i3 : envelope_465_i3 =
    insert (3, 4) (Finset.univ.biUnion childrenD_465_i3) := by
  exact envelope_eq_combination childrenD_465_i3 (3, 4) envelope_465_i3
    pivot_mem_465_i3 child_envelope_sub_465_i3 envelope_origin_465_i3
def checked_465_i3 : CheckedCard where
  required := required_465_i3
  envelope := envelope_465_i3
  height := height_465_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_465_i3
def height_465_i2 : ℕ := 3
def childrenH_465_i2 : Fin 2 → ℕ := ![height_5, height_465_i3]
theorem height_exact_465_i2 : height_465_i2 = 1 + Finset.univ.sup childrenH_465_i2 := by decide +kernel
theorem required_origin_465_i2 : ∀ x ∈ required_465_i2,
    (∃ j, x ∈ childrenC_465_i2 j) ∨ ∀ j, x ∈ childrenD_465_i2 j := by decide +kernel
theorem required_exact_465_i2 : required_465_i2 =
    ((Finset.univ.biUnion childrenC_465_i2) ∪ commonEnvelope childrenD_465_i2).erase (2, 4) := by
  exact required_eq_combination childrenC_465_i2 childrenD_465_i2 (2, 4) required_465_i2
    (by decide +kernel) child_required_sub_465_i2 common_sub_465_i2 required_origin_465_i2
theorem envelope_origin_465_i2 : ∀ x ∈ envelope_465_i2,
    x = (2, 4) ∨ ∃ j, x ∈ childrenD_465_i2 j := by decide +kernel
theorem envelope_exact_465_i2 : envelope_465_i2 =
    insert (2, 4) (Finset.univ.biUnion childrenD_465_i2) := by
  exact envelope_eq_combination childrenD_465_i2 (2, 4) envelope_465_i2
    pivot_mem_465_i2 child_envelope_sub_465_i2 envelope_origin_465_i2
def checked_465_i2 : CheckedCard where
  required := required_465_i2
  envelope := envelope_465_i2
  height := height_465_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_465_i2
def height_465_i1 : ℕ := 4
def childrenH_465_i1 : Fin 2 → ℕ := ![height_5, height_465_i2]
theorem height_exact_465_i1 : height_465_i1 = 1 + Finset.univ.sup childrenH_465_i1 := by decide +kernel
theorem required_origin_465_i1 : ∀ x ∈ required_465_i1,
    (∃ j, x ∈ childrenC_465_i1 j) ∨ ∀ j, x ∈ childrenD_465_i1 j := by decide +kernel
theorem required_exact_465_i1 : required_465_i1 =
    ((Finset.univ.biUnion childrenC_465_i1) ∪ commonEnvelope childrenD_465_i1).erase (0, 4) := by
  exact required_eq_combination childrenC_465_i1 childrenD_465_i1 (0, 4) required_465_i1
    (by decide +kernel) child_required_sub_465_i1 common_sub_465_i1 required_origin_465_i1
theorem envelope_origin_465_i1 : ∀ x ∈ envelope_465_i1,
    x = (0, 4) ∨ ∃ j, x ∈ childrenD_465_i1 j := by decide +kernel
theorem envelope_exact_465_i1 : envelope_465_i1 =
    insert (0, 4) (Finset.univ.biUnion childrenD_465_i1) := by
  exact envelope_eq_combination childrenD_465_i1 (0, 4) envelope_465_i1
    pivot_mem_465_i1 child_envelope_sub_465_i1 envelope_origin_465_i1
def checked_465_i1 : CheckedCard where
  required := required_465_i1
  envelope := envelope_465_i1
  height := height_465_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_465_i1
def height_465_i0 : ℕ := 5
def childrenH_465_i0 : Fin 3 → ℕ := ![height_39, height_42, height_465_i1]
theorem height_exact_465_i0 : height_465_i0 = 1 + Finset.univ.sup childrenH_465_i0 := by decide +kernel
theorem required_origin_465_i0 : ∀ x ∈ required_465_i0,
    (∃ j, x ∈ childrenC_465_i0 j) ∨ ∀ j, x ∈ childrenD_465_i0 j := by decide +kernel
theorem required_exact_465_i0 : required_465_i0 =
    ((Finset.univ.biUnion childrenC_465_i0) ∪ commonEnvelope childrenD_465_i0).erase (4, 5) := by
  exact required_eq_combination childrenC_465_i0 childrenD_465_i0 (4, 5) required_465_i0
    (by decide +kernel) child_required_sub_465_i0 common_sub_465_i0 required_origin_465_i0
theorem envelope_origin_465_i0 : ∀ x ∈ envelope_465_i0,
    x = (4, 5) ∨ ∃ j, x ∈ childrenD_465_i0 j := by decide +kernel
theorem envelope_exact_465_i0 : envelope_465_i0 =
    insert (4, 5) (Finset.univ.biUnion childrenD_465_i0) := by
  exact envelope_eq_combination childrenD_465_i0 (4, 5) envelope_465_i0
    pivot_mem_465_i0 child_envelope_sub_465_i0 envelope_origin_465_i0
def checked_465_i0 : CheckedCard where
  required := required_465_i0
  envelope := envelope_465_i0
  height := height_465_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_465_i0
def height_465 : ℕ := 6
def childrenH_465 : Fin 2 → ℕ := ![height_25, height_465_i0]
theorem height_exact_465 : height_465 = 1 + Finset.univ.sup childrenH_465 := by decide +kernel
theorem required_origin_465 : ∀ x ∈ required_465,
    (∃ j, x ∈ childrenC_465 j) ∨ ∀ j, x ∈ childrenD_465 j := by decide +kernel
theorem required_exact_465 : required_465 =
    ((Finset.univ.biUnion childrenC_465) ∪ commonEnvelope childrenD_465).erase (3, 2) := by
  exact required_eq_combination childrenC_465 childrenD_465 (3, 2) required_465
    (by decide +kernel) child_required_sub_465 common_sub_465 required_origin_465
theorem envelope_origin_465 : ∀ x ∈ envelope_465,
    x = (3, 2) ∨ ∃ j, x ∈ childrenD_465 j := by decide +kernel
theorem envelope_exact_465 : envelope_465 =
    insert (3, 2) (Finset.univ.biUnion childrenD_465) := by
  exact envelope_eq_combination childrenD_465 (3, 2) envelope_465
    pivot_mem_465 child_envelope_sub_465 envelope_origin_465
def checked_465 : CheckedCard where
  required := required_465
  envelope := envelope_465
  height := height_465
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_465
def height_471_i0 : ℕ := 5
def childrenH_471_i0 : Fin 2 → ℕ := ![height_11, height_354]
theorem height_exact_471_i0 : height_471_i0 = 1 + Finset.univ.sup childrenH_471_i0 := by decide +kernel
theorem required_origin_471_i0 : ∀ x ∈ required_471_i0,
    (∃ j, x ∈ childrenC_471_i0 j) ∨ ∀ j, x ∈ childrenD_471_i0 j := by decide +kernel
theorem required_exact_471_i0 : required_471_i0 =
    ((Finset.univ.biUnion childrenC_471_i0) ∪ commonEnvelope childrenD_471_i0).erase (3, 4) := by
  exact required_eq_combination childrenC_471_i0 childrenD_471_i0 (3, 4) required_471_i0
    (by decide +kernel) child_required_sub_471_i0 common_sub_471_i0 required_origin_471_i0
theorem envelope_origin_471_i0 : ∀ x ∈ envelope_471_i0,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_471_i0 j := by decide +kernel
theorem envelope_exact_471_i0 : envelope_471_i0 =
    insert (3, 4) (Finset.univ.biUnion childrenD_471_i0) := by
  exact envelope_eq_combination childrenD_471_i0 (3, 4) envelope_471_i0
    pivot_mem_471_i0 child_envelope_sub_471_i0 envelope_origin_471_i0
def checked_471_i0 : CheckedCard where
  required := required_471_i0
  envelope := envelope_471_i0
  height := height_471_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_471_i0
def height_471 : ℕ := 6
def childrenH_471 : Fin 2 → ℕ := ![height_5, height_471_i0]
theorem height_exact_471 : height_471 = 1 + Finset.univ.sup childrenH_471 := by decide +kernel
theorem required_origin_471 : ∀ x ∈ required_471,
    (∃ j, x ∈ childrenC_471 j) ∨ ∀ j, x ∈ childrenD_471 j := by decide +kernel
theorem required_exact_471 : required_471 =
    ((Finset.univ.biUnion childrenC_471) ∪ commonEnvelope childrenD_471).erase (3, 3) := by
  exact required_eq_combination childrenC_471 childrenD_471 (3, 3) required_471
    (by decide +kernel) child_required_sub_471 common_sub_471 required_origin_471
theorem envelope_origin_471 : ∀ x ∈ envelope_471,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_471 j := by decide +kernel
theorem envelope_exact_471 : envelope_471 =
    insert (3, 3) (Finset.univ.biUnion childrenD_471) := by
  exact envelope_eq_combination childrenD_471 (3, 3) envelope_471
    pivot_mem_471 child_envelope_sub_471 envelope_origin_471
def checked_471 : CheckedCard where
  required := required_471
  envelope := envelope_471
  height := height_471
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_471
def height_486_i2 : ℕ := 3
def childrenH_486_i2 : Fin 2 → ℕ := ![height_5, height_156]
theorem height_exact_486_i2 : height_486_i2 = 1 + Finset.univ.sup childrenH_486_i2 := by decide +kernel
theorem required_origin_486_i2 : ∀ x ∈ required_486_i2,
    (∃ j, x ∈ childrenC_486_i2 j) ∨ ∀ j, x ∈ childrenD_486_i2 j := by decide +kernel
theorem required_exact_486_i2 : required_486_i2 =
    ((Finset.univ.biUnion childrenC_486_i2) ∪ commonEnvelope childrenD_486_i2).erase (1, 4) := by
  exact required_eq_combination childrenC_486_i2 childrenD_486_i2 (1, 4) required_486_i2
    (by decide +kernel) child_required_sub_486_i2 common_sub_486_i2 required_origin_486_i2
theorem envelope_origin_486_i2 : ∀ x ∈ envelope_486_i2,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_486_i2 j := by decide +kernel
theorem envelope_exact_486_i2 : envelope_486_i2 =
    insert (1, 4) (Finset.univ.biUnion childrenD_486_i2) := by
  exact envelope_eq_combination childrenD_486_i2 (1, 4) envelope_486_i2
    pivot_mem_486_i2 child_envelope_sub_486_i2 envelope_origin_486_i2
def checked_486_i2 : CheckedCard where
  required := required_486_i2
  envelope := envelope_486_i2
  height := height_486_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_486_i2
def height_486_i1 : ℕ := 4
def childrenH_486_i1 : Fin 2 → ℕ := ![height_5, height_486_i2]
theorem height_exact_486_i1 : height_486_i1 = 1 + Finset.univ.sup childrenH_486_i1 := by decide +kernel
theorem required_origin_486_i1 : ∀ x ∈ required_486_i1,
    (∃ j, x ∈ childrenC_486_i1 j) ∨ ∀ j, x ∈ childrenD_486_i1 j := by decide +kernel
theorem required_exact_486_i1 : required_486_i1 =
    ((Finset.univ.biUnion childrenC_486_i1) ∪ commonEnvelope childrenD_486_i1).erase (4, 2) := by
  exact required_eq_combination childrenC_486_i1 childrenD_486_i1 (4, 2) required_486_i1
    (by decide +kernel) child_required_sub_486_i1 common_sub_486_i1 required_origin_486_i1
theorem envelope_origin_486_i1 : ∀ x ∈ envelope_486_i1,
    x = (4, 2) ∨ ∃ j, x ∈ childrenD_486_i1 j := by decide +kernel
theorem envelope_exact_486_i1 : envelope_486_i1 =
    insert (4, 2) (Finset.univ.biUnion childrenD_486_i1) := by
  exact envelope_eq_combination childrenD_486_i1 (4, 2) envelope_486_i1
    pivot_mem_486_i1 child_envelope_sub_486_i1 envelope_origin_486_i1
def checked_486_i1 : CheckedCard where
  required := required_486_i1
  envelope := envelope_486_i1
  height := height_486_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_486_i1
def height_486_i0 : ℕ := 5
def childrenH_486_i0 : Fin 2 → ℕ := ![height_5, height_486_i1]
theorem height_exact_486_i0 : height_486_i0 = 1 + Finset.univ.sup childrenH_486_i0 := by decide +kernel
theorem required_origin_486_i0 : ∀ x ∈ required_486_i0,
    (∃ j, x ∈ childrenC_486_i0 j) ∨ ∀ j, x ∈ childrenD_486_i0 j := by decide +kernel
theorem required_exact_486_i0 : required_486_i0 =
    ((Finset.univ.biUnion childrenC_486_i0) ∪ commonEnvelope childrenD_486_i0).erase (1, 2) := by
  exact required_eq_combination childrenC_486_i0 childrenD_486_i0 (1, 2) required_486_i0
    (by decide +kernel) child_required_sub_486_i0 common_sub_486_i0 required_origin_486_i0
theorem envelope_origin_486_i0 : ∀ x ∈ envelope_486_i0,
    x = (1, 2) ∨ ∃ j, x ∈ childrenD_486_i0 j := by decide +kernel
theorem envelope_exact_486_i0 : envelope_486_i0 =
    insert (1, 2) (Finset.univ.biUnion childrenD_486_i0) := by
  exact envelope_eq_combination childrenD_486_i0 (1, 2) envelope_486_i0
    pivot_mem_486_i0 child_envelope_sub_486_i0 envelope_origin_486_i0
def checked_486_i0 : CheckedCard where
  required := required_486_i0
  envelope := envelope_486_i0
  height := height_486_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_486_i0
def height_486 : ℕ := 6
def childrenH_486 : Fin 4 → ℕ := ![height_19, height_84, height_314, height_486_i0]
theorem height_exact_486 : height_486 = 1 + Finset.univ.sup childrenH_486 := by decide +kernel
theorem required_origin_486 : ∀ x ∈ required_486,
    (∃ j, x ∈ childrenC_486 j) ∨ ∀ j, x ∈ childrenD_486 j := by decide +kernel
theorem required_exact_486 : required_486 =
    ((Finset.univ.biUnion childrenC_486) ∪ commonEnvelope childrenD_486).erase (4, 3) := by
  exact required_eq_combination childrenC_486 childrenD_486 (4, 3) required_486
    (by decide +kernel) child_required_sub_486 common_sub_486 required_origin_486
theorem envelope_origin_486 : ∀ x ∈ envelope_486,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_486 j := by decide +kernel
theorem envelope_exact_486 : envelope_486 =
    insert (4, 3) (Finset.univ.biUnion childrenD_486) := by
  exact envelope_eq_combination childrenD_486 (4, 3) envelope_486
    pivot_mem_486 child_envelope_sub_486 envelope_origin_486
def checked_486 : CheckedCard where
  required := required_486
  envelope := envelope_486
  height := height_486
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_486
def height_493 : ℕ := 6
def childrenH_493 : Fin 3 → ℕ := ![height_87, height_197, height_492]
theorem height_exact_493 : height_493 = 1 + Finset.univ.sup childrenH_493 := by decide +kernel
theorem required_origin_493 : ∀ x ∈ required_493,
    (∃ j, x ∈ childrenC_493 j) ∨ ∀ j, x ∈ childrenD_493 j := by decide +kernel
theorem required_exact_493 : required_493 =
    ((Finset.univ.biUnion childrenC_493) ∪ commonEnvelope childrenD_493).erase (3, 3) := by
  exact required_eq_combination childrenC_493 childrenD_493 (3, 3) required_493
    (by decide +kernel) child_required_sub_493 common_sub_493 required_origin_493
theorem envelope_origin_493 : ∀ x ∈ envelope_493,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_493 j := by decide +kernel
theorem envelope_exact_493 : envelope_493 =
    insert (3, 3) (Finset.univ.biUnion childrenD_493) := by
  exact envelope_eq_combination childrenD_493 (3, 3) envelope_493
    pivot_mem_493 child_envelope_sub_493 envelope_origin_493
def checked_493 : CheckedCard where
  required := required_493
  envelope := envelope_493
  height := height_493
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_493
def height_498 : ℕ := 6
def childrenH_498 : Fin 2 → ℕ := ![height_114, height_496]
theorem height_exact_498 : height_498 = 1 + Finset.univ.sup childrenH_498 := by decide +kernel
theorem required_origin_498 : ∀ x ∈ required_498,
    (∃ j, x ∈ childrenC_498 j) ∨ ∀ j, x ∈ childrenD_498 j := by decide +kernel
theorem required_exact_498 : required_498 =
    ((Finset.univ.biUnion childrenC_498) ∪ commonEnvelope childrenD_498).erase (4, 3) := by
  exact required_eq_combination childrenC_498 childrenD_498 (4, 3) required_498
    (by decide +kernel) child_required_sub_498 common_sub_498 required_origin_498
theorem envelope_origin_498 : ∀ x ∈ envelope_498,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_498 j := by decide +kernel
theorem envelope_exact_498 : envelope_498 =
    insert (4, 3) (Finset.univ.biUnion childrenD_498) := by
  exact envelope_eq_combination childrenD_498 (4, 3) envelope_498
    pivot_mem_498 child_envelope_sub_498 envelope_origin_498
def checked_498 : CheckedCard where
  required := required_498
  envelope := envelope_498
  height := height_498
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_498
def height_503 : ℕ := 6
def childrenH_503 : Fin 2 → ℕ := ![height_0, height_502]
theorem height_exact_503 : height_503 = 1 + Finset.univ.sup childrenH_503 := by decide +kernel
theorem required_origin_503 : ∀ x ∈ required_503,
    (∃ j, x ∈ childrenC_503 j) ∨ ∀ j, x ∈ childrenD_503 j := by decide +kernel
theorem required_exact_503 : required_503 =
    ((Finset.univ.biUnion childrenC_503) ∪ commonEnvelope childrenD_503).erase (2, 3) := by
  exact required_eq_combination childrenC_503 childrenD_503 (2, 3) required_503
    (by decide +kernel) child_required_sub_503 common_sub_503 required_origin_503
theorem envelope_origin_503 : ∀ x ∈ envelope_503,
    x = (2, 3) ∨ ∃ j, x ∈ childrenD_503 j := by decide +kernel
theorem envelope_exact_503 : envelope_503 =
    insert (2, 3) (Finset.univ.biUnion childrenD_503) := by
  exact envelope_eq_combination childrenD_503 (2, 3) envelope_503
    pivot_mem_503 child_envelope_sub_503 envelope_origin_503
def checked_503 : CheckedCard where
  required := required_503
  envelope := envelope_503
  height := height_503
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_503
def height_516_i0 : ℕ := 3
def childrenH_516_i0 : Fin 2 → ℕ := ![height_3, height_83]
theorem height_exact_516_i0 : height_516_i0 = 1 + Finset.univ.sup childrenH_516_i0 := by decide +kernel
theorem required_origin_516_i0 : ∀ x ∈ required_516_i0,
    (∃ j, x ∈ childrenC_516_i0 j) ∨ ∀ j, x ∈ childrenD_516_i0 j := by decide +kernel
theorem required_exact_516_i0 : required_516_i0 =
    ((Finset.univ.biUnion childrenC_516_i0) ∪ commonEnvelope childrenD_516_i0).erase (2, 3) := by
  exact required_eq_combination childrenC_516_i0 childrenD_516_i0 (2, 3) required_516_i0
    (by decide +kernel) child_required_sub_516_i0 common_sub_516_i0 required_origin_516_i0
theorem envelope_origin_516_i0 : ∀ x ∈ envelope_516_i0,
    x = (2, 3) ∨ ∃ j, x ∈ childrenD_516_i0 j := by decide +kernel
theorem envelope_exact_516_i0 : envelope_516_i0 =
    insert (2, 3) (Finset.univ.biUnion childrenD_516_i0) := by
  exact envelope_eq_combination childrenD_516_i0 (2, 3) envelope_516_i0
    pivot_mem_516_i0 child_envelope_sub_516_i0 envelope_origin_516_i0
def checked_516_i0 : CheckedCard where
  required := required_516_i0
  envelope := envelope_516_i0
  height := height_516_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_516_i0
def height_516 : ℕ := 6
def childrenH_516 : Fin 3 → ℕ := ![height_52, height_516_i0, height_515]
theorem height_exact_516 : height_516 = 1 + Finset.univ.sup childrenH_516 := by decide +kernel
theorem required_origin_516 : ∀ x ∈ required_516,
    (∃ j, x ∈ childrenC_516 j) ∨ ∀ j, x ∈ childrenD_516 j := by decide +kernel
theorem required_exact_516 : required_516 =
    ((Finset.univ.biUnion childrenC_516) ∪ commonEnvelope childrenD_516).erase (4, 3) := by
  exact required_eq_combination childrenC_516 childrenD_516 (4, 3) required_516
    (by decide +kernel) child_required_sub_516 common_sub_516 required_origin_516
theorem envelope_origin_516 : ∀ x ∈ envelope_516,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_516 j := by decide +kernel
theorem envelope_exact_516 : envelope_516 =
    insert (4, 3) (Finset.univ.biUnion childrenD_516) := by
  exact envelope_eq_combination childrenD_516 (4, 3) envelope_516
    pivot_mem_516 child_envelope_sub_516 envelope_origin_516
def checked_516 : CheckedCard where
  required := required_516
  envelope := envelope_516
  height := height_516
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_516
end SnakyPrototype.Certificate21

end OAI
