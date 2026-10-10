import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part06
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part06
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_511_i1 : Finset Cell := ⟨(([(0, 3), (1, 3), (1, 4), (3, 2), (3, 3), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_511_i1 : Finset Cell := ⟨(([(0, 3), (1, 3), (1, 4), (2, 4), (3, 1), (3, 2), (3, 3), (3, 4), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_511_i1 : Fin 2 → Finset Cell := ![(placed21 6 (4, 4) required_2), (placed21 0 (3, 1) required_44)]
def childrenD_511_i1 : Fin 2 → Finset Cell := ![(placed21 6 (4, 4) envelope_2), (placed21 0 (3, 1) envelope_44)]
theorem common_sub_511_i1 : commonEnvelope childrenD_511_i1 ⊆ insert (4, 4) required_511_i1 := by decide +kernel
theorem child_required_sub_511_i1 : ∀ j, childrenC_511_i1 j ⊆ insert (4, 4) required_511_i1 := by decide +kernel
theorem child_envelope_sub_511_i1 : ∀ j, childrenD_511_i1 j ⊆ envelope_511_i1 := by decide +kernel
theorem pivot_mem_511_i1 : (4, 4) ∈ envelope_511_i1 := by decide +kernel
theorem children_work_511_i1 : ∀ j, Template HasSnaky 3 (childrenC_511_i1 j) (childrenD_511_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_2 6 (4, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_44 0 (3, 1)).mono (by decide +kernel)
theorem row_works_511_i1 : Template HasSnaky 4 required_511_i1 envelope_511_i1 := by
  refine compose HasSnaky 3 childrenC_511_i1 childrenD_511_i1 children_work_511_i1 (4, 4)
    required_511_i1 envelope_511_i1 pivot_mem_511_i1 child_required_sub_511_i1 child_envelope_sub_511_i1 ?_
  intro b hb
  exact common_sub_511_i1 (mem_commonEnvelope childrenD_511_i1 b hb)
def required_511_i3 : Finset Cell := ⟨(([(1, 4), (2, 4), (3, 2), (3, 3), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_511_i3 : Finset Cell := ⟨(([(1, 4), (2, 4), (2, 5), (2, 6), (2, 7), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 1), (4, 2), (4, 3), (4, 5), (4, 6), (4, 7), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_511_i3 : Fin 3 → Finset Cell := ![(placed21 0 (3, 1) required_7), (placed21 2 (4, 1) required_9), (placed21 0 (1, 2) required_221)]
def childrenD_511_i3 : Fin 3 → Finset Cell := ![(placed21 0 (3, 1) envelope_7), (placed21 2 (4, 1) envelope_9), (placed21 0 (1, 2) envelope_221)]
theorem common_sub_511_i3 : commonEnvelope childrenD_511_i3 ⊆ insert (3, 5) required_511_i3 := by decide +kernel
theorem child_required_sub_511_i3 : ∀ j, childrenC_511_i3 j ⊆ insert (3, 5) required_511_i3 := by decide +kernel
theorem child_envelope_sub_511_i3 : ∀ j, childrenD_511_i3 j ⊆ envelope_511_i3 := by decide +kernel
theorem pivot_mem_511_i3 : (3, 5) ∈ envelope_511_i3 := by decide +kernel
theorem children_work_511_i3 : ∀ j, Template HasSnaky 3 (childrenC_511_i3 j) (childrenD_511_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 0 (3, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_9 2 (4, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_221 0 (1, 2)).mono (by decide +kernel)
theorem row_works_511_i3 : Template HasSnaky 4 required_511_i3 envelope_511_i3 := by
  refine compose HasSnaky 3 childrenC_511_i3 childrenD_511_i3 children_work_511_i3 (3, 5)
    required_511_i3 envelope_511_i3 pivot_mem_511_i3 child_required_sub_511_i3 child_envelope_sub_511_i3 ?_
  intro b hb
  exact common_sub_511_i3 (mem_commonEnvelope childrenD_511_i3 b hb)
def required_511_i2 : Finset Cell := ⟨(([(0, 3), (1, 3), (1, 4), (3, 2), (3, 3), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_511_i2 : Finset Cell := ⟨(([(0, 3), (1, 3), (1, 4), (2, 4), (2, 5), (2, 6), (2, 7), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_511_i2 : Fin 2 → Finset Cell := ![(placed21 6 (4, 4) required_0), required_511_i3]
def childrenD_511_i2 : Fin 2 → Finset Cell := ![(placed21 6 (4, 4) envelope_0), envelope_511_i3]
theorem common_sub_511_i2 : commonEnvelope childrenD_511_i2 ⊆ insert (2, 4) required_511_i2 := by decide +kernel
theorem child_required_sub_511_i2 : ∀ j, childrenC_511_i2 j ⊆ insert (2, 4) required_511_i2 := by decide +kernel
theorem child_envelope_sub_511_i2 : ∀ j, childrenD_511_i2 j ⊆ envelope_511_i2 := by decide +kernel
theorem pivot_mem_511_i2 : (2, 4) ∈ envelope_511_i2 := by decide +kernel
theorem children_work_511_i2 : ∀ j, Template HasSnaky 4 (childrenC_511_i2 j) (childrenD_511_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 6 (4, 4)).mono (by decide +kernel)
  · exact row_works_511_i3.mono (by decide +kernel)
theorem row_works_511_i2 : Template HasSnaky 5 required_511_i2 envelope_511_i2 := by
  refine compose HasSnaky 4 childrenC_511_i2 childrenD_511_i2 children_work_511_i2 (2, 4)
    required_511_i2 envelope_511_i2 pivot_mem_511_i2 child_required_sub_511_i2 child_envelope_sub_511_i2 ?_
  intro b hb
  exact common_sub_511_i2 (mem_commonEnvelope childrenD_511_i2 b hb)
def required_511_i0 : Finset Cell := ⟨(([(0, 3), (1, 3), (1, 4), (3, 2), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_511_i0 : Finset Cell := ⟨(([(0, 3), (1, 3), (1, 4), (2, 4), (2, 5), (2, 6), (2, 7), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_511_i0 : Fin 5 → Finset Cell := ![(placed21 2 (4, 0) required_13), (placed21 2 (4, 0) required_14), (placed21 0 (0, 1) required_240), required_511_i1, required_511_i2]
def childrenD_511_i0 : Fin 5 → Finset Cell := ![(placed21 2 (4, 0) envelope_13), (placed21 2 (4, 0) envelope_14), (placed21 0 (0, 1) envelope_240), envelope_511_i1, envelope_511_i2]
theorem common_sub_511_i0 : commonEnvelope childrenD_511_i0 ⊆ insert (3, 4) required_511_i0 := by decide +kernel
theorem child_required_sub_511_i0 : ∀ j, childrenC_511_i0 j ⊆ insert (3, 4) required_511_i0 := by decide +kernel
theorem child_envelope_sub_511_i0 : ∀ j, childrenD_511_i0 j ⊆ envelope_511_i0 := by decide +kernel
theorem pivot_mem_511_i0 : (3, 4) ∈ envelope_511_i0 := by decide +kernel
theorem children_work_511_i0 : ∀ j, Template HasSnaky 5 (childrenC_511_i0 j) (childrenD_511_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_13 2 (4, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_14 2 (4, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_240 0 (0, 1)).mono (by decide +kernel)
  · exact row_works_511_i1.mono (by decide +kernel)
  · exact row_works_511_i2.mono (by decide +kernel)
theorem row_works_511_i0 : Template HasSnaky 6 required_511_i0 envelope_511_i0 := by
  refine compose HasSnaky 5 childrenC_511_i0 childrenD_511_i0 children_work_511_i0 (3, 4)
    required_511_i0 envelope_511_i0 pivot_mem_511_i0 child_required_sub_511_i0 child_envelope_sub_511_i0 ?_
  intro b hb
  exact common_sub_511_i0 (mem_commonEnvelope childrenD_511_i0 b hb)
def required_511 : Finset Cell := ⟨(([(0, 2), (0, 3), (1, 2), (1, 3), (3, 2), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_511 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (1, 4), (1, 5), (2, 4), (2, 5), (2, 6), (2, 7), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_511 : Fin 2 → Finset Cell := ![(placed21 6 (1, 5) required_15), required_511_i0]
def childrenD_511 : Fin 2 → Finset Cell := ![(placed21 6 (1, 5) envelope_15), envelope_511_i0]
theorem common_sub_511 : commonEnvelope childrenD_511 ⊆ insert (1, 4) required_511 := by decide +kernel
theorem child_required_sub_511 : ∀ j, childrenC_511 j ⊆ insert (1, 4) required_511 := by decide +kernel
theorem child_envelope_sub_511 : ∀ j, childrenD_511 j ⊆ envelope_511 := by decide +kernel
theorem pivot_mem_511 : (1, 4) ∈ envelope_511 := by decide +kernel
theorem children_work_511 : ∀ j, Template HasSnaky 6 (childrenC_511 j) (childrenD_511 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_15 6 (1, 5)).mono (by decide +kernel)
  · exact row_works_511_i0.mono (by decide +kernel)
theorem row_works_511 : Template HasSnaky 7 required_511 envelope_511 := by
  refine compose HasSnaky 6 childrenC_511 childrenD_511 children_work_511 (1, 4)
    required_511 envelope_511 pivot_mem_511 child_required_sub_511 child_envelope_sub_511 ?_
  intro b hb
  exact common_sub_511 (mem_commonEnvelope childrenD_511 b hb)
def required_522_i0 : Finset Cell := ⟨(([(1, 2), (2, 2), (2, 3), (3, 2), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_522_i0 : Finset Cell := ⟨(([(0, 3), (1, 2), (1, 3), (2, 2), (2, 3), (3, 0), (3, 1), (3, 2), (3, 3), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 1), (5, 3), (5, 4), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_522_i0 : Fin 2 → Finset Cell := ![(placed21 2 (4, 2) required_5), (placed21 0 (1, 0) required_416)]
def childrenD_522_i0 : Fin 2 → Finset Cell := ![(placed21 2 (4, 2) envelope_5), (placed21 0 (1, 0) envelope_416)]
theorem common_sub_522_i0 : commonEnvelope childrenD_522_i0 ⊆ insert (1, 3) required_522_i0 := by decide +kernel
theorem child_required_sub_522_i0 : ∀ j, childrenC_522_i0 j ⊆ insert (1, 3) required_522_i0 := by decide +kernel
theorem child_envelope_sub_522_i0 : ∀ j, childrenD_522_i0 j ⊆ envelope_522_i0 := by decide +kernel
theorem pivot_mem_522_i0 : (1, 3) ∈ envelope_522_i0 := by decide +kernel
theorem children_work_522_i0 : ∀ j, Template HasSnaky 5 (childrenC_522_i0 j) (childrenD_522_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 2 (4, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_416 0 (1, 0)).mono (by decide +kernel)
theorem row_works_522_i0 : Template HasSnaky 6 required_522_i0 envelope_522_i0 := by
  refine compose HasSnaky 5 childrenC_522_i0 childrenD_522_i0 children_work_522_i0 (1, 3)
    required_522_i0 envelope_522_i0 pivot_mem_522_i0 child_required_sub_522_i0 child_envelope_sub_522_i0 ?_
  intro b hb
  exact common_sub_522_i0 (mem_commonEnvelope childrenD_522_i0 b hb)
def required_522 : Finset Cell := ⟨(([(1, 2), (2, 2), (2, 3), (3, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_522 : Finset Cell := ⟨(([(0, 3), (1, 2), (1, 3), (2, 2), (2, 3), (3, 0), (3, 1), (3, 2), (3, 3), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (6, 1), (6, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_522 : Fin 3 → Finset Cell := ![(placed21 0 (1, 1) required_8), (placed21 1 (0, 2) required_11), required_522_i0]
def childrenD_522 : Fin 3 → Finset Cell := ![(placed21 0 (1, 1) envelope_8), (placed21 1 (0, 2) envelope_11), envelope_522_i0]
theorem common_sub_522 : commonEnvelope childrenD_522 ⊆ insert (4, 2) required_522 := by decide +kernel
theorem child_required_sub_522 : ∀ j, childrenC_522 j ⊆ insert (4, 2) required_522 := by decide +kernel
theorem child_envelope_sub_522 : ∀ j, childrenD_522 j ⊆ envelope_522 := by decide +kernel
theorem pivot_mem_522 : (4, 2) ∈ envelope_522 := by decide +kernel
theorem children_work_522 : ∀ j, Template HasSnaky 6 (childrenC_522 j) (childrenD_522 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_8 0 (1, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_11 1 (0, 2)).mono (by decide +kernel)
  · exact row_works_522_i0.mono (by decide +kernel)
theorem row_works_522 : Template HasSnaky 7 required_522 envelope_522 := by
  refine compose HasSnaky 6 childrenC_522 childrenD_522 children_work_522 (4, 2)
    required_522 envelope_522 pivot_mem_522 child_required_sub_522 child_envelope_sub_522 ?_
  intro b hb
  exact common_sub_522 (mem_commonEnvelope childrenD_522 b hb)
def required_526 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 1), (1, 2), (2, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_526 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 1), (1, 2), (1, 3), (2, 0), (2, 1), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_526 : Fin 2 → Finset Cell := ![(placed21 2 (4, 1) required_0), required_525]
def childrenD_526 : Fin 2 → Finset Cell := ![(placed21 2 (4, 1) envelope_0), envelope_525]
theorem common_sub_526 : commonEnvelope childrenD_526 ⊆ insert (3, 1) required_526 := by decide +kernel
theorem child_required_sub_526 : ∀ j, childrenC_526 j ⊆ insert (3, 1) required_526 := by decide +kernel
theorem child_envelope_sub_526 : ∀ j, childrenD_526 j ⊆ envelope_526 := by decide +kernel
theorem pivot_mem_526 : (3, 1) ∈ envelope_526 := by decide +kernel
theorem children_work_526 : ∀ j, Template HasSnaky 6 (childrenC_526 j) (childrenD_526 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 2 (4, 1)).mono (by decide +kernel)
  · exact row_works_525.mono (by decide +kernel)
theorem row_works_526 : Template HasSnaky 7 required_526 envelope_526 := by
  refine compose HasSnaky 6 childrenC_526 childrenD_526 children_work_526 (3, 1)
    required_526 envelope_526 pivot_mem_526 child_required_sub_526 child_envelope_sub_526 ?_
  intro b hb
  exact common_sub_526 (mem_commonEnvelope childrenD_526 b hb)
def required_542_i3 : Finset Cell := ⟨(([(1, 3), (2, 1), (3, 1), (3, 2), (3, 3), (4, 2), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_542_i3 : Finset Cell := ⟨(([(1, 3), (2, 1), (2, 3), (3, 1), (3, 2), (3, 3), (4, 2), (4, 3), (5, 2), (6, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_542_i3 : Fin 2 → Finset Cell := ![(placed21 6 (6, 2) required_0), (placed21 4 (1, 3) required_1)]
def childrenD_542_i3 : Fin 2 → Finset Cell := ![(placed21 6 (6, 2) envelope_0), (placed21 4 (1, 3) envelope_1)]
theorem common_sub_542_i3 : commonEnvelope childrenD_542_i3 ⊆ insert (5, 2) required_542_i3 := by decide +kernel
theorem child_required_sub_542_i3 : ∀ j, childrenC_542_i3 j ⊆ insert (5, 2) required_542_i3 := by decide +kernel
theorem child_envelope_sub_542_i3 : ∀ j, childrenD_542_i3 j ⊆ envelope_542_i3 := by decide +kernel
theorem pivot_mem_542_i3 : (5, 2) ∈ envelope_542_i3 := by decide +kernel
theorem children_work_542_i3 : ∀ j, Template HasSnaky 1 (childrenC_542_i3 j) (childrenD_542_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 6 (6, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_1 4 (1, 3)).mono (by decide +kernel)
theorem row_works_542_i3 : Template HasSnaky 2 required_542_i3 envelope_542_i3 := by
  refine compose HasSnaky 1 childrenC_542_i3 childrenD_542_i3 children_work_542_i3 (5, 2)
    required_542_i3 envelope_542_i3 pivot_mem_542_i3 child_required_sub_542_i3 child_envelope_sub_542_i3 ?_
  intro b hb
  exact common_sub_542_i3 (mem_commonEnvelope childrenD_542_i3 b hb)
def required_542_i2 : Finset Cell := ⟨(([(1, 3), (2, 1), (3, 1), (3, 2), (3, 3), (3, 4), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_542_i2 : Finset Cell := ⟨(([(1, 3), (2, 1), (2, 3), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 2), (6, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_542_i2 : Fin 2 → Finset Cell := ![(placed21 0 (3, 1) required_29), required_542_i3]
def childrenD_542_i2 : Fin 2 → Finset Cell := ![(placed21 0 (3, 1) envelope_29), envelope_542_i3]
theorem common_sub_542_i2 : commonEnvelope childrenD_542_i2 ⊆ insert (4, 3) required_542_i2 := by decide +kernel
theorem child_required_sub_542_i2 : ∀ j, childrenC_542_i2 j ⊆ insert (4, 3) required_542_i2 := by decide +kernel
theorem child_envelope_sub_542_i2 : ∀ j, childrenD_542_i2 j ⊆ envelope_542_i2 := by decide +kernel
theorem pivot_mem_542_i2 : (4, 3) ∈ envelope_542_i2 := by decide +kernel
theorem children_work_542_i2 : ∀ j, Template HasSnaky 3 (childrenC_542_i2 j) (childrenD_542_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_29 0 (3, 1)).mono (by decide +kernel)
  · exact row_works_542_i3.mono (by decide +kernel)
theorem row_works_542_i2 : Template HasSnaky 4 required_542_i2 envelope_542_i2 := by
  refine compose HasSnaky 3 childrenC_542_i2 childrenD_542_i2 children_work_542_i2 (4, 3)
    required_542_i2 envelope_542_i2 pivot_mem_542_i2 child_required_sub_542_i2 child_envelope_sub_542_i2 ?_
  intro b hb
  exact common_sub_542_i2 (mem_commonEnvelope childrenD_542_i2 b hb)
def required_542_i1 : Finset Cell := ⟨(([(0, 1), (1, 3), (2, 1), (3, 1), (3, 2), (3, 3), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_542_i1 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 3), (2, 1), (2, 3), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 2), (6, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_542_i1 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) required_1), required_542_i2]
def childrenD_542_i1 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) envelope_1), envelope_542_i2]
theorem common_sub_542_i1 : commonEnvelope childrenD_542_i1 ⊆ insert (4, 2) required_542_i1 := by decide +kernel
theorem child_required_sub_542_i1 : ∀ j, childrenC_542_i1 j ⊆ insert (4, 2) required_542_i1 := by decide +kernel
theorem child_envelope_sub_542_i1 : ∀ j, childrenD_542_i1 j ⊆ envelope_542_i1 := by decide +kernel
theorem pivot_mem_542_i1 : (4, 2) ∈ envelope_542_i1 := by decide +kernel
theorem children_work_542_i1 : ∀ j, Template HasSnaky 4 (childrenC_542_i1 j) (childrenD_542_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_1 0 (0, 1)).mono (by decide +kernel)
  · exact row_works_542_i2.mono (by decide +kernel)
theorem row_works_542_i1 : Template HasSnaky 5 required_542_i1 envelope_542_i1 := by
  refine compose HasSnaky 4 childrenC_542_i1 childrenD_542_i1 children_work_542_i1 (4, 2)
    required_542_i1 envelope_542_i1 pivot_mem_542_i1 child_required_sub_542_i1 child_envelope_sub_542_i1 ?_
  intro b hb
  exact common_sub_542_i1 (mem_commonEnvelope childrenD_542_i1 b hb)
def required_542_i0 : Finset Cell := ⟨(([(0, 1), (1, 3), (3, 1), (3, 2), (3, 3), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_542_i0 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 3), (2, 0), (2, 1), (2, 3), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 2), (6, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_542_i0 : Fin 2 → Finset Cell := ![(placed21 7 (3, 4) required_5), required_542_i1]
def childrenD_542_i0 : Fin 2 → Finset Cell := ![(placed21 7 (3, 4) envelope_5), envelope_542_i1]
theorem common_sub_542_i0 : commonEnvelope childrenD_542_i0 ⊆ insert (2, 1) required_542_i0 := by decide +kernel
theorem child_required_sub_542_i0 : ∀ j, childrenC_542_i0 j ⊆ insert (2, 1) required_542_i0 := by decide +kernel
theorem child_envelope_sub_542_i0 : ∀ j, childrenD_542_i0 j ⊆ envelope_542_i0 := by decide +kernel
theorem pivot_mem_542_i0 : (2, 1) ∈ envelope_542_i0 := by decide +kernel
theorem children_work_542_i0 : ∀ j, Template HasSnaky 5 (childrenC_542_i0 j) (childrenD_542_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 7 (3, 4)).mono (by decide +kernel)
  · exact row_works_542_i1.mono (by decide +kernel)
theorem row_works_542_i0 : Template HasSnaky 6 required_542_i0 envelope_542_i0 := by
  refine compose HasSnaky 5 childrenC_542_i0 childrenD_542_i0 children_work_542_i0 (2, 1)
    required_542_i0 envelope_542_i0 pivot_mem_542_i0 child_required_sub_542_i0 child_envelope_sub_542_i0 ?_
  intro b hb
  exact common_sub_542_i0 (mem_commonEnvelope childrenD_542_i0 b hb)
def required_542 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 4), (1, 5), (3, 1), (3, 2), (3, 3), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_542 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 3), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 2), (6, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_542 : Fin 2 → Finset Cell := ![(placed21 7 (1, 5) required_3), required_542_i0]
def childrenD_542 : Fin 2 → Finset Cell := ![(placed21 7 (1, 5) envelope_3), envelope_542_i0]
theorem common_sub_542 : commonEnvelope childrenD_542 ⊆ insert (1, 3) required_542 := by decide +kernel
theorem child_required_sub_542 : ∀ j, childrenC_542 j ⊆ insert (1, 3) required_542 := by decide +kernel
theorem child_envelope_sub_542 : ∀ j, childrenD_542 j ⊆ envelope_542 := by decide +kernel
theorem pivot_mem_542 : (1, 3) ∈ envelope_542 := by decide +kernel
theorem children_work_542 : ∀ j, Template HasSnaky 6 (childrenC_542 j) (childrenD_542 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_3 7 (1, 5)).mono (by decide +kernel)
  · exact row_works_542_i0.mono (by decide +kernel)
theorem row_works_542 : Template HasSnaky 7 required_542 envelope_542 := by
  refine compose HasSnaky 6 childrenC_542 childrenD_542 children_work_542 (1, 3)
    required_542 envelope_542 pivot_mem_542 child_required_sub_542 child_envelope_sub_542 ?_
  intro b hb
  exact common_sub_542 (mem_commonEnvelope childrenD_542 b hb)
def required_554_i0 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 3), (0, 4), (1, 4), (2, 6), (2, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_554_i0 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 3), (1, 4), (2, 4), (2, 5), (2, 6), (2, 7), (3, 3), (3, 4), (3, 5), (3, 6), (4, 3), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_554_i0 : Fin 2 → Finset Cell := ![(placed21 1 (0, 0) required_0), (placed21 0 (0, 3) required_515)]
def childrenD_554_i0 : Fin 2 → Finset Cell := ![(placed21 1 (0, 0) envelope_0), (placed21 0 (0, 3) envelope_515)]
theorem common_sub_554_i0 : commonEnvelope childrenD_554_i0 ⊆ insert (1, 3) required_554_i0 := by decide +kernel
theorem child_required_sub_554_i0 : ∀ j, childrenC_554_i0 j ⊆ insert (1, 3) required_554_i0 := by decide +kernel
theorem child_envelope_sub_554_i0 : ∀ j, childrenD_554_i0 j ⊆ envelope_554_i0 := by decide +kernel
theorem pivot_mem_554_i0 : (1, 3) ∈ envelope_554_i0 := by decide +kernel
theorem children_work_554_i0 : ∀ j, Template HasSnaky 5 (childrenC_554_i0 j) (childrenD_554_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 1 (0, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_515 0 (0, 3)).mono (by decide +kernel)
theorem row_works_554_i0 : Template HasSnaky 6 required_554_i0 envelope_554_i0 := by
  refine compose HasSnaky 5 childrenC_554_i0 childrenD_554_i0 children_work_554_i0 (1, 3)
    required_554_i0 envelope_554_i0 pivot_mem_554_i0 child_required_sub_554_i0 child_envelope_sub_554_i0 ?_
  intro b hb
  exact common_sub_554_i0 (mem_commonEnvelope childrenD_554_i0 b hb)
def required_554 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 3), (0, 4), (2, 6), (2, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_554 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 3), (1, 4), (1, 5), (2, 4), (2, 5), (2, 6), (2, 7), (3, 3), (3, 4), (3, 5), (3, 6), (4, 3), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_554 : Fin 2 → Finset Cell := ![(placed21 1 (0, 1) required_5), required_554_i0]
def childrenD_554 : Fin 2 → Finset Cell := ![(placed21 1 (0, 1) envelope_5), envelope_554_i0]
theorem common_sub_554 : commonEnvelope childrenD_554 ⊆ insert (1, 4) required_554 := by decide +kernel
theorem child_required_sub_554 : ∀ j, childrenC_554 j ⊆ insert (1, 4) required_554 := by decide +kernel
theorem child_envelope_sub_554 : ∀ j, childrenD_554 j ⊆ envelope_554 := by decide +kernel
theorem pivot_mem_554 : (1, 4) ∈ envelope_554 := by decide +kernel
theorem children_work_554 : ∀ j, Template HasSnaky 6 (childrenC_554 j) (childrenD_554 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 1 (0, 1)).mono (by decide +kernel)
  · exact row_works_554_i0.mono (by decide +kernel)
theorem row_works_554 : Template HasSnaky 7 required_554 envelope_554 := by
  refine compose HasSnaky 6 childrenC_554 childrenD_554 children_work_554 (1, 4)
    required_554 envelope_554 pivot_mem_554 child_required_sub_554 child_envelope_sub_554 ?_
  intro b hb
  exact common_sub_554 (mem_commonEnvelope childrenD_554 b hb)
def required_565_i0 : Finset Cell := ⟨(([(2, 3), (3, 3), (4, 3), (5, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_565_i0 : Finset Cell := ⟨(([(1, 2), (1, 4), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (4, 3), (5, 2), (5, 3), (6, 2), (6, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_565_i0 : Fin 2 → Finset Cell := ![(placed21 4 (2, 3) required_5), (placed21 0 (1, 1) required_179)]
def childrenD_565_i0 : Fin 2 → Finset Cell := ![(placed21 4 (2, 3) envelope_5), (placed21 0 (1, 1) envelope_179)]
theorem common_sub_565_i0 : commonEnvelope childrenD_565_i0 ⊆ insert (5, 3) required_565_i0 := by decide +kernel
theorem child_required_sub_565_i0 : ∀ j, childrenC_565_i0 j ⊆ insert (5, 3) required_565_i0 := by decide +kernel
theorem child_envelope_sub_565_i0 : ∀ j, childrenD_565_i0 j ⊆ envelope_565_i0 := by decide +kernel
theorem pivot_mem_565_i0 : (5, 3) ∈ envelope_565_i0 := by decide +kernel
theorem children_work_565_i0 : ∀ j, Template HasSnaky 5 (childrenC_565_i0 j) (childrenD_565_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 4 (2, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_179 0 (1, 1)).mono (by decide +kernel)
theorem row_works_565_i0 : Template HasSnaky 6 required_565_i0 envelope_565_i0 := by
  refine compose HasSnaky 5 childrenC_565_i0 childrenD_565_i0 children_work_565_i0 (5, 3)
    required_565_i0 envelope_565_i0 pivot_mem_565_i0 child_required_sub_565_i0 child_envelope_sub_565_i0 ?_
  intro b hb
  exact common_sub_565_i0 (mem_commonEnvelope childrenD_565_i0 b hb)
def required_565_i1 : Finset Cell := ⟨(([(2, 3), (3, 3), (4, 3), (5, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_565_i1 : Finset Cell := ⟨(([(0, 2), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 3), (4, 2), (4, 3), (5, 2), (5, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_565_i1 : Fin 2 → Finset Cell := ![(placed21 4 (1, 3) required_4), required_142]
def childrenD_565_i1 : Fin 2 → Finset Cell := ![(placed21 4 (1, 3) envelope_4), envelope_142]
theorem common_sub_565_i1 : commonEnvelope childrenD_565_i1 ⊆ insert (1, 3) required_565_i1 := by decide +kernel
theorem child_required_sub_565_i1 : ∀ j, childrenC_565_i1 j ⊆ insert (1, 3) required_565_i1 := by decide +kernel
theorem child_envelope_sub_565_i1 : ∀ j, childrenD_565_i1 j ⊆ envelope_565_i1 := by decide +kernel
theorem pivot_mem_565_i1 : (1, 3) ∈ envelope_565_i1 := by decide +kernel
theorem children_work_565_i1 : ∀ j, Template HasSnaky 5 (childrenC_565_i1 j) (childrenD_565_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_4 4 (1, 3)).mono (by decide +kernel)
  · exact row_works_142.mono (by decide +kernel)
theorem row_works_565_i1 : Template HasSnaky 6 required_565_i1 envelope_565_i1 := by
  refine compose HasSnaky 5 childrenC_565_i1 childrenD_565_i1 children_work_565_i1 (1, 3)
    required_565_i1 envelope_565_i1 pivot_mem_565_i1 child_required_sub_565_i1 child_envelope_sub_565_i1 ?_
  intro b hb
  exact common_sub_565_i1 (mem_commonEnvelope childrenD_565_i1 b hb)
def required_565 : Finset Cell := ⟨(([(2, 3), (3, 3), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_565 : Finset Cell := ⟨(([(0, 2), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (4, 2), (4, 3), (5, 2), (5, 3), (6, 2), (6, 3), (7, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_565 : Fin 3 → Finset Cell := ![(placed21 3 (1, 3) required_140), required_565_i0, required_565_i1]
def childrenD_565 : Fin 3 → Finset Cell := ![(placed21 3 (1, 3) envelope_140), envelope_565_i0, envelope_565_i1]
theorem common_sub_565 : commonEnvelope childrenD_565 ⊆ insert (5, 2) required_565 := by decide +kernel
theorem child_required_sub_565 : ∀ j, childrenC_565 j ⊆ insert (5, 2) required_565 := by decide +kernel
theorem child_envelope_sub_565 : ∀ j, childrenD_565 j ⊆ envelope_565 := by decide +kernel
theorem pivot_mem_565 : (5, 2) ∈ envelope_565 := by decide +kernel
theorem children_work_565 : ∀ j, Template HasSnaky 6 (childrenC_565 j) (childrenD_565 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_140 3 (1, 3)).mono (by decide +kernel)
  · exact row_works_565_i0.mono (by decide +kernel)
  · exact row_works_565_i1.mono (by decide +kernel)
theorem row_works_565 : Template HasSnaky 7 required_565 envelope_565 := by
  refine compose HasSnaky 6 childrenC_565 childrenD_565 children_work_565 (5, 2)
    required_565 envelope_565 pivot_mem_565 child_required_sub_565 child_envelope_sub_565 ?_
  intro b hb
  exact common_sub_565 (mem_commonEnvelope childrenD_565 b hb)
def required_576_i2 : Finset Cell := ⟨(([(4, 2), (4, 3), (4, 4), (4, 5), (5, 4), (6, 4), (7, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_576_i2 : Finset Cell := ⟨(([(4, 2), (4, 3), (4, 4), (4, 5), (5, 4), (5, 5), (5, 6), (6, 4), (7, 4), (8, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_576_i2 : Fin 2 → Finset Cell := ![(placed21 2 (8, 4) required_0), (placed21 1 (4, 2) required_5)]
def childrenD_576_i2 : Fin 2 → Finset Cell := ![(placed21 2 (8, 4) envelope_0), (placed21 1 (4, 2) envelope_5)]
theorem common_sub_576_i2 : commonEnvelope childrenD_576_i2 ⊆ insert (5, 5) required_576_i2 := by decide +kernel
theorem child_required_sub_576_i2 : ∀ j, childrenC_576_i2 j ⊆ insert (5, 5) required_576_i2 := by decide +kernel
theorem child_envelope_sub_576_i2 : ∀ j, childrenD_576_i2 j ⊆ envelope_576_i2 := by decide +kernel
theorem pivot_mem_576_i2 : (5, 5) ∈ envelope_576_i2 := by decide +kernel
theorem children_work_576_i2 : ∀ j, Template HasSnaky 1 (childrenC_576_i2 j) (childrenD_576_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 2 (8, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_5 1 (4, 2)).mono (by decide +kernel)
theorem row_works_576_i2 : Template HasSnaky 2 required_576_i2 envelope_576_i2 := by
  refine compose HasSnaky 1 childrenC_576_i2 childrenD_576_i2 children_work_576_i2 (5, 5)
    required_576_i2 envelope_576_i2 pivot_mem_576_i2 child_required_sub_576_i2 child_envelope_sub_576_i2 ?_
  intro b hb
  exact common_sub_576_i2 (mem_commonEnvelope childrenD_576_i2 b hb)
def required_576_i3 : Finset Cell := ⟨(([(1, 2), (1, 5), (2, 2), (4, 2), (4, 3), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_576_i3 : Finset Cell := ⟨(([(0, 1), (0, 3), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 1), (2, 2), (3, 1), (3, 2), (4, 2), (4, 3), (4, 4), (4, 5), (5, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_576_i3 : Fin 2 → Finset Cell := ![(placed21 7 (4, 5) required_5), (placed21 3 (0, 5) required_87)]
def childrenD_576_i3 : Fin 2 → Finset Cell := ![(placed21 7 (4, 5) envelope_5), (placed21 3 (0, 5) envelope_87)]
theorem common_sub_576_i3 : commonEnvelope childrenD_576_i3 ⊆ insert (3, 2) required_576_i3 := by decide +kernel
theorem child_required_sub_576_i3 : ∀ j, childrenC_576_i3 j ⊆ insert (3, 2) required_576_i3 := by decide +kernel
theorem child_envelope_sub_576_i3 : ∀ j, childrenD_576_i3 j ⊆ envelope_576_i3 := by decide +kernel
theorem pivot_mem_576_i3 : (3, 2) ∈ envelope_576_i3 := by decide +kernel
theorem children_work_576_i3 : ∀ j, Template HasSnaky 3 (childrenC_576_i3 j) (childrenD_576_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 7 (4, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_87 3 (0, 5)).mono (by decide +kernel)
theorem row_works_576_i3 : Template HasSnaky 4 required_576_i3 envelope_576_i3 := by
  refine compose HasSnaky 3 childrenC_576_i3 childrenD_576_i3 children_work_576_i3 (3, 2)
    required_576_i3 envelope_576_i3 pivot_mem_576_i3 child_required_sub_576_i3 child_envelope_sub_576_i3 ?_
  intro b hb
  exact common_sub_576_i3 (mem_commonEnvelope childrenD_576_i3 b hb)
def required_576_i1 : Finset Cell := ⟨(([(1, 2), (1, 5), (2, 2), (4, 2), (4, 3), (4, 4), (5, 4), (6, 4), (7, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_576_i1 : Finset Cell := ⟨(([(0, 1), (0, 3), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 1), (2, 2), (3, 1), (3, 2), (4, 2), (4, 3), (4, 4), (4, 5), (5, 2), (5, 4), (5, 5), (5, 6), (6, 4), (7, 4), (8, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_576_i1 : Fin 2 → Finset Cell := ![required_576_i2, required_576_i3]
def childrenD_576_i1 : Fin 2 → Finset Cell := ![envelope_576_i2, envelope_576_i3]
theorem common_sub_576_i1 : commonEnvelope childrenD_576_i1 ⊆ insert (4, 5) required_576_i1 := by decide +kernel
theorem child_required_sub_576_i1 : ∀ j, childrenC_576_i1 j ⊆ insert (4, 5) required_576_i1 := by decide +kernel
theorem child_envelope_sub_576_i1 : ∀ j, childrenD_576_i1 j ⊆ envelope_576_i1 := by decide +kernel
theorem pivot_mem_576_i1 : (4, 5) ∈ envelope_576_i1 := by decide +kernel
theorem children_work_576_i1 : ∀ j, Template HasSnaky 4 (childrenC_576_i1 j) (childrenD_576_i1 j) := by
  intro j
  fin_cases j
  · exact row_works_576_i2.mono (by decide +kernel)
  · exact row_works_576_i3.mono (by decide +kernel)
theorem row_works_576_i1 : Template HasSnaky 5 required_576_i1 envelope_576_i1 := by
  refine compose HasSnaky 4 childrenC_576_i1 childrenD_576_i1 children_work_576_i1 (4, 5)
    required_576_i1 envelope_576_i1 pivot_mem_576_i1 child_required_sub_576_i1 child_envelope_sub_576_i1 ?_
  intro b hb
  exact common_sub_576_i1 (mem_commonEnvelope childrenD_576_i1 b hb)
def required_576_i4 : Finset Cell := ⟨(([(1, 2), (1, 5), (2, 2), (4, 2), (4, 3), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_576_i4 : Finset Cell := ⟨(([(0, 1), (0, 3), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 1), (2, 2), (3, 0), (3, 1), (3, 2), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 1), (5, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_576_i4 : Fin 2 → Finset Cell := ![(placed21 3 (0, 5) required_87), (placed21 0 (1, 0) required_215)]
def childrenD_576_i4 : Fin 2 → Finset Cell := ![(placed21 3 (0, 5) envelope_87), (placed21 0 (1, 0) envelope_215)]
theorem common_sub_576_i4 : commonEnvelope childrenD_576_i4 ⊆ insert (3, 2) required_576_i4 := by decide +kernel
theorem child_required_sub_576_i4 : ∀ j, childrenC_576_i4 j ⊆ insert (3, 2) required_576_i4 := by decide +kernel
theorem child_envelope_sub_576_i4 : ∀ j, childrenD_576_i4 j ⊆ envelope_576_i4 := by decide +kernel
theorem pivot_mem_576_i4 : (3, 2) ∈ envelope_576_i4 := by decide +kernel
theorem children_work_576_i4 : ∀ j, Template HasSnaky 3 (childrenC_576_i4 j) (childrenD_576_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_87 3 (0, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_215 0 (1, 0)).mono (by decide +kernel)
theorem row_works_576_i4 : Template HasSnaky 4 required_576_i4 envelope_576_i4 := by
  refine compose HasSnaky 3 childrenC_576_i4 childrenD_576_i4 children_work_576_i4 (3, 2)
    required_576_i4 envelope_576_i4 pivot_mem_576_i4 child_required_sub_576_i4 child_envelope_sub_576_i4 ?_
  intro b hb
  exact common_sub_576_i4 (mem_commonEnvelope childrenD_576_i4 b hb)
def required_576_i0 : Finset Cell := ⟨(([(1, 2), (1, 5), (2, 2), (4, 3), (4, 4), (5, 4), (6, 4), (7, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_576_i0 : Finset Cell := ⟨(([(0, 1), (0, 3), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 1), (2, 2), (3, 0), (3, 1), (3, 2), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 0), (5, 1), (5, 2), (5, 4), (5, 5), (5, 6), (5, 7), (6, 4), (7, 4), (8, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_576_i0 : Fin 4 → Finset Cell := ![(placed21 0 (4, 1) required_52), (placed21 6 (5, 5) required_246), required_576_i1, required_576_i4]
def childrenD_576_i0 : Fin 4 → Finset Cell := ![(placed21 0 (4, 1) envelope_52), (placed21 6 (5, 5) envelope_246), envelope_576_i1, envelope_576_i4]
theorem common_sub_576_i0 : commonEnvelope childrenD_576_i0 ⊆ insert (4, 2) required_576_i0 := by decide +kernel
theorem child_required_sub_576_i0 : ∀ j, childrenC_576_i0 j ⊆ insert (4, 2) required_576_i0 := by decide +kernel
theorem child_envelope_sub_576_i0 : ∀ j, childrenD_576_i0 j ⊆ envelope_576_i0 := by decide +kernel
theorem pivot_mem_576_i0 : (4, 2) ∈ envelope_576_i0 := by decide +kernel
theorem children_work_576_i0 : ∀ j, Template HasSnaky 5 (childrenC_576_i0 j) (childrenD_576_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_52 0 (4, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_246 6 (5, 5)).mono (by decide +kernel)
  · exact row_works_576_i1.mono (by decide +kernel)
  · exact row_works_576_i4.mono (by decide +kernel)
theorem row_works_576_i0 : Template HasSnaky 6 required_576_i0 envelope_576_i0 := by
  refine compose HasSnaky 5 childrenC_576_i0 childrenD_576_i0 children_work_576_i0 (4, 2)
    required_576_i0 envelope_576_i0 pivot_mem_576_i0 child_required_sub_576_i0 child_envelope_sub_576_i0 ?_
  intro b hb
  exact common_sub_576_i0 (mem_commonEnvelope childrenD_576_i0 b hb)
def required_576 : Finset Cell := ⟨(([(1, 2), (1, 5), (2, 2), (4, 4), (5, 4), (6, 4), (7, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_576 : Finset Cell := ⟨(([(0, 1), (0, 3), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 1), (2, 2), (3, 0), (3, 1), (3, 2), (3, 3), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 0), (5, 1), (5, 2), (5, 4), (5, 5), (5, 6), (5, 7), (6, 4), (7, 4), (8, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_576 : Fin 2 → Finset Cell := ![(placed21 6 (7, 4) required_5), required_576_i0]
def childrenD_576 : Fin 2 → Finset Cell := ![(placed21 6 (7, 4) envelope_5), envelope_576_i0]
theorem common_sub_576 : commonEnvelope childrenD_576 ⊆ insert (4, 3) required_576 := by decide +kernel
theorem child_required_sub_576 : ∀ j, childrenC_576 j ⊆ insert (4, 3) required_576 := by decide +kernel
theorem child_envelope_sub_576 : ∀ j, childrenD_576 j ⊆ envelope_576 := by decide +kernel
theorem pivot_mem_576 : (4, 3) ∈ envelope_576 := by decide +kernel
theorem children_work_576 : ∀ j, Template HasSnaky 6 (childrenC_576 j) (childrenD_576 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 6 (7, 4)).mono (by decide +kernel)
  · exact row_works_576_i0.mono (by decide +kernel)
theorem row_works_576 : Template HasSnaky 7 required_576 envelope_576 := by
  refine compose HasSnaky 6 childrenC_576 childrenD_576 children_work_576 (4, 3)
    required_576 envelope_576 pivot_mem_576 child_required_sub_576 child_envelope_sub_576 ?_
  intro b hb
  exact common_sub_576 (mem_commonEnvelope childrenD_576 b hb)
def height_511_i1 : ℕ := 4
def childrenH_511_i1 : Fin 2 → ℕ := ![height_2, height_44]
theorem height_exact_511_i1 : height_511_i1 = 1 + Finset.univ.sup childrenH_511_i1 := by decide +kernel
theorem required_origin_511_i1 : ∀ x ∈ required_511_i1,
    (∃ j, x ∈ childrenC_511_i1 j) ∨ ∀ j, x ∈ childrenD_511_i1 j := by decide +kernel
theorem required_exact_511_i1 : required_511_i1 =
    ((Finset.univ.biUnion childrenC_511_i1) ∪ commonEnvelope childrenD_511_i1).erase (4, 4) := by
  exact required_eq_combination childrenC_511_i1 childrenD_511_i1 (4, 4) required_511_i1
    (by decide +kernel) child_required_sub_511_i1 common_sub_511_i1 required_origin_511_i1
theorem envelope_origin_511_i1 : ∀ x ∈ envelope_511_i1,
    x = (4, 4) ∨ ∃ j, x ∈ childrenD_511_i1 j := by decide +kernel
theorem envelope_exact_511_i1 : envelope_511_i1 =
    insert (4, 4) (Finset.univ.biUnion childrenD_511_i1) := by
  exact envelope_eq_combination childrenD_511_i1 (4, 4) envelope_511_i1
    pivot_mem_511_i1 child_envelope_sub_511_i1 envelope_origin_511_i1
def checked_511_i1 : CheckedCard where
  required := required_511_i1
  envelope := envelope_511_i1
  height := height_511_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_511_i1
def height_511_i3 : ℕ := 4
def childrenH_511_i3 : Fin 3 → ℕ := ![height_7, height_9, height_221]
theorem height_exact_511_i3 : height_511_i3 = 1 + Finset.univ.sup childrenH_511_i3 := by decide +kernel
theorem required_origin_511_i3 : ∀ x ∈ required_511_i3,
    (∃ j, x ∈ childrenC_511_i3 j) ∨ ∀ j, x ∈ childrenD_511_i3 j := by decide +kernel
theorem required_exact_511_i3 : required_511_i3 =
    ((Finset.univ.biUnion childrenC_511_i3) ∪ commonEnvelope childrenD_511_i3).erase (3, 5) := by
  exact required_eq_combination childrenC_511_i3 childrenD_511_i3 (3, 5) required_511_i3
    (by decide +kernel) child_required_sub_511_i3 common_sub_511_i3 required_origin_511_i3
theorem envelope_origin_511_i3 : ∀ x ∈ envelope_511_i3,
    x = (3, 5) ∨ ∃ j, x ∈ childrenD_511_i3 j := by decide +kernel
theorem envelope_exact_511_i3 : envelope_511_i3 =
    insert (3, 5) (Finset.univ.biUnion childrenD_511_i3) := by
  exact envelope_eq_combination childrenD_511_i3 (3, 5) envelope_511_i3
    pivot_mem_511_i3 child_envelope_sub_511_i3 envelope_origin_511_i3
def checked_511_i3 : CheckedCard where
  required := required_511_i3
  envelope := envelope_511_i3
  height := height_511_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_511_i3
def height_511_i2 : ℕ := 5
def childrenH_511_i2 : Fin 2 → ℕ := ![height_0, height_511_i3]
theorem height_exact_511_i2 : height_511_i2 = 1 + Finset.univ.sup childrenH_511_i2 := by decide +kernel
theorem required_origin_511_i2 : ∀ x ∈ required_511_i2,
    (∃ j, x ∈ childrenC_511_i2 j) ∨ ∀ j, x ∈ childrenD_511_i2 j := by decide +kernel
theorem required_exact_511_i2 : required_511_i2 =
    ((Finset.univ.biUnion childrenC_511_i2) ∪ commonEnvelope childrenD_511_i2).erase (2, 4) := by
  exact required_eq_combination childrenC_511_i2 childrenD_511_i2 (2, 4) required_511_i2
    (by decide +kernel) child_required_sub_511_i2 common_sub_511_i2 required_origin_511_i2
theorem envelope_origin_511_i2 : ∀ x ∈ envelope_511_i2,
    x = (2, 4) ∨ ∃ j, x ∈ childrenD_511_i2 j := by decide +kernel
theorem envelope_exact_511_i2 : envelope_511_i2 =
    insert (2, 4) (Finset.univ.biUnion childrenD_511_i2) := by
  exact envelope_eq_combination childrenD_511_i2 (2, 4) envelope_511_i2
    pivot_mem_511_i2 child_envelope_sub_511_i2 envelope_origin_511_i2
def checked_511_i2 : CheckedCard where
  required := required_511_i2
  envelope := envelope_511_i2
  height := height_511_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_511_i2
def height_511_i0 : ℕ := 6
def childrenH_511_i0 : Fin 5 → ℕ := ![height_13, height_14, height_240, height_511_i1, height_511_i2]
theorem height_exact_511_i0 : height_511_i0 = 1 + Finset.univ.sup childrenH_511_i0 := by decide +kernel
theorem required_origin_511_i0 : ∀ x ∈ required_511_i0,
    (∃ j, x ∈ childrenC_511_i0 j) ∨ ∀ j, x ∈ childrenD_511_i0 j := by decide +kernel
theorem required_exact_511_i0 : required_511_i0 =
    ((Finset.univ.biUnion childrenC_511_i0) ∪ commonEnvelope childrenD_511_i0).erase (3, 4) := by
  exact required_eq_combination childrenC_511_i0 childrenD_511_i0 (3, 4) required_511_i0
    (by decide +kernel) child_required_sub_511_i0 common_sub_511_i0 required_origin_511_i0
theorem envelope_origin_511_i0 : ∀ x ∈ envelope_511_i0,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_511_i0 j := by decide +kernel
theorem envelope_exact_511_i0 : envelope_511_i0 =
    insert (3, 4) (Finset.univ.biUnion childrenD_511_i0) := by
  exact envelope_eq_combination childrenD_511_i0 (3, 4) envelope_511_i0
    pivot_mem_511_i0 child_envelope_sub_511_i0 envelope_origin_511_i0
def checked_511_i0 : CheckedCard where
  required := required_511_i0
  envelope := envelope_511_i0
  height := height_511_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_511_i0
def height_511 : ℕ := 7
def childrenH_511 : Fin 2 → ℕ := ![height_15, height_511_i0]
theorem height_exact_511 : height_511 = 1 + Finset.univ.sup childrenH_511 := by decide +kernel
theorem required_origin_511 : ∀ x ∈ required_511,
    (∃ j, x ∈ childrenC_511 j) ∨ ∀ j, x ∈ childrenD_511 j := by decide +kernel
theorem required_exact_511 : required_511 =
    ((Finset.univ.biUnion childrenC_511) ∪ commonEnvelope childrenD_511).erase (1, 4) := by
  exact required_eq_combination childrenC_511 childrenD_511 (1, 4) required_511
    (by decide +kernel) child_required_sub_511 common_sub_511 required_origin_511
theorem envelope_origin_511 : ∀ x ∈ envelope_511,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_511 j := by decide +kernel
theorem envelope_exact_511 : envelope_511 =
    insert (1, 4) (Finset.univ.biUnion childrenD_511) := by
  exact envelope_eq_combination childrenD_511 (1, 4) envelope_511
    pivot_mem_511 child_envelope_sub_511 envelope_origin_511
def checked_511 : CheckedCard where
  required := required_511
  envelope := envelope_511
  height := height_511
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_511
def height_522_i0 : ℕ := 6
def childrenH_522_i0 : Fin 2 → ℕ := ![height_5, height_416]
theorem height_exact_522_i0 : height_522_i0 = 1 + Finset.univ.sup childrenH_522_i0 := by decide +kernel
theorem required_origin_522_i0 : ∀ x ∈ required_522_i0,
    (∃ j, x ∈ childrenC_522_i0 j) ∨ ∀ j, x ∈ childrenD_522_i0 j := by decide +kernel
theorem required_exact_522_i0 : required_522_i0 =
    ((Finset.univ.biUnion childrenC_522_i0) ∪ commonEnvelope childrenD_522_i0).erase (1, 3) := by
  exact required_eq_combination childrenC_522_i0 childrenD_522_i0 (1, 3) required_522_i0
    (by decide +kernel) child_required_sub_522_i0 common_sub_522_i0 required_origin_522_i0
theorem envelope_origin_522_i0 : ∀ x ∈ envelope_522_i0,
    x = (1, 3) ∨ ∃ j, x ∈ childrenD_522_i0 j := by decide +kernel
theorem envelope_exact_522_i0 : envelope_522_i0 =
    insert (1, 3) (Finset.univ.biUnion childrenD_522_i0) := by
  exact envelope_eq_combination childrenD_522_i0 (1, 3) envelope_522_i0
    pivot_mem_522_i0 child_envelope_sub_522_i0 envelope_origin_522_i0
def checked_522_i0 : CheckedCard where
  required := required_522_i0
  envelope := envelope_522_i0
  height := height_522_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_522_i0
def height_522 : ℕ := 7
def childrenH_522 : Fin 3 → ℕ := ![height_8, height_11, height_522_i0]
theorem height_exact_522 : height_522 = 1 + Finset.univ.sup childrenH_522 := by decide +kernel
theorem required_origin_522 : ∀ x ∈ required_522,
    (∃ j, x ∈ childrenC_522 j) ∨ ∀ j, x ∈ childrenD_522 j := by decide +kernel
theorem required_exact_522 : required_522 =
    ((Finset.univ.biUnion childrenC_522) ∪ commonEnvelope childrenD_522).erase (4, 2) := by
  exact required_eq_combination childrenC_522 childrenD_522 (4, 2) required_522
    (by decide +kernel) child_required_sub_522 common_sub_522 required_origin_522
theorem envelope_origin_522 : ∀ x ∈ envelope_522,
    x = (4, 2) ∨ ∃ j, x ∈ childrenD_522 j := by decide +kernel
theorem envelope_exact_522 : envelope_522 =
    insert (4, 2) (Finset.univ.biUnion childrenD_522) := by
  exact envelope_eq_combination childrenD_522 (4, 2) envelope_522
    pivot_mem_522 child_envelope_sub_522 envelope_origin_522
def checked_522 : CheckedCard where
  required := required_522
  envelope := envelope_522
  height := height_522
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_522
def height_526 : ℕ := 7
def childrenH_526 : Fin 2 → ℕ := ![height_0, height_525]
theorem height_exact_526 : height_526 = 1 + Finset.univ.sup childrenH_526 := by decide +kernel
theorem required_origin_526 : ∀ x ∈ required_526,
    (∃ j, x ∈ childrenC_526 j) ∨ ∀ j, x ∈ childrenD_526 j := by decide +kernel
theorem required_exact_526 : required_526 =
    ((Finset.univ.biUnion childrenC_526) ∪ commonEnvelope childrenD_526).erase (3, 1) := by
  exact required_eq_combination childrenC_526 childrenD_526 (3, 1) required_526
    (by decide +kernel) child_required_sub_526 common_sub_526 required_origin_526
theorem envelope_origin_526 : ∀ x ∈ envelope_526,
    x = (3, 1) ∨ ∃ j, x ∈ childrenD_526 j := by decide +kernel
theorem envelope_exact_526 : envelope_526 =
    insert (3, 1) (Finset.univ.biUnion childrenD_526) := by
  exact envelope_eq_combination childrenD_526 (3, 1) envelope_526
    pivot_mem_526 child_envelope_sub_526 envelope_origin_526
def checked_526 : CheckedCard where
  required := required_526
  envelope := envelope_526
  height := height_526
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_526
def height_542_i3 : ℕ := 2
def childrenH_542_i3 : Fin 2 → ℕ := ![height_0, height_1]
theorem height_exact_542_i3 : height_542_i3 = 1 + Finset.univ.sup childrenH_542_i3 := by decide +kernel
theorem required_origin_542_i3 : ∀ x ∈ required_542_i3,
    (∃ j, x ∈ childrenC_542_i3 j) ∨ ∀ j, x ∈ childrenD_542_i3 j := by decide +kernel
theorem required_exact_542_i3 : required_542_i3 =
    ((Finset.univ.biUnion childrenC_542_i3) ∪ commonEnvelope childrenD_542_i3).erase (5, 2) := by
  exact required_eq_combination childrenC_542_i3 childrenD_542_i3 (5, 2) required_542_i3
    (by decide +kernel) child_required_sub_542_i3 common_sub_542_i3 required_origin_542_i3
theorem envelope_origin_542_i3 : ∀ x ∈ envelope_542_i3,
    x = (5, 2) ∨ ∃ j, x ∈ childrenD_542_i3 j := by decide +kernel
theorem envelope_exact_542_i3 : envelope_542_i3 =
    insert (5, 2) (Finset.univ.biUnion childrenD_542_i3) := by
  exact envelope_eq_combination childrenD_542_i3 (5, 2) envelope_542_i3
    pivot_mem_542_i3 child_envelope_sub_542_i3 envelope_origin_542_i3
def checked_542_i3 : CheckedCard where
  required := required_542_i3
  envelope := envelope_542_i3
  height := height_542_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_542_i3
def height_542_i2 : ℕ := 4
def childrenH_542_i2 : Fin 2 → ℕ := ![height_29, height_542_i3]
theorem height_exact_542_i2 : height_542_i2 = 1 + Finset.univ.sup childrenH_542_i2 := by decide +kernel
theorem required_origin_542_i2 : ∀ x ∈ required_542_i2,
    (∃ j, x ∈ childrenC_542_i2 j) ∨ ∀ j, x ∈ childrenD_542_i2 j := by decide +kernel
theorem required_exact_542_i2 : required_542_i2 =
    ((Finset.univ.biUnion childrenC_542_i2) ∪ commonEnvelope childrenD_542_i2).erase (4, 3) := by
  exact required_eq_combination childrenC_542_i2 childrenD_542_i2 (4, 3) required_542_i2
    (by decide +kernel) child_required_sub_542_i2 common_sub_542_i2 required_origin_542_i2
theorem envelope_origin_542_i2 : ∀ x ∈ envelope_542_i2,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_542_i2 j := by decide +kernel
theorem envelope_exact_542_i2 : envelope_542_i2 =
    insert (4, 3) (Finset.univ.biUnion childrenD_542_i2) := by
  exact envelope_eq_combination childrenD_542_i2 (4, 3) envelope_542_i2
    pivot_mem_542_i2 child_envelope_sub_542_i2 envelope_origin_542_i2
def checked_542_i2 : CheckedCard where
  required := required_542_i2
  envelope := envelope_542_i2
  height := height_542_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_542_i2
def height_542_i1 : ℕ := 5
def childrenH_542_i1 : Fin 2 → ℕ := ![height_1, height_542_i2]
theorem height_exact_542_i1 : height_542_i1 = 1 + Finset.univ.sup childrenH_542_i1 := by decide +kernel
theorem required_origin_542_i1 : ∀ x ∈ required_542_i1,
    (∃ j, x ∈ childrenC_542_i1 j) ∨ ∀ j, x ∈ childrenD_542_i1 j := by decide +kernel
theorem required_exact_542_i1 : required_542_i1 =
    ((Finset.univ.biUnion childrenC_542_i1) ∪ commonEnvelope childrenD_542_i1).erase (4, 2) := by
  exact required_eq_combination childrenC_542_i1 childrenD_542_i1 (4, 2) required_542_i1
    (by decide +kernel) child_required_sub_542_i1 common_sub_542_i1 required_origin_542_i1
theorem envelope_origin_542_i1 : ∀ x ∈ envelope_542_i1,
    x = (4, 2) ∨ ∃ j, x ∈ childrenD_542_i1 j := by decide +kernel
theorem envelope_exact_542_i1 : envelope_542_i1 =
    insert (4, 2) (Finset.univ.biUnion childrenD_542_i1) := by
  exact envelope_eq_combination childrenD_542_i1 (4, 2) envelope_542_i1
    pivot_mem_542_i1 child_envelope_sub_542_i1 envelope_origin_542_i1
def checked_542_i1 : CheckedCard where
  required := required_542_i1
  envelope := envelope_542_i1
  height := height_542_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_542_i1
def height_542_i0 : ℕ := 6
def childrenH_542_i0 : Fin 2 → ℕ := ![height_5, height_542_i1]
theorem height_exact_542_i0 : height_542_i0 = 1 + Finset.univ.sup childrenH_542_i0 := by decide +kernel
theorem required_origin_542_i0 : ∀ x ∈ required_542_i0,
    (∃ j, x ∈ childrenC_542_i0 j) ∨ ∀ j, x ∈ childrenD_542_i0 j := by decide +kernel
theorem required_exact_542_i0 : required_542_i0 =
    ((Finset.univ.biUnion childrenC_542_i0) ∪ commonEnvelope childrenD_542_i0).erase (2, 1) := by
  exact required_eq_combination childrenC_542_i0 childrenD_542_i0 (2, 1) required_542_i0
    (by decide +kernel) child_required_sub_542_i0 common_sub_542_i0 required_origin_542_i0
theorem envelope_origin_542_i0 : ∀ x ∈ envelope_542_i0,
    x = (2, 1) ∨ ∃ j, x ∈ childrenD_542_i0 j := by decide +kernel
theorem envelope_exact_542_i0 : envelope_542_i0 =
    insert (2, 1) (Finset.univ.biUnion childrenD_542_i0) := by
  exact envelope_eq_combination childrenD_542_i0 (2, 1) envelope_542_i0
    pivot_mem_542_i0 child_envelope_sub_542_i0 envelope_origin_542_i0
def checked_542_i0 : CheckedCard where
  required := required_542_i0
  envelope := envelope_542_i0
  height := height_542_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_542_i0
def height_542 : ℕ := 7
def childrenH_542 : Fin 2 → ℕ := ![height_3, height_542_i0]
theorem height_exact_542 : height_542 = 1 + Finset.univ.sup childrenH_542 := by decide +kernel
theorem required_origin_542 : ∀ x ∈ required_542,
    (∃ j, x ∈ childrenC_542 j) ∨ ∀ j, x ∈ childrenD_542 j := by decide +kernel
theorem required_exact_542 : required_542 =
    ((Finset.univ.biUnion childrenC_542) ∪ commonEnvelope childrenD_542).erase (1, 3) := by
  exact required_eq_combination childrenC_542 childrenD_542 (1, 3) required_542
    (by decide +kernel) child_required_sub_542 common_sub_542 required_origin_542
theorem envelope_origin_542 : ∀ x ∈ envelope_542,
    x = (1, 3) ∨ ∃ j, x ∈ childrenD_542 j := by decide +kernel
theorem envelope_exact_542 : envelope_542 =
    insert (1, 3) (Finset.univ.biUnion childrenD_542) := by
  exact envelope_eq_combination childrenD_542 (1, 3) envelope_542
    pivot_mem_542 child_envelope_sub_542 envelope_origin_542
def checked_542 : CheckedCard where
  required := required_542
  envelope := envelope_542
  height := height_542
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_542
def height_554_i0 : ℕ := 6
def childrenH_554_i0 : Fin 2 → ℕ := ![height_0, height_515]
theorem height_exact_554_i0 : height_554_i0 = 1 + Finset.univ.sup childrenH_554_i0 := by decide +kernel
theorem required_origin_554_i0 : ∀ x ∈ required_554_i0,
    (∃ j, x ∈ childrenC_554_i0 j) ∨ ∀ j, x ∈ childrenD_554_i0 j := by decide +kernel
theorem required_exact_554_i0 : required_554_i0 =
    ((Finset.univ.biUnion childrenC_554_i0) ∪ commonEnvelope childrenD_554_i0).erase (1, 3) := by
  exact required_eq_combination childrenC_554_i0 childrenD_554_i0 (1, 3) required_554_i0
    (by decide +kernel) child_required_sub_554_i0 common_sub_554_i0 required_origin_554_i0
theorem envelope_origin_554_i0 : ∀ x ∈ envelope_554_i0,
    x = (1, 3) ∨ ∃ j, x ∈ childrenD_554_i0 j := by decide +kernel
theorem envelope_exact_554_i0 : envelope_554_i0 =
    insert (1, 3) (Finset.univ.biUnion childrenD_554_i0) := by
  exact envelope_eq_combination childrenD_554_i0 (1, 3) envelope_554_i0
    pivot_mem_554_i0 child_envelope_sub_554_i0 envelope_origin_554_i0
def checked_554_i0 : CheckedCard where
  required := required_554_i0
  envelope := envelope_554_i0
  height := height_554_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_554_i0
def height_554 : ℕ := 7
def childrenH_554 : Fin 2 → ℕ := ![height_5, height_554_i0]
theorem height_exact_554 : height_554 = 1 + Finset.univ.sup childrenH_554 := by decide +kernel
theorem required_origin_554 : ∀ x ∈ required_554,
    (∃ j, x ∈ childrenC_554 j) ∨ ∀ j, x ∈ childrenD_554 j := by decide +kernel
theorem required_exact_554 : required_554 =
    ((Finset.univ.biUnion childrenC_554) ∪ commonEnvelope childrenD_554).erase (1, 4) := by
  exact required_eq_combination childrenC_554 childrenD_554 (1, 4) required_554
    (by decide +kernel) child_required_sub_554 common_sub_554 required_origin_554
theorem envelope_origin_554 : ∀ x ∈ envelope_554,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_554 j := by decide +kernel
theorem envelope_exact_554 : envelope_554 =
    insert (1, 4) (Finset.univ.biUnion childrenD_554) := by
  exact envelope_eq_combination childrenD_554 (1, 4) envelope_554
    pivot_mem_554 child_envelope_sub_554 envelope_origin_554
def checked_554 : CheckedCard where
  required := required_554
  envelope := envelope_554
  height := height_554
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_554
def height_565_i0 : ℕ := 6
def childrenH_565_i0 : Fin 2 → ℕ := ![height_5, height_179]
theorem height_exact_565_i0 : height_565_i0 = 1 + Finset.univ.sup childrenH_565_i0 := by decide +kernel
theorem required_origin_565_i0 : ∀ x ∈ required_565_i0,
    (∃ j, x ∈ childrenC_565_i0 j) ∨ ∀ j, x ∈ childrenD_565_i0 j := by decide +kernel
theorem required_exact_565_i0 : required_565_i0 =
    ((Finset.univ.biUnion childrenC_565_i0) ∪ commonEnvelope childrenD_565_i0).erase (5, 3) := by
  exact required_eq_combination childrenC_565_i0 childrenD_565_i0 (5, 3) required_565_i0
    (by decide +kernel) child_required_sub_565_i0 common_sub_565_i0 required_origin_565_i0
theorem envelope_origin_565_i0 : ∀ x ∈ envelope_565_i0,
    x = (5, 3) ∨ ∃ j, x ∈ childrenD_565_i0 j := by decide +kernel
theorem envelope_exact_565_i0 : envelope_565_i0 =
    insert (5, 3) (Finset.univ.biUnion childrenD_565_i0) := by
  exact envelope_eq_combination childrenD_565_i0 (5, 3) envelope_565_i0
    pivot_mem_565_i0 child_envelope_sub_565_i0 envelope_origin_565_i0
def checked_565_i0 : CheckedCard where
  required := required_565_i0
  envelope := envelope_565_i0
  height := height_565_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_565_i0
def height_565_i1 : ℕ := 6
def childrenH_565_i1 : Fin 2 → ℕ := ![height_4, height_142]
theorem height_exact_565_i1 : height_565_i1 = 1 + Finset.univ.sup childrenH_565_i1 := by decide +kernel
theorem required_origin_565_i1 : ∀ x ∈ required_565_i1,
    (∃ j, x ∈ childrenC_565_i1 j) ∨ ∀ j, x ∈ childrenD_565_i1 j := by decide +kernel
theorem required_exact_565_i1 : required_565_i1 =
    ((Finset.univ.biUnion childrenC_565_i1) ∪ commonEnvelope childrenD_565_i1).erase (1, 3) := by
  exact required_eq_combination childrenC_565_i1 childrenD_565_i1 (1, 3) required_565_i1
    (by decide +kernel) child_required_sub_565_i1 common_sub_565_i1 required_origin_565_i1
theorem envelope_origin_565_i1 : ∀ x ∈ envelope_565_i1,
    x = (1, 3) ∨ ∃ j, x ∈ childrenD_565_i1 j := by decide +kernel
theorem envelope_exact_565_i1 : envelope_565_i1 =
    insert (1, 3) (Finset.univ.biUnion childrenD_565_i1) := by
  exact envelope_eq_combination childrenD_565_i1 (1, 3) envelope_565_i1
    pivot_mem_565_i1 child_envelope_sub_565_i1 envelope_origin_565_i1
def checked_565_i1 : CheckedCard where
  required := required_565_i1
  envelope := envelope_565_i1
  height := height_565_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_565_i1
def height_565 : ℕ := 7
def childrenH_565 : Fin 3 → ℕ := ![height_140, height_565_i0, height_565_i1]
theorem height_exact_565 : height_565 = 1 + Finset.univ.sup childrenH_565 := by decide +kernel
theorem required_origin_565 : ∀ x ∈ required_565,
    (∃ j, x ∈ childrenC_565 j) ∨ ∀ j, x ∈ childrenD_565 j := by decide +kernel
theorem required_exact_565 : required_565 =
    ((Finset.univ.biUnion childrenC_565) ∪ commonEnvelope childrenD_565).erase (5, 2) := by
  exact required_eq_combination childrenC_565 childrenD_565 (5, 2) required_565
    (by decide +kernel) child_required_sub_565 common_sub_565 required_origin_565
theorem envelope_origin_565 : ∀ x ∈ envelope_565,
    x = (5, 2) ∨ ∃ j, x ∈ childrenD_565 j := by decide +kernel
theorem envelope_exact_565 : envelope_565 =
    insert (5, 2) (Finset.univ.biUnion childrenD_565) := by
  exact envelope_eq_combination childrenD_565 (5, 2) envelope_565
    pivot_mem_565 child_envelope_sub_565 envelope_origin_565
def checked_565 : CheckedCard where
  required := required_565
  envelope := envelope_565
  height := height_565
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_565
def height_576_i2 : ℕ := 2
def childrenH_576_i2 : Fin 2 → ℕ := ![height_0, height_5]
theorem height_exact_576_i2 : height_576_i2 = 1 + Finset.univ.sup childrenH_576_i2 := by decide +kernel
theorem required_origin_576_i2 : ∀ x ∈ required_576_i2,
    (∃ j, x ∈ childrenC_576_i2 j) ∨ ∀ j, x ∈ childrenD_576_i2 j := by decide +kernel
theorem required_exact_576_i2 : required_576_i2 =
    ((Finset.univ.biUnion childrenC_576_i2) ∪ commonEnvelope childrenD_576_i2).erase (5, 5) := by
  exact required_eq_combination childrenC_576_i2 childrenD_576_i2 (5, 5) required_576_i2
    (by decide +kernel) child_required_sub_576_i2 common_sub_576_i2 required_origin_576_i2
theorem envelope_origin_576_i2 : ∀ x ∈ envelope_576_i2,
    x = (5, 5) ∨ ∃ j, x ∈ childrenD_576_i2 j := by decide +kernel
theorem envelope_exact_576_i2 : envelope_576_i2 =
    insert (5, 5) (Finset.univ.biUnion childrenD_576_i2) := by
  exact envelope_eq_combination childrenD_576_i2 (5, 5) envelope_576_i2
    pivot_mem_576_i2 child_envelope_sub_576_i2 envelope_origin_576_i2
def checked_576_i2 : CheckedCard where
  required := required_576_i2
  envelope := envelope_576_i2
  height := height_576_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_576_i2
def height_576_i3 : ℕ := 4
def childrenH_576_i3 : Fin 2 → ℕ := ![height_5, height_87]
theorem height_exact_576_i3 : height_576_i3 = 1 + Finset.univ.sup childrenH_576_i3 := by decide +kernel
theorem required_origin_576_i3 : ∀ x ∈ required_576_i3,
    (∃ j, x ∈ childrenC_576_i3 j) ∨ ∀ j, x ∈ childrenD_576_i3 j := by decide +kernel
theorem required_exact_576_i3 : required_576_i3 =
    ((Finset.univ.biUnion childrenC_576_i3) ∪ commonEnvelope childrenD_576_i3).erase (3, 2) := by
  exact required_eq_combination childrenC_576_i3 childrenD_576_i3 (3, 2) required_576_i3
    (by decide +kernel) child_required_sub_576_i3 common_sub_576_i3 required_origin_576_i3
theorem envelope_origin_576_i3 : ∀ x ∈ envelope_576_i3,
    x = (3, 2) ∨ ∃ j, x ∈ childrenD_576_i3 j := by decide +kernel
theorem envelope_exact_576_i3 : envelope_576_i3 =
    insert (3, 2) (Finset.univ.biUnion childrenD_576_i3) := by
  exact envelope_eq_combination childrenD_576_i3 (3, 2) envelope_576_i3
    pivot_mem_576_i3 child_envelope_sub_576_i3 envelope_origin_576_i3
def checked_576_i3 : CheckedCard where
  required := required_576_i3
  envelope := envelope_576_i3
  height := height_576_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_576_i3
def height_576_i1 : ℕ := 5
def childrenH_576_i1 : Fin 2 → ℕ := ![height_576_i2, height_576_i3]
theorem height_exact_576_i1 : height_576_i1 = 1 + Finset.univ.sup childrenH_576_i1 := by decide +kernel
theorem required_origin_576_i1 : ∀ x ∈ required_576_i1,
    (∃ j, x ∈ childrenC_576_i1 j) ∨ ∀ j, x ∈ childrenD_576_i1 j := by decide +kernel
theorem required_exact_576_i1 : required_576_i1 =
    ((Finset.univ.biUnion childrenC_576_i1) ∪ commonEnvelope childrenD_576_i1).erase (4, 5) := by
  exact required_eq_combination childrenC_576_i1 childrenD_576_i1 (4, 5) required_576_i1
    (by decide +kernel) child_required_sub_576_i1 common_sub_576_i1 required_origin_576_i1
theorem envelope_origin_576_i1 : ∀ x ∈ envelope_576_i1,
    x = (4, 5) ∨ ∃ j, x ∈ childrenD_576_i1 j := by decide +kernel
theorem envelope_exact_576_i1 : envelope_576_i1 =
    insert (4, 5) (Finset.univ.biUnion childrenD_576_i1) := by
  exact envelope_eq_combination childrenD_576_i1 (4, 5) envelope_576_i1
    pivot_mem_576_i1 child_envelope_sub_576_i1 envelope_origin_576_i1
def checked_576_i1 : CheckedCard where
  required := required_576_i1
  envelope := envelope_576_i1
  height := height_576_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_576_i1
def height_576_i4 : ℕ := 4
def childrenH_576_i4 : Fin 2 → ℕ := ![height_87, height_215]
theorem height_exact_576_i4 : height_576_i4 = 1 + Finset.univ.sup childrenH_576_i4 := by decide +kernel
theorem required_origin_576_i4 : ∀ x ∈ required_576_i4,
    (∃ j, x ∈ childrenC_576_i4 j) ∨ ∀ j, x ∈ childrenD_576_i4 j := by decide +kernel
theorem required_exact_576_i4 : required_576_i4 =
    ((Finset.univ.biUnion childrenC_576_i4) ∪ commonEnvelope childrenD_576_i4).erase (3, 2) := by
  exact required_eq_combination childrenC_576_i4 childrenD_576_i4 (3, 2) required_576_i4
    (by decide +kernel) child_required_sub_576_i4 common_sub_576_i4 required_origin_576_i4
theorem envelope_origin_576_i4 : ∀ x ∈ envelope_576_i4,
    x = (3, 2) ∨ ∃ j, x ∈ childrenD_576_i4 j := by decide +kernel
theorem envelope_exact_576_i4 : envelope_576_i4 =
    insert (3, 2) (Finset.univ.biUnion childrenD_576_i4) := by
  exact envelope_eq_combination childrenD_576_i4 (3, 2) envelope_576_i4
    pivot_mem_576_i4 child_envelope_sub_576_i4 envelope_origin_576_i4
def checked_576_i4 : CheckedCard where
  required := required_576_i4
  envelope := envelope_576_i4
  height := height_576_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_576_i4
def height_576_i0 : ℕ := 6
def childrenH_576_i0 : Fin 4 → ℕ := ![height_52, height_246, height_576_i1, height_576_i4]
theorem height_exact_576_i0 : height_576_i0 = 1 + Finset.univ.sup childrenH_576_i0 := by decide +kernel
theorem required_origin_576_i0 : ∀ x ∈ required_576_i0,
    (∃ j, x ∈ childrenC_576_i0 j) ∨ ∀ j, x ∈ childrenD_576_i0 j := by decide +kernel
theorem required_exact_576_i0 : required_576_i0 =
    ((Finset.univ.biUnion childrenC_576_i0) ∪ commonEnvelope childrenD_576_i0).erase (4, 2) := by
  exact required_eq_combination childrenC_576_i0 childrenD_576_i0 (4, 2) required_576_i0
    (by decide +kernel) child_required_sub_576_i0 common_sub_576_i0 required_origin_576_i0
theorem envelope_origin_576_i0 : ∀ x ∈ envelope_576_i0,
    x = (4, 2) ∨ ∃ j, x ∈ childrenD_576_i0 j := by decide +kernel
theorem envelope_exact_576_i0 : envelope_576_i0 =
    insert (4, 2) (Finset.univ.biUnion childrenD_576_i0) := by
  exact envelope_eq_combination childrenD_576_i0 (4, 2) envelope_576_i0
    pivot_mem_576_i0 child_envelope_sub_576_i0 envelope_origin_576_i0
def checked_576_i0 : CheckedCard where
  required := required_576_i0
  envelope := envelope_576_i0
  height := height_576_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_576_i0
def height_576 : ℕ := 7
def childrenH_576 : Fin 2 → ℕ := ![height_5, height_576_i0]
theorem height_exact_576 : height_576 = 1 + Finset.univ.sup childrenH_576 := by decide +kernel
theorem required_origin_576 : ∀ x ∈ required_576,
    (∃ j, x ∈ childrenC_576 j) ∨ ∀ j, x ∈ childrenD_576 j := by decide +kernel
theorem required_exact_576 : required_576 =
    ((Finset.univ.biUnion childrenC_576) ∪ commonEnvelope childrenD_576).erase (4, 3) := by
  exact required_eq_combination childrenC_576 childrenD_576 (4, 3) required_576
    (by decide +kernel) child_required_sub_576 common_sub_576 required_origin_576
theorem envelope_origin_576 : ∀ x ∈ envelope_576,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_576 j := by decide +kernel
theorem envelope_exact_576 : envelope_576 =
    insert (4, 3) (Finset.univ.biUnion childrenD_576) := by
  exact envelope_eq_combination childrenD_576 (4, 3) envelope_576
    pivot_mem_576 child_envelope_sub_576 envelope_origin_576
def checked_576 : CheckedCard where
  required := required_576
  envelope := envelope_576
  height := height_576
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_576
end SnakyPrototype.Certificate21

end OAI
