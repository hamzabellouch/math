import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part06
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part03
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_529_i4 : Finset Cell := ⟨(([(2, 5), (4, 6), (5, 6), (6, 6), (7, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_529_i4 : Finset Cell := ⟨(([(2, 5), (3, 5), (3, 6), (4, 6), (5, 6), (6, 5), (6, 6), (7, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_529_i4 : Fin 2 → Finset Cell := ![(placed21 6 (6, 6) required_4), (placed21 4 (3, 6) required_4)]
def childrenD_529_i4 : Fin 2 → Finset Cell := ![(placed21 6 (6, 6) envelope_4), (placed21 4 (3, 6) envelope_4)]
theorem common_sub_529_i4 : commonEnvelope childrenD_529_i4 ⊆ insert (3, 6) required_529_i4 := by decide +kernel
theorem child_required_sub_529_i4 : ∀ j, childrenC_529_i4 j ⊆ insert (3, 6) required_529_i4 := by decide +kernel
theorem child_envelope_sub_529_i4 : ∀ j, childrenD_529_i4 j ⊆ envelope_529_i4 := by decide +kernel
theorem pivot_mem_529_i4 : (3, 6) ∈ envelope_529_i4 := by decide +kernel
theorem children_work_529_i4 : ∀ j, Template HasSnaky 1 (childrenC_529_i4 j) (childrenD_529_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_4 6 (6, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_4 4 (3, 6)).mono (by decide +kernel)
theorem row_works_529_i4 : Template HasSnaky 2 required_529_i4 envelope_529_i4 := by
  refine compose HasSnaky 1 childrenC_529_i4 childrenD_529_i4 children_work_529_i4 (3, 6)
    required_529_i4 envelope_529_i4 pivot_mem_529_i4 child_required_sub_529_i4 child_envelope_sub_529_i4 ?_
  intro b hb
  exact common_sub_529_i4 (mem_commonEnvelope childrenD_529_i4 b hb)
def required_529_i5 : Finset Cell := ⟨(([(4, 4), (4, 6), (5, 3), (5, 4), (5, 5), (5, 6), (6, 6), (7, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_529_i5 : Finset Cell := ⟨(([(4, 4), (4, 6), (5, 3), (5, 4), (5, 5), (5, 6), (6, 2), (6, 3), (6, 6), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (8, 3), (8, 5), (8, 6), (8, 7), (9, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_529_i5 : Fin 2 → Finset Cell := ![(placed21 3 (4, 6) required_38), (placed21 4 (4, 7) required_351)]
def childrenD_529_i5 : Fin 2 → Finset Cell := ![(placed21 3 (4, 6) envelope_38), (placed21 4 (4, 7) envelope_351)]
theorem common_sub_529_i5 : commonEnvelope childrenD_529_i5 ⊆ insert (7, 3) required_529_i5 := by decide +kernel
theorem child_required_sub_529_i5 : ∀ j, childrenC_529_i5 j ⊆ insert (7, 3) required_529_i5 := by decide +kernel
theorem child_envelope_sub_529_i5 : ∀ j, childrenD_529_i5 j ⊆ envelope_529_i5 := by decide +kernel
theorem pivot_mem_529_i5 : (7, 3) ∈ envelope_529_i5 := by decide +kernel
theorem children_work_529_i5 : ∀ j, Template HasSnaky 4 (childrenC_529_i5 j) (childrenD_529_i5 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_38 3 (4, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_351 4 (4, 7)).mono (by decide +kernel)
theorem row_works_529_i5 : Template HasSnaky 5 required_529_i5 envelope_529_i5 := by
  refine compose HasSnaky 4 childrenC_529_i5 childrenD_529_i5 children_work_529_i5 (7, 3)
    required_529_i5 envelope_529_i5 pivot_mem_529_i5 child_required_sub_529_i5 child_envelope_sub_529_i5 ?_
  intro b hb
  exact common_sub_529_i5 (mem_commonEnvelope childrenD_529_i5 b hb)
def required_529_i3 : Finset Cell := ⟨(([(2, 5), (4, 4), (4, 6), (5, 3), (5, 4), (5, 5), (5, 6), (6, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_529_i3 : Finset Cell := ⟨(([(2, 5), (3, 5), (3, 6), (4, 4), (4, 6), (5, 3), (5, 4), (5, 5), (5, 6), (6, 2), (6, 3), (6, 5), (6, 6), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (8, 3), (8, 5), (8, 6), (8, 7), (9, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_529_i3 : Fin 2 → Finset Cell := ![required_529_i4, required_529_i5]
def childrenD_529_i3 : Fin 2 → Finset Cell := ![envelope_529_i4, envelope_529_i5]
theorem common_sub_529_i3 : commonEnvelope childrenD_529_i3 ⊆ insert (7, 5) required_529_i3 := by decide +kernel
theorem child_required_sub_529_i3 : ∀ j, childrenC_529_i3 j ⊆ insert (7, 5) required_529_i3 := by decide +kernel
theorem child_envelope_sub_529_i3 : ∀ j, childrenD_529_i3 j ⊆ envelope_529_i3 := by decide +kernel
theorem pivot_mem_529_i3 : (7, 5) ∈ envelope_529_i3 := by decide +kernel
theorem children_work_529_i3 : ∀ j, Template HasSnaky 5 (childrenC_529_i3 j) (childrenD_529_i3 j) := by
  intro j
  fin_cases j
  · exact row_works_529_i4.mono (by decide +kernel)
  · exact row_works_529_i5.mono (by decide +kernel)
theorem row_works_529_i3 : Template HasSnaky 6 required_529_i3 envelope_529_i3 := by
  refine compose HasSnaky 5 childrenC_529_i3 childrenD_529_i3 children_work_529_i3 (7, 5)
    required_529_i3 envelope_529_i3 pivot_mem_529_i3 child_required_sub_529_i3 child_envelope_sub_529_i3 ?_
  intro b hb
  exact common_sub_529_i3 (mem_commonEnvelope childrenD_529_i3 b hb)
def required_529_i2 : Finset Cell := ⟨(([(2, 5), (4, 4), (5, 3), (5, 4), (5, 5), (5, 6), (6, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_529_i2 : Finset Cell := ⟨(([(2, 5), (3, 5), (3, 6), (4, 4), (4, 6), (4, 7), (5, 3), (5, 4), (5, 5), (5, 6), (6, 2), (6, 3), (6, 5), (6, 6), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (8, 3), (8, 5), (8, 6), (8, 7), (9, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_529_i2 : Fin 2 → Finset Cell := ![(placed21 5 (5, 3) required_5), required_529_i3]
def childrenD_529_i2 : Fin 2 → Finset Cell := ![(placed21 5 (5, 3) envelope_5), envelope_529_i3]
theorem common_sub_529_i2 : commonEnvelope childrenD_529_i2 ⊆ insert (4, 6) required_529_i2 := by decide +kernel
theorem child_required_sub_529_i2 : ∀ j, childrenC_529_i2 j ⊆ insert (4, 6) required_529_i2 := by decide +kernel
theorem child_envelope_sub_529_i2 : ∀ j, childrenD_529_i2 j ⊆ envelope_529_i2 := by decide +kernel
theorem pivot_mem_529_i2 : (4, 6) ∈ envelope_529_i2 := by decide +kernel
theorem children_work_529_i2 : ∀ j, Template HasSnaky 6 (childrenC_529_i2 j) (childrenD_529_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 5 (5, 3)).mono (by decide +kernel)
  · exact row_works_529_i3.mono (by decide +kernel)
theorem row_works_529_i2 : Template HasSnaky 7 required_529_i2 envelope_529_i2 := by
  refine compose HasSnaky 6 childrenC_529_i2 childrenD_529_i2 children_work_529_i2 (4, 6)
    required_529_i2 envelope_529_i2 pivot_mem_529_i2 child_required_sub_529_i2 child_envelope_sub_529_i2 ?_
  intro b hb
  exact common_sub_529_i2 (mem_commonEnvelope childrenD_529_i2 b hb)
def required_529_i1 : Finset Cell := ⟨(([(2, 5), (4, 4), (5, 3), (5, 4), (5, 5), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_529_i1 : Finset Cell := ⟨(([(2, 5), (3, 5), (3, 6), (4, 4), (4, 6), (4, 7), (5, 3), (5, 4), (5, 5), (5, 6), (6, 2), (6, 3), (6, 5), (6, 6), (6, 7), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (8, 3), (8, 5), (8, 6), (8, 7), (9, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_529_i1 : Fin 2 → Finset Cell := ![(placed21 1 (5, 3) required_5), required_529_i2]
def childrenD_529_i1 : Fin 2 → Finset Cell := ![(placed21 1 (5, 3) envelope_5), envelope_529_i2]
theorem common_sub_529_i1 : commonEnvelope childrenD_529_i1 ⊆ insert (6, 6) required_529_i1 := by decide +kernel
theorem child_required_sub_529_i1 : ∀ j, childrenC_529_i1 j ⊆ insert (6, 6) required_529_i1 := by decide +kernel
theorem child_envelope_sub_529_i1 : ∀ j, childrenD_529_i1 j ⊆ envelope_529_i1 := by decide +kernel
theorem pivot_mem_529_i1 : (6, 6) ∈ envelope_529_i1 := by decide +kernel
theorem children_work_529_i1 : ∀ j, Template HasSnaky 7 (childrenC_529_i1 j) (childrenD_529_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 1 (5, 3)).mono (by decide +kernel)
  · exact row_works_529_i2.mono (by decide +kernel)
theorem row_works_529_i1 : Template HasSnaky 8 required_529_i1 envelope_529_i1 := by
  refine compose HasSnaky 7 childrenC_529_i1 childrenD_529_i1 children_work_529_i1 (6, 6)
    required_529_i1 envelope_529_i1 pivot_mem_529_i1 child_required_sub_529_i1 child_envelope_sub_529_i1 ?_
  intro b hb
  exact common_sub_529_i1 (mem_commonEnvelope childrenD_529_i1 b hb)
def required_529_i0 : Finset Cell := ⟨(([(1, 2), (2, 2), (2, 5), (4, 4), (5, 4), (5, 5), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_529_i0 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 2), (2, 1), (2, 2), (2, 5), (3, 2), (3, 5), (3, 6), (4, 1), (4, 2), (4, 4), (4, 6), (4, 7), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (6, 0), (6, 1), (6, 2), (6, 3), (6, 5), (6, 6), (6, 7), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (8, 3), (8, 5), (8, 6), (8, 7), (9, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_529_i0 : Fin 3 → Finset Cell := ![(placed21 3 (3, 7) required_133), required_529_i1, (placed21 7 (6, 6) required_505)]
def childrenD_529_i0 : Fin 3 → Finset Cell := ![(placed21 3 (3, 7) envelope_133), envelope_529_i1, (placed21 7 (6, 6) envelope_505)]
theorem common_sub_529_i0 : commonEnvelope childrenD_529_i0 ⊆ insert (5, 3) required_529_i0 := by decide +kernel
theorem child_required_sub_529_i0 : ∀ j, childrenC_529_i0 j ⊆ insert (5, 3) required_529_i0 := by decide +kernel
theorem child_envelope_sub_529_i0 : ∀ j, childrenD_529_i0 j ⊆ envelope_529_i0 := by decide +kernel
theorem pivot_mem_529_i0 : (5, 3) ∈ envelope_529_i0 := by decide +kernel
theorem children_work_529_i0 : ∀ j, Template HasSnaky 8 (childrenC_529_i0 j) (childrenD_529_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_133 3 (3, 7)).mono (by decide +kernel)
  · exact row_works_529_i1.mono (by decide +kernel)
  · exact (placed21_template row_works_505 7 (6, 6)).mono (by decide +kernel)
theorem row_works_529_i0 : Template HasSnaky 9 required_529_i0 envelope_529_i0 := by
  refine compose HasSnaky 8 childrenC_529_i0 childrenD_529_i0 children_work_529_i0 (5, 3)
    required_529_i0 envelope_529_i0 pivot_mem_529_i0 child_required_sub_529_i0 child_envelope_sub_529_i0 ?_
  intro b hb
  exact common_sub_529_i0 (mem_commonEnvelope childrenD_529_i0 b hb)
def required_529 : Finset Cell := ⟨(([(1, 2), (2, 2), (2, 5), (4, 4), (5, 4), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_529 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 2), (2, 1), (2, 2), (2, 5), (3, 2), (3, 5), (3, 6), (4, 0), (4, 1), (4, 2), (4, 4), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (9, 3), (9, 4), (9, 5), (9, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_529 : Fin 7 → Finset Cell := ![(placed21 2 (6, 2) required_12), (placed21 1 (3, 3) required_181), (placed21 2 (6, 2) required_189), (placed21 2 (6, 1) required_369), (placed21 1 (3, 3) required_474), (placed21 0 (4, 0) required_528), required_529_i0]
def childrenD_529 : Fin 7 → Finset Cell := ![(placed21 2 (6, 2) envelope_12), (placed21 1 (3, 3) envelope_181), (placed21 2 (6, 2) envelope_189), (placed21 2 (6, 1) envelope_369), (placed21 1 (3, 3) envelope_474), (placed21 0 (4, 0) envelope_528), envelope_529_i0]
theorem common_sub_529 : commonEnvelope childrenD_529 ⊆ insert (5, 6) required_529 := by decide +kernel
theorem child_required_sub_529 : ∀ j, childrenC_529 j ⊆ insert (5, 6) required_529 := by decide +kernel
theorem child_envelope_sub_529 : ∀ j, childrenD_529 j ⊆ envelope_529 := by decide +kernel
theorem pivot_mem_529 : (5, 6) ∈ envelope_529 := by decide +kernel
theorem children_work_529 : ∀ j, Template HasSnaky 9 (childrenC_529 j) (childrenD_529 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_12 2 (6, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_181 1 (3, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_189 2 (6, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_369 2 (6, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_474 1 (3, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_528 0 (4, 0)).mono (by decide +kernel)
  · exact row_works_529_i0.mono (by decide +kernel)
theorem row_works_529 : Template HasSnaky 10 required_529 envelope_529 := by
  refine compose HasSnaky 9 childrenC_529 childrenD_529 children_work_529 (5, 6)
    required_529 envelope_529 pivot_mem_529 child_required_sub_529 child_envelope_sub_529 ?_
  intro b hb
  exact common_sub_529 (mem_commonEnvelope childrenD_529 b hb)
def required_535 : Finset Cell := ⟨(([(1, 5), (2, 4), (2, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_535 : Finset Cell := ⟨(([(0, 2), (0, 4), (1, 0), (1, 1), (1, 2), (1, 4), (1, 5), (1, 7), (1, 8), (1, 9), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (6, 3), (6, 4), (6, 5), (6, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_535 : Fin 7 → Finset Cell := ![(placed21 4 (0, 7) required_345), (placed21 3 (0, 6) required_421), (placed21 4 (0, 7) required_522), (placed21 4 (1, 8) required_530), required_532, (placed21 0 (0, 2) required_533), (placed21 4 (0, 8) required_534)]
def childrenD_535 : Fin 7 → Finset Cell := ![(placed21 4 (0, 7) envelope_345), (placed21 3 (0, 6) envelope_421), (placed21 4 (0, 7) envelope_522), (placed21 4 (1, 8) envelope_530), envelope_532, (placed21 0 (0, 2) envelope_533), (placed21 4 (0, 8) envelope_534)]
theorem common_sub_535 : commonEnvelope childrenD_535 ⊆ insert (3, 5) required_535 := by decide +kernel
theorem child_required_sub_535 : ∀ j, childrenC_535 j ⊆ insert (3, 5) required_535 := by decide +kernel
theorem child_envelope_sub_535 : ∀ j, childrenD_535 j ⊆ envelope_535 := by decide +kernel
theorem pivot_mem_535 : (3, 5) ∈ envelope_535 := by decide +kernel
theorem children_work_535 : ∀ j, Template HasSnaky 9 (childrenC_535 j) (childrenD_535 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_345 4 (0, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_421 3 (0, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_522 4 (0, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_530 4 (1, 8)).mono (by decide +kernel)
  · exact row_works_532.mono (by decide +kernel)
  · exact (placed21_template row_works_533 0 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_534 4 (0, 8)).mono (by decide +kernel)
theorem row_works_535 : Template HasSnaky 10 required_535 envelope_535 := by
  refine compose HasSnaky 9 childrenC_535 childrenD_535 children_work_535 (3, 5)
    required_535 envelope_535 pivot_mem_535 child_required_sub_535 child_envelope_sub_535 ?_
  intro b hb
  exact common_sub_535 (mem_commonEnvelope childrenD_535 b hb)
def required_540_i0 : Finset Cell := ⟨(([(0, 3), (0, 4), (1, 6), (1, 7), (3, 3), (3, 4), (3, 5), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_540_i0 : Finset Cell := ⟨(([(0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 2), (2, 3), (3, 3), (3, 4), (3, 5), (3, 6), (4, 3), (5, 2), (5, 3), (5, 4), (6, 2), (6, 3), (6, 4), (7, 2), (7, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_540_i0 : Fin 2 → Finset Cell := ![(placed21 1 (1, 2) required_237), (placed21 5 (4, 3) required_281)]
def childrenD_540_i0 : Fin 2 → Finset Cell := ![(placed21 1 (1, 2) envelope_237), (placed21 5 (4, 3) envelope_281)]
theorem common_sub_540_i0 : commonEnvelope childrenD_540_i0 ⊆ insert (2, 3) required_540_i0 := by decide +kernel
theorem child_required_sub_540_i0 : ∀ j, childrenC_540_i0 j ⊆ insert (2, 3) required_540_i0 := by decide +kernel
theorem child_envelope_sub_540_i0 : ∀ j, childrenD_540_i0 j ⊆ envelope_540_i0 := by decide +kernel
theorem pivot_mem_540_i0 : (2, 3) ∈ envelope_540_i0 := by decide +kernel
theorem children_work_540_i0 : ∀ j, Template HasSnaky 5 (childrenC_540_i0 j) (childrenD_540_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_237 1 (1, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_281 5 (4, 3)).mono (by decide +kernel)
theorem row_works_540_i0 : Template HasSnaky 6 required_540_i0 envelope_540_i0 := by
  refine compose HasSnaky 5 childrenC_540_i0 childrenD_540_i0 children_work_540_i0 (2, 3)
    required_540_i0 envelope_540_i0 pivot_mem_540_i0 child_required_sub_540_i0 child_envelope_sub_540_i0 ?_
  intro b hb
  exact common_sub_540_i0 (mem_commonEnvelope childrenD_540_i0 b hb)
def required_540_i3 : Finset Cell := ⟨(([(0, 3), (3, 3), (3, 4), (3, 5), (4, 3), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_540_i3 : Finset Cell := ⟨(([(0, 3), (1, 3), (2, 3), (3, 3), (3, 4), (3, 5), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 2), (6, 3), (6, 4), (7, 2), (7, 3), (7, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_540_i3 : Fin 3 → Finset Cell := ![(placed21 3 (1, 5) required_164), (placed21 4 (3, 7) required_199), (placed21 0 (0, 1) required_283)]
def childrenD_540_i3 : Fin 3 → Finset Cell := ![(placed21 3 (1, 5) envelope_164), (placed21 4 (3, 7) envelope_199), (placed21 0 (0, 1) envelope_283)]
theorem common_sub_540_i3 : commonEnvelope childrenD_540_i3 ⊆ insert (4, 4) required_540_i3 := by decide +kernel
theorem child_required_sub_540_i3 : ∀ j, childrenC_540_i3 j ⊆ insert (4, 4) required_540_i3 := by decide +kernel
theorem child_envelope_sub_540_i3 : ∀ j, childrenD_540_i3 j ⊆ envelope_540_i3 := by decide +kernel
theorem pivot_mem_540_i3 : (4, 4) ∈ envelope_540_i3 := by decide +kernel
theorem children_work_540_i3 : ∀ j, Template HasSnaky 6 (childrenC_540_i3 j) (childrenD_540_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_164 3 (1, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_199 4 (3, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_283 0 (0, 1)).mono (by decide +kernel)
theorem row_works_540_i3 : Template HasSnaky 7 required_540_i3 envelope_540_i3 := by
  refine compose HasSnaky 6 childrenC_540_i3 childrenD_540_i3 children_work_540_i3 (4, 4)
    required_540_i3 envelope_540_i3 pivot_mem_540_i3 child_required_sub_540_i3 child_envelope_sub_540_i3 ?_
  intro b hb
  exact common_sub_540_i3 (mem_commonEnvelope childrenD_540_i3 b hb)
def required_540_i2 : Finset Cell := ⟨(([(0, 3), (0, 4), (0, 6), (1, 6), (1, 7), (3, 3), (3, 4), (3, 5), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_540_i2 : Finset Cell := ⟨(([(0, 3), (0, 4), (0, 6), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 3), (2, 5), (3, 3), (3, 4), (3, 5), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 2), (6, 3), (6, 4), (7, 2), (7, 3), (7, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_540_i2 : Fin 2 → Finset Cell := ![(placed21 0 (0, 3) required_170), required_540_i3]
def childrenD_540_i2 : Fin 2 → Finset Cell := ![(placed21 0 (0, 3) envelope_170), envelope_540_i3]
theorem common_sub_540_i2 : commonEnvelope childrenD_540_i2 ⊆ insert (4, 5) required_540_i2 := by decide +kernel
theorem child_required_sub_540_i2 : ∀ j, childrenC_540_i2 j ⊆ insert (4, 5) required_540_i2 := by decide +kernel
theorem child_envelope_sub_540_i2 : ∀ j, childrenD_540_i2 j ⊆ envelope_540_i2 := by decide +kernel
theorem pivot_mem_540_i2 : (4, 5) ∈ envelope_540_i2 := by decide +kernel
theorem children_work_540_i2 : ∀ j, Template HasSnaky 7 (childrenC_540_i2 j) (childrenD_540_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_170 0 (0, 3)).mono (by decide +kernel)
  · exact row_works_540_i3.mono (by decide +kernel)
theorem row_works_540_i2 : Template HasSnaky 8 required_540_i2 envelope_540_i2 := by
  refine compose HasSnaky 7 childrenC_540_i2 childrenD_540_i2 children_work_540_i2 (4, 5)
    required_540_i2 envelope_540_i2 pivot_mem_540_i2 child_required_sub_540_i2 child_envelope_sub_540_i2 ?_
  intro b hb
  exact common_sub_540_i2 (mem_commonEnvelope childrenD_540_i2 b hb)
def required_540_i1 : Finset Cell := ⟨(([(0, 3), (0, 4), (1, 6), (1, 7), (1, 8), (1, 9), (3, 3), (3, 4), (3, 5), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_540_i1 : Finset Cell := ⟨(([(0, 3), (0, 4), (0, 6), (0, 7), (0, 9), (0, 10), (0, 11), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (2, 3), (2, 5), (3, 3), (3, 4), (3, 5), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 2), (6, 3), (6, 4), (7, 2), (7, 3), (7, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_540_i1 : Fin 2 → Finset Cell := ![(placed21 2 (1, 6) required_16), required_540_i2]
def childrenD_540_i1 : Fin 2 → Finset Cell := ![(placed21 2 (1, 6) envelope_16), envelope_540_i2]
theorem common_sub_540_i1 : commonEnvelope childrenD_540_i1 ⊆ insert (0, 6) required_540_i1 := by decide +kernel
theorem child_required_sub_540_i1 : ∀ j, childrenC_540_i1 j ⊆ insert (0, 6) required_540_i1 := by decide +kernel
theorem child_envelope_sub_540_i1 : ∀ j, childrenD_540_i1 j ⊆ envelope_540_i1 := by decide +kernel
theorem pivot_mem_540_i1 : (0, 6) ∈ envelope_540_i1 := by decide +kernel
theorem children_work_540_i1 : ∀ j, Template HasSnaky 8 (childrenC_540_i1 j) (childrenD_540_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_16 2 (1, 6)).mono (by decide +kernel)
  · exact row_works_540_i2.mono (by decide +kernel)
theorem row_works_540_i1 : Template HasSnaky 9 required_540_i1 envelope_540_i1 := by
  refine compose HasSnaky 8 childrenC_540_i1 childrenD_540_i1 children_work_540_i1 (0, 6)
    required_540_i1 envelope_540_i1 pivot_mem_540_i1 child_required_sub_540_i1 child_envelope_sub_540_i1 ?_
  intro b hb
  exact common_sub_540_i1 (mem_commonEnvelope childrenD_540_i1 b hb)
def required_540 : Finset Cell := ⟨(([(0, 3), (0, 4), (1, 6), (1, 7), (1, 8), (1, 9), (3, 3), (3, 4), (3, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_540 : Finset Cell := ⟨(([(0, 3), (0, 4), (0, 6), (0, 7), (0, 9), (0, 10), (0, 11), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (2, 2), (2, 3), (2, 5), (3, 3), (3, 4), (3, 5), (3, 6), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 2), (6, 3), (6, 4), (7, 2), (7, 3), (7, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_540 : Fin 3 → Finset Cell := ![(placed21 4 (3, 6) required_44), required_540_i0, required_540_i1]
def childrenD_540 : Fin 3 → Finset Cell := ![(placed21 4 (3, 6) envelope_44), envelope_540_i0, envelope_540_i1]
theorem common_sub_540 : commonEnvelope childrenD_540 ⊆ insert (4, 3) required_540 := by decide +kernel
theorem child_required_sub_540 : ∀ j, childrenC_540 j ⊆ insert (4, 3) required_540 := by decide +kernel
theorem child_envelope_sub_540 : ∀ j, childrenD_540 j ⊆ envelope_540 := by decide +kernel
theorem pivot_mem_540 : (4, 3) ∈ envelope_540 := by decide +kernel
theorem children_work_540 : ∀ j, Template HasSnaky 9 (childrenC_540 j) (childrenD_540 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_44 4 (3, 6)).mono (by decide +kernel)
  · exact row_works_540_i0.mono (by decide +kernel)
  · exact row_works_540_i1.mono (by decide +kernel)
theorem row_works_540 : Template HasSnaky 10 required_540 envelope_540 := by
  refine compose HasSnaky 9 childrenC_540 childrenD_540 children_work_540 (4, 3)
    required_540 envelope_540 pivot_mem_540 child_required_sub_540 child_envelope_sub_540 ?_
  intro b hb
  exact common_sub_540 (mem_commonEnvelope childrenD_540 b hb)
def required_541_i6 : Finset Cell := ⟨(([(0, 1), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_541_i6 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 0), (2, 1), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 2), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_541_i6 : Fin 2 → Finset Cell := ![(placed21 3 (3, 6) required_0), (placed21 7 (4, 4) required_35)]
def childrenD_541_i6 : Fin 2 → Finset Cell := ![(placed21 3 (3, 6) envelope_0), (placed21 7 (4, 4) envelope_35)]
theorem common_sub_541_i6 : commonEnvelope childrenD_541_i6 ⊆ insert (4, 2) required_541_i6 := by decide +kernel
theorem child_required_sub_541_i6 : ∀ j, childrenC_541_i6 j ⊆ insert (4, 2) required_541_i6 := by decide +kernel
theorem child_envelope_sub_541_i6 : ∀ j, childrenD_541_i6 j ⊆ envelope_541_i6 := by decide +kernel
theorem pivot_mem_541_i6 : (4, 2) ∈ envelope_541_i6 := by decide +kernel
theorem children_work_541_i6 : ∀ j, Template HasSnaky 2 (childrenC_541_i6 j) (childrenD_541_i6 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 3 (3, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_35 7 (4, 4)).mono (by decide +kernel)
theorem row_works_541_i6 : Template HasSnaky 3 required_541_i6 envelope_541_i6 := by
  refine compose HasSnaky 2 childrenC_541_i6 childrenD_541_i6 children_work_541_i6 (4, 2)
    required_541_i6 envelope_541_i6 pivot_mem_541_i6 child_required_sub_541_i6 child_envelope_sub_541_i6 ?_
  intro b hb
  exact common_sub_541_i6 (mem_commonEnvelope childrenD_541_i6 b hb)
def required_541_i5 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 4), (1, 4), (1, 5), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_541_i5 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 4), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 3), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 2), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_541_i5 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) required_170), required_541_i6]
def childrenD_541_i5 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) envelope_170), envelope_541_i6]
theorem common_sub_541_i5 : commonEnvelope childrenD_541_i5 ⊆ insert (4, 3) required_541_i5 := by decide +kernel
theorem child_required_sub_541_i5 : ∀ j, childrenC_541_i5 j ⊆ insert (4, 3) required_541_i5 := by decide +kernel
theorem child_envelope_sub_541_i5 : ∀ j, childrenD_541_i5 j ⊆ envelope_541_i5 := by decide +kernel
theorem pivot_mem_541_i5 : (4, 3) ∈ envelope_541_i5 := by decide +kernel
theorem children_work_541_i5 : ∀ j, Template HasSnaky 3 (childrenC_541_i5 j) (childrenD_541_i5 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_170 0 (0, 1)).mono (by decide +kernel)
  · exact row_works_541_i6.mono (by decide +kernel)
theorem row_works_541_i5 : Template HasSnaky 4 required_541_i5 envelope_541_i5 := by
  refine compose HasSnaky 3 childrenC_541_i5 childrenD_541_i5 children_work_541_i5 (4, 3)
    required_541_i5 envelope_541_i5 pivot_mem_541_i5 child_required_sub_541_i5 child_envelope_sub_541_i5 ?_
  intro b hb
  exact common_sub_541_i5 (mem_commonEnvelope childrenD_541_i5 b hb)
def required_541_i4 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 4), (1, 4), (1, 5), (3, 1), (3, 2), (3, 3), (3, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_541_i4 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 4), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 3), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 0), (4, 1), (4, 2), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_541_i4 : Fin 3 → Finset Cell := ![(placed21 4 (3, 5) required_6), required_86, required_541_i5]
def childrenD_541_i4 : Fin 3 → Finset Cell := ![(placed21 4 (3, 5) envelope_6), envelope_86, envelope_541_i5]
theorem common_sub_541_i4 : commonEnvelope childrenD_541_i4 ⊆ insert (3, 4) required_541_i4 := by decide +kernel
theorem child_required_sub_541_i4 : ∀ j, childrenC_541_i4 j ⊆ insert (3, 4) required_541_i4 := by decide +kernel
theorem child_envelope_sub_541_i4 : ∀ j, childrenD_541_i4 j ⊆ envelope_541_i4 := by decide +kernel
theorem pivot_mem_541_i4 : (3, 4) ∈ envelope_541_i4 := by decide +kernel
theorem children_work_541_i4 : ∀ j, Template HasSnaky 4 (childrenC_541_i4 j) (childrenD_541_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_6 4 (3, 5)).mono (by decide +kernel)
  · exact row_works_86.mono (by decide +kernel)
  · exact row_works_541_i5.mono (by decide +kernel)
theorem row_works_541_i4 : Template HasSnaky 5 required_541_i4 envelope_541_i4 := by
  refine compose HasSnaky 4 childrenC_541_i4 childrenD_541_i4 children_work_541_i4 (3, 4)
    required_541_i4 envelope_541_i4 pivot_mem_541_i4 child_required_sub_541_i4 child_envelope_sub_541_i4 ?_
  intro b hb
  exact common_sub_541_i4 (mem_commonEnvelope childrenD_541_i4 b hb)
def required_541_i3 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 4), (1, 4), (1, 5), (2, 5), (3, 1), (3, 2), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_541_i3 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 4), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 3), (2, 5), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 0), (4, 1), (4, 2), (4, 3), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_541_i3 : Fin 2 → Finset Cell := ![(placed21 6 (4, 5) required_0), required_541_i4]
def childrenD_541_i3 : Fin 2 → Finset Cell := ![(placed21 6 (4, 5) envelope_0), envelope_541_i4]
theorem common_sub_541_i3 : commonEnvelope childrenD_541_i3 ⊆ insert (3, 5) required_541_i3 := by decide +kernel
theorem child_required_sub_541_i3 : ∀ j, childrenC_541_i3 j ⊆ insert (3, 5) required_541_i3 := by decide +kernel
theorem child_envelope_sub_541_i3 : ∀ j, childrenD_541_i3 j ⊆ envelope_541_i3 := by decide +kernel
theorem pivot_mem_541_i3 : (3, 5) ∈ envelope_541_i3 := by decide +kernel
theorem children_work_541_i3 : ∀ j, Template HasSnaky 5 (childrenC_541_i3 j) (childrenD_541_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 6 (4, 5)).mono (by decide +kernel)
  · exact row_works_541_i4.mono (by decide +kernel)
theorem row_works_541_i3 : Template HasSnaky 6 required_541_i3 envelope_541_i3 := by
  refine compose HasSnaky 5 childrenC_541_i3 childrenD_541_i3 children_work_541_i3 (3, 5)
    required_541_i3 envelope_541_i3 pivot_mem_541_i3 child_required_sub_541_i3 child_envelope_sub_541_i3 ?_
  intro b hb
  exact common_sub_541_i3 (mem_commonEnvelope childrenD_541_i3 b hb)
def required_541_i2 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 4), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (3, 1), (3, 2), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_541_i2 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 4), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, 0), (2, 1), (2, 3), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 0), (4, 1), (4, 2), (4, 3), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_541_i2 : Fin 2 → Finset Cell := ![(placed21 3 (1, 9) required_4), required_541_i3]
def childrenD_541_i2 : Fin 2 → Finset Cell := ![(placed21 3 (1, 9) envelope_4), envelope_541_i3]
theorem common_sub_541_i2 : commonEnvelope childrenD_541_i2 ⊆ insert (2, 5) required_541_i2 := by decide +kernel
theorem child_required_sub_541_i2 : ∀ j, childrenC_541_i2 j ⊆ insert (2, 5) required_541_i2 := by decide +kernel
theorem child_envelope_sub_541_i2 : ∀ j, childrenD_541_i2 j ⊆ envelope_541_i2 := by decide +kernel
theorem pivot_mem_541_i2 : (2, 5) ∈ envelope_541_i2 := by decide +kernel
theorem children_work_541_i2 : ∀ j, Template HasSnaky 6 (childrenC_541_i2 j) (childrenD_541_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_4 3 (1, 9)).mono (by decide +kernel)
  · exact row_works_541_i3.mono (by decide +kernel)
theorem row_works_541_i2 : Template HasSnaky 7 required_541_i2 envelope_541_i2 := by
  refine compose HasSnaky 6 childrenC_541_i2 childrenD_541_i2 children_work_541_i2 (2, 5)
    required_541_i2 envelope_541_i2 pivot_mem_541_i2 child_required_sub_541_i2 child_envelope_sub_541_i2 ?_
  intro b hb
  exact common_sub_541_i2 (mem_commonEnvelope childrenD_541_i2 b hb)
def required_541_i1 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (3, 1), (3, 2), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_541_i1 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 4), (0, 5), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, 0), (2, 1), (2, 3), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 0), (4, 1), (4, 2), (4, 3), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_541_i1 : Fin 2 → Finset Cell := ![(placed21 7 (1, 8) required_4), required_541_i2]
def childrenD_541_i1 : Fin 2 → Finset Cell := ![(placed21 7 (1, 8) envelope_4), envelope_541_i2]
theorem common_sub_541_i1 : commonEnvelope childrenD_541_i1 ⊆ insert (0, 4) required_541_i1 := by decide +kernel
theorem child_required_sub_541_i1 : ∀ j, childrenC_541_i1 j ⊆ insert (0, 4) required_541_i1 := by decide +kernel
theorem child_envelope_sub_541_i1 : ∀ j, childrenD_541_i1 j ⊆ envelope_541_i1 := by decide +kernel
theorem pivot_mem_541_i1 : (0, 4) ∈ envelope_541_i1 := by decide +kernel
theorem children_work_541_i1 : ∀ j, Template HasSnaky 7 (childrenC_541_i1 j) (childrenD_541_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_4 7 (1, 8)).mono (by decide +kernel)
  · exact row_works_541_i2.mono (by decide +kernel)
theorem row_works_541_i1 : Template HasSnaky 8 required_541_i1 envelope_541_i1 := by
  refine compose HasSnaky 7 childrenC_541_i1 childrenD_541_i1 children_work_541_i1 (0, 4)
    required_541_i1 envelope_541_i1 pivot_mem_541_i1 child_required_sub_541_i1 child_envelope_sub_541_i1 ?_
  intro b hb
  exact common_sub_541_i1 (mem_commonEnvelope childrenD_541_i1 b hb)
def required_541_i0 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (3, 1), (3, 2), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_541_i0 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 4), (0, 5), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, 0), (2, 1), (2, 3), (2, 5), (2, 6), (2, 8), (2, 9), (2, 10), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 0), (4, 1), (4, 2), (4, 3), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_541_i0 : Fin 2 → Finset Cell := ![(placed21 0 (1, 5) required_6), required_541_i1]
def childrenD_541_i0 : Fin 2 → Finset Cell := ![(placed21 0 (1, 5) envelope_6), envelope_541_i1]
theorem common_sub_541_i0 : commonEnvelope childrenD_541_i0 ⊆ insert (1, 9) required_541_i0 := by decide +kernel
theorem child_required_sub_541_i0 : ∀ j, childrenC_541_i0 j ⊆ insert (1, 9) required_541_i0 := by decide +kernel
theorem child_envelope_sub_541_i0 : ∀ j, childrenD_541_i0 j ⊆ envelope_541_i0 := by decide +kernel
theorem pivot_mem_541_i0 : (1, 9) ∈ envelope_541_i0 := by decide +kernel
theorem children_work_541_i0 : ∀ j, Template HasSnaky 8 (childrenC_541_i0 j) (childrenD_541_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_6 0 (1, 5)).mono (by decide +kernel)
  · exact row_works_541_i1.mono (by decide +kernel)
theorem row_works_541_i0 : Template HasSnaky 9 required_541_i0 envelope_541_i0 := by
  refine compose HasSnaky 8 childrenC_541_i0 childrenD_541_i0 children_work_541_i0 (1, 9)
    required_541_i0 envelope_541_i0 pivot_mem_541_i0 child_required_sub_541_i0 child_envelope_sub_541_i0 ?_
  intro b hb
  exact common_sub_541_i0 (mem_commonEnvelope childrenD_541_i0 b hb)
def required_541 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 4), (1, 5), (1, 6), (1, 7), (3, 1), (3, 2), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_541 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 4), (0, 5), (0, 7), (0, 8), (0, 9), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, 0), (2, 1), (2, 3), (2, 5), (2, 6), (2, 8), (2, 9), (2, 10), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 0), (4, 1), (4, 2), (4, 3), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_541 : Fin 2 → Finset Cell := ![(placed21 2 (1, 4) required_6), required_541_i0]
def childrenD_541 : Fin 2 → Finset Cell := ![(placed21 2 (1, 4) envelope_6), envelope_541_i0]
theorem common_sub_541 : commonEnvelope childrenD_541 ⊆ insert (1, 8) required_541 := by decide +kernel
theorem child_required_sub_541 : ∀ j, childrenC_541 j ⊆ insert (1, 8) required_541 := by decide +kernel
theorem child_envelope_sub_541 : ∀ j, childrenD_541 j ⊆ envelope_541 := by decide +kernel
theorem pivot_mem_541 : (1, 8) ∈ envelope_541 := by decide +kernel
theorem children_work_541 : ∀ j, Template HasSnaky 9 (childrenC_541 j) (childrenD_541 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_6 2 (1, 4)).mono (by decide +kernel)
  · exact row_works_541_i0.mono (by decide +kernel)
theorem row_works_541 : Template HasSnaky 10 required_541 envelope_541 := by
  refine compose HasSnaky 9 childrenC_541 childrenD_541 children_work_541 (1, 8)
    required_541 envelope_541 pivot_mem_541 child_required_sub_541 child_envelope_sub_541 ?_
  intro b hb
  exact common_sub_541 (mem_commonEnvelope childrenD_541 b hb)
def required_545_i0 : Finset Cell := ⟨(([(1, 3), (1, 4), (1, 5), (2, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_545_i0 : Finset Cell := ⟨(([(0, 2), (0, 3), (0, 7), (0, 8), (0, 9), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (3, 2), (3, 3), (3, 4), (4, 2), (4, 3), (4, 4), (5, 2), (5, 3), (5, 4), (6, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_545_i0 : Fin 4 → Finset Cell := ![(placed21 2 (2, 2) required_19), (placed21 2 (2, 2) required_84), (placed21 5 (2, 3) required_314), (placed21 4 (0, 7) required_419)]
def childrenD_545_i0 : Fin 4 → Finset Cell := ![(placed21 2 (2, 2) envelope_19), (placed21 2 (2, 2) envelope_84), (placed21 5 (2, 3) envelope_314), (placed21 4 (0, 7) envelope_419)]
theorem common_sub_545_i0 : commonEnvelope childrenD_545_i0 ⊆ insert (1, 6) required_545_i0 := by decide +kernel
theorem child_required_sub_545_i0 : ∀ j, childrenC_545_i0 j ⊆ insert (1, 6) required_545_i0 := by decide +kernel
theorem child_envelope_sub_545_i0 : ∀ j, childrenD_545_i0 j ⊆ envelope_545_i0 := by decide +kernel
theorem pivot_mem_545_i0 : (1, 6) ∈ envelope_545_i0 := by decide +kernel
theorem children_work_545_i0 : ∀ j, Template HasSnaky 8 (childrenC_545_i0 j) (childrenD_545_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_19 2 (2, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_84 2 (2, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_314 5 (2, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_419 4 (0, 7)).mono (by decide +kernel)
theorem row_works_545_i0 : Template HasSnaky 9 required_545_i0 envelope_545_i0 := by
  refine compose HasSnaky 8 childrenC_545_i0 childrenD_545_i0 children_work_545_i0 (1, 6)
    required_545_i0 envelope_545_i0 pivot_mem_545_i0 child_required_sub_545_i0 child_envelope_sub_545_i0 ?_
  intro b hb
  exact common_sub_545_i0 (mem_commonEnvelope childrenD_545_i0 b hb)
def required_545 : Finset Cell := ⟨(([(1, 4), (1, 5), (2, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_545 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 3), (0, 7), (0, 8), (0, 9), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (3, 2), (3, 3), (3, 4), (4, 2), (4, 3), (4, 4), (5, 2), (5, 3), (5, 4), (6, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_545 : Fin 4 → Finset Cell := ![(placed21 4 (1, 6) required_27), (placed21 0 (1, 2) required_52), (placed21 6 (2, 9) required_284), required_545_i0]
def childrenD_545 : Fin 4 → Finset Cell := ![(placed21 4 (1, 6) envelope_27), (placed21 0 (1, 2) envelope_52), (placed21 6 (2, 9) envelope_284), envelope_545_i0]
theorem common_sub_545 : commonEnvelope childrenD_545 ⊆ insert (1, 3) required_545 := by decide +kernel
theorem child_required_sub_545 : ∀ j, childrenC_545 j ⊆ insert (1, 3) required_545 := by decide +kernel
theorem child_envelope_sub_545 : ∀ j, childrenD_545 j ⊆ envelope_545 := by decide +kernel
theorem pivot_mem_545 : (1, 3) ∈ envelope_545 := by decide +kernel
theorem children_work_545 : ∀ j, Template HasSnaky 9 (childrenC_545 j) (childrenD_545 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_27 4 (1, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_52 0 (1, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_284 6 (2, 9)).mono (by decide +kernel)
  · exact row_works_545_i0.mono (by decide +kernel)
theorem row_works_545 : Template HasSnaky 10 required_545 envelope_545 := by
  refine compose HasSnaky 9 childrenC_545 childrenD_545 children_work_545 (1, 3)
    required_545 envelope_545 pivot_mem_545 child_required_sub_545 child_envelope_sub_545 ?_
  intro b hb
  exact common_sub_545 (mem_commonEnvelope childrenD_545 b hb)
def height_529_i4 : ℕ := 2
def childrenH_529_i4 : Fin 2 → ℕ := ![height_4, height_4]
theorem height_exact_529_i4 : height_529_i4 = 1 + Finset.univ.sup childrenH_529_i4 := by decide +kernel
theorem required_origin_529_i4 : ∀ x ∈ required_529_i4,
    (∃ j, x ∈ childrenC_529_i4 j) ∨ ∀ j, x ∈ childrenD_529_i4 j := by decide +kernel
theorem required_exact_529_i4 : required_529_i4 =
    ((Finset.univ.biUnion childrenC_529_i4) ∪ commonEnvelope childrenD_529_i4).erase (3, 6) := by
  exact required_eq_combination childrenC_529_i4 childrenD_529_i4 (3, 6) required_529_i4
    (by decide +kernel) child_required_sub_529_i4 common_sub_529_i4 required_origin_529_i4
theorem envelope_origin_529_i4 : ∀ x ∈ envelope_529_i4,
    x = (3, 6) ∨ ∃ j, x ∈ childrenD_529_i4 j := by decide +kernel
theorem envelope_exact_529_i4 : envelope_529_i4 =
    insert (3, 6) (Finset.univ.biUnion childrenD_529_i4) := by
  exact envelope_eq_combination childrenD_529_i4 (3, 6) envelope_529_i4
    pivot_mem_529_i4 child_envelope_sub_529_i4 envelope_origin_529_i4
def checked_529_i4 : CheckedCard where
  required := required_529_i4
  envelope := envelope_529_i4
  height := height_529_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_529_i4
def height_529_i5 : ℕ := 5
def childrenH_529_i5 : Fin 2 → ℕ := ![height_38, height_351]
theorem height_exact_529_i5 : height_529_i5 = 1 + Finset.univ.sup childrenH_529_i5 := by decide +kernel
theorem required_origin_529_i5 : ∀ x ∈ required_529_i5,
    (∃ j, x ∈ childrenC_529_i5 j) ∨ ∀ j, x ∈ childrenD_529_i5 j := by decide +kernel
theorem required_exact_529_i5 : required_529_i5 =
    ((Finset.univ.biUnion childrenC_529_i5) ∪ commonEnvelope childrenD_529_i5).erase (7, 3) := by
  exact required_eq_combination childrenC_529_i5 childrenD_529_i5 (7, 3) required_529_i5
    (by decide +kernel) child_required_sub_529_i5 common_sub_529_i5 required_origin_529_i5
theorem envelope_origin_529_i5 : ∀ x ∈ envelope_529_i5,
    x = (7, 3) ∨ ∃ j, x ∈ childrenD_529_i5 j := by decide +kernel
theorem envelope_exact_529_i5 : envelope_529_i5 =
    insert (7, 3) (Finset.univ.biUnion childrenD_529_i5) := by
  exact envelope_eq_combination childrenD_529_i5 (7, 3) envelope_529_i5
    pivot_mem_529_i5 child_envelope_sub_529_i5 envelope_origin_529_i5
def checked_529_i5 : CheckedCard where
  required := required_529_i5
  envelope := envelope_529_i5
  height := height_529_i5
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_529_i5
def height_529_i3 : ℕ := 6
def childrenH_529_i3 : Fin 2 → ℕ := ![height_529_i4, height_529_i5]
theorem height_exact_529_i3 : height_529_i3 = 1 + Finset.univ.sup childrenH_529_i3 := by decide +kernel
theorem required_origin_529_i3 : ∀ x ∈ required_529_i3,
    (∃ j, x ∈ childrenC_529_i3 j) ∨ ∀ j, x ∈ childrenD_529_i3 j := by decide +kernel
theorem required_exact_529_i3 : required_529_i3 =
    ((Finset.univ.biUnion childrenC_529_i3) ∪ commonEnvelope childrenD_529_i3).erase (7, 5) := by
  exact required_eq_combination childrenC_529_i3 childrenD_529_i3 (7, 5) required_529_i3
    (by decide +kernel) child_required_sub_529_i3 common_sub_529_i3 required_origin_529_i3
theorem envelope_origin_529_i3 : ∀ x ∈ envelope_529_i3,
    x = (7, 5) ∨ ∃ j, x ∈ childrenD_529_i3 j := by decide +kernel
theorem envelope_exact_529_i3 : envelope_529_i3 =
    insert (7, 5) (Finset.univ.biUnion childrenD_529_i3) := by
  exact envelope_eq_combination childrenD_529_i3 (7, 5) envelope_529_i3
    pivot_mem_529_i3 child_envelope_sub_529_i3 envelope_origin_529_i3
def checked_529_i3 : CheckedCard where
  required := required_529_i3
  envelope := envelope_529_i3
  height := height_529_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_529_i3
def height_529_i2 : ℕ := 7
def childrenH_529_i2 : Fin 2 → ℕ := ![height_5, height_529_i3]
theorem height_exact_529_i2 : height_529_i2 = 1 + Finset.univ.sup childrenH_529_i2 := by decide +kernel
theorem required_origin_529_i2 : ∀ x ∈ required_529_i2,
    (∃ j, x ∈ childrenC_529_i2 j) ∨ ∀ j, x ∈ childrenD_529_i2 j := by decide +kernel
theorem required_exact_529_i2 : required_529_i2 =
    ((Finset.univ.biUnion childrenC_529_i2) ∪ commonEnvelope childrenD_529_i2).erase (4, 6) := by
  exact required_eq_combination childrenC_529_i2 childrenD_529_i2 (4, 6) required_529_i2
    (by decide +kernel) child_required_sub_529_i2 common_sub_529_i2 required_origin_529_i2
theorem envelope_origin_529_i2 : ∀ x ∈ envelope_529_i2,
    x = (4, 6) ∨ ∃ j, x ∈ childrenD_529_i2 j := by decide +kernel
theorem envelope_exact_529_i2 : envelope_529_i2 =
    insert (4, 6) (Finset.univ.biUnion childrenD_529_i2) := by
  exact envelope_eq_combination childrenD_529_i2 (4, 6) envelope_529_i2
    pivot_mem_529_i2 child_envelope_sub_529_i2 envelope_origin_529_i2
def checked_529_i2 : CheckedCard where
  required := required_529_i2
  envelope := envelope_529_i2
  height := height_529_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_529_i2
def height_529_i1 : ℕ := 8
def childrenH_529_i1 : Fin 2 → ℕ := ![height_5, height_529_i2]
theorem height_exact_529_i1 : height_529_i1 = 1 + Finset.univ.sup childrenH_529_i1 := by decide +kernel
theorem required_origin_529_i1 : ∀ x ∈ required_529_i1,
    (∃ j, x ∈ childrenC_529_i1 j) ∨ ∀ j, x ∈ childrenD_529_i1 j := by decide +kernel
theorem required_exact_529_i1 : required_529_i1 =
    ((Finset.univ.biUnion childrenC_529_i1) ∪ commonEnvelope childrenD_529_i1).erase (6, 6) := by
  exact required_eq_combination childrenC_529_i1 childrenD_529_i1 (6, 6) required_529_i1
    (by decide +kernel) child_required_sub_529_i1 common_sub_529_i1 required_origin_529_i1
theorem envelope_origin_529_i1 : ∀ x ∈ envelope_529_i1,
    x = (6, 6) ∨ ∃ j, x ∈ childrenD_529_i1 j := by decide +kernel
theorem envelope_exact_529_i1 : envelope_529_i1 =
    insert (6, 6) (Finset.univ.biUnion childrenD_529_i1) := by
  exact envelope_eq_combination childrenD_529_i1 (6, 6) envelope_529_i1
    pivot_mem_529_i1 child_envelope_sub_529_i1 envelope_origin_529_i1
def checked_529_i1 : CheckedCard where
  required := required_529_i1
  envelope := envelope_529_i1
  height := height_529_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_529_i1
def height_529_i0 : ℕ := 9
def childrenH_529_i0 : Fin 3 → ℕ := ![height_133, height_529_i1, height_505]
theorem height_exact_529_i0 : height_529_i0 = 1 + Finset.univ.sup childrenH_529_i0 := by decide +kernel
theorem required_origin_529_i0 : ∀ x ∈ required_529_i0,
    (∃ j, x ∈ childrenC_529_i0 j) ∨ ∀ j, x ∈ childrenD_529_i0 j := by decide +kernel
theorem required_exact_529_i0 : required_529_i0 =
    ((Finset.univ.biUnion childrenC_529_i0) ∪ commonEnvelope childrenD_529_i0).erase (5, 3) := by
  exact required_eq_combination childrenC_529_i0 childrenD_529_i0 (5, 3) required_529_i0
    (by decide +kernel) child_required_sub_529_i0 common_sub_529_i0 required_origin_529_i0
theorem envelope_origin_529_i0 : ∀ x ∈ envelope_529_i0,
    x = (5, 3) ∨ ∃ j, x ∈ childrenD_529_i0 j := by decide +kernel
theorem envelope_exact_529_i0 : envelope_529_i0 =
    insert (5, 3) (Finset.univ.biUnion childrenD_529_i0) := by
  exact envelope_eq_combination childrenD_529_i0 (5, 3) envelope_529_i0
    pivot_mem_529_i0 child_envelope_sub_529_i0 envelope_origin_529_i0
def checked_529_i0 : CheckedCard where
  required := required_529_i0
  envelope := envelope_529_i0
  height := height_529_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_529_i0
def height_529 : ℕ := 10
def childrenH_529 : Fin 7 → ℕ := ![height_12, height_181, height_189, height_369, height_474, height_528, height_529_i0]
theorem height_exact_529 : height_529 = 1 + Finset.univ.sup childrenH_529 := by decide +kernel
theorem required_origin_529 : ∀ x ∈ required_529,
    (∃ j, x ∈ childrenC_529 j) ∨ ∀ j, x ∈ childrenD_529 j := by decide +kernel
theorem required_exact_529 : required_529 =
    ((Finset.univ.biUnion childrenC_529) ∪ commonEnvelope childrenD_529).erase (5, 6) := by
  exact required_eq_combination childrenC_529 childrenD_529 (5, 6) required_529
    (by decide +kernel) child_required_sub_529 common_sub_529 required_origin_529
theorem envelope_origin_529 : ∀ x ∈ envelope_529,
    x = (5, 6) ∨ ∃ j, x ∈ childrenD_529 j := by decide +kernel
theorem envelope_exact_529 : envelope_529 =
    insert (5, 6) (Finset.univ.biUnion childrenD_529) := by
  exact envelope_eq_combination childrenD_529 (5, 6) envelope_529
    pivot_mem_529 child_envelope_sub_529 envelope_origin_529
def checked_529 : CheckedCard where
  required := required_529
  envelope := envelope_529
  height := height_529
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_529
def height_535 : ℕ := 10
def childrenH_535 : Fin 7 → ℕ := ![height_345, height_421, height_522, height_530, height_532, height_533, height_534]
theorem height_exact_535 : height_535 = 1 + Finset.univ.sup childrenH_535 := by decide +kernel
theorem required_origin_535 : ∀ x ∈ required_535,
    (∃ j, x ∈ childrenC_535 j) ∨ ∀ j, x ∈ childrenD_535 j := by decide +kernel
theorem required_exact_535 : required_535 =
    ((Finset.univ.biUnion childrenC_535) ∪ commonEnvelope childrenD_535).erase (3, 5) := by
  exact required_eq_combination childrenC_535 childrenD_535 (3, 5) required_535
    (by decide +kernel) child_required_sub_535 common_sub_535 required_origin_535
theorem envelope_origin_535 : ∀ x ∈ envelope_535,
    x = (3, 5) ∨ ∃ j, x ∈ childrenD_535 j := by decide +kernel
theorem envelope_exact_535 : envelope_535 =
    insert (3, 5) (Finset.univ.biUnion childrenD_535) := by
  exact envelope_eq_combination childrenD_535 (3, 5) envelope_535
    pivot_mem_535 child_envelope_sub_535 envelope_origin_535
def checked_535 : CheckedCard where
  required := required_535
  envelope := envelope_535
  height := height_535
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_535
def height_540_i0 : ℕ := 6
def childrenH_540_i0 : Fin 2 → ℕ := ![height_237, height_281]
theorem height_exact_540_i0 : height_540_i0 = 1 + Finset.univ.sup childrenH_540_i0 := by decide +kernel
theorem required_origin_540_i0 : ∀ x ∈ required_540_i0,
    (∃ j, x ∈ childrenC_540_i0 j) ∨ ∀ j, x ∈ childrenD_540_i0 j := by decide +kernel
theorem required_exact_540_i0 : required_540_i0 =
    ((Finset.univ.biUnion childrenC_540_i0) ∪ commonEnvelope childrenD_540_i0).erase (2, 3) := by
  exact required_eq_combination childrenC_540_i0 childrenD_540_i0 (2, 3) required_540_i0
    (by decide +kernel) child_required_sub_540_i0 common_sub_540_i0 required_origin_540_i0
theorem envelope_origin_540_i0 : ∀ x ∈ envelope_540_i0,
    x = (2, 3) ∨ ∃ j, x ∈ childrenD_540_i0 j := by decide +kernel
theorem envelope_exact_540_i0 : envelope_540_i0 =
    insert (2, 3) (Finset.univ.biUnion childrenD_540_i0) := by
  exact envelope_eq_combination childrenD_540_i0 (2, 3) envelope_540_i0
    pivot_mem_540_i0 child_envelope_sub_540_i0 envelope_origin_540_i0
def checked_540_i0 : CheckedCard where
  required := required_540_i0
  envelope := envelope_540_i0
  height := height_540_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_540_i0
def height_540_i3 : ℕ := 7
def childrenH_540_i3 : Fin 3 → ℕ := ![height_164, height_199, height_283]
theorem height_exact_540_i3 : height_540_i3 = 1 + Finset.univ.sup childrenH_540_i3 := by decide +kernel
theorem required_origin_540_i3 : ∀ x ∈ required_540_i3,
    (∃ j, x ∈ childrenC_540_i3 j) ∨ ∀ j, x ∈ childrenD_540_i3 j := by decide +kernel
theorem required_exact_540_i3 : required_540_i3 =
    ((Finset.univ.biUnion childrenC_540_i3) ∪ commonEnvelope childrenD_540_i3).erase (4, 4) := by
  exact required_eq_combination childrenC_540_i3 childrenD_540_i3 (4, 4) required_540_i3
    (by decide +kernel) child_required_sub_540_i3 common_sub_540_i3 required_origin_540_i3
theorem envelope_origin_540_i3 : ∀ x ∈ envelope_540_i3,
    x = (4, 4) ∨ ∃ j, x ∈ childrenD_540_i3 j := by decide +kernel
theorem envelope_exact_540_i3 : envelope_540_i3 =
    insert (4, 4) (Finset.univ.biUnion childrenD_540_i3) := by
  exact envelope_eq_combination childrenD_540_i3 (4, 4) envelope_540_i3
    pivot_mem_540_i3 child_envelope_sub_540_i3 envelope_origin_540_i3
def checked_540_i3 : CheckedCard where
  required := required_540_i3
  envelope := envelope_540_i3
  height := height_540_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_540_i3
def height_540_i2 : ℕ := 8
def childrenH_540_i2 : Fin 2 → ℕ := ![height_170, height_540_i3]
theorem height_exact_540_i2 : height_540_i2 = 1 + Finset.univ.sup childrenH_540_i2 := by decide +kernel
theorem required_origin_540_i2 : ∀ x ∈ required_540_i2,
    (∃ j, x ∈ childrenC_540_i2 j) ∨ ∀ j, x ∈ childrenD_540_i2 j := by decide +kernel
theorem required_exact_540_i2 : required_540_i2 =
    ((Finset.univ.biUnion childrenC_540_i2) ∪ commonEnvelope childrenD_540_i2).erase (4, 5) := by
  exact required_eq_combination childrenC_540_i2 childrenD_540_i2 (4, 5) required_540_i2
    (by decide +kernel) child_required_sub_540_i2 common_sub_540_i2 required_origin_540_i2
theorem envelope_origin_540_i2 : ∀ x ∈ envelope_540_i2,
    x = (4, 5) ∨ ∃ j, x ∈ childrenD_540_i2 j := by decide +kernel
theorem envelope_exact_540_i2 : envelope_540_i2 =
    insert (4, 5) (Finset.univ.biUnion childrenD_540_i2) := by
  exact envelope_eq_combination childrenD_540_i2 (4, 5) envelope_540_i2
    pivot_mem_540_i2 child_envelope_sub_540_i2 envelope_origin_540_i2
def checked_540_i2 : CheckedCard where
  required := required_540_i2
  envelope := envelope_540_i2
  height := height_540_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_540_i2
def height_540_i1 : ℕ := 9
def childrenH_540_i1 : Fin 2 → ℕ := ![height_16, height_540_i2]
theorem height_exact_540_i1 : height_540_i1 = 1 + Finset.univ.sup childrenH_540_i1 := by decide +kernel
theorem required_origin_540_i1 : ∀ x ∈ required_540_i1,
    (∃ j, x ∈ childrenC_540_i1 j) ∨ ∀ j, x ∈ childrenD_540_i1 j := by decide +kernel
theorem required_exact_540_i1 : required_540_i1 =
    ((Finset.univ.biUnion childrenC_540_i1) ∪ commonEnvelope childrenD_540_i1).erase (0, 6) := by
  exact required_eq_combination childrenC_540_i1 childrenD_540_i1 (0, 6) required_540_i1
    (by decide +kernel) child_required_sub_540_i1 common_sub_540_i1 required_origin_540_i1
theorem envelope_origin_540_i1 : ∀ x ∈ envelope_540_i1,
    x = (0, 6) ∨ ∃ j, x ∈ childrenD_540_i1 j := by decide +kernel
theorem envelope_exact_540_i1 : envelope_540_i1 =
    insert (0, 6) (Finset.univ.biUnion childrenD_540_i1) := by
  exact envelope_eq_combination childrenD_540_i1 (0, 6) envelope_540_i1
    pivot_mem_540_i1 child_envelope_sub_540_i1 envelope_origin_540_i1
def checked_540_i1 : CheckedCard where
  required := required_540_i1
  envelope := envelope_540_i1
  height := height_540_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_540_i1
def height_540 : ℕ := 10
def childrenH_540 : Fin 3 → ℕ := ![height_44, height_540_i0, height_540_i1]
theorem height_exact_540 : height_540 = 1 + Finset.univ.sup childrenH_540 := by decide +kernel
theorem required_origin_540 : ∀ x ∈ required_540,
    (∃ j, x ∈ childrenC_540 j) ∨ ∀ j, x ∈ childrenD_540 j := by decide +kernel
theorem required_exact_540 : required_540 =
    ((Finset.univ.biUnion childrenC_540) ∪ commonEnvelope childrenD_540).erase (4, 3) := by
  exact required_eq_combination childrenC_540 childrenD_540 (4, 3) required_540
    (by decide +kernel) child_required_sub_540 common_sub_540 required_origin_540
theorem envelope_origin_540 : ∀ x ∈ envelope_540,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_540 j := by decide +kernel
theorem envelope_exact_540 : envelope_540 =
    insert (4, 3) (Finset.univ.biUnion childrenD_540) := by
  exact envelope_eq_combination childrenD_540 (4, 3) envelope_540
    pivot_mem_540 child_envelope_sub_540 envelope_origin_540
def checked_540 : CheckedCard where
  required := required_540
  envelope := envelope_540
  height := height_540
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_540
def height_541_i6 : ℕ := 3
def childrenH_541_i6 : Fin 2 → ℕ := ![height_0, height_35]
theorem height_exact_541_i6 : height_541_i6 = 1 + Finset.univ.sup childrenH_541_i6 := by decide +kernel
theorem required_origin_541_i6 : ∀ x ∈ required_541_i6,
    (∃ j, x ∈ childrenC_541_i6 j) ∨ ∀ j, x ∈ childrenD_541_i6 j := by decide +kernel
theorem required_exact_541_i6 : required_541_i6 =
    ((Finset.univ.biUnion childrenC_541_i6) ∪ commonEnvelope childrenD_541_i6).erase (4, 2) := by
  exact required_eq_combination childrenC_541_i6 childrenD_541_i6 (4, 2) required_541_i6
    (by decide +kernel) child_required_sub_541_i6 common_sub_541_i6 required_origin_541_i6
theorem envelope_origin_541_i6 : ∀ x ∈ envelope_541_i6,
    x = (4, 2) ∨ ∃ j, x ∈ childrenD_541_i6 j := by decide +kernel
theorem envelope_exact_541_i6 : envelope_541_i6 =
    insert (4, 2) (Finset.univ.biUnion childrenD_541_i6) := by
  exact envelope_eq_combination childrenD_541_i6 (4, 2) envelope_541_i6
    pivot_mem_541_i6 child_envelope_sub_541_i6 envelope_origin_541_i6
def checked_541_i6 : CheckedCard where
  required := required_541_i6
  envelope := envelope_541_i6
  height := height_541_i6
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_541_i6
def height_541_i5 : ℕ := 4
def childrenH_541_i5 : Fin 2 → ℕ := ![height_170, height_541_i6]
theorem height_exact_541_i5 : height_541_i5 = 1 + Finset.univ.sup childrenH_541_i5 := by decide +kernel
theorem required_origin_541_i5 : ∀ x ∈ required_541_i5,
    (∃ j, x ∈ childrenC_541_i5 j) ∨ ∀ j, x ∈ childrenD_541_i5 j := by decide +kernel
theorem required_exact_541_i5 : required_541_i5 =
    ((Finset.univ.biUnion childrenC_541_i5) ∪ commonEnvelope childrenD_541_i5).erase (4, 3) := by
  exact required_eq_combination childrenC_541_i5 childrenD_541_i5 (4, 3) required_541_i5
    (by decide +kernel) child_required_sub_541_i5 common_sub_541_i5 required_origin_541_i5
theorem envelope_origin_541_i5 : ∀ x ∈ envelope_541_i5,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_541_i5 j := by decide +kernel
theorem envelope_exact_541_i5 : envelope_541_i5 =
    insert (4, 3) (Finset.univ.biUnion childrenD_541_i5) := by
  exact envelope_eq_combination childrenD_541_i5 (4, 3) envelope_541_i5
    pivot_mem_541_i5 child_envelope_sub_541_i5 envelope_origin_541_i5
def checked_541_i5 : CheckedCard where
  required := required_541_i5
  envelope := envelope_541_i5
  height := height_541_i5
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_541_i5
def height_541_i4 : ℕ := 5
def childrenH_541_i4 : Fin 3 → ℕ := ![height_6, height_86, height_541_i5]
theorem height_exact_541_i4 : height_541_i4 = 1 + Finset.univ.sup childrenH_541_i4 := by decide +kernel
theorem required_origin_541_i4 : ∀ x ∈ required_541_i4,
    (∃ j, x ∈ childrenC_541_i4 j) ∨ ∀ j, x ∈ childrenD_541_i4 j := by decide +kernel
theorem required_exact_541_i4 : required_541_i4 =
    ((Finset.univ.biUnion childrenC_541_i4) ∪ commonEnvelope childrenD_541_i4).erase (3, 4) := by
  exact required_eq_combination childrenC_541_i4 childrenD_541_i4 (3, 4) required_541_i4
    (by decide +kernel) child_required_sub_541_i4 common_sub_541_i4 required_origin_541_i4
theorem envelope_origin_541_i4 : ∀ x ∈ envelope_541_i4,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_541_i4 j := by decide +kernel
theorem envelope_exact_541_i4 : envelope_541_i4 =
    insert (3, 4) (Finset.univ.biUnion childrenD_541_i4) := by
  exact envelope_eq_combination childrenD_541_i4 (3, 4) envelope_541_i4
    pivot_mem_541_i4 child_envelope_sub_541_i4 envelope_origin_541_i4
def checked_541_i4 : CheckedCard where
  required := required_541_i4
  envelope := envelope_541_i4
  height := height_541_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_541_i4
def height_541_i3 : ℕ := 6
def childrenH_541_i3 : Fin 2 → ℕ := ![height_0, height_541_i4]
theorem height_exact_541_i3 : height_541_i3 = 1 + Finset.univ.sup childrenH_541_i3 := by decide +kernel
theorem required_origin_541_i3 : ∀ x ∈ required_541_i3,
    (∃ j, x ∈ childrenC_541_i3 j) ∨ ∀ j, x ∈ childrenD_541_i3 j := by decide +kernel
theorem required_exact_541_i3 : required_541_i3 =
    ((Finset.univ.biUnion childrenC_541_i3) ∪ commonEnvelope childrenD_541_i3).erase (3, 5) := by
  exact required_eq_combination childrenC_541_i3 childrenD_541_i3 (3, 5) required_541_i3
    (by decide +kernel) child_required_sub_541_i3 common_sub_541_i3 required_origin_541_i3
theorem envelope_origin_541_i3 : ∀ x ∈ envelope_541_i3,
    x = (3, 5) ∨ ∃ j, x ∈ childrenD_541_i3 j := by decide +kernel
theorem envelope_exact_541_i3 : envelope_541_i3 =
    insert (3, 5) (Finset.univ.biUnion childrenD_541_i3) := by
  exact envelope_eq_combination childrenD_541_i3 (3, 5) envelope_541_i3
    pivot_mem_541_i3 child_envelope_sub_541_i3 envelope_origin_541_i3
def checked_541_i3 : CheckedCard where
  required := required_541_i3
  envelope := envelope_541_i3
  height := height_541_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_541_i3
def height_541_i2 : ℕ := 7
def childrenH_541_i2 : Fin 2 → ℕ := ![height_4, height_541_i3]
theorem height_exact_541_i2 : height_541_i2 = 1 + Finset.univ.sup childrenH_541_i2 := by decide +kernel
theorem required_origin_541_i2 : ∀ x ∈ required_541_i2,
    (∃ j, x ∈ childrenC_541_i2 j) ∨ ∀ j, x ∈ childrenD_541_i2 j := by decide +kernel
theorem required_exact_541_i2 : required_541_i2 =
    ((Finset.univ.biUnion childrenC_541_i2) ∪ commonEnvelope childrenD_541_i2).erase (2, 5) := by
  exact required_eq_combination childrenC_541_i2 childrenD_541_i2 (2, 5) required_541_i2
    (by decide +kernel) child_required_sub_541_i2 common_sub_541_i2 required_origin_541_i2
theorem envelope_origin_541_i2 : ∀ x ∈ envelope_541_i2,
    x = (2, 5) ∨ ∃ j, x ∈ childrenD_541_i2 j := by decide +kernel
theorem envelope_exact_541_i2 : envelope_541_i2 =
    insert (2, 5) (Finset.univ.biUnion childrenD_541_i2) := by
  exact envelope_eq_combination childrenD_541_i2 (2, 5) envelope_541_i2
    pivot_mem_541_i2 child_envelope_sub_541_i2 envelope_origin_541_i2
def checked_541_i2 : CheckedCard where
  required := required_541_i2
  envelope := envelope_541_i2
  height := height_541_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_541_i2
def height_541_i1 : ℕ := 8
def childrenH_541_i1 : Fin 2 → ℕ := ![height_4, height_541_i2]
theorem height_exact_541_i1 : height_541_i1 = 1 + Finset.univ.sup childrenH_541_i1 := by decide +kernel
theorem required_origin_541_i1 : ∀ x ∈ required_541_i1,
    (∃ j, x ∈ childrenC_541_i1 j) ∨ ∀ j, x ∈ childrenD_541_i1 j := by decide +kernel
theorem required_exact_541_i1 : required_541_i1 =
    ((Finset.univ.biUnion childrenC_541_i1) ∪ commonEnvelope childrenD_541_i1).erase (0, 4) := by
  exact required_eq_combination childrenC_541_i1 childrenD_541_i1 (0, 4) required_541_i1
    (by decide +kernel) child_required_sub_541_i1 common_sub_541_i1 required_origin_541_i1
theorem envelope_origin_541_i1 : ∀ x ∈ envelope_541_i1,
    x = (0, 4) ∨ ∃ j, x ∈ childrenD_541_i1 j := by decide +kernel
theorem envelope_exact_541_i1 : envelope_541_i1 =
    insert (0, 4) (Finset.univ.biUnion childrenD_541_i1) := by
  exact envelope_eq_combination childrenD_541_i1 (0, 4) envelope_541_i1
    pivot_mem_541_i1 child_envelope_sub_541_i1 envelope_origin_541_i1
def checked_541_i1 : CheckedCard where
  required := required_541_i1
  envelope := envelope_541_i1
  height := height_541_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_541_i1
def height_541_i0 : ℕ := 9
def childrenH_541_i0 : Fin 2 → ℕ := ![height_6, height_541_i1]
theorem height_exact_541_i0 : height_541_i0 = 1 + Finset.univ.sup childrenH_541_i0 := by decide +kernel
theorem required_origin_541_i0 : ∀ x ∈ required_541_i0,
    (∃ j, x ∈ childrenC_541_i0 j) ∨ ∀ j, x ∈ childrenD_541_i0 j := by decide +kernel
theorem required_exact_541_i0 : required_541_i0 =
    ((Finset.univ.biUnion childrenC_541_i0) ∪ commonEnvelope childrenD_541_i0).erase (1, 9) := by
  exact required_eq_combination childrenC_541_i0 childrenD_541_i0 (1, 9) required_541_i0
    (by decide +kernel) child_required_sub_541_i0 common_sub_541_i0 required_origin_541_i0
theorem envelope_origin_541_i0 : ∀ x ∈ envelope_541_i0,
    x = (1, 9) ∨ ∃ j, x ∈ childrenD_541_i0 j := by decide +kernel
theorem envelope_exact_541_i0 : envelope_541_i0 =
    insert (1, 9) (Finset.univ.biUnion childrenD_541_i0) := by
  exact envelope_eq_combination childrenD_541_i0 (1, 9) envelope_541_i0
    pivot_mem_541_i0 child_envelope_sub_541_i0 envelope_origin_541_i0
def checked_541_i0 : CheckedCard where
  required := required_541_i0
  envelope := envelope_541_i0
  height := height_541_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_541_i0
def height_541 : ℕ := 10
def childrenH_541 : Fin 2 → ℕ := ![height_6, height_541_i0]
theorem height_exact_541 : height_541 = 1 + Finset.univ.sup childrenH_541 := by decide +kernel
theorem required_origin_541 : ∀ x ∈ required_541,
    (∃ j, x ∈ childrenC_541 j) ∨ ∀ j, x ∈ childrenD_541 j := by decide +kernel
theorem required_exact_541 : required_541 =
    ((Finset.univ.biUnion childrenC_541) ∪ commonEnvelope childrenD_541).erase (1, 8) := by
  exact required_eq_combination childrenC_541 childrenD_541 (1, 8) required_541
    (by decide +kernel) child_required_sub_541 common_sub_541 required_origin_541
theorem envelope_origin_541 : ∀ x ∈ envelope_541,
    x = (1, 8) ∨ ∃ j, x ∈ childrenD_541 j := by decide +kernel
theorem envelope_exact_541 : envelope_541 =
    insert (1, 8) (Finset.univ.biUnion childrenD_541) := by
  exact envelope_eq_combination childrenD_541 (1, 8) envelope_541
    pivot_mem_541 child_envelope_sub_541 envelope_origin_541
def checked_541 : CheckedCard where
  required := required_541
  envelope := envelope_541
  height := height_541
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_541
def height_545_i0 : ℕ := 9
def childrenH_545_i0 : Fin 4 → ℕ := ![height_19, height_84, height_314, height_419]
theorem height_exact_545_i0 : height_545_i0 = 1 + Finset.univ.sup childrenH_545_i0 := by decide +kernel
theorem required_origin_545_i0 : ∀ x ∈ required_545_i0,
    (∃ j, x ∈ childrenC_545_i0 j) ∨ ∀ j, x ∈ childrenD_545_i0 j := by decide +kernel
theorem required_exact_545_i0 : required_545_i0 =
    ((Finset.univ.biUnion childrenC_545_i0) ∪ commonEnvelope childrenD_545_i0).erase (1, 6) := by
  exact required_eq_combination childrenC_545_i0 childrenD_545_i0 (1, 6) required_545_i0
    (by decide +kernel) child_required_sub_545_i0 common_sub_545_i0 required_origin_545_i0
theorem envelope_origin_545_i0 : ∀ x ∈ envelope_545_i0,
    x = (1, 6) ∨ ∃ j, x ∈ childrenD_545_i0 j := by decide +kernel
theorem envelope_exact_545_i0 : envelope_545_i0 =
    insert (1, 6) (Finset.univ.biUnion childrenD_545_i0) := by
  exact envelope_eq_combination childrenD_545_i0 (1, 6) envelope_545_i0
    pivot_mem_545_i0 child_envelope_sub_545_i0 envelope_origin_545_i0
def checked_545_i0 : CheckedCard where
  required := required_545_i0
  envelope := envelope_545_i0
  height := height_545_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_545_i0
def height_545 : ℕ := 10
def childrenH_545 : Fin 4 → ℕ := ![height_27, height_52, height_284, height_545_i0]
theorem height_exact_545 : height_545 = 1 + Finset.univ.sup childrenH_545 := by decide +kernel
theorem required_origin_545 : ∀ x ∈ required_545,
    (∃ j, x ∈ childrenC_545 j) ∨ ∀ j, x ∈ childrenD_545 j := by decide +kernel
theorem required_exact_545 : required_545 =
    ((Finset.univ.biUnion childrenC_545) ∪ commonEnvelope childrenD_545).erase (1, 3) := by
  exact required_eq_combination childrenC_545 childrenD_545 (1, 3) required_545
    (by decide +kernel) child_required_sub_545 common_sub_545 required_origin_545
theorem envelope_origin_545 : ∀ x ∈ envelope_545,
    x = (1, 3) ∨ ∃ j, x ∈ childrenD_545 j := by decide +kernel
theorem envelope_exact_545 : envelope_545 =
    insert (1, 3) (Finset.univ.biUnion childrenD_545) := by
  exact envelope_eq_combination childrenD_545 (1, 3) envelope_545
    pivot_mem_545 child_envelope_sub_545 envelope_origin_545
def checked_545 : CheckedCard where
  required := required_545
  envelope := envelope_545
  height := height_545
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_545
end SnakyPrototype.Certificate21

end OAI
