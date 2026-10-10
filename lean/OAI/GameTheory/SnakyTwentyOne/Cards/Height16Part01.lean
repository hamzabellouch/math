import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part06
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height10Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height10Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height11Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height11Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height12Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height13Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height13Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height13Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height14Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height14Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height15Part01
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_602_i1 : Finset Cell := ⟨(([(3, 5), (3, 8), (4, 5), (4, 8), (6, 7), (6, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_602_i1 : Finset Cell := ⟨(([(2, 7), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 4), (4, 5), (4, 7), (4, 8), (5, 4), (5, 5), (5, 6), (5, 8), (5, 9), (5, 10), (5, 11), (5, 12), (5, 13), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (6, 12), (7, 4), (7, 5), (7, 6), (7, 8), (7, 9), (7, 10), (7, 11), (7, 12)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_602_i1 : Fin 2 → Finset Cell := ![(placed21 0 (3, 4) required_320), (placed21 3 (2, 8) required_496)]
def childrenD_602_i1 : Fin 2 → Finset Cell := ![(placed21 0 (3, 4) envelope_320), (placed21 3 (2, 8) envelope_496)]
theorem common_sub_602_i1 : commonEnvelope childrenD_602_i1 ⊆ insert (5, 8) required_602_i1 := by decide +kernel
theorem child_required_sub_602_i1 : ∀ j, childrenC_602_i1 j ⊆ insert (5, 8) required_602_i1 := by decide +kernel
theorem child_envelope_sub_602_i1 : ∀ j, childrenD_602_i1 j ⊆ envelope_602_i1 := by decide +kernel
theorem pivot_mem_602_i1 : (5, 8) ∈ envelope_602_i1 := by decide +kernel
theorem children_work_602_i1 : ∀ j, Template HasSnaky 7 (childrenC_602_i1 j) (childrenD_602_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_320 0 (3, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_496 3 (2, 8)).mono (by decide +kernel)
theorem row_works_602_i1 : Template HasSnaky 8 required_602_i1 envelope_602_i1 := by
  refine compose HasSnaky 7 childrenC_602_i1 childrenD_602_i1 children_work_602_i1 (5, 8)
    required_602_i1 envelope_602_i1 pivot_mem_602_i1 child_required_sub_602_i1 child_envelope_sub_602_i1 ?_
  intro b hb
  exact common_sub_602_i1 (mem_commonEnvelope childrenD_602_i1 b hb)
def required_602_i0 : Finset Cell := ⟨(([(3, 5), (3, 8), (4, 5), (4, 8), (6, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_602_i0 : Finset Cell := ⟨(([(2, 7), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 4), (4, 5), (4, 7), (4, 8), (5, 3), (5, 4), (5, 5), (5, 6), (5, 8), (5, 9), (5, 10), (5, 11), (5, 12), (5, 13), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (6, 12), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (7, 12), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (9, 6), (9, 7), (9, 8), (9, 9), (9, 10), (10, 8), (10, 9), (10, 10), (11, 8), (11, 10)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_602_i0 : Fin 4 → Finset Cell := ![(placed21 4 (3, 11) required_59), (placed21 3 (2, 8) required_497), required_602_i1, (placed21 0 (3, 3) required_555)]
def childrenD_602_i0 : Fin 4 → Finset Cell := ![(placed21 4 (3, 11) envelope_59), (placed21 3 (2, 8) envelope_497), envelope_602_i1, (placed21 0 (3, 3) envelope_555)]
theorem common_sub_602_i0 : commonEnvelope childrenD_602_i0 ⊆ insert (6, 8) required_602_i0 := by decide +kernel
theorem child_required_sub_602_i0 : ∀ j, childrenC_602_i0 j ⊆ insert (6, 8) required_602_i0 := by decide +kernel
theorem child_envelope_sub_602_i0 : ∀ j, childrenD_602_i0 j ⊆ envelope_602_i0 := by decide +kernel
theorem pivot_mem_602_i0 : (6, 8) ∈ envelope_602_i0 := by decide +kernel
theorem children_work_602_i0 : ∀ j, Template HasSnaky 13 (childrenC_602_i0 j) (childrenD_602_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_59 4 (3, 11)).mono (by decide +kernel)
  · exact (placed21_template row_works_497 3 (2, 8)).mono (by decide +kernel)
  · exact row_works_602_i1.mono (by decide +kernel)
  · exact (placed21_template row_works_555 0 (3, 3)).mono (by decide +kernel)
theorem row_works_602_i0 : Template HasSnaky 14 required_602_i0 envelope_602_i0 := by
  refine compose HasSnaky 13 childrenC_602_i0 childrenD_602_i0 children_work_602_i0 (6, 8)
    required_602_i0 envelope_602_i0 pivot_mem_602_i0 child_required_sub_602_i0 child_envelope_sub_602_i0 ?_
  intro b hb
  exact common_sub_602_i0 (mem_commonEnvelope childrenD_602_i0 b hb)
def required_602_i3 : Finset Cell := ⟨(([(3, 8), (4, 8), (6, 7), (7, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_602_i3 : Finset Cell := ⟨(([(3, 8), (4, 8), (5, 3), (5, 4), (5, 5), (5, 8), (5, 9), (5, 10), (5, 11), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (7, 12), (8, 8), (8, 9), (8, 10), (9, 8), (9, 9), (9, 10), (10, 8), (10, 9), (10, 10), (11, 10)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_602_i3 : Fin 2 → Finset Cell := ![(placed21 4 (3, 8) required_2), (placed21 4 (5, 12) required_545)]
def childrenD_602_i3 : Fin 2 → Finset Cell := ![(placed21 4 (3, 8) envelope_2), (placed21 4 (5, 12) envelope_545)]
theorem common_sub_602_i3 : commonEnvelope childrenD_602_i3 ⊆ insert (6, 8) required_602_i3 := by decide +kernel
theorem child_required_sub_602_i3 : ∀ j, childrenC_602_i3 j ⊆ insert (6, 8) required_602_i3 := by decide +kernel
theorem child_envelope_sub_602_i3 : ∀ j, childrenD_602_i3 j ⊆ envelope_602_i3 := by decide +kernel
theorem pivot_mem_602_i3 : (6, 8) ∈ envelope_602_i3 := by decide +kernel
theorem children_work_602_i3 : ∀ j, Template HasSnaky 10 (childrenC_602_i3 j) (childrenD_602_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_2 4 (3, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_545 4 (5, 12)).mono (by decide +kernel)
theorem row_works_602_i3 : Template HasSnaky 11 required_602_i3 envelope_602_i3 := by
  refine compose HasSnaky 10 childrenC_602_i3 childrenD_602_i3 children_work_602_i3 (6, 8)
    required_602_i3 envelope_602_i3 pivot_mem_602_i3 child_required_sub_602_i3 child_envelope_sub_602_i3 ?_
  intro b hb
  exact common_sub_602_i3 (mem_commonEnvelope childrenD_602_i3 b hb)
def required_602_i2 : Finset Cell := ⟨(([(3, 8), (4, 8), (6, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_602_i2 : Finset Cell := ⟨(([(3, 8), (4, 7), (4, 8), (5, 3), (5, 4), (5, 5), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (7, 12), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (8, 11), (9, 6), (9, 7), (9, 8), (9, 9), (9, 10), (9, 11), (10, 6), (10, 7), (10, 8), (10, 9), (10, 10), (11, 6), (11, 7), (11, 8), (11, 10), (12, 6), (12, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_602_i2 : Fin 4 → Finset Cell := ![(placed21 3 (3, 8) required_107), (placed21 3 (3, 8) required_163), (placed21 4 (3, 11) required_556), required_602_i3]
def childrenD_602_i2 : Fin 4 → Finset Cell := ![(placed21 3 (3, 8) envelope_107), (placed21 3 (3, 8) envelope_163), (placed21 4 (3, 11) envelope_556), envelope_602_i3]
theorem common_sub_602_i2 : commonEnvelope childrenD_602_i2 ⊆ insert (7, 7) required_602_i2 := by decide +kernel
theorem child_required_sub_602_i2 : ∀ j, childrenC_602_i2 j ⊆ insert (7, 7) required_602_i2 := by decide +kernel
theorem child_envelope_sub_602_i2 : ∀ j, childrenD_602_i2 j ⊆ envelope_602_i2 := by decide +kernel
theorem pivot_mem_602_i2 : (7, 7) ∈ envelope_602_i2 := by decide +kernel
theorem children_work_602_i2 : ∀ j, Template HasSnaky 11 (childrenC_602_i2 j) (childrenD_602_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_107 3 (3, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_163 3 (3, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_556 4 (3, 11)).mono (by decide +kernel)
  · exact row_works_602_i3.mono (by decide +kernel)
theorem row_works_602_i2 : Template HasSnaky 12 required_602_i2 envelope_602_i2 := by
  refine compose HasSnaky 11 childrenC_602_i2 childrenD_602_i2 children_work_602_i2 (7, 7)
    required_602_i2 envelope_602_i2 pivot_mem_602_i2 child_required_sub_602_i2 child_envelope_sub_602_i2 ?_
  intro b hb
  exact common_sub_602_i2 (mem_commonEnvelope childrenD_602_i2 b hb)
def required_602_i6 : Finset Cell := ⟨(([(3, 5), (4, 5), (4, 8), (5, 5), (6, 7), (6, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_602_i6 : Finset Cell := ⟨(([(2, 4), (2, 6), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 3), (4, 4), (4, 5), (4, 7), (4, 8), (5, 5), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (7, 4), (7, 5), (8, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_602_i6 : Fin 2 → Finset Cell := ![(placed21 0 (3, 4) required_157), (placed21 2 (6, 3) required_383)]
def childrenD_602_i6 : Fin 2 → Finset Cell := ![(placed21 0 (3, 4) envelope_157), (placed21 2 (6, 3) envelope_383)]
theorem common_sub_602_i6 : commonEnvelope childrenD_602_i6 ⊆ insert (6, 5) required_602_i6 := by decide +kernel
theorem child_required_sub_602_i6 : ∀ j, childrenC_602_i6 j ⊆ insert (6, 5) required_602_i6 := by decide +kernel
theorem child_envelope_sub_602_i6 : ∀ j, childrenD_602_i6 j ⊆ envelope_602_i6 := by decide +kernel
theorem pivot_mem_602_i6 : (6, 5) ∈ envelope_602_i6 := by decide +kernel
theorem children_work_602_i6 : ∀ j, Template HasSnaky 5 (childrenC_602_i6 j) (childrenD_602_i6 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_157 0 (3, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_383 2 (6, 3)).mono (by decide +kernel)
theorem row_works_602_i6 : Template HasSnaky 6 required_602_i6 envelope_602_i6 := by
  refine compose HasSnaky 5 childrenC_602_i6 childrenD_602_i6 children_work_602_i6 (6, 5)
    required_602_i6 envelope_602_i6 pivot_mem_602_i6 child_required_sub_602_i6 child_envelope_sub_602_i6 ?_
  intro b hb
  exact common_sub_602_i6 (mem_commonEnvelope childrenD_602_i6 b hb)
def required_602_i7 : Finset Cell := ⟨(([(4, 5), (5, 5), (6, 7), (6, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_602_i7 : Finset Cell := ⟨(([(3, 5), (4, 5), (5, 4), (5, 5), (5, 6), (5, 9), (5, 10), (5, 11), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, 3), (7, 4), (7, 5), (7, 9), (7, 10), (7, 11)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_602_i7 : Fin 2 → Finset Cell := ![(placed21 0 (5, 5) required_18), (placed21 7 (7, 8) required_381)]
def childrenD_602_i7 : Fin 2 → Finset Cell := ![(placed21 0 (5, 5) envelope_18), (placed21 7 (7, 8) envelope_381)]
theorem common_sub_602_i7 : commonEnvelope childrenD_602_i7 ⊆ insert (6, 6) required_602_i7 := by decide +kernel
theorem child_required_sub_602_i7 : ∀ j, childrenC_602_i7 j ⊆ insert (6, 6) required_602_i7 := by decide +kernel
theorem child_envelope_sub_602_i7 : ∀ j, childrenD_602_i7 j ⊆ envelope_602_i7 := by decide +kernel
theorem pivot_mem_602_i7 : (6, 6) ∈ envelope_602_i7 := by decide +kernel
theorem children_work_602_i7 : ∀ j, Template HasSnaky 4 (childrenC_602_i7 j) (childrenD_602_i7 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_18 0 (5, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_381 7 (7, 8)).mono (by decide +kernel)
theorem row_works_602_i7 : Template HasSnaky 5 required_602_i7 envelope_602_i7 := by
  refine compose HasSnaky 4 childrenC_602_i7 childrenD_602_i7 children_work_602_i7 (6, 6)
    required_602_i7 envelope_602_i7 pivot_mem_602_i7 child_required_sub_602_i7 child_envelope_sub_602_i7 ?_
  intro b hb
  exact common_sub_602_i7 (mem_commonEnvelope childrenD_602_i7 b hb)
def required_602_i8 : Finset Cell := ⟨(([(3, 5), (3, 8), (4, 5), (4, 8), (5, 5), (6, 7), (6, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_602_i8 : Finset Cell := ⟨(([(2, 6), (3, 5), (3, 6), (3, 7), (3, 8), (4, 4), (4, 5), (4, 7), (4, 8), (5, 4), (5, 5), (5, 6), (5, 7), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, 7), (7, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_602_i8 : Fin 2 → Finset Cell := ![(placed21 0 (5, 4) required_64), (placed21 3 (2, 8) required_500)]
def childrenD_602_i8 : Fin 2 → Finset Cell := ![(placed21 0 (5, 4) envelope_64), (placed21 3 (2, 8) envelope_500)]
theorem common_sub_602_i8 : commonEnvelope childrenD_602_i8 ⊆ insert (5, 7) required_602_i8 := by decide +kernel
theorem child_required_sub_602_i8 : ∀ j, childrenC_602_i8 j ⊆ insert (5, 7) required_602_i8 := by decide +kernel
theorem child_envelope_sub_602_i8 : ∀ j, childrenD_602_i8 j ⊆ envelope_602_i8 := by decide +kernel
theorem pivot_mem_602_i8 : (5, 7) ∈ envelope_602_i8 := by decide +kernel
theorem children_work_602_i8 : ∀ j, Template HasSnaky 4 (childrenC_602_i8 j) (childrenD_602_i8 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_64 0 (5, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_500 3 (2, 8)).mono (by decide +kernel)
theorem row_works_602_i8 : Template HasSnaky 5 required_602_i8 envelope_602_i8 := by
  refine compose HasSnaky 4 childrenC_602_i8 childrenD_602_i8 children_work_602_i8 (5, 7)
    required_602_i8 envelope_602_i8 pivot_mem_602_i8 child_required_sub_602_i8 child_envelope_sub_602_i8 ?_
  intro b hb
  exact common_sub_602_i8 (mem_commonEnvelope childrenD_602_i8 b hb)
def required_602_i5 : Finset Cell := ⟨(([(3, 5), (3, 8), (4, 5), (4, 8), (6, 7), (6, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_602_i5 : Finset Cell := ⟨(([(1, 3), (1, 4), (2, 1), (2, 2), (2, 3), (2, 4), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 7), (4, 8), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 9), (5, 10), (5, 11), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, 3), (7, 4), (7, 5), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (8, 3), (8, 4), (8, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_602_i5 : Fin 4 → Finset Cell := ![required_602_i6, required_602_i7, required_602_i8, (placed21 3 (1, 8) required_601)]
def childrenD_602_i5 : Fin 4 → Finset Cell := ![envelope_602_i6, envelope_602_i7, envelope_602_i8, (placed21 3 (1, 8) envelope_601)]
theorem common_sub_602_i5 : commonEnvelope childrenD_602_i5 ⊆ insert (5, 5) required_602_i5 := by decide +kernel
theorem child_required_sub_602_i5 : ∀ j, childrenC_602_i5 j ⊆ insert (5, 5) required_602_i5 := by decide +kernel
theorem child_envelope_sub_602_i5 : ∀ j, childrenD_602_i5 j ⊆ envelope_602_i5 := by decide +kernel
theorem pivot_mem_602_i5 : (5, 5) ∈ envelope_602_i5 := by decide +kernel
theorem children_work_602_i5 : ∀ j, Template HasSnaky 11 (childrenC_602_i5 j) (childrenD_602_i5 j) := by
  intro j
  fin_cases j
  · exact row_works_602_i6.mono (by decide +kernel)
  · exact row_works_602_i7.mono (by decide +kernel)
  · exact row_works_602_i8.mono (by decide +kernel)
  · exact (placed21_template row_works_601 3 (1, 8)).mono (by decide +kernel)
theorem row_works_602_i5 : Template HasSnaky 12 required_602_i5 envelope_602_i5 := by
  refine compose HasSnaky 11 childrenC_602_i5 childrenD_602_i5 children_work_602_i5 (5, 5)
    required_602_i5 envelope_602_i5 pivot_mem_602_i5 child_required_sub_602_i5 child_envelope_sub_602_i5 ?_
  intro b hb
  exact common_sub_602_i5 (mem_commonEnvelope childrenD_602_i5 b hb)
def required_602_i4 : Finset Cell := ⟨(([(3, 5), (3, 8), (4, 5), (4, 8), (6, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_602_i4 : Finset Cell := ⟨(([(1, 3), (1, 4), (2, 1), (2, 2), (2, 3), (2, 4), (2, 6), (2, 7), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 7), (4, 8), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (5, 12), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (7, 3), (7, 4), (7, 5), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (7, 12), (8, 3), (8, 4), (8, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_602_i4 : Fin 4 → Finset Cell := ![(placed21 0 (3, 5) required_119), (placed21 3 (2, 8) required_497), (placed21 1 (2, 4) required_498), required_602_i5]
def childrenD_602_i4 : Fin 4 → Finset Cell := ![(placed21 0 (3, 5) envelope_119), (placed21 3 (2, 8) envelope_497), (placed21 1 (2, 4) envelope_498), envelope_602_i5]
theorem common_sub_602_i4 : commonEnvelope childrenD_602_i4 ⊆ insert (6, 8) required_602_i4 := by decide +kernel
theorem child_required_sub_602_i4 : ∀ j, childrenC_602_i4 j ⊆ insert (6, 8) required_602_i4 := by decide +kernel
theorem child_envelope_sub_602_i4 : ∀ j, childrenD_602_i4 j ⊆ envelope_602_i4 := by decide +kernel
theorem pivot_mem_602_i4 : (6, 8) ∈ envelope_602_i4 := by decide +kernel
theorem children_work_602_i4 : ∀ j, Template HasSnaky 12 (childrenC_602_i4 j) (childrenD_602_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_119 0 (3, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_497 3 (2, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_498 1 (2, 4)).mono (by decide +kernel)
  · exact row_works_602_i5.mono (by decide +kernel)
theorem row_works_602_i4 : Template HasSnaky 13 required_602_i4 envelope_602_i4 := by
  refine compose HasSnaky 12 childrenC_602_i4 childrenD_602_i4 children_work_602_i4 (6, 8)
    required_602_i4 envelope_602_i4 pivot_mem_602_i4 child_required_sub_602_i4 child_envelope_sub_602_i4 ?_
  intro b hb
  exact common_sub_602_i4 (mem_commonEnvelope childrenD_602_i4 b hb)
def required_602 : Finset Cell := ⟨(([(3, 5), (3, 8), (4, 5), (4, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_602 : Finset Cell := ⟨(([(0, 3), (0, 4), (0, 7), (1, 3), (1, 4), (1, 7), (2, 1), (2, 2), (2, 3), (2, 4), (2, 6), (2, 7), (2, 9), (2, 10), (2, 11), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 7), (4, 8), (4, 10), (4, 11), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (5, 12), (5, 13), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (6, 12), (6, 13), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (7, 12), (7, 13), (7, 14), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (8, 11), (8, 12), (8, 13), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (9, 10), (9, 11), (9, 12), (9, 13), (9, 14), (10, 1), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (10, 9), (10, 10), (10, 11), (10, 12), (11, 5), (11, 6), (11, 7), (11, 8), (11, 9), (11, 10), (11, 11), (12, 6), (12, 8), (12, 10)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_602 : Fin 12 → Finset Cell := ![(placed21 0 (0, 1) required_553), required_602_i0, required_602_i2, (placed21 0 (2, 2) required_557), (placed21 1 (2, 4) required_564), (placed21 1 (2, 4) required_568), (placed21 3 (0, 8) required_573), (placed21 4 (2, 10) required_574), (placed21 4 (0, 13) required_583), (placed21 4 (0, 12) required_598), (placed21 0 (3, 4) required_599), required_602_i4]
def childrenD_602 : Fin 12 → Finset Cell := ![(placed21 0 (0, 1) envelope_553), envelope_602_i0, envelope_602_i2, (placed21 0 (2, 2) envelope_557), (placed21 1 (2, 4) envelope_564), (placed21 1 (2, 4) envelope_568), (placed21 3 (0, 8) envelope_573), (placed21 4 (2, 10) envelope_574), (placed21 4 (0, 13) envelope_583), (placed21 4 (0, 12) envelope_598), (placed21 0 (3, 4) envelope_599), envelope_602_i4]
theorem common_sub_602 : commonEnvelope childrenD_602 ⊆ insert (6, 7) required_602 := by decide +kernel
theorem child_required_sub_602 : ∀ j, childrenC_602 j ⊆ insert (6, 7) required_602 := by decide +kernel
theorem child_envelope_sub_602 : ∀ j, childrenD_602 j ⊆ envelope_602 := by decide +kernel
theorem pivot_mem_602 : (6, 7) ∈ envelope_602 := by decide +kernel
theorem children_work_602 : ∀ j, Template HasSnaky 15 (childrenC_602 j) (childrenD_602 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_553 0 (0, 1)).mono (by decide +kernel)
  · exact row_works_602_i0.mono (by decide +kernel)
  · exact row_works_602_i2.mono (by decide +kernel)
  · exact (placed21_template row_works_557 0 (2, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_564 1 (2, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_568 1 (2, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_573 3 (0, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_574 4 (2, 10)).mono (by decide +kernel)
  · exact (placed21_template row_works_583 4 (0, 13)).mono (by decide +kernel)
  · exact (placed21_template row_works_598 4 (0, 12)).mono (by decide +kernel)
  · exact (placed21_template row_works_599 0 (3, 4)).mono (by decide +kernel)
  · exact row_works_602_i4.mono (by decide +kernel)
theorem row_works_602 : Template HasSnaky 16 required_602 envelope_602 := by
  refine compose HasSnaky 15 childrenC_602 childrenD_602 children_work_602 (6, 7)
    required_602 envelope_602 pivot_mem_602 child_required_sub_602 child_envelope_sub_602 ?_
  intro b hb
  exact common_sub_602 (mem_commonEnvelope childrenD_602 b hb)
def required_627_i0 : Finset Cell := ⟨(([(3, 4), (5, 4), (6, 3), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_627_i0 : Finset Cell := ⟨(([(2, 5), (3, 4), (3, 5), (4, 4), (4, 5), (4, 6), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, 3), (7, 5), (7, 6), (7, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_627_i0 : Fin 2 → Finset Cell := ![(placed21 4 (3, 4) required_5), (placed21 2 (7, 2) required_472)]
def childrenD_627_i0 : Fin 2 → Finset Cell := ![(placed21 4 (3, 4) envelope_5), (placed21 2 (7, 2) envelope_472)]
theorem common_sub_627_i0 : commonEnvelope childrenD_627_i0 ⊆ insert (4, 4) required_627_i0 := by decide +kernel
theorem child_required_sub_627_i0 : ∀ j, childrenC_627_i0 j ⊆ insert (4, 4) required_627_i0 := by decide +kernel
theorem child_envelope_sub_627_i0 : ∀ j, childrenD_627_i0 j ⊆ envelope_627_i0 := by decide +kernel
theorem pivot_mem_627_i0 : (4, 4) ∈ envelope_627_i0 := by decide +kernel
theorem children_work_627_i0 : ∀ j, Template HasSnaky 7 (childrenC_627_i0 j) (childrenD_627_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 4 (3, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_472 2 (7, 2)).mono (by decide +kernel)
theorem row_works_627_i0 : Template HasSnaky 8 required_627_i0 envelope_627_i0 := by
  refine compose HasSnaky 7 childrenC_627_i0 childrenD_627_i0 children_work_627_i0 (4, 4)
    required_627_i0 envelope_627_i0 pivot_mem_627_i0 child_required_sub_627_i0 child_envelope_sub_627_i0 ?_
  intro b hb
  exact common_sub_627_i0 (mem_commonEnvelope childrenD_627_i0 b hb)
def required_627_i3 : Finset Cell := ⟨(([(3, 3), (5, 4), (5, 5), (5, 6), (6, 3), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_627_i3 : Finset Cell := ⟨(([(2, 3), (3, 3), (4, 2), (4, 3), (4, 5), (4, 6), (4, 7), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (6, 3), (6, 4), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_627_i3 : Fin 2 → Finset Cell := ![(placed21 7 (6, 6) required_38), (placed21 6 (6, 7) required_205)]
def childrenD_627_i3 : Fin 2 → Finset Cell := ![(placed21 7 (6, 6) envelope_38), (placed21 6 (6, 7) envelope_205)]
theorem common_sub_627_i3 : commonEnvelope childrenD_627_i3 ⊆ insert (5, 3) required_627_i3 := by decide +kernel
theorem child_required_sub_627_i3 : ∀ j, childrenC_627_i3 j ⊆ insert (5, 3) required_627_i3 := by decide +kernel
theorem child_envelope_sub_627_i3 : ∀ j, childrenD_627_i3 j ⊆ envelope_627_i3 := by decide +kernel
theorem pivot_mem_627_i3 : (5, 3) ∈ envelope_627_i3 := by decide +kernel
theorem children_work_627_i3 : ∀ j, Template HasSnaky 3 (childrenC_627_i3 j) (childrenD_627_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_38 7 (6, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_205 6 (6, 7)).mono (by decide +kernel)
theorem row_works_627_i3 : Template HasSnaky 4 required_627_i3 envelope_627_i3 := by
  refine compose HasSnaky 3 childrenC_627_i3 childrenD_627_i3 children_work_627_i3 (5, 3)
    required_627_i3 envelope_627_i3 pivot_mem_627_i3 child_required_sub_627_i3 child_envelope_sub_627_i3 ?_
  intro b hb
  exact common_sub_627_i3 (mem_commonEnvelope childrenD_627_i3 b hb)
def required_627_i2 : Finset Cell := ⟨(([(3, 3), (5, 4), (5, 6), (6, 3), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_627_i2 : Finset Cell := ⟨(([(2, 3), (3, 3), (4, 2), (4, 3), (4, 5), (4, 6), (4, 7), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 3), (6, 4), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_627_i2 : Fin 2 → Finset Cell := ![(placed21 3 (5, 7) required_0), required_627_i3]
def childrenD_627_i2 : Fin 2 → Finset Cell := ![(placed21 3 (5, 7) envelope_0), envelope_627_i3]
theorem common_sub_627_i2 : commonEnvelope childrenD_627_i2 ⊆ insert (5, 5) required_627_i2 := by decide +kernel
theorem child_required_sub_627_i2 : ∀ j, childrenC_627_i2 j ⊆ insert (5, 5) required_627_i2 := by decide +kernel
theorem child_envelope_sub_627_i2 : ∀ j, childrenD_627_i2 j ⊆ envelope_627_i2 := by decide +kernel
theorem pivot_mem_627_i2 : (5, 5) ∈ envelope_627_i2 := by decide +kernel
theorem children_work_627_i2 : ∀ j, Template HasSnaky 4 (childrenC_627_i2 j) (childrenD_627_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 3 (5, 7)).mono (by decide +kernel)
  · exact row_works_627_i3.mono (by decide +kernel)
theorem row_works_627_i2 : Template HasSnaky 5 required_627_i2 envelope_627_i2 := by
  refine compose HasSnaky 4 childrenC_627_i2 childrenD_627_i2 children_work_627_i2 (5, 5)
    required_627_i2 envelope_627_i2 pivot_mem_627_i2 child_required_sub_627_i2 child_envelope_sub_627_i2 ?_
  intro b hb
  exact common_sub_627_i2 (mem_commonEnvelope childrenD_627_i2 b hb)
def required_627_i5 : Finset Cell := ⟨(([(3, 3), (5, 4), (5, 5), (5, 6), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_627_i5 : Finset Cell := ⟨(([(2, 3), (3, 3), (3, 5), (4, 2), (4, 3), (4, 5), (4, 6), (4, 7), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (6, 4), (6, 6), (6, 7), (7, 6), (8, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_627_i5 : Fin 2 → Finset Cell := ![(placed21 7 (6, 6) required_38), (placed21 3 (3, 7) required_179)]
def childrenD_627_i5 : Fin 2 → Finset Cell := ![(placed21 7 (6, 6) envelope_38), (placed21 3 (3, 7) envelope_179)]
theorem common_sub_627_i5 : commonEnvelope childrenD_627_i5 ⊆ insert (5, 3) required_627_i5 := by decide +kernel
theorem child_required_sub_627_i5 : ∀ j, childrenC_627_i5 j ⊆ insert (5, 3) required_627_i5 := by decide +kernel
theorem child_envelope_sub_627_i5 : ∀ j, childrenD_627_i5 j ⊆ envelope_627_i5 := by decide +kernel
theorem pivot_mem_627_i5 : (5, 3) ∈ envelope_627_i5 := by decide +kernel
theorem children_work_627_i5 : ∀ j, Template HasSnaky 5 (childrenC_627_i5 j) (childrenD_627_i5 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_38 7 (6, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_179 3 (3, 7)).mono (by decide +kernel)
theorem row_works_627_i5 : Template HasSnaky 6 required_627_i5 envelope_627_i5 := by
  refine compose HasSnaky 5 childrenC_627_i5 childrenD_627_i5 children_work_627_i5 (5, 3)
    required_627_i5 envelope_627_i5 pivot_mem_627_i5 child_required_sub_627_i5 child_envelope_sub_627_i5 ?_
  intro b hb
  exact common_sub_627_i5 (mem_commonEnvelope childrenD_627_i5 b hb)
def required_627_i4 : Finset Cell := ⟨(([(3, 3), (5, 4), (5, 6), (6, 3), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_627_i4 : Finset Cell := ⟨(([(2, 3), (3, 3), (3, 5), (4, 2), (4, 3), (4, 5), (4, 6), (4, 7), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 3), (6, 4), (6, 6), (6, 7), (7, 6), (8, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_627_i4 : Fin 2 → Finset Cell := ![(placed21 3 (5, 7) required_0), required_627_i5]
def childrenD_627_i4 : Fin 2 → Finset Cell := ![(placed21 3 (5, 7) envelope_0), envelope_627_i5]
theorem common_sub_627_i4 : commonEnvelope childrenD_627_i4 ⊆ insert (5, 5) required_627_i4 := by decide +kernel
theorem child_required_sub_627_i4 : ∀ j, childrenC_627_i4 j ⊆ insert (5, 5) required_627_i4 := by decide +kernel
theorem child_envelope_sub_627_i4 : ∀ j, childrenD_627_i4 j ⊆ envelope_627_i4 := by decide +kernel
theorem pivot_mem_627_i4 : (5, 5) ∈ envelope_627_i4 := by decide +kernel
theorem children_work_627_i4 : ∀ j, Template HasSnaky 6 (childrenC_627_i4 j) (childrenD_627_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 3 (5, 7)).mono (by decide +kernel)
  · exact row_works_627_i5.mono (by decide +kernel)
theorem row_works_627_i4 : Template HasSnaky 7 required_627_i4 envelope_627_i4 := by
  refine compose HasSnaky 6 childrenC_627_i4 childrenD_627_i4 children_work_627_i4 (5, 5)
    required_627_i4 envelope_627_i4 pivot_mem_627_i4 child_required_sub_627_i4 child_envelope_sub_627_i4 ?_
  intro b hb
  exact common_sub_627_i4 (mem_commonEnvelope childrenD_627_i4 b hb)
def required_627_i6 : Finset Cell := ⟨(([(5, 4), (5, 6), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_627_i6 : Finset Cell := ⟨(([(0, 7), (1, 5), (1, 6), (1, 7), (2, 5), (2, 6), (2, 7), (3, 5), (3, 6), (3, 7), (4, 6), (4, 7), (4, 8), (4, 9), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (8, 11), (9, 5), (9, 6), (9, 7), (9, 8), (10, 5), (10, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_627_i6 : Fin 6 → Finset Cell := ![(placed21 2 (6, 3) required_50), (placed21 2 (6, 3) required_97), (placed21 0 (5, 3) required_98), (placed21 4 (4, 8) required_454), (placed21 1 (4, 4) required_455), (placed21 5 (10, 3) required_624)]
def childrenD_627_i6 : Fin 6 → Finset Cell := ![(placed21 2 (6, 3) envelope_50), (placed21 2 (6, 3) envelope_97), (placed21 0 (5, 3) envelope_98), (placed21 4 (4, 8) envelope_454), (placed21 1 (4, 4) envelope_455), (placed21 5 (10, 3) envelope_624)]
theorem common_sub_627_i6 : commonEnvelope childrenD_627_i6 ⊆ insert (5, 7) required_627_i6 := by decide +kernel
theorem child_required_sub_627_i6 : ∀ j, childrenC_627_i6 j ⊆ insert (5, 7) required_627_i6 := by decide +kernel
theorem child_envelope_sub_627_i6 : ∀ j, childrenD_627_i6 j ⊆ envelope_627_i6 := by decide +kernel
theorem pivot_mem_627_i6 : (5, 7) ∈ envelope_627_i6 := by decide +kernel
theorem children_work_627_i6 : ∀ j, Template HasSnaky 11 (childrenC_627_i6 j) (childrenD_627_i6 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_50 2 (6, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_97 2 (6, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_98 0 (5, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_454 4 (4, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_455 1 (4, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_624 5 (10, 3)).mono (by decide +kernel)
theorem row_works_627_i6 : Template HasSnaky 12 required_627_i6 envelope_627_i6 := by
  refine compose HasSnaky 11 childrenC_627_i6 childrenD_627_i6 children_work_627_i6 (5, 7)
    required_627_i6 envelope_627_i6 pivot_mem_627_i6 child_required_sub_627_i6 child_envelope_sub_627_i6 ?_
  intro b hb
  exact common_sub_627_i6 (mem_commonEnvelope childrenD_627_i6 b hb)
def required_627_i8 : Finset Cell := ⟨(([(3, 3), (5, 4), (5, 5), (5, 6), (6, 3), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_627_i8 : Finset Cell := ⟨(([(2, 3), (3, 3), (4, 2), (4, 3), (4, 5), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, 6), (7, 7), (8, 6), (9, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_627_i8 : Fin 2 → Finset Cell := ![(placed21 7 (6, 6) required_38), (placed21 0 (4, 2) required_413)]
def childrenD_627_i8 : Fin 2 → Finset Cell := ![(placed21 7 (6, 6) envelope_38), (placed21 0 (4, 2) envelope_413)]
theorem common_sub_627_i8 : commonEnvelope childrenD_627_i8 ⊆ insert (5, 3) required_627_i8 := by decide +kernel
theorem child_required_sub_627_i8 : ∀ j, childrenC_627_i8 j ⊆ insert (5, 3) required_627_i8 := by decide +kernel
theorem child_envelope_sub_627_i8 : ∀ j, childrenD_627_i8 j ⊆ envelope_627_i8 := by decide +kernel
theorem pivot_mem_627_i8 : (5, 3) ∈ envelope_627_i8 := by decide +kernel
theorem children_work_627_i8 : ∀ j, Template HasSnaky 5 (childrenC_627_i8 j) (childrenD_627_i8 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_38 7 (6, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_413 0 (4, 2)).mono (by decide +kernel)
theorem row_works_627_i8 : Template HasSnaky 6 required_627_i8 envelope_627_i8 := by
  refine compose HasSnaky 5 childrenC_627_i8 childrenD_627_i8 children_work_627_i8 (5, 3)
    required_627_i8 envelope_627_i8 pivot_mem_627_i8 child_required_sub_627_i8 child_envelope_sub_627_i8 ?_
  intro b hb
  exact common_sub_627_i8 (mem_commonEnvelope childrenD_627_i8 b hb)
def required_627_i7 : Finset Cell := ⟨(([(3, 3), (5, 4), (5, 6), (6, 3), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_627_i7 : Finset Cell := ⟨(([(2, 3), (3, 3), (4, 2), (4, 3), (4, 5), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, 6), (7, 7), (8, 6), (9, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_627_i7 : Fin 2 → Finset Cell := ![(placed21 3 (5, 7) required_0), required_627_i8]
def childrenD_627_i7 : Fin 2 → Finset Cell := ![(placed21 3 (5, 7) envelope_0), envelope_627_i8]
theorem common_sub_627_i7 : commonEnvelope childrenD_627_i7 ⊆ insert (5, 5) required_627_i7 := by decide +kernel
theorem child_required_sub_627_i7 : ∀ j, childrenC_627_i7 j ⊆ insert (5, 5) required_627_i7 := by decide +kernel
theorem child_envelope_sub_627_i7 : ∀ j, childrenD_627_i7 j ⊆ envelope_627_i7 := by decide +kernel
theorem pivot_mem_627_i7 : (5, 5) ∈ envelope_627_i7 := by decide +kernel
theorem children_work_627_i7 : ∀ j, Template HasSnaky 6 (childrenC_627_i7 j) (childrenD_627_i7 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 3 (5, 7)).mono (by decide +kernel)
  · exact row_works_627_i8.mono (by decide +kernel)
theorem row_works_627_i7 : Template HasSnaky 7 required_627_i7 envelope_627_i7 := by
  refine compose HasSnaky 6 childrenC_627_i7 childrenD_627_i7 children_work_627_i7 (5, 5)
    required_627_i7 envelope_627_i7 pivot_mem_627_i7 child_required_sub_627_i7 child_envelope_sub_627_i7 ?_
  intro b hb
  exact common_sub_627_i7 (mem_commonEnvelope childrenD_627_i7 b hb)
def required_627_i9 : Finset Cell := ⟨(([(5, 4), (5, 6), (6, 3), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_627_i9 : Finset Cell := ⟨(([(2, 5), (2, 6), (2, 7), (3, 5), (3, 6), (3, 7), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 2), (5, 3), (5, 4), (5, 6), (5, 7), (5, 8), (5, 9), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (8, 11), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (9, 10), (10, 5), (10, 6), (10, 7), (11, 5), (11, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_627_i9 : Fin 4 → Finset Cell := ![(placed21 5 (9, 3) required_59), (placed21 2 (6, 2) required_105), (placed21 3 (2, 7) required_323), (placed21 1 (2, 5) required_603)]
def childrenD_627_i9 : Fin 4 → Finset Cell := ![(placed21 5 (9, 3) envelope_59), (placed21 2 (6, 2) envelope_105), (placed21 3 (2, 7) envelope_323), (placed21 1 (2, 5) envelope_603)]
theorem common_sub_627_i9 : commonEnvelope childrenD_627_i9 ⊆ insert (6, 6) required_627_i9 := by decide +kernel
theorem child_required_sub_627_i9 : ∀ j, childrenC_627_i9 j ⊆ insert (6, 6) required_627_i9 := by decide +kernel
theorem child_envelope_sub_627_i9 : ∀ j, childrenD_627_i9 j ⊆ envelope_627_i9 := by decide +kernel
theorem pivot_mem_627_i9 : (6, 6) ∈ envelope_627_i9 := by decide +kernel
theorem children_work_627_i9 : ∀ j, Template HasSnaky 13 (childrenC_627_i9 j) (childrenD_627_i9 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_59 5 (9, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_105 2 (6, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_323 3 (2, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_603 1 (2, 5)).mono (by decide +kernel)
theorem row_works_627_i9 : Template HasSnaky 14 required_627_i9 envelope_627_i9 := by
  refine compose HasSnaky 13 childrenC_627_i9 childrenD_627_i9 children_work_627_i9 (6, 6)
    required_627_i9 envelope_627_i9 pivot_mem_627_i9 child_required_sub_627_i9 child_envelope_sub_627_i9 ?_
  intro b hb
  exact common_sub_627_i9 (mem_commonEnvelope childrenD_627_i9 b hb)
def required_627_i1 : Finset Cell := ⟨(([(3, 3), (5, 4), (6, 3), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_627_i1 : Finset Cell := ⟨(([(0, 5), (0, 7), (1, 5), (1, 6), (1, 7), (2, 3), (2, 5), (2, 6), (2, 7), (3, 3), (3, 5), (3, 6), (3, 7), (4, 1), (4, 2), (4, 3), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (7, 2), (7, 3), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (8, 11), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (9, 10), (10, 5), (10, 6), (10, 7), (11, 5), (11, 6), (11, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_627_i1 : Fin 6 → Finset Cell := ![required_627_i2, required_627_i4, required_627_i6, (placed21 1 (0, 1) required_626), required_627_i7, required_627_i9]
def childrenD_627_i1 : Fin 6 → Finset Cell := ![envelope_627_i2, envelope_627_i4, envelope_627_i6, (placed21 1 (0, 1) envelope_626), envelope_627_i7, envelope_627_i9]
theorem common_sub_627_i1 : commonEnvelope childrenD_627_i1 ⊆ insert (5, 6) required_627_i1 := by decide +kernel
theorem child_required_sub_627_i1 : ∀ j, childrenC_627_i1 j ⊆ insert (5, 6) required_627_i1 := by decide +kernel
theorem child_envelope_sub_627_i1 : ∀ j, childrenD_627_i1 j ⊆ envelope_627_i1 := by decide +kernel
theorem pivot_mem_627_i1 : (5, 6) ∈ envelope_627_i1 := by decide +kernel
theorem children_work_627_i1 : ∀ j, Template HasSnaky 14 (childrenC_627_i1 j) (childrenD_627_i1 j) := by
  intro j
  fin_cases j
  · exact row_works_627_i2.mono (by decide +kernel)
  · exact row_works_627_i4.mono (by decide +kernel)
  · exact row_works_627_i6.mono (by decide +kernel)
  · exact (placed21_template row_works_626 1 (0, 1)).mono (by decide +kernel)
  · exact row_works_627_i7.mono (by decide +kernel)
  · exact row_works_627_i9.mono (by decide +kernel)
theorem row_works_627_i1 : Template HasSnaky 15 required_627_i1 envelope_627_i1 := by
  refine compose HasSnaky 14 childrenC_627_i1 childrenD_627_i1 children_work_627_i1 (5, 6)
    required_627_i1 envelope_627_i1 pivot_mem_627_i1 child_required_sub_627_i1 child_envelope_sub_627_i1 ?_
  intro b hb
  exact common_sub_627_i1 (mem_commonEnvelope childrenD_627_i1 b hb)
def required_627 : Finset Cell := ⟨(([(3, 3), (3, 4), (6, 3), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_627 : Finset Cell := ⟨(([(0, 5), (0, 7), (1, 5), (1, 6), (1, 7), (2, 3), (2, 5), (2, 6), (2, 7), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (7, 2), (7, 3), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (8, 11), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (9, 10), (10, 5), (10, 6), (10, 7), (11, 5), (11, 6), (11, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_627 : Fin 4 → Finset Cell := ![(placed21 7 (7, 4) required_34), (placed21 0 (2, 2) required_478), required_627_i0, required_627_i1]
def childrenD_627 : Fin 4 → Finset Cell := ![(placed21 7 (7, 4) envelope_34), (placed21 0 (2, 2) envelope_478), envelope_627_i0, envelope_627_i1]
theorem common_sub_627 : commonEnvelope childrenD_627 ⊆ insert (5, 4) required_627 := by decide +kernel
theorem child_required_sub_627 : ∀ j, childrenC_627 j ⊆ insert (5, 4) required_627 := by decide +kernel
theorem child_envelope_sub_627 : ∀ j, childrenD_627 j ⊆ envelope_627 := by decide +kernel
theorem pivot_mem_627 : (5, 4) ∈ envelope_627 := by decide +kernel
theorem children_work_627 : ∀ j, Template HasSnaky 15 (childrenC_627 j) (childrenD_627 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_34 7 (7, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_478 0 (2, 2)).mono (by decide +kernel)
  · exact row_works_627_i0.mono (by decide +kernel)
  · exact row_works_627_i1.mono (by decide +kernel)
theorem row_works_627 : Template HasSnaky 16 required_627 envelope_627 := by
  refine compose HasSnaky 15 childrenC_627 childrenD_627 children_work_627 (5, 4)
    required_627 envelope_627 pivot_mem_627 child_required_sub_627 child_envelope_sub_627 ?_
  intro b hb
  exact common_sub_627 (mem_commonEnvelope childrenD_627 b hb)
def height_602_i1 : ℕ := 8
def childrenH_602_i1 : Fin 2 → ℕ := ![height_320, height_496]
theorem height_exact_602_i1 : height_602_i1 = 1 + Finset.univ.sup childrenH_602_i1 := by decide +kernel
theorem required_origin_602_i1 : ∀ x ∈ required_602_i1,
    (∃ j, x ∈ childrenC_602_i1 j) ∨ ∀ j, x ∈ childrenD_602_i1 j := by decide +kernel
theorem required_exact_602_i1 : required_602_i1 =
    ((Finset.univ.biUnion childrenC_602_i1) ∪ commonEnvelope childrenD_602_i1).erase (5, 8) := by
  exact required_eq_combination childrenC_602_i1 childrenD_602_i1 (5, 8) required_602_i1
    (by decide +kernel) child_required_sub_602_i1 common_sub_602_i1 required_origin_602_i1
theorem envelope_origin_602_i1 : ∀ x ∈ envelope_602_i1,
    x = (5, 8) ∨ ∃ j, x ∈ childrenD_602_i1 j := by decide +kernel
theorem envelope_exact_602_i1 : envelope_602_i1 =
    insert (5, 8) (Finset.univ.biUnion childrenD_602_i1) := by
  exact envelope_eq_combination childrenD_602_i1 (5, 8) envelope_602_i1
    pivot_mem_602_i1 child_envelope_sub_602_i1 envelope_origin_602_i1
def checked_602_i1 : CheckedCard where
  required := required_602_i1
  envelope := envelope_602_i1
  height := height_602_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_602_i1
def height_602_i0 : ℕ := 14
def childrenH_602_i0 : Fin 4 → ℕ := ![height_59, height_497, height_602_i1, height_555]
theorem height_exact_602_i0 : height_602_i0 = 1 + Finset.univ.sup childrenH_602_i0 := by decide +kernel
theorem required_origin_602_i0 : ∀ x ∈ required_602_i0,
    (∃ j, x ∈ childrenC_602_i0 j) ∨ ∀ j, x ∈ childrenD_602_i0 j := by decide +kernel
theorem required_exact_602_i0 : required_602_i0 =
    ((Finset.univ.biUnion childrenC_602_i0) ∪ commonEnvelope childrenD_602_i0).erase (6, 8) := by
  exact required_eq_combination childrenC_602_i0 childrenD_602_i0 (6, 8) required_602_i0
    (by decide +kernel) child_required_sub_602_i0 common_sub_602_i0 required_origin_602_i0
theorem envelope_origin_602_i0 : ∀ x ∈ envelope_602_i0,
    x = (6, 8) ∨ ∃ j, x ∈ childrenD_602_i0 j := by decide +kernel
theorem envelope_exact_602_i0 : envelope_602_i0 =
    insert (6, 8) (Finset.univ.biUnion childrenD_602_i0) := by
  exact envelope_eq_combination childrenD_602_i0 (6, 8) envelope_602_i0
    pivot_mem_602_i0 child_envelope_sub_602_i0 envelope_origin_602_i0
def checked_602_i0 : CheckedCard where
  required := required_602_i0
  envelope := envelope_602_i0
  height := height_602_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_602_i0
def height_602_i3 : ℕ := 11
def childrenH_602_i3 : Fin 2 → ℕ := ![height_2, height_545]
theorem height_exact_602_i3 : height_602_i3 = 1 + Finset.univ.sup childrenH_602_i3 := by decide +kernel
theorem required_origin_602_i3 : ∀ x ∈ required_602_i3,
    (∃ j, x ∈ childrenC_602_i3 j) ∨ ∀ j, x ∈ childrenD_602_i3 j := by decide +kernel
theorem required_exact_602_i3 : required_602_i3 =
    ((Finset.univ.biUnion childrenC_602_i3) ∪ commonEnvelope childrenD_602_i3).erase (6, 8) := by
  exact required_eq_combination childrenC_602_i3 childrenD_602_i3 (6, 8) required_602_i3
    (by decide +kernel) child_required_sub_602_i3 common_sub_602_i3 required_origin_602_i3
theorem envelope_origin_602_i3 : ∀ x ∈ envelope_602_i3,
    x = (6, 8) ∨ ∃ j, x ∈ childrenD_602_i3 j := by decide +kernel
theorem envelope_exact_602_i3 : envelope_602_i3 =
    insert (6, 8) (Finset.univ.biUnion childrenD_602_i3) := by
  exact envelope_eq_combination childrenD_602_i3 (6, 8) envelope_602_i3
    pivot_mem_602_i3 child_envelope_sub_602_i3 envelope_origin_602_i3
def checked_602_i3 : CheckedCard where
  required := required_602_i3
  envelope := envelope_602_i3
  height := height_602_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_602_i3
def height_602_i2 : ℕ := 12
def childrenH_602_i2 : Fin 4 → ℕ := ![height_107, height_163, height_556, height_602_i3]
theorem height_exact_602_i2 : height_602_i2 = 1 + Finset.univ.sup childrenH_602_i2 := by decide +kernel
theorem required_origin_602_i2 : ∀ x ∈ required_602_i2,
    (∃ j, x ∈ childrenC_602_i2 j) ∨ ∀ j, x ∈ childrenD_602_i2 j := by decide +kernel
theorem required_exact_602_i2 : required_602_i2 =
    ((Finset.univ.biUnion childrenC_602_i2) ∪ commonEnvelope childrenD_602_i2).erase (7, 7) := by
  exact required_eq_combination childrenC_602_i2 childrenD_602_i2 (7, 7) required_602_i2
    (by decide +kernel) child_required_sub_602_i2 common_sub_602_i2 required_origin_602_i2
theorem envelope_origin_602_i2 : ∀ x ∈ envelope_602_i2,
    x = (7, 7) ∨ ∃ j, x ∈ childrenD_602_i2 j := by decide +kernel
theorem envelope_exact_602_i2 : envelope_602_i2 =
    insert (7, 7) (Finset.univ.biUnion childrenD_602_i2) := by
  exact envelope_eq_combination childrenD_602_i2 (7, 7) envelope_602_i2
    pivot_mem_602_i2 child_envelope_sub_602_i2 envelope_origin_602_i2
def checked_602_i2 : CheckedCard where
  required := required_602_i2
  envelope := envelope_602_i2
  height := height_602_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_602_i2
def height_602_i6 : ℕ := 6
def childrenH_602_i6 : Fin 2 → ℕ := ![height_157, height_383]
theorem height_exact_602_i6 : height_602_i6 = 1 + Finset.univ.sup childrenH_602_i6 := by decide +kernel
theorem required_origin_602_i6 : ∀ x ∈ required_602_i6,
    (∃ j, x ∈ childrenC_602_i6 j) ∨ ∀ j, x ∈ childrenD_602_i6 j := by decide +kernel
theorem required_exact_602_i6 : required_602_i6 =
    ((Finset.univ.biUnion childrenC_602_i6) ∪ commonEnvelope childrenD_602_i6).erase (6, 5) := by
  exact required_eq_combination childrenC_602_i6 childrenD_602_i6 (6, 5) required_602_i6
    (by decide +kernel) child_required_sub_602_i6 common_sub_602_i6 required_origin_602_i6
theorem envelope_origin_602_i6 : ∀ x ∈ envelope_602_i6,
    x = (6, 5) ∨ ∃ j, x ∈ childrenD_602_i6 j := by decide +kernel
theorem envelope_exact_602_i6 : envelope_602_i6 =
    insert (6, 5) (Finset.univ.biUnion childrenD_602_i6) := by
  exact envelope_eq_combination childrenD_602_i6 (6, 5) envelope_602_i6
    pivot_mem_602_i6 child_envelope_sub_602_i6 envelope_origin_602_i6
def checked_602_i6 : CheckedCard where
  required := required_602_i6
  envelope := envelope_602_i6
  height := height_602_i6
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_602_i6
def height_602_i7 : ℕ := 5
def childrenH_602_i7 : Fin 2 → ℕ := ![height_18, height_381]
theorem height_exact_602_i7 : height_602_i7 = 1 + Finset.univ.sup childrenH_602_i7 := by decide +kernel
theorem required_origin_602_i7 : ∀ x ∈ required_602_i7,
    (∃ j, x ∈ childrenC_602_i7 j) ∨ ∀ j, x ∈ childrenD_602_i7 j := by decide +kernel
theorem required_exact_602_i7 : required_602_i7 =
    ((Finset.univ.biUnion childrenC_602_i7) ∪ commonEnvelope childrenD_602_i7).erase (6, 6) := by
  exact required_eq_combination childrenC_602_i7 childrenD_602_i7 (6, 6) required_602_i7
    (by decide +kernel) child_required_sub_602_i7 common_sub_602_i7 required_origin_602_i7
theorem envelope_origin_602_i7 : ∀ x ∈ envelope_602_i7,
    x = (6, 6) ∨ ∃ j, x ∈ childrenD_602_i7 j := by decide +kernel
theorem envelope_exact_602_i7 : envelope_602_i7 =
    insert (6, 6) (Finset.univ.biUnion childrenD_602_i7) := by
  exact envelope_eq_combination childrenD_602_i7 (6, 6) envelope_602_i7
    pivot_mem_602_i7 child_envelope_sub_602_i7 envelope_origin_602_i7
def checked_602_i7 : CheckedCard where
  required := required_602_i7
  envelope := envelope_602_i7
  height := height_602_i7
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_602_i7
def height_602_i8 : ℕ := 5
def childrenH_602_i8 : Fin 2 → ℕ := ![height_64, height_500]
theorem height_exact_602_i8 : height_602_i8 = 1 + Finset.univ.sup childrenH_602_i8 := by decide +kernel
theorem required_origin_602_i8 : ∀ x ∈ required_602_i8,
    (∃ j, x ∈ childrenC_602_i8 j) ∨ ∀ j, x ∈ childrenD_602_i8 j := by decide +kernel
theorem required_exact_602_i8 : required_602_i8 =
    ((Finset.univ.biUnion childrenC_602_i8) ∪ commonEnvelope childrenD_602_i8).erase (5, 7) := by
  exact required_eq_combination childrenC_602_i8 childrenD_602_i8 (5, 7) required_602_i8
    (by decide +kernel) child_required_sub_602_i8 common_sub_602_i8 required_origin_602_i8
theorem envelope_origin_602_i8 : ∀ x ∈ envelope_602_i8,
    x = (5, 7) ∨ ∃ j, x ∈ childrenD_602_i8 j := by decide +kernel
theorem envelope_exact_602_i8 : envelope_602_i8 =
    insert (5, 7) (Finset.univ.biUnion childrenD_602_i8) := by
  exact envelope_eq_combination childrenD_602_i8 (5, 7) envelope_602_i8
    pivot_mem_602_i8 child_envelope_sub_602_i8 envelope_origin_602_i8
def checked_602_i8 : CheckedCard where
  required := required_602_i8
  envelope := envelope_602_i8
  height := height_602_i8
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_602_i8
def height_602_i5 : ℕ := 12
def childrenH_602_i5 : Fin 4 → ℕ := ![height_602_i6, height_602_i7, height_602_i8, height_601]
theorem height_exact_602_i5 : height_602_i5 = 1 + Finset.univ.sup childrenH_602_i5 := by decide +kernel
theorem required_origin_602_i5 : ∀ x ∈ required_602_i5,
    (∃ j, x ∈ childrenC_602_i5 j) ∨ ∀ j, x ∈ childrenD_602_i5 j := by decide +kernel
theorem required_exact_602_i5 : required_602_i5 =
    ((Finset.univ.biUnion childrenC_602_i5) ∪ commonEnvelope childrenD_602_i5).erase (5, 5) := by
  exact required_eq_combination childrenC_602_i5 childrenD_602_i5 (5, 5) required_602_i5
    (by decide +kernel) child_required_sub_602_i5 common_sub_602_i5 required_origin_602_i5
theorem envelope_origin_602_i5 : ∀ x ∈ envelope_602_i5,
    x = (5, 5) ∨ ∃ j, x ∈ childrenD_602_i5 j := by decide +kernel
theorem envelope_exact_602_i5 : envelope_602_i5 =
    insert (5, 5) (Finset.univ.biUnion childrenD_602_i5) := by
  exact envelope_eq_combination childrenD_602_i5 (5, 5) envelope_602_i5
    pivot_mem_602_i5 child_envelope_sub_602_i5 envelope_origin_602_i5
def checked_602_i5 : CheckedCard where
  required := required_602_i5
  envelope := envelope_602_i5
  height := height_602_i5
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_602_i5
def height_602_i4 : ℕ := 13
def childrenH_602_i4 : Fin 4 → ℕ := ![height_119, height_497, height_498, height_602_i5]
theorem height_exact_602_i4 : height_602_i4 = 1 + Finset.univ.sup childrenH_602_i4 := by decide +kernel
theorem required_origin_602_i4 : ∀ x ∈ required_602_i4,
    (∃ j, x ∈ childrenC_602_i4 j) ∨ ∀ j, x ∈ childrenD_602_i4 j := by decide +kernel
theorem required_exact_602_i4 : required_602_i4 =
    ((Finset.univ.biUnion childrenC_602_i4) ∪ commonEnvelope childrenD_602_i4).erase (6, 8) := by
  exact required_eq_combination childrenC_602_i4 childrenD_602_i4 (6, 8) required_602_i4
    (by decide +kernel) child_required_sub_602_i4 common_sub_602_i4 required_origin_602_i4
theorem envelope_origin_602_i4 : ∀ x ∈ envelope_602_i4,
    x = (6, 8) ∨ ∃ j, x ∈ childrenD_602_i4 j := by decide +kernel
theorem envelope_exact_602_i4 : envelope_602_i4 =
    insert (6, 8) (Finset.univ.biUnion childrenD_602_i4) := by
  exact envelope_eq_combination childrenD_602_i4 (6, 8) envelope_602_i4
    pivot_mem_602_i4 child_envelope_sub_602_i4 envelope_origin_602_i4
def checked_602_i4 : CheckedCard where
  required := required_602_i4
  envelope := envelope_602_i4
  height := height_602_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_602_i4
def height_602 : ℕ := 16
def childrenH_602 : Fin 12 → ℕ := ![height_553, height_602_i0, height_602_i2, height_557, height_564, height_568, height_573, height_574, height_583, height_598, height_599, height_602_i4]
theorem height_exact_602 : height_602 = 1 + Finset.univ.sup childrenH_602 := by decide +kernel
theorem required_origin_602 : ∀ x ∈ required_602,
    (∃ j, x ∈ childrenC_602 j) ∨ ∀ j, x ∈ childrenD_602 j := by decide +kernel
theorem required_exact_602 : required_602 =
    ((Finset.univ.biUnion childrenC_602) ∪ commonEnvelope childrenD_602).erase (6, 7) := by
  exact required_eq_combination childrenC_602 childrenD_602 (6, 7) required_602
    (by decide +kernel) child_required_sub_602 common_sub_602 required_origin_602
theorem envelope_origin_602 : ∀ x ∈ envelope_602,
    x = (6, 7) ∨ ∃ j, x ∈ childrenD_602 j := by decide +kernel
theorem envelope_exact_602 : envelope_602 =
    insert (6, 7) (Finset.univ.biUnion childrenD_602) := by
  exact envelope_eq_combination childrenD_602 (6, 7) envelope_602
    pivot_mem_602 child_envelope_sub_602 envelope_origin_602
def checked_602 : CheckedCard where
  required := required_602
  envelope := envelope_602
  height := height_602
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_602
def height_627_i0 : ℕ := 8
def childrenH_627_i0 : Fin 2 → ℕ := ![height_5, height_472]
theorem height_exact_627_i0 : height_627_i0 = 1 + Finset.univ.sup childrenH_627_i0 := by decide +kernel
theorem required_origin_627_i0 : ∀ x ∈ required_627_i0,
    (∃ j, x ∈ childrenC_627_i0 j) ∨ ∀ j, x ∈ childrenD_627_i0 j := by decide +kernel
theorem required_exact_627_i0 : required_627_i0 =
    ((Finset.univ.biUnion childrenC_627_i0) ∪ commonEnvelope childrenD_627_i0).erase (4, 4) := by
  exact required_eq_combination childrenC_627_i0 childrenD_627_i0 (4, 4) required_627_i0
    (by decide +kernel) child_required_sub_627_i0 common_sub_627_i0 required_origin_627_i0
theorem envelope_origin_627_i0 : ∀ x ∈ envelope_627_i0,
    x = (4, 4) ∨ ∃ j, x ∈ childrenD_627_i0 j := by decide +kernel
theorem envelope_exact_627_i0 : envelope_627_i0 =
    insert (4, 4) (Finset.univ.biUnion childrenD_627_i0) := by
  exact envelope_eq_combination childrenD_627_i0 (4, 4) envelope_627_i0
    pivot_mem_627_i0 child_envelope_sub_627_i0 envelope_origin_627_i0
def checked_627_i0 : CheckedCard where
  required := required_627_i0
  envelope := envelope_627_i0
  height := height_627_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_627_i0
def height_627_i3 : ℕ := 4
def childrenH_627_i3 : Fin 2 → ℕ := ![height_38, height_205]
theorem height_exact_627_i3 : height_627_i3 = 1 + Finset.univ.sup childrenH_627_i3 := by decide +kernel
theorem required_origin_627_i3 : ∀ x ∈ required_627_i3,
    (∃ j, x ∈ childrenC_627_i3 j) ∨ ∀ j, x ∈ childrenD_627_i3 j := by decide +kernel
theorem required_exact_627_i3 : required_627_i3 =
    ((Finset.univ.biUnion childrenC_627_i3) ∪ commonEnvelope childrenD_627_i3).erase (5, 3) := by
  exact required_eq_combination childrenC_627_i3 childrenD_627_i3 (5, 3) required_627_i3
    (by decide +kernel) child_required_sub_627_i3 common_sub_627_i3 required_origin_627_i3
theorem envelope_origin_627_i3 : ∀ x ∈ envelope_627_i3,
    x = (5, 3) ∨ ∃ j, x ∈ childrenD_627_i3 j := by decide +kernel
theorem envelope_exact_627_i3 : envelope_627_i3 =
    insert (5, 3) (Finset.univ.biUnion childrenD_627_i3) := by
  exact envelope_eq_combination childrenD_627_i3 (5, 3) envelope_627_i3
    pivot_mem_627_i3 child_envelope_sub_627_i3 envelope_origin_627_i3
def checked_627_i3 : CheckedCard where
  required := required_627_i3
  envelope := envelope_627_i3
  height := height_627_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_627_i3
def height_627_i2 : ℕ := 5
def childrenH_627_i2 : Fin 2 → ℕ := ![height_0, height_627_i3]
theorem height_exact_627_i2 : height_627_i2 = 1 + Finset.univ.sup childrenH_627_i2 := by decide +kernel
theorem required_origin_627_i2 : ∀ x ∈ required_627_i2,
    (∃ j, x ∈ childrenC_627_i2 j) ∨ ∀ j, x ∈ childrenD_627_i2 j := by decide +kernel
theorem required_exact_627_i2 : required_627_i2 =
    ((Finset.univ.biUnion childrenC_627_i2) ∪ commonEnvelope childrenD_627_i2).erase (5, 5) := by
  exact required_eq_combination childrenC_627_i2 childrenD_627_i2 (5, 5) required_627_i2
    (by decide +kernel) child_required_sub_627_i2 common_sub_627_i2 required_origin_627_i2
theorem envelope_origin_627_i2 : ∀ x ∈ envelope_627_i2,
    x = (5, 5) ∨ ∃ j, x ∈ childrenD_627_i2 j := by decide +kernel
theorem envelope_exact_627_i2 : envelope_627_i2 =
    insert (5, 5) (Finset.univ.biUnion childrenD_627_i2) := by
  exact envelope_eq_combination childrenD_627_i2 (5, 5) envelope_627_i2
    pivot_mem_627_i2 child_envelope_sub_627_i2 envelope_origin_627_i2
def checked_627_i2 : CheckedCard where
  required := required_627_i2
  envelope := envelope_627_i2
  height := height_627_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_627_i2
def height_627_i5 : ℕ := 6
def childrenH_627_i5 : Fin 2 → ℕ := ![height_38, height_179]
theorem height_exact_627_i5 : height_627_i5 = 1 + Finset.univ.sup childrenH_627_i5 := by decide +kernel
theorem required_origin_627_i5 : ∀ x ∈ required_627_i5,
    (∃ j, x ∈ childrenC_627_i5 j) ∨ ∀ j, x ∈ childrenD_627_i5 j := by decide +kernel
theorem required_exact_627_i5 : required_627_i5 =
    ((Finset.univ.biUnion childrenC_627_i5) ∪ commonEnvelope childrenD_627_i5).erase (5, 3) := by
  exact required_eq_combination childrenC_627_i5 childrenD_627_i5 (5, 3) required_627_i5
    (by decide +kernel) child_required_sub_627_i5 common_sub_627_i5 required_origin_627_i5
theorem envelope_origin_627_i5 : ∀ x ∈ envelope_627_i5,
    x = (5, 3) ∨ ∃ j, x ∈ childrenD_627_i5 j := by decide +kernel
theorem envelope_exact_627_i5 : envelope_627_i5 =
    insert (5, 3) (Finset.univ.biUnion childrenD_627_i5) := by
  exact envelope_eq_combination childrenD_627_i5 (5, 3) envelope_627_i5
    pivot_mem_627_i5 child_envelope_sub_627_i5 envelope_origin_627_i5
def checked_627_i5 : CheckedCard where
  required := required_627_i5
  envelope := envelope_627_i5
  height := height_627_i5
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_627_i5
def height_627_i4 : ℕ := 7
def childrenH_627_i4 : Fin 2 → ℕ := ![height_0, height_627_i5]
theorem height_exact_627_i4 : height_627_i4 = 1 + Finset.univ.sup childrenH_627_i4 := by decide +kernel
theorem required_origin_627_i4 : ∀ x ∈ required_627_i4,
    (∃ j, x ∈ childrenC_627_i4 j) ∨ ∀ j, x ∈ childrenD_627_i4 j := by decide +kernel
theorem required_exact_627_i4 : required_627_i4 =
    ((Finset.univ.biUnion childrenC_627_i4) ∪ commonEnvelope childrenD_627_i4).erase (5, 5) := by
  exact required_eq_combination childrenC_627_i4 childrenD_627_i4 (5, 5) required_627_i4
    (by decide +kernel) child_required_sub_627_i4 common_sub_627_i4 required_origin_627_i4
theorem envelope_origin_627_i4 : ∀ x ∈ envelope_627_i4,
    x = (5, 5) ∨ ∃ j, x ∈ childrenD_627_i4 j := by decide +kernel
theorem envelope_exact_627_i4 : envelope_627_i4 =
    insert (5, 5) (Finset.univ.biUnion childrenD_627_i4) := by
  exact envelope_eq_combination childrenD_627_i4 (5, 5) envelope_627_i4
    pivot_mem_627_i4 child_envelope_sub_627_i4 envelope_origin_627_i4
def checked_627_i4 : CheckedCard where
  required := required_627_i4
  envelope := envelope_627_i4
  height := height_627_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_627_i4
def height_627_i6 : ℕ := 12
def childrenH_627_i6 : Fin 6 → ℕ := ![height_50, height_97, height_98, height_454, height_455, height_624]
theorem height_exact_627_i6 : height_627_i6 = 1 + Finset.univ.sup childrenH_627_i6 := by decide +kernel
theorem required_origin_627_i6 : ∀ x ∈ required_627_i6,
    (∃ j, x ∈ childrenC_627_i6 j) ∨ ∀ j, x ∈ childrenD_627_i6 j := by decide +kernel
theorem required_exact_627_i6 : required_627_i6 =
    ((Finset.univ.biUnion childrenC_627_i6) ∪ commonEnvelope childrenD_627_i6).erase (5, 7) := by
  exact required_eq_combination childrenC_627_i6 childrenD_627_i6 (5, 7) required_627_i6
    (by decide +kernel) child_required_sub_627_i6 common_sub_627_i6 required_origin_627_i6
theorem envelope_origin_627_i6 : ∀ x ∈ envelope_627_i6,
    x = (5, 7) ∨ ∃ j, x ∈ childrenD_627_i6 j := by decide +kernel
theorem envelope_exact_627_i6 : envelope_627_i6 =
    insert (5, 7) (Finset.univ.biUnion childrenD_627_i6) := by
  exact envelope_eq_combination childrenD_627_i6 (5, 7) envelope_627_i6
    pivot_mem_627_i6 child_envelope_sub_627_i6 envelope_origin_627_i6
def checked_627_i6 : CheckedCard where
  required := required_627_i6
  envelope := envelope_627_i6
  height := height_627_i6
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_627_i6
def height_627_i8 : ℕ := 6
def childrenH_627_i8 : Fin 2 → ℕ := ![height_38, height_413]
theorem height_exact_627_i8 : height_627_i8 = 1 + Finset.univ.sup childrenH_627_i8 := by decide +kernel
theorem required_origin_627_i8 : ∀ x ∈ required_627_i8,
    (∃ j, x ∈ childrenC_627_i8 j) ∨ ∀ j, x ∈ childrenD_627_i8 j := by decide +kernel
theorem required_exact_627_i8 : required_627_i8 =
    ((Finset.univ.biUnion childrenC_627_i8) ∪ commonEnvelope childrenD_627_i8).erase (5, 3) := by
  exact required_eq_combination childrenC_627_i8 childrenD_627_i8 (5, 3) required_627_i8
    (by decide +kernel) child_required_sub_627_i8 common_sub_627_i8 required_origin_627_i8
theorem envelope_origin_627_i8 : ∀ x ∈ envelope_627_i8,
    x = (5, 3) ∨ ∃ j, x ∈ childrenD_627_i8 j := by decide +kernel
theorem envelope_exact_627_i8 : envelope_627_i8 =
    insert (5, 3) (Finset.univ.biUnion childrenD_627_i8) := by
  exact envelope_eq_combination childrenD_627_i8 (5, 3) envelope_627_i8
    pivot_mem_627_i8 child_envelope_sub_627_i8 envelope_origin_627_i8
def checked_627_i8 : CheckedCard where
  required := required_627_i8
  envelope := envelope_627_i8
  height := height_627_i8
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_627_i8
def height_627_i7 : ℕ := 7
def childrenH_627_i7 : Fin 2 → ℕ := ![height_0, height_627_i8]
theorem height_exact_627_i7 : height_627_i7 = 1 + Finset.univ.sup childrenH_627_i7 := by decide +kernel
theorem required_origin_627_i7 : ∀ x ∈ required_627_i7,
    (∃ j, x ∈ childrenC_627_i7 j) ∨ ∀ j, x ∈ childrenD_627_i7 j := by decide +kernel
theorem required_exact_627_i7 : required_627_i7 =
    ((Finset.univ.biUnion childrenC_627_i7) ∪ commonEnvelope childrenD_627_i7).erase (5, 5) := by
  exact required_eq_combination childrenC_627_i7 childrenD_627_i7 (5, 5) required_627_i7
    (by decide +kernel) child_required_sub_627_i7 common_sub_627_i7 required_origin_627_i7
theorem envelope_origin_627_i7 : ∀ x ∈ envelope_627_i7,
    x = (5, 5) ∨ ∃ j, x ∈ childrenD_627_i7 j := by decide +kernel
theorem envelope_exact_627_i7 : envelope_627_i7 =
    insert (5, 5) (Finset.univ.biUnion childrenD_627_i7) := by
  exact envelope_eq_combination childrenD_627_i7 (5, 5) envelope_627_i7
    pivot_mem_627_i7 child_envelope_sub_627_i7 envelope_origin_627_i7
def checked_627_i7 : CheckedCard where
  required := required_627_i7
  envelope := envelope_627_i7
  height := height_627_i7
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_627_i7
def height_627_i9 : ℕ := 14
def childrenH_627_i9 : Fin 4 → ℕ := ![height_59, height_105, height_323, height_603]
theorem height_exact_627_i9 : height_627_i9 = 1 + Finset.univ.sup childrenH_627_i9 := by decide +kernel
theorem required_origin_627_i9 : ∀ x ∈ required_627_i9,
    (∃ j, x ∈ childrenC_627_i9 j) ∨ ∀ j, x ∈ childrenD_627_i9 j := by decide +kernel
theorem required_exact_627_i9 : required_627_i9 =
    ((Finset.univ.biUnion childrenC_627_i9) ∪ commonEnvelope childrenD_627_i9).erase (6, 6) := by
  exact required_eq_combination childrenC_627_i9 childrenD_627_i9 (6, 6) required_627_i9
    (by decide +kernel) child_required_sub_627_i9 common_sub_627_i9 required_origin_627_i9
theorem envelope_origin_627_i9 : ∀ x ∈ envelope_627_i9,
    x = (6, 6) ∨ ∃ j, x ∈ childrenD_627_i9 j := by decide +kernel
theorem envelope_exact_627_i9 : envelope_627_i9 =
    insert (6, 6) (Finset.univ.biUnion childrenD_627_i9) := by
  exact envelope_eq_combination childrenD_627_i9 (6, 6) envelope_627_i9
    pivot_mem_627_i9 child_envelope_sub_627_i9 envelope_origin_627_i9
def checked_627_i9 : CheckedCard where
  required := required_627_i9
  envelope := envelope_627_i9
  height := height_627_i9
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_627_i9
def height_627_i1 : ℕ := 15
def childrenH_627_i1 : Fin 6 → ℕ := ![height_627_i2, height_627_i4, height_627_i6, height_626, height_627_i7, height_627_i9]
theorem height_exact_627_i1 : height_627_i1 = 1 + Finset.univ.sup childrenH_627_i1 := by decide +kernel
theorem required_origin_627_i1 : ∀ x ∈ required_627_i1,
    (∃ j, x ∈ childrenC_627_i1 j) ∨ ∀ j, x ∈ childrenD_627_i1 j := by decide +kernel
theorem required_exact_627_i1 : required_627_i1 =
    ((Finset.univ.biUnion childrenC_627_i1) ∪ commonEnvelope childrenD_627_i1).erase (5, 6) := by
  exact required_eq_combination childrenC_627_i1 childrenD_627_i1 (5, 6) required_627_i1
    (by decide +kernel) child_required_sub_627_i1 common_sub_627_i1 required_origin_627_i1
theorem envelope_origin_627_i1 : ∀ x ∈ envelope_627_i1,
    x = (5, 6) ∨ ∃ j, x ∈ childrenD_627_i1 j := by decide +kernel
theorem envelope_exact_627_i1 : envelope_627_i1 =
    insert (5, 6) (Finset.univ.biUnion childrenD_627_i1) := by
  exact envelope_eq_combination childrenD_627_i1 (5, 6) envelope_627_i1
    pivot_mem_627_i1 child_envelope_sub_627_i1 envelope_origin_627_i1
def checked_627_i1 : CheckedCard where
  required := required_627_i1
  envelope := envelope_627_i1
  height := height_627_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_627_i1
def height_627 : ℕ := 16
def childrenH_627 : Fin 4 → ℕ := ![height_34, height_478, height_627_i0, height_627_i1]
theorem height_exact_627 : height_627 = 1 + Finset.univ.sup childrenH_627 := by decide +kernel
theorem required_origin_627 : ∀ x ∈ required_627,
    (∃ j, x ∈ childrenC_627 j) ∨ ∀ j, x ∈ childrenD_627 j := by decide +kernel
theorem required_exact_627 : required_627 =
    ((Finset.univ.biUnion childrenC_627) ∪ commonEnvelope childrenD_627).erase (5, 4) := by
  exact required_eq_combination childrenC_627 childrenD_627 (5, 4) required_627
    (by decide +kernel) child_required_sub_627 common_sub_627 required_origin_627
theorem envelope_origin_627 : ∀ x ∈ envelope_627,
    x = (5, 4) ∨ ∃ j, x ∈ childrenD_627 j := by decide +kernel
theorem envelope_exact_627 : envelope_627 =
    insert (5, 4) (Finset.univ.biUnion childrenD_627) := by
  exact envelope_eq_combination childrenD_627 (5, 4) envelope_627
    pivot_mem_627 child_envelope_sub_627 envelope_origin_627
def checked_627 : CheckedCard where
  required := required_627
  envelope := envelope_627
  height := height_627
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_627
end SnakyPrototype.Certificate21

end OAI
