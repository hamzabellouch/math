import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part06
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part06
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part06
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height10Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height11Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height13Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height13Part05
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_697_i4 : Finset Cell := ⟨(([(2, 3), (3, 3), (4, 3), (5, 3), (6, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_697_i4 : Finset Cell := ⟨(([(0, 2), (1, 2), (1, 3), (2, 2), (2, 3), (3, 3), (4, 2), (4, 3), (5, 2), (5, 3), (5, 4), (6, 3), (6, 4), (6, 5), (6, 6), (7, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_697_i4 : Fin 2 → Finset Cell := ![(placed21 7 (5, 3) required_16), (placed21 0 (2, 2) required_374)]
def childrenD_697_i4 : Fin 2 → Finset Cell := ![(placed21 7 (5, 3) envelope_16), (placed21 0 (2, 2) envelope_374)]
theorem common_sub_697_i4 : commonEnvelope childrenD_697_i4 ⊆ insert (5, 2) required_697_i4 := by decide +kernel
theorem child_required_sub_697_i4 : ∀ j, childrenC_697_i4 j ⊆ insert (5, 2) required_697_i4 := by decide +kernel
theorem child_envelope_sub_697_i4 : ∀ j, childrenD_697_i4 j ⊆ envelope_697_i4 := by decide +kernel
theorem pivot_mem_697_i4 : (5, 2) ∈ envelope_697_i4 := by decide +kernel
theorem children_work_697_i4 : ∀ j, Template HasSnaky 3 (childrenC_697_i4 j) (childrenD_697_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_16 7 (5, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_374 0 (2, 2)).mono (by decide +kernel)
theorem row_works_697_i4 : Template HasSnaky 4 required_697_i4 envelope_697_i4 := by
  refine compose HasSnaky 3 childrenC_697_i4 childrenD_697_i4 children_work_697_i4 (5, 2)
    required_697_i4 envelope_697_i4 pivot_mem_697_i4 child_required_sub_697_i4 child_envelope_sub_697_i4 ?_
  intro b hb
  exact common_sub_697_i4 (mem_commonEnvelope childrenD_697_i4 b hb)
def required_697_i3 : Finset Cell := ⟨(([(2, 3), (3, 3), (3, 6), (4, 3), (5, 3), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_697_i3 : Finset Cell := ⟨(([(0, 2), (0, 5), (0, 7), (1, 2), (1, 3), (1, 5), (1, 6), (1, 7), (2, 2), (2, 3), (2, 5), (2, 6), (2, 7), (3, 3), (3, 6), (3, 7), (4, 2), (4, 3), (4, 6), (4, 7), (5, 2), (5, 3), (5, 4), (5, 6), (5, 7), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, 4), (7, 5), (7, 6), (7, 7), (8, 5), (8, 6), (8, 7), (9, 5), (9, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_697_i3 : Fin 2 → Finset Cell := ![(placed21 7 (9, 7) required_95), required_697_i4]
def childrenD_697_i3 : Fin 2 → Finset Cell := ![(placed21 7 (9, 7) envelope_95), envelope_697_i4]
theorem common_sub_697_i3 : commonEnvelope childrenD_697_i3 ⊆ insert (6, 6) required_697_i3 := by decide +kernel
theorem child_required_sub_697_i3 : ∀ j, childrenC_697_i3 j ⊆ insert (6, 6) required_697_i3 := by decide +kernel
theorem child_envelope_sub_697_i3 : ∀ j, childrenD_697_i3 j ⊆ envelope_697_i3 := by decide +kernel
theorem pivot_mem_697_i3 : (6, 6) ∈ envelope_697_i3 := by decide +kernel
theorem children_work_697_i3 : ∀ j, Template HasSnaky 6 (childrenC_697_i3 j) (childrenD_697_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_95 7 (9, 7)).mono (by decide +kernel)
  · exact row_works_697_i4.mono (by decide +kernel)
theorem row_works_697_i3 : Template HasSnaky 7 required_697_i3 envelope_697_i3 := by
  refine compose HasSnaky 6 childrenC_697_i3 childrenD_697_i3 children_work_697_i3 (6, 6)
    required_697_i3 envelope_697_i3 pivot_mem_697_i3 child_required_sub_697_i3 child_envelope_sub_697_i3 ?_
  intro b hb
  exact common_sub_697_i3 (mem_commonEnvelope childrenD_697_i3 b hb)
def required_697_i2 : Finset Cell := ⟨(([(2, 3), (3, 3), (3, 6), (4, 3), (5, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_697_i2 : Finset Cell := ⟨(([(0, 2), (0, 5), (0, 7), (1, 2), (1, 3), (1, 5), (1, 6), (1, 7), (2, 2), (2, 3), (2, 5), (2, 6), (2, 7), (3, 3), (3, 6), (3, 7), (3, 8), (4, 2), (4, 3), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, 5), (8, 6), (8, 7), (9, 5), (9, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_697_i2 : Fin 3 → Finset Cell := ![(placed21 7 (6, 6) required_151), (placed21 5 (8, 5) required_460), required_697_i3]
def childrenD_697_i2 : Fin 3 → Finset Cell := ![(placed21 7 (6, 6) envelope_151), (placed21 5 (8, 5) envelope_460), envelope_697_i3]
theorem common_sub_697_i2 : commonEnvelope childrenD_697_i2 ⊆ insert (5, 6) required_697_i2 := by decide +kernel
theorem child_required_sub_697_i2 : ∀ j, childrenC_697_i2 j ⊆ insert (5, 6) required_697_i2 := by decide +kernel
theorem child_envelope_sub_697_i2 : ∀ j, childrenD_697_i2 j ⊆ envelope_697_i2 := by decide +kernel
theorem pivot_mem_697_i2 : (5, 6) ∈ envelope_697_i2 := by decide +kernel
theorem children_work_697_i2 : ∀ j, Template HasSnaky 10 (childrenC_697_i2 j) (childrenD_697_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_151 7 (6, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_460 5 (8, 5)).mono (by decide +kernel)
  · exact row_works_697_i3.mono (by decide +kernel)
theorem row_works_697_i2 : Template HasSnaky 11 required_697_i2 envelope_697_i2 := by
  refine compose HasSnaky 10 childrenC_697_i2 childrenD_697_i2 children_work_697_i2 (5, 6)
    required_697_i2 envelope_697_i2 pivot_mem_697_i2 child_required_sub_697_i2 child_envelope_sub_697_i2 ?_
  intro b hb
  exact common_sub_697_i2 (mem_commonEnvelope childrenD_697_i2 b hb)
def required_697_i1 : Finset Cell := ⟨(([(2, 3), (3, 3), (3, 4), (4, 3), (5, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_697_i1 : Finset Cell := ⟨(([(0, 2), (0, 5), (0, 7), (1, 2), (1, 3), (1, 5), (1, 6), (1, 7), (2, 2), (2, 3), (2, 5), (2, 6), (2, 7), (2, 8), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 2), (4, 3), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, 5), (8, 6), (8, 7), (9, 5), (9, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_697_i1 : Fin 3 → Finset Cell := ![(placed21 2 (4, 2) required_39), (placed21 2 (5, 2) required_121), required_697_i2]
def childrenD_697_i1 : Fin 3 → Finset Cell := ![(placed21 2 (4, 2) envelope_39), (placed21 2 (5, 2) envelope_121), envelope_697_i2]
theorem common_sub_697_i1 : commonEnvelope childrenD_697_i1 ⊆ insert (3, 6) required_697_i1 := by decide +kernel
theorem child_required_sub_697_i1 : ∀ j, childrenC_697_i1 j ⊆ insert (3, 6) required_697_i1 := by decide +kernel
theorem child_envelope_sub_697_i1 : ∀ j, childrenD_697_i1 j ⊆ envelope_697_i1 := by decide +kernel
theorem pivot_mem_697_i1 : (3, 6) ∈ envelope_697_i1 := by decide +kernel
theorem children_work_697_i1 : ∀ j, Template HasSnaky 11 (childrenC_697_i1 j) (childrenD_697_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_39 2 (4, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_121 2 (5, 2)).mono (by decide +kernel)
  · exact row_works_697_i2.mono (by decide +kernel)
theorem row_works_697_i1 : Template HasSnaky 12 required_697_i1 envelope_697_i1 := by
  refine compose HasSnaky 11 childrenC_697_i1 childrenD_697_i1 children_work_697_i1 (3, 6)
    required_697_i1 envelope_697_i1 pivot_mem_697_i1 child_required_sub_697_i1 child_envelope_sub_697_i1 ?_
  intro b hb
  exact common_sub_697_i1 (mem_commonEnvelope childrenD_697_i1 b hb)
def required_697_i0 : Finset Cell := ⟨(([(2, 3), (3, 3), (4, 3), (5, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_697_i0 : Finset Cell := ⟨(([(0, 2), (0, 5), (0, 7), (1, 2), (1, 3), (1, 5), (1, 6), (1, 7), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 2), (4, 3), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, 5), (8, 6), (8, 7), (9, 5), (9, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_697_i0 : Fin 3 → Finset Cell := ![(placed21 1 (2, 3) required_21), (placed21 6 (5, 6) required_56), required_697_i1]
def childrenD_697_i0 : Fin 3 → Finset Cell := ![(placed21 1 (2, 3) envelope_21), (placed21 6 (5, 6) envelope_56), envelope_697_i1]
theorem common_sub_697_i0 : commonEnvelope childrenD_697_i0 ⊆ insert (3, 4) required_697_i0 := by decide +kernel
theorem child_required_sub_697_i0 : ∀ j, childrenC_697_i0 j ⊆ insert (3, 4) required_697_i0 := by decide +kernel
theorem child_envelope_sub_697_i0 : ∀ j, childrenD_697_i0 j ⊆ envelope_697_i0 := by decide +kernel
theorem pivot_mem_697_i0 : (3, 4) ∈ envelope_697_i0 := by decide +kernel
theorem children_work_697_i0 : ∀ j, Template HasSnaky 12 (childrenC_697_i0 j) (childrenD_697_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_21 1 (2, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_56 6 (5, 6)).mono (by decide +kernel)
  · exact row_works_697_i1.mono (by decide +kernel)
theorem row_works_697_i0 : Template HasSnaky 13 required_697_i0 envelope_697_i0 := by
  refine compose HasSnaky 12 childrenC_697_i0 childrenD_697_i0 children_work_697_i0 (3, 4)
    required_697_i0 envelope_697_i0 pivot_mem_697_i0 child_required_sub_697_i0 child_envelope_sub_697_i0 ?_
  intro b hb
  exact common_sub_697_i0 (mem_commonEnvelope childrenD_697_i0 b hb)
def required_697 : Finset Cell := ⟨(([(2, 3), (3, 3), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_697 : Finset Cell := ⟨(([(0, 2), (0, 5), (0, 7), (1, 2), (1, 3), (1, 5), (1, 6), (1, 7), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 2), (4, 3), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, 2), (8, 5), (8, 6), (8, 7), (9, 5), (9, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_697 : Fin 4 → Finset Cell := ![(placed21 7 (6, 3) required_7), (placed21 0 (2, 2) required_8), required_690, required_697_i0]
def childrenD_697 : Fin 4 → Finset Cell := ![(placed21 7 (6, 3) envelope_7), (placed21 0 (2, 2) envelope_8), envelope_690, envelope_697_i0]
theorem common_sub_697 : commonEnvelope childrenD_697 ⊆ insert (5, 3) required_697 := by decide +kernel
theorem child_required_sub_697 : ∀ j, childrenC_697 j ⊆ insert (5, 3) required_697 := by decide +kernel
theorem child_envelope_sub_697 : ∀ j, childrenD_697 j ⊆ envelope_697 := by decide +kernel
theorem pivot_mem_697 : (5, 3) ∈ envelope_697 := by decide +kernel
theorem children_work_697 : ∀ j, Template HasSnaky 13 (childrenC_697 j) (childrenD_697 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 7 (6, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_8 0 (2, 2)).mono (by decide +kernel)
  · exact row_works_690.mono (by decide +kernel)
  · exact row_works_697_i0.mono (by decide +kernel)
theorem row_works_697 : Template HasSnaky 14 required_697 envelope_697 := by
  refine compose HasSnaky 13 childrenC_697 childrenD_697 children_work_697 (5, 3)
    required_697 envelope_697 pivot_mem_697 child_required_sub_697 child_envelope_sub_697 ?_
  intro b hb
  exact common_sub_697 (mem_commonEnvelope childrenD_697 b hb)
def required_705_i1 : Finset Cell := ⟨(([(2, 5), (3, 5), (5, 4), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_705_i1 : Finset Cell := ⟨(([(2, 5), (3, 5), (3, 6), (4, 1), (4, 2), (4, 3), (4, 6), (4, 7), (4, 8), (4, 9), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, 5), (7, 6), (7, 7), (7, 8), (8, 6), (8, 7), (8, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_705_i1 : Fin 6 → Finset Cell := ![(placed21 6 (6, 8) required_14), (placed21 4 (2, 7) required_79), (placed21 1 (3, 3) required_181), (placed21 2 (6, 2) required_189), (placed21 4 (4, 8) required_367), (placed21 1 (3, 3) required_474)]
def childrenD_705_i1 : Fin 6 → Finset Cell := ![(placed21 6 (6, 8) envelope_14), (placed21 4 (2, 7) envelope_79), (placed21 1 (3, 3) envelope_181), (placed21 2 (6, 2) envelope_189), (placed21 4 (4, 8) envelope_367), (placed21 1 (3, 3) envelope_474)]
theorem common_sub_705_i1 : commonEnvelope childrenD_705_i1 ⊆ insert (5, 6) required_705_i1 := by decide +kernel
theorem child_required_sub_705_i1 : ∀ j, childrenC_705_i1 j ⊆ insert (5, 6) required_705_i1 := by decide +kernel
theorem child_envelope_sub_705_i1 : ∀ j, childrenD_705_i1 j ⊆ envelope_705_i1 := by decide +kernel
theorem pivot_mem_705_i1 : (5, 6) ∈ envelope_705_i1 := by decide +kernel
theorem children_work_705_i1 : ∀ j, Template HasSnaky 9 (childrenC_705_i1 j) (childrenD_705_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_14 6 (6, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_79 4 (2, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_181 1 (3, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_189 2 (6, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_367 4 (4, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_474 1 (3, 3)).mono (by decide +kernel)
theorem row_works_705_i1 : Template HasSnaky 10 required_705_i1 envelope_705_i1 := by
  refine compose HasSnaky 9 childrenC_705_i1 childrenD_705_i1 children_work_705_i1 (5, 6)
    required_705_i1 envelope_705_i1 pivot_mem_705_i1 child_required_sub_705_i1 child_envelope_sub_705_i1 ?_
  intro b hb
  exact common_sub_705_i1 (mem_commonEnvelope childrenD_705_i1 b hb)
def required_705_i0 : Finset Cell := ⟨(([(2, 5), (3, 4), (3, 5), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_705_i0 : Finset Cell := ⟨(([(1, 4), (2, 4), (2, 5), (3, 4), (3, 5), (3, 6), (4, 1), (4, 2), (4, 3), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, 5), (7, 6), (7, 7), (7, 8), (8, 6), (8, 7), (8, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_705_i0 : Fin 4 → Finset Cell := ![(placed21 4 (2, 8) required_59), (placed21 3 (1, 5) required_105), (placed21 2 (6, 1) required_323), required_705_i1]
def childrenD_705_i0 : Fin 4 → Finset Cell := ![(placed21 4 (2, 8) envelope_59), (placed21 3 (1, 5) envelope_105), (placed21 2 (6, 1) envelope_323), envelope_705_i1]
theorem common_sub_705_i0 : commonEnvelope childrenD_705_i0 ⊆ insert (5, 5) required_705_i0 := by decide +kernel
theorem child_required_sub_705_i0 : ∀ j, childrenC_705_i0 j ⊆ insert (5, 5) required_705_i0 := by decide +kernel
theorem child_envelope_sub_705_i0 : ∀ j, childrenD_705_i0 j ⊆ envelope_705_i0 := by decide +kernel
theorem pivot_mem_705_i0 : (5, 5) ∈ envelope_705_i0 := by decide +kernel
theorem children_work_705_i0 : ∀ j, Template HasSnaky 10 (childrenC_705_i0 j) (childrenD_705_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_59 4 (2, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_105 3 (1, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_323 2 (6, 1)).mono (by decide +kernel)
  · exact row_works_705_i1.mono (by decide +kernel)
theorem row_works_705_i0 : Template HasSnaky 11 required_705_i0 envelope_705_i0 := by
  refine compose HasSnaky 10 childrenC_705_i0 childrenD_705_i0 children_work_705_i0 (5, 5)
    required_705_i0 envelope_705_i0 pivot_mem_705_i0 child_required_sub_705_i0 child_envelope_sub_705_i0 ?_
  intro b hb
  exact common_sub_705_i0 (mem_commonEnvelope childrenD_705_i0 b hb)
def required_705_i4 : Finset Cell := ⟨(([(2, 5), (3, 4), (3, 5), (5, 4), (5, 5), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_705_i4 : Finset Cell := ⟨(([(1, 3), (2, 2), (2, 3), (2, 4), (2, 5), (3, 4), (3, 5), (3, 6), (3, 7), (4, 1), (4, 2), (4, 3), (4, 4), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_705_i4 : Fin 2 → Finset Cell := ![(placed21 6 (5, 7) required_52), (placed21 2 (6, 2) required_242)]
def childrenD_705_i4 : Fin 2 → Finset Cell := ![(placed21 6 (5, 7) envelope_52), (placed21 2 (6, 2) envelope_242)]
theorem common_sub_705_i4 : commonEnvelope childrenD_705_i4 ⊆ insert (4, 4) required_705_i4 := by decide +kernel
theorem child_required_sub_705_i4 : ∀ j, childrenC_705_i4 j ⊆ insert (4, 4) required_705_i4 := by decide +kernel
theorem child_envelope_sub_705_i4 : ∀ j, childrenD_705_i4 j ⊆ envelope_705_i4 := by decide +kernel
theorem pivot_mem_705_i4 : (4, 4) ∈ envelope_705_i4 := by decide +kernel
theorem children_work_705_i4 : ∀ j, Template HasSnaky 4 (childrenC_705_i4 j) (childrenD_705_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_52 6 (5, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_242 2 (6, 2)).mono (by decide +kernel)
theorem row_works_705_i4 : Template HasSnaky 5 required_705_i4 envelope_705_i4 := by
  refine compose HasSnaky 4 childrenC_705_i4 childrenD_705_i4 children_work_705_i4 (4, 4)
    required_705_i4 envelope_705_i4 pivot_mem_705_i4 child_required_sub_705_i4 child_envelope_sub_705_i4 ?_
  intro b hb
  exact common_sub_705_i4 (mem_commonEnvelope childrenD_705_i4 b hb)
def required_705_i3 : Finset Cell := ⟨(([(2, 5), (3, 4), (3, 5), (5, 4), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_705_i3 : Finset Cell := ⟨(([(1, 3), (2, 2), (2, 3), (2, 4), (2, 5), (2, 7), (3, 4), (3, 5), (3, 6), (3, 7), (4, 1), (4, 2), (4, 3), (4, 4), (4, 6), (4, 7), (4, 8), (4, 9), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 1), (6, 2), (6, 3), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, 6), (8, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_705_i3 : Fin 4 → Finset Cell := ![(placed21 4 (2, 7) required_79), (placed21 2 (6, 2) required_243), (placed21 2 (8, 1) required_518), required_705_i4]
def childrenD_705_i3 : Fin 4 → Finset Cell := ![(placed21 4 (2, 7) envelope_79), (placed21 2 (6, 2) envelope_243), (placed21 2 (8, 1) envelope_518), envelope_705_i4]
theorem common_sub_705_i3 : commonEnvelope childrenD_705_i3 ⊆ insert (5, 6) required_705_i3 := by decide +kernel
theorem child_required_sub_705_i3 : ∀ j, childrenC_705_i3 j ⊆ insert (5, 6) required_705_i3 := by decide +kernel
theorem child_envelope_sub_705_i3 : ∀ j, childrenD_705_i3 j ⊆ envelope_705_i3 := by decide +kernel
theorem pivot_mem_705_i3 : (5, 6) ∈ envelope_705_i3 := by decide +kernel
theorem children_work_705_i3 : ∀ j, Template HasSnaky 8 (childrenC_705_i3 j) (childrenD_705_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_79 4 (2, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_243 2 (6, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_518 2 (8, 1)).mono (by decide +kernel)
  · exact row_works_705_i4.mono (by decide +kernel)
theorem row_works_705_i3 : Template HasSnaky 9 required_705_i3 envelope_705_i3 := by
  refine compose HasSnaky 8 childrenC_705_i3 childrenD_705_i3 children_work_705_i3 (5, 6)
    required_705_i3 envelope_705_i3 pivot_mem_705_i3 child_required_sub_705_i3 child_envelope_sub_705_i3 ?_
  intro b hb
  exact common_sub_705_i3 (mem_commonEnvelope childrenD_705_i3 b hb)
def required_705_i2 : Finset Cell := ⟨(([(2, 5), (3, 4), (3, 5), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_705_i2 : Finset Cell := ⟨(([(0, 3), (1, 3), (1, 4), (2, 2), (2, 3), (2, 4), (2, 5), (2, 7), (3, 4), (3, 5), (3, 6), (3, 7), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 1), (6, 2), (6, 3), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, 6), (8, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_705_i2 : Fin 6 → Finset Cell := ![(placed21 2 (6, 1) required_323), (placed21 0 (2, 1) required_430), (placed21 0 (1, 2) required_431), (placed21 7 (6, 5) required_592), (placed21 4 (1, 9) required_681), required_705_i3]
def childrenD_705_i2 : Fin 6 → Finset Cell := ![(placed21 2 (6, 1) envelope_323), (placed21 0 (2, 1) envelope_430), (placed21 0 (1, 2) envelope_431), (placed21 7 (6, 5) envelope_592), (placed21 4 (1, 9) envelope_681), envelope_705_i3]
theorem common_sub_705_i2 : commonEnvelope childrenD_705_i2 ⊆ insert (5, 5) required_705_i2 := by decide +kernel
theorem child_required_sub_705_i2 : ∀ j, childrenC_705_i2 j ⊆ insert (5, 5) required_705_i2 := by decide +kernel
theorem child_envelope_sub_705_i2 : ∀ j, childrenD_705_i2 j ⊆ envelope_705_i2 := by decide +kernel
theorem pivot_mem_705_i2 : (5, 5) ∈ envelope_705_i2 := by decide +kernel
theorem children_work_705_i2 : ∀ j, Template HasSnaky 9 (childrenC_705_i2 j) (childrenD_705_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_323 2 (6, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_430 0 (2, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_431 0 (1, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_592 7 (6, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_681 4 (1, 9)).mono (by decide +kernel)
  · exact row_works_705_i3.mono (by decide +kernel)
theorem row_works_705_i2 : Template HasSnaky 10 required_705_i2 envelope_705_i2 := by
  refine compose HasSnaky 9 childrenC_705_i2 childrenD_705_i2 children_work_705_i2 (5, 5)
    required_705_i2 envelope_705_i2 pivot_mem_705_i2 child_required_sub_705_i2 child_envelope_sub_705_i2 ?_
  intro b hb
  exact common_sub_705_i2 (mem_commonEnvelope childrenD_705_i2 b hb)
def required_705 : Finset Cell := ⟨(([(2, 5), (3, 4), (3, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_705 : Finset Cell := ⟨(([(0, 3), (1, 3), (1, 4), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 7), (3, 4), (3, 5), (3, 6), (3, 7), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_705 : Fin 7 → Finset Cell := ![(placed21 2 (6, 2) required_422), (placed21 4 (1, 8) required_450), (placed21 6 (6, 7) required_503), (placed21 0 (2, 0) required_642), (placed21 4 (1, 7) required_680), required_705_i0, required_705_i2]
def childrenD_705 : Fin 7 → Finset Cell := ![(placed21 2 (6, 2) envelope_422), (placed21 4 (1, 8) envelope_450), (placed21 6 (6, 7) envelope_503), (placed21 0 (2, 0) envelope_642), (placed21 4 (1, 7) envelope_680), envelope_705_i0, envelope_705_i2]
theorem common_sub_705 : commonEnvelope childrenD_705 ⊆ insert (5, 4) required_705 := by decide +kernel
theorem child_required_sub_705 : ∀ j, childrenC_705 j ⊆ insert (5, 4) required_705 := by decide +kernel
theorem child_envelope_sub_705 : ∀ j, childrenD_705 j ⊆ envelope_705 := by decide +kernel
theorem pivot_mem_705 : (5, 4) ∈ envelope_705 := by decide +kernel
theorem children_work_705 : ∀ j, Template HasSnaky 13 (childrenC_705 j) (childrenD_705 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_422 2 (6, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_450 4 (1, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_503 6 (6, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_642 0 (2, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_680 4 (1, 7)).mono (by decide +kernel)
  · exact row_works_705_i0.mono (by decide +kernel)
  · exact row_works_705_i2.mono (by decide +kernel)
theorem row_works_705 : Template HasSnaky 14 required_705 envelope_705 := by
  refine compose HasSnaky 13 childrenC_705 childrenD_705 children_work_705 (5, 4)
    required_705 envelope_705 pivot_mem_705 child_required_sub_705 child_envelope_sub_705 ?_
  intro b hb
  exact common_sub_705 (mem_commonEnvelope childrenD_705 b hb)
def required_711_i0 : Finset Cell := ⟨(([(4, 5), (4, 6), (6, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_711_i0 : Finset Cell := ⟨(([(1, 4), (1, 6), (2, 4), (2, 5), (2, 6), (3, 4), (3, 5), (3, 6), (3, 8), (4, 4), (4, 5), (4, 6), (4, 8), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 7), (5, 8), (5, 9), (5, 10), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_711_i0 : Fin 6 → Finset Cell := ![(placed21 3 (1, 6) required_104), (placed21 3 (1, 6) required_359), (placed21 4 (1, 9) required_452), (placed21 0 (3, 2) required_476), (placed21 4 (3, 9) required_479), (placed21 2 (9, 0) required_520)]
def childrenD_711_i0 : Fin 6 → Finset Cell := ![(placed21 3 (1, 6) envelope_104), (placed21 3 (1, 6) envelope_359), (placed21 4 (1, 9) envelope_452), (placed21 0 (3, 2) envelope_476), (placed21 4 (3, 9) envelope_479), (placed21 2 (9, 0) envelope_520)]
theorem common_sub_711_i0 : commonEnvelope childrenD_711_i0 ⊆ insert (6, 5) required_711_i0 := by decide +kernel
theorem child_required_sub_711_i0 : ∀ j, childrenC_711_i0 j ⊆ insert (6, 5) required_711_i0 := by decide +kernel
theorem child_envelope_sub_711_i0 : ∀ j, childrenD_711_i0 j ⊆ envelope_711_i0 := by decide +kernel
theorem pivot_mem_711_i0 : (6, 5) ∈ envelope_711_i0 := by decide +kernel
theorem children_work_711_i0 : ∀ j, Template HasSnaky 10 (childrenC_711_i0 j) (childrenD_711_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_104 3 (1, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_359 3 (1, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_452 4 (1, 9)).mono (by decide +kernel)
  · exact (placed21_template row_works_476 0 (3, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_479 4 (3, 9)).mono (by decide +kernel)
  · exact (placed21_template row_works_520 2 (9, 0)).mono (by decide +kernel)
theorem row_works_711_i0 : Template HasSnaky 11 required_711_i0 envelope_711_i0 := by
  refine compose HasSnaky 10 childrenC_711_i0 childrenD_711_i0 children_work_711_i0 (6, 5)
    required_711_i0 envelope_711_i0 pivot_mem_711_i0 child_required_sub_711_i0 child_envelope_sub_711_i0 ?_
  intro b hb
  exact common_sub_711_i0 (mem_commonEnvelope childrenD_711_i0 b hb)
def required_711 : Finset Cell := ⟨(([(4, 5), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_711 : Finset Cell := ⟨(([(0, 5), (1, 4), (1, 5), (1, 6), (1, 7), (2, 4), (2, 5), (2, 6), (2, 7), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 4), (4, 5), (4, 6), (4, 8), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (10, 5), (10, 6), (10, 7), (11, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_711 : Fin 9 → Finset Cell := ![(placed21 2 (7, 3) required_120), (placed21 1 (1, 4) required_338), (placed21 1 (1, 3) required_437), (placed21 1 (0, 4) required_611), (placed21 3 (1, 7) required_613), (placed21 4 (1, 10) required_634), (placed21 4 (3, 10) required_642), (placed21 4 (3, 10) required_643), required_711_i0]
def childrenD_711 : Fin 9 → Finset Cell := ![(placed21 2 (7, 3) envelope_120), (placed21 1 (1, 4) envelope_338), (placed21 1 (1, 3) envelope_437), (placed21 1 (0, 4) envelope_611), (placed21 3 (1, 7) envelope_613), (placed21 4 (1, 10) envelope_634), (placed21 4 (3, 10) envelope_642), (placed21 4 (3, 10) envelope_643), envelope_711_i0]
theorem common_sub_711 : commonEnvelope childrenD_711 ⊆ insert (6, 6) required_711 := by decide +kernel
theorem child_required_sub_711 : ∀ j, childrenC_711 j ⊆ insert (6, 6) required_711 := by decide +kernel
theorem child_envelope_sub_711 : ∀ j, childrenD_711 j ⊆ envelope_711 := by decide +kernel
theorem pivot_mem_711 : (6, 6) ∈ envelope_711 := by decide +kernel
theorem children_work_711 : ∀ j, Template HasSnaky 13 (childrenC_711 j) (childrenD_711 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_120 2 (7, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_338 1 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_437 1 (1, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_611 1 (0, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_613 3 (1, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_634 4 (1, 10)).mono (by decide +kernel)
  · exact (placed21_template row_works_642 4 (3, 10)).mono (by decide +kernel)
  · exact (placed21_template row_works_643 4 (3, 10)).mono (by decide +kernel)
  · exact row_works_711_i0.mono (by decide +kernel)
theorem row_works_711 : Template HasSnaky 14 required_711 envelope_711 := by
  refine compose HasSnaky 13 childrenC_711 childrenD_711 children_work_711 (6, 6)
    required_711 envelope_711 pivot_mem_711 child_required_sub_711 child_envelope_sub_711 ?_
  intro b hb
  exact common_sub_711 (mem_commonEnvelope childrenD_711 b hb)
def height_697_i4 : ℕ := 4
def childrenH_697_i4 : Fin 2 → ℕ := ![height_16, height_374]
theorem height_exact_697_i4 : height_697_i4 = 1 + Finset.univ.sup childrenH_697_i4 := by decide +kernel
theorem required_origin_697_i4 : ∀ x ∈ required_697_i4,
    (∃ j, x ∈ childrenC_697_i4 j) ∨ ∀ j, x ∈ childrenD_697_i4 j := by decide +kernel
theorem required_exact_697_i4 : required_697_i4 =
    ((Finset.univ.biUnion childrenC_697_i4) ∪ commonEnvelope childrenD_697_i4).erase (5, 2) := by
  exact required_eq_combination childrenC_697_i4 childrenD_697_i4 (5, 2) required_697_i4
    (by decide +kernel) child_required_sub_697_i4 common_sub_697_i4 required_origin_697_i4
theorem envelope_origin_697_i4 : ∀ x ∈ envelope_697_i4,
    x = (5, 2) ∨ ∃ j, x ∈ childrenD_697_i4 j := by decide +kernel
theorem envelope_exact_697_i4 : envelope_697_i4 =
    insert (5, 2) (Finset.univ.biUnion childrenD_697_i4) := by
  exact envelope_eq_combination childrenD_697_i4 (5, 2) envelope_697_i4
    pivot_mem_697_i4 child_envelope_sub_697_i4 envelope_origin_697_i4
def checked_697_i4 : CheckedCard where
  required := required_697_i4
  envelope := envelope_697_i4
  height := height_697_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_697_i4
def height_697_i3 : ℕ := 7
def childrenH_697_i3 : Fin 2 → ℕ := ![height_95, height_697_i4]
theorem height_exact_697_i3 : height_697_i3 = 1 + Finset.univ.sup childrenH_697_i3 := by decide +kernel
theorem required_origin_697_i3 : ∀ x ∈ required_697_i3,
    (∃ j, x ∈ childrenC_697_i3 j) ∨ ∀ j, x ∈ childrenD_697_i3 j := by decide +kernel
theorem required_exact_697_i3 : required_697_i3 =
    ((Finset.univ.biUnion childrenC_697_i3) ∪ commonEnvelope childrenD_697_i3).erase (6, 6) := by
  exact required_eq_combination childrenC_697_i3 childrenD_697_i3 (6, 6) required_697_i3
    (by decide +kernel) child_required_sub_697_i3 common_sub_697_i3 required_origin_697_i3
theorem envelope_origin_697_i3 : ∀ x ∈ envelope_697_i3,
    x = (6, 6) ∨ ∃ j, x ∈ childrenD_697_i3 j := by decide +kernel
theorem envelope_exact_697_i3 : envelope_697_i3 =
    insert (6, 6) (Finset.univ.biUnion childrenD_697_i3) := by
  exact envelope_eq_combination childrenD_697_i3 (6, 6) envelope_697_i3
    pivot_mem_697_i3 child_envelope_sub_697_i3 envelope_origin_697_i3
def checked_697_i3 : CheckedCard where
  required := required_697_i3
  envelope := envelope_697_i3
  height := height_697_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_697_i3
def height_697_i2 : ℕ := 11
def childrenH_697_i2 : Fin 3 → ℕ := ![height_151, height_460, height_697_i3]
theorem height_exact_697_i2 : height_697_i2 = 1 + Finset.univ.sup childrenH_697_i2 := by decide +kernel
theorem required_origin_697_i2 : ∀ x ∈ required_697_i2,
    (∃ j, x ∈ childrenC_697_i2 j) ∨ ∀ j, x ∈ childrenD_697_i2 j := by decide +kernel
theorem required_exact_697_i2 : required_697_i2 =
    ((Finset.univ.biUnion childrenC_697_i2) ∪ commonEnvelope childrenD_697_i2).erase (5, 6) := by
  exact required_eq_combination childrenC_697_i2 childrenD_697_i2 (5, 6) required_697_i2
    (by decide +kernel) child_required_sub_697_i2 common_sub_697_i2 required_origin_697_i2
theorem envelope_origin_697_i2 : ∀ x ∈ envelope_697_i2,
    x = (5, 6) ∨ ∃ j, x ∈ childrenD_697_i2 j := by decide +kernel
theorem envelope_exact_697_i2 : envelope_697_i2 =
    insert (5, 6) (Finset.univ.biUnion childrenD_697_i2) := by
  exact envelope_eq_combination childrenD_697_i2 (5, 6) envelope_697_i2
    pivot_mem_697_i2 child_envelope_sub_697_i2 envelope_origin_697_i2
def checked_697_i2 : CheckedCard where
  required := required_697_i2
  envelope := envelope_697_i2
  height := height_697_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_697_i2
def height_697_i1 : ℕ := 12
def childrenH_697_i1 : Fin 3 → ℕ := ![height_39, height_121, height_697_i2]
theorem height_exact_697_i1 : height_697_i1 = 1 + Finset.univ.sup childrenH_697_i1 := by decide +kernel
theorem required_origin_697_i1 : ∀ x ∈ required_697_i1,
    (∃ j, x ∈ childrenC_697_i1 j) ∨ ∀ j, x ∈ childrenD_697_i1 j := by decide +kernel
theorem required_exact_697_i1 : required_697_i1 =
    ((Finset.univ.biUnion childrenC_697_i1) ∪ commonEnvelope childrenD_697_i1).erase (3, 6) := by
  exact required_eq_combination childrenC_697_i1 childrenD_697_i1 (3, 6) required_697_i1
    (by decide +kernel) child_required_sub_697_i1 common_sub_697_i1 required_origin_697_i1
theorem envelope_origin_697_i1 : ∀ x ∈ envelope_697_i1,
    x = (3, 6) ∨ ∃ j, x ∈ childrenD_697_i1 j := by decide +kernel
theorem envelope_exact_697_i1 : envelope_697_i1 =
    insert (3, 6) (Finset.univ.biUnion childrenD_697_i1) := by
  exact envelope_eq_combination childrenD_697_i1 (3, 6) envelope_697_i1
    pivot_mem_697_i1 child_envelope_sub_697_i1 envelope_origin_697_i1
def checked_697_i1 : CheckedCard where
  required := required_697_i1
  envelope := envelope_697_i1
  height := height_697_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_697_i1
def height_697_i0 : ℕ := 13
def childrenH_697_i0 : Fin 3 → ℕ := ![height_21, height_56, height_697_i1]
theorem height_exact_697_i0 : height_697_i0 = 1 + Finset.univ.sup childrenH_697_i0 := by decide +kernel
theorem required_origin_697_i0 : ∀ x ∈ required_697_i0,
    (∃ j, x ∈ childrenC_697_i0 j) ∨ ∀ j, x ∈ childrenD_697_i0 j := by decide +kernel
theorem required_exact_697_i0 : required_697_i0 =
    ((Finset.univ.biUnion childrenC_697_i0) ∪ commonEnvelope childrenD_697_i0).erase (3, 4) := by
  exact required_eq_combination childrenC_697_i0 childrenD_697_i0 (3, 4) required_697_i0
    (by decide +kernel) child_required_sub_697_i0 common_sub_697_i0 required_origin_697_i0
theorem envelope_origin_697_i0 : ∀ x ∈ envelope_697_i0,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_697_i0 j := by decide +kernel
theorem envelope_exact_697_i0 : envelope_697_i0 =
    insert (3, 4) (Finset.univ.biUnion childrenD_697_i0) := by
  exact envelope_eq_combination childrenD_697_i0 (3, 4) envelope_697_i0
    pivot_mem_697_i0 child_envelope_sub_697_i0 envelope_origin_697_i0
def checked_697_i0 : CheckedCard where
  required := required_697_i0
  envelope := envelope_697_i0
  height := height_697_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_697_i0
def height_697 : ℕ := 14
def childrenH_697 : Fin 4 → ℕ := ![height_7, height_8, height_690, height_697_i0]
theorem height_exact_697 : height_697 = 1 + Finset.univ.sup childrenH_697 := by decide +kernel
theorem required_origin_697 : ∀ x ∈ required_697,
    (∃ j, x ∈ childrenC_697 j) ∨ ∀ j, x ∈ childrenD_697 j := by decide +kernel
theorem required_exact_697 : required_697 =
    ((Finset.univ.biUnion childrenC_697) ∪ commonEnvelope childrenD_697).erase (5, 3) := by
  exact required_eq_combination childrenC_697 childrenD_697 (5, 3) required_697
    (by decide +kernel) child_required_sub_697 common_sub_697 required_origin_697
theorem envelope_origin_697 : ∀ x ∈ envelope_697,
    x = (5, 3) ∨ ∃ j, x ∈ childrenD_697 j := by decide +kernel
theorem envelope_exact_697 : envelope_697 =
    insert (5, 3) (Finset.univ.biUnion childrenD_697) := by
  exact envelope_eq_combination childrenD_697 (5, 3) envelope_697
    pivot_mem_697 child_envelope_sub_697 envelope_origin_697
def checked_697 : CheckedCard where
  required := required_697
  envelope := envelope_697
  height := height_697
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_697
def height_705_i1 : ℕ := 10
def childrenH_705_i1 : Fin 6 → ℕ := ![height_14, height_79, height_181, height_189, height_367, height_474]
theorem height_exact_705_i1 : height_705_i1 = 1 + Finset.univ.sup childrenH_705_i1 := by decide +kernel
theorem required_origin_705_i1 : ∀ x ∈ required_705_i1,
    (∃ j, x ∈ childrenC_705_i1 j) ∨ ∀ j, x ∈ childrenD_705_i1 j := by decide +kernel
theorem required_exact_705_i1 : required_705_i1 =
    ((Finset.univ.biUnion childrenC_705_i1) ∪ commonEnvelope childrenD_705_i1).erase (5, 6) := by
  exact required_eq_combination childrenC_705_i1 childrenD_705_i1 (5, 6) required_705_i1
    (by decide +kernel) child_required_sub_705_i1 common_sub_705_i1 required_origin_705_i1
theorem envelope_origin_705_i1 : ∀ x ∈ envelope_705_i1,
    x = (5, 6) ∨ ∃ j, x ∈ childrenD_705_i1 j := by decide +kernel
theorem envelope_exact_705_i1 : envelope_705_i1 =
    insert (5, 6) (Finset.univ.biUnion childrenD_705_i1) := by
  exact envelope_eq_combination childrenD_705_i1 (5, 6) envelope_705_i1
    pivot_mem_705_i1 child_envelope_sub_705_i1 envelope_origin_705_i1
def checked_705_i1 : CheckedCard where
  required := required_705_i1
  envelope := envelope_705_i1
  height := height_705_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_705_i1
def height_705_i0 : ℕ := 11
def childrenH_705_i0 : Fin 4 → ℕ := ![height_59, height_105, height_323, height_705_i1]
theorem height_exact_705_i0 : height_705_i0 = 1 + Finset.univ.sup childrenH_705_i0 := by decide +kernel
theorem required_origin_705_i0 : ∀ x ∈ required_705_i0,
    (∃ j, x ∈ childrenC_705_i0 j) ∨ ∀ j, x ∈ childrenD_705_i0 j := by decide +kernel
theorem required_exact_705_i0 : required_705_i0 =
    ((Finset.univ.biUnion childrenC_705_i0) ∪ commonEnvelope childrenD_705_i0).erase (5, 5) := by
  exact required_eq_combination childrenC_705_i0 childrenD_705_i0 (5, 5) required_705_i0
    (by decide +kernel) child_required_sub_705_i0 common_sub_705_i0 required_origin_705_i0
theorem envelope_origin_705_i0 : ∀ x ∈ envelope_705_i0,
    x = (5, 5) ∨ ∃ j, x ∈ childrenD_705_i0 j := by decide +kernel
theorem envelope_exact_705_i0 : envelope_705_i0 =
    insert (5, 5) (Finset.univ.biUnion childrenD_705_i0) := by
  exact envelope_eq_combination childrenD_705_i0 (5, 5) envelope_705_i0
    pivot_mem_705_i0 child_envelope_sub_705_i0 envelope_origin_705_i0
def checked_705_i0 : CheckedCard where
  required := required_705_i0
  envelope := envelope_705_i0
  height := height_705_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_705_i0
def height_705_i4 : ℕ := 5
def childrenH_705_i4 : Fin 2 → ℕ := ![height_52, height_242]
theorem height_exact_705_i4 : height_705_i4 = 1 + Finset.univ.sup childrenH_705_i4 := by decide +kernel
theorem required_origin_705_i4 : ∀ x ∈ required_705_i4,
    (∃ j, x ∈ childrenC_705_i4 j) ∨ ∀ j, x ∈ childrenD_705_i4 j := by decide +kernel
theorem required_exact_705_i4 : required_705_i4 =
    ((Finset.univ.biUnion childrenC_705_i4) ∪ commonEnvelope childrenD_705_i4).erase (4, 4) := by
  exact required_eq_combination childrenC_705_i4 childrenD_705_i4 (4, 4) required_705_i4
    (by decide +kernel) child_required_sub_705_i4 common_sub_705_i4 required_origin_705_i4
theorem envelope_origin_705_i4 : ∀ x ∈ envelope_705_i4,
    x = (4, 4) ∨ ∃ j, x ∈ childrenD_705_i4 j := by decide +kernel
theorem envelope_exact_705_i4 : envelope_705_i4 =
    insert (4, 4) (Finset.univ.biUnion childrenD_705_i4) := by
  exact envelope_eq_combination childrenD_705_i4 (4, 4) envelope_705_i4
    pivot_mem_705_i4 child_envelope_sub_705_i4 envelope_origin_705_i4
def checked_705_i4 : CheckedCard where
  required := required_705_i4
  envelope := envelope_705_i4
  height := height_705_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_705_i4
def height_705_i3 : ℕ := 9
def childrenH_705_i3 : Fin 4 → ℕ := ![height_79, height_243, height_518, height_705_i4]
theorem height_exact_705_i3 : height_705_i3 = 1 + Finset.univ.sup childrenH_705_i3 := by decide +kernel
theorem required_origin_705_i3 : ∀ x ∈ required_705_i3,
    (∃ j, x ∈ childrenC_705_i3 j) ∨ ∀ j, x ∈ childrenD_705_i3 j := by decide +kernel
theorem required_exact_705_i3 : required_705_i3 =
    ((Finset.univ.biUnion childrenC_705_i3) ∪ commonEnvelope childrenD_705_i3).erase (5, 6) := by
  exact required_eq_combination childrenC_705_i3 childrenD_705_i3 (5, 6) required_705_i3
    (by decide +kernel) child_required_sub_705_i3 common_sub_705_i3 required_origin_705_i3
theorem envelope_origin_705_i3 : ∀ x ∈ envelope_705_i3,
    x = (5, 6) ∨ ∃ j, x ∈ childrenD_705_i3 j := by decide +kernel
theorem envelope_exact_705_i3 : envelope_705_i3 =
    insert (5, 6) (Finset.univ.biUnion childrenD_705_i3) := by
  exact envelope_eq_combination childrenD_705_i3 (5, 6) envelope_705_i3
    pivot_mem_705_i3 child_envelope_sub_705_i3 envelope_origin_705_i3
def checked_705_i3 : CheckedCard where
  required := required_705_i3
  envelope := envelope_705_i3
  height := height_705_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_705_i3
def height_705_i2 : ℕ := 10
def childrenH_705_i2 : Fin 6 → ℕ := ![height_323, height_430, height_431, height_592, height_681, height_705_i3]
theorem height_exact_705_i2 : height_705_i2 = 1 + Finset.univ.sup childrenH_705_i2 := by decide +kernel
theorem required_origin_705_i2 : ∀ x ∈ required_705_i2,
    (∃ j, x ∈ childrenC_705_i2 j) ∨ ∀ j, x ∈ childrenD_705_i2 j := by decide +kernel
theorem required_exact_705_i2 : required_705_i2 =
    ((Finset.univ.biUnion childrenC_705_i2) ∪ commonEnvelope childrenD_705_i2).erase (5, 5) := by
  exact required_eq_combination childrenC_705_i2 childrenD_705_i2 (5, 5) required_705_i2
    (by decide +kernel) child_required_sub_705_i2 common_sub_705_i2 required_origin_705_i2
theorem envelope_origin_705_i2 : ∀ x ∈ envelope_705_i2,
    x = (5, 5) ∨ ∃ j, x ∈ childrenD_705_i2 j := by decide +kernel
theorem envelope_exact_705_i2 : envelope_705_i2 =
    insert (5, 5) (Finset.univ.biUnion childrenD_705_i2) := by
  exact envelope_eq_combination childrenD_705_i2 (5, 5) envelope_705_i2
    pivot_mem_705_i2 child_envelope_sub_705_i2 envelope_origin_705_i2
def checked_705_i2 : CheckedCard where
  required := required_705_i2
  envelope := envelope_705_i2
  height := height_705_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_705_i2
def height_705 : ℕ := 14
def childrenH_705 : Fin 7 → ℕ := ![height_422, height_450, height_503, height_642, height_680, height_705_i0, height_705_i2]
theorem height_exact_705 : height_705 = 1 + Finset.univ.sup childrenH_705 := by decide +kernel
theorem required_origin_705 : ∀ x ∈ required_705,
    (∃ j, x ∈ childrenC_705 j) ∨ ∀ j, x ∈ childrenD_705 j := by decide +kernel
theorem required_exact_705 : required_705 =
    ((Finset.univ.biUnion childrenC_705) ∪ commonEnvelope childrenD_705).erase (5, 4) := by
  exact required_eq_combination childrenC_705 childrenD_705 (5, 4) required_705
    (by decide +kernel) child_required_sub_705 common_sub_705 required_origin_705
theorem envelope_origin_705 : ∀ x ∈ envelope_705,
    x = (5, 4) ∨ ∃ j, x ∈ childrenD_705 j := by decide +kernel
theorem envelope_exact_705 : envelope_705 =
    insert (5, 4) (Finset.univ.biUnion childrenD_705) := by
  exact envelope_eq_combination childrenD_705 (5, 4) envelope_705
    pivot_mem_705 child_envelope_sub_705 envelope_origin_705
def checked_705 : CheckedCard where
  required := required_705
  envelope := envelope_705
  height := height_705
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_705
def height_711_i0 : ℕ := 11
def childrenH_711_i0 : Fin 6 → ℕ := ![height_104, height_359, height_452, height_476, height_479, height_520]
theorem height_exact_711_i0 : height_711_i0 = 1 + Finset.univ.sup childrenH_711_i0 := by decide +kernel
theorem required_origin_711_i0 : ∀ x ∈ required_711_i0,
    (∃ j, x ∈ childrenC_711_i0 j) ∨ ∀ j, x ∈ childrenD_711_i0 j := by decide +kernel
theorem required_exact_711_i0 : required_711_i0 =
    ((Finset.univ.biUnion childrenC_711_i0) ∪ commonEnvelope childrenD_711_i0).erase (6, 5) := by
  exact required_eq_combination childrenC_711_i0 childrenD_711_i0 (6, 5) required_711_i0
    (by decide +kernel) child_required_sub_711_i0 common_sub_711_i0 required_origin_711_i0
theorem envelope_origin_711_i0 : ∀ x ∈ envelope_711_i0,
    x = (6, 5) ∨ ∃ j, x ∈ childrenD_711_i0 j := by decide +kernel
theorem envelope_exact_711_i0 : envelope_711_i0 =
    insert (6, 5) (Finset.univ.biUnion childrenD_711_i0) := by
  exact envelope_eq_combination childrenD_711_i0 (6, 5) envelope_711_i0
    pivot_mem_711_i0 child_envelope_sub_711_i0 envelope_origin_711_i0
def checked_711_i0 : CheckedCard where
  required := required_711_i0
  envelope := envelope_711_i0
  height := height_711_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_711_i0
def height_711 : ℕ := 14
def childrenH_711 : Fin 9 → ℕ := ![height_120, height_338, height_437, height_611, height_613, height_634, height_642, height_643, height_711_i0]
theorem height_exact_711 : height_711 = 1 + Finset.univ.sup childrenH_711 := by decide +kernel
theorem required_origin_711 : ∀ x ∈ required_711,
    (∃ j, x ∈ childrenC_711 j) ∨ ∀ j, x ∈ childrenD_711 j := by decide +kernel
theorem required_exact_711 : required_711 =
    ((Finset.univ.biUnion childrenC_711) ∪ commonEnvelope childrenD_711).erase (6, 6) := by
  exact required_eq_combination childrenC_711 childrenD_711 (6, 6) required_711
    (by decide +kernel) child_required_sub_711 common_sub_711 required_origin_711
theorem envelope_origin_711 : ∀ x ∈ envelope_711,
    x = (6, 6) ∨ ∃ j, x ∈ childrenD_711 j := by decide +kernel
theorem envelope_exact_711 : envelope_711 =
    insert (6, 6) (Finset.univ.biUnion childrenD_711) := by
  exact envelope_eq_combination childrenD_711 (6, 6) envelope_711
    pivot_mem_711 child_envelope_sub_711 envelope_origin_711
def checked_711 : CheckedCard where
  required := required_711
  envelope := envelope_711
  height := height_711
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_711
end SnakyPrototype.Certificate21

end OAI
