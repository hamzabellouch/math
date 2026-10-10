import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part06
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part06
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height10Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height10Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height10Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height11Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height12Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height12Part02
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_462 : Finset Cell := ⟨(([(1, 3), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_462 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 5), (0, 6), (0, 7), (0, 8), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 1), (5, 2), (5, 3), (5, 5), (5, 7), (6, 1), (6, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_462 : Fin 7 → Finset Cell := ![(placed21 2 (2, 1) required_13), (placed21 6 (2, 7) required_14), (placed21 4 (0, 7) required_31), (placed21 2 (2, 1) required_189), (placed21 4 (0, 7) required_367), (placed21 4 (0, 6) required_428), (placed21 0 (0, 2) required_457)]
def childrenD_462 : Fin 7 → Finset Cell := ![(placed21 2 (2, 1) envelope_13), (placed21 6 (2, 7) envelope_14), (placed21 4 (0, 7) envelope_31), (placed21 2 (2, 1) envelope_189), (placed21 4 (0, 7) envelope_367), (placed21 4 (0, 6) envelope_428), (placed21 0 (0, 2) envelope_457)]
theorem common_sub_462 : commonEnvelope childrenD_462 ⊆ insert (1, 5) required_462 := by decide +kernel
theorem child_required_sub_462 : ∀ j, childrenC_462 j ⊆ insert (1, 5) required_462 := by decide +kernel
theorem child_envelope_sub_462 : ∀ j, childrenD_462 j ⊆ envelope_462 := by decide +kernel
theorem pivot_mem_462 : (1, 5) ∈ envelope_462 := by decide +kernel
theorem children_work_462 : ∀ j, Template HasSnaky 12 (childrenC_462 j) (childrenD_462 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_13 2 (2, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_14 6 (2, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_31 4 (0, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_189 2 (2, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_367 4 (0, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_428 4 (0, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_457 0 (0, 2)).mono (by decide +kernel)
theorem row_works_462 : Template HasSnaky 13 required_462 envelope_462 := by
  refine compose HasSnaky 12 childrenC_462 childrenD_462 children_work_462 (1, 5)
    required_462 envelope_462 pivot_mem_462 child_required_sub_462 child_envelope_sub_462 ?_
  intro b hb
  exact common_sub_462 (mem_commonEnvelope childrenD_462 b hb)
def required_490 : Finset Cell := ⟨(([(2, 7), (3, 7), (4, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_490 : Finset Cell := ⟨(([(0, 3), (0, 5), (0, 9), (0, 11), (1, 3), (1, 4), (1, 5), (1, 6), (1, 8), (1, 9), (1, 10), (1, 11), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, 2), (3, 3), (3, 4), (3, 5), (3, 7), (3, 9), (3, 10), (3, 11), (3, 12), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (4, 13), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (5, 12), (5, 13), (5, 14), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (6, 12), (6, 13), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (7, 12), (7, 13), (7, 14), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (8, 11), (9, 3), (9, 5), (9, 6), (9, 8), (9, 9), (9, 11)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_490 : Fin 6 → Finset Cell := ![(placed21 0 (2, 3) required_321), (placed21 4 (2, 11) required_321), (placed21 1 (0, 6) required_485), (placed21 3 (0, 8) required_485), (placed21 0 (0, 2) required_489), (placed21 4 (0, 12) required_489)]
def childrenD_490 : Fin 6 → Finset Cell := ![(placed21 0 (2, 3) envelope_321), (placed21 4 (2, 11) envelope_321), (placed21 1 (0, 6) envelope_485), (placed21 3 (0, 8) envelope_485), (placed21 0 (0, 2) envelope_489), (placed21 4 (0, 12) envelope_489)]
theorem common_sub_490 : commonEnvelope childrenD_490 ⊆ insert (5, 7) required_490 := by decide +kernel
theorem child_required_sub_490 : ∀ j, childrenC_490 j ⊆ insert (5, 7) required_490 := by decide +kernel
theorem child_envelope_sub_490 : ∀ j, childrenD_490 j ⊆ envelope_490 := by decide +kernel
theorem pivot_mem_490 : (5, 7) ∈ envelope_490 := by decide +kernel
theorem children_work_490 : ∀ j, Template HasSnaky 12 (childrenC_490 j) (childrenD_490 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_321 0 (2, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_321 4 (2, 11)).mono (by decide +kernel)
  · exact (placed21_template row_works_485 1 (0, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_485 3 (0, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_489 0 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_489 4 (0, 12)).mono (by decide +kernel)
theorem row_works_490 : Template HasSnaky 13 required_490 envelope_490 := by
  refine compose HasSnaky 12 childrenC_490 childrenD_490 children_work_490 (5, 7)
    required_490 envelope_490 pivot_mem_490 child_required_sub_490 child_envelope_sub_490 ?_
  intro b hb
  exact common_sub_490 (mem_commonEnvelope childrenD_490 b hb)
def required_538_i0 : Finset Cell := ⟨(([(1, 6), (2, 6), (4, 5), (5, 5), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_538_i0 : Finset Cell := ⟨(([(1, 6), (1, 8), (1, 9), (2, 6), (2, 8), (2, 9), (3, 6), (3, 7), (3, 8), (3, 9), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (7, 6), (7, 7), (7, 8), (8, 6), (8, 7), (8, 8), (9, 6), (9, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_538_i0 : Fin 6 → Finset Cell := ![(placed21 0 (3, 3) required_190), (placed21 2 (7, 3) required_190), (placed21 5 (8, 5) required_258), (placed21 4 (1, 9) required_273), (placed21 0 (1, 4) required_415), (placed21 1 (2, 4) required_507)]
def childrenD_538_i0 : Fin 6 → Finset Cell := ![(placed21 0 (3, 3) envelope_190), (placed21 2 (7, 3) envelope_190), (placed21 5 (8, 5) envelope_258), (placed21 4 (1, 9) envelope_273), (placed21 0 (1, 4) envelope_415), (placed21 1 (2, 4) envelope_507)]
theorem common_sub_538_i0 : commonEnvelope childrenD_538_i0 ⊆ insert (5, 7) required_538_i0 := by decide +kernel
theorem child_required_sub_538_i0 : ∀ j, childrenC_538_i0 j ⊆ insert (5, 7) required_538_i0 := by decide +kernel
theorem child_envelope_sub_538_i0 : ∀ j, childrenD_538_i0 j ⊆ envelope_538_i0 := by decide +kernel
theorem pivot_mem_538_i0 : (5, 7) ∈ envelope_538_i0 := by decide +kernel
theorem children_work_538_i0 : ∀ j, Template HasSnaky 8 (childrenC_538_i0 j) (childrenD_538_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_190 0 (3, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_190 2 (7, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_258 5 (8, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_273 4 (1, 9)).mono (by decide +kernel)
  · exact (placed21_template row_works_415 0 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_507 1 (2, 4)).mono (by decide +kernel)
theorem row_works_538_i0 : Template HasSnaky 9 required_538_i0 envelope_538_i0 := by
  refine compose HasSnaky 8 childrenC_538_i0 childrenD_538_i0 children_work_538_i0 (5, 7)
    required_538_i0 envelope_538_i0 pivot_mem_538_i0 child_required_sub_538_i0 child_envelope_sub_538_i0 ?_
  intro b hb
  exact common_sub_538_i0 (mem_commonEnvelope childrenD_538_i0 b hb)
def required_538_i1 : Finset Cell := ⟨(([(1, 6), (2, 6), (4, 5), (5, 5), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_538_i1 : Finset Cell := ⟨(([(1, 6), (2, 6), (3, 6), (3, 7), (4, 3), (4, 5), (4, 6), (4, 7), (4, 8), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (9, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_538_i1 : Fin 2 → Finset Cell := ![(placed21 4 (1, 6) required_2), (placed21 4 (3, 9) required_512)]
def childrenD_538_i1 : Fin 2 → Finset Cell := ![(placed21 4 (1, 6) envelope_2), (placed21 4 (3, 9) envelope_512)]
theorem common_sub_538_i1 : commonEnvelope childrenD_538_i1 ⊆ insert (4, 6) required_538_i1 := by decide +kernel
theorem child_required_sub_538_i1 : ∀ j, childrenC_538_i1 j ⊆ insert (4, 6) required_538_i1 := by decide +kernel
theorem child_envelope_sub_538_i1 : ∀ j, childrenD_538_i1 j ⊆ envelope_538_i1 := by decide +kernel
theorem pivot_mem_538_i1 : (4, 6) ∈ envelope_538_i1 := by decide +kernel
theorem children_work_538_i1 : ∀ j, Template HasSnaky 9 (childrenC_538_i1 j) (childrenD_538_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_2 4 (1, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_512 4 (3, 9)).mono (by decide +kernel)
theorem row_works_538_i1 : Template HasSnaky 10 required_538_i1 envelope_538_i1 := by
  refine compose HasSnaky 9 childrenC_538_i1 childrenD_538_i1 children_work_538_i1 (4, 6)
    required_538_i1 envelope_538_i1 pivot_mem_538_i1 child_required_sub_538_i1 child_envelope_sub_538_i1 ?_
  intro b hb
  exact common_sub_538_i1 (mem_commonEnvelope childrenD_538_i1 b hb)
def required_538_i3 : Finset Cell := ⟨(([(2, 6), (5, 4), (5, 5), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_538_i3 : Finset Cell := ⟨(([(2, 6), (3, 6), (3, 7), (4, 6), (4, 7), (4, 8), (4, 9), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 3), (6, 4), (6, 5), (6, 7), (6, 8), (6, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_538_i3 : Fin 3 → Finset Cell := ![(placed21 0 (5, 3) required_7), (placed21 2 (6, 3) required_9), (placed21 5 (6, 4) required_354)]
def childrenD_538_i3 : Fin 3 → Finset Cell := ![(placed21 0 (5, 3) envelope_7), (placed21 2 (6, 3) envelope_9), (placed21 5 (6, 4) envelope_354)]
theorem common_sub_538_i3 : commonEnvelope childrenD_538_i3 ⊆ insert (5, 7) required_538_i3 := by decide +kernel
theorem child_required_sub_538_i3 : ∀ j, childrenC_538_i3 j ⊆ insert (5, 7) required_538_i3 := by decide +kernel
theorem child_envelope_sub_538_i3 : ∀ j, childrenD_538_i3 j ⊆ envelope_538_i3 := by decide +kernel
theorem pivot_mem_538_i3 : (5, 7) ∈ envelope_538_i3 := by decide +kernel
theorem children_work_538_i3 : ∀ j, Template HasSnaky 4 (childrenC_538_i3 j) (childrenD_538_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 0 (5, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_9 2 (6, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_354 5 (6, 4)).mono (by decide +kernel)
theorem row_works_538_i3 : Template HasSnaky 5 required_538_i3 envelope_538_i3 := by
  refine compose HasSnaky 4 childrenC_538_i3 childrenD_538_i3 children_work_538_i3 (5, 7)
    required_538_i3 envelope_538_i3 pivot_mem_538_i3 child_required_sub_538_i3 child_envelope_sub_538_i3 ?_
  intro b hb
  exact common_sub_538_i3 (mem_commonEnvelope childrenD_538_i3 b hb)
def required_538_i4 : Finset Cell := ⟨(([(1, 6), (2, 6), (4, 5), (5, 4), (5, 5), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_538_i4 : Finset Cell := ⟨(([(1, 6), (2, 6), (3, 6), (4, 5), (4, 6), (4, 7), (4, 8), (5, 3), (5, 4), (5, 5), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_538_i4 : Fin 2 → Finset Cell := ![(placed21 4 (1, 6) required_2), (placed21 2 (5, 3) required_15)]
def childrenD_538_i4 : Fin 2 → Finset Cell := ![(placed21 4 (1, 6) envelope_2), (placed21 2 (5, 3) envelope_15)]
theorem common_sub_538_i4 : commonEnvelope childrenD_538_i4 ⊆ insert (4, 6) required_538_i4 := by decide +kernel
theorem child_required_sub_538_i4 : ∀ j, childrenC_538_i4 j ⊆ insert (4, 6) required_538_i4 := by decide +kernel
theorem child_envelope_sub_538_i4 : ∀ j, childrenD_538_i4 j ⊆ envelope_538_i4 := by decide +kernel
theorem pivot_mem_538_i4 : (4, 6) ∈ envelope_538_i4 := by decide +kernel
theorem children_work_538_i4 : ∀ j, Template HasSnaky 2 (childrenC_538_i4 j) (childrenD_538_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_2 4 (1, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_15 2 (5, 3)).mono (by decide +kernel)
theorem row_works_538_i4 : Template HasSnaky 3 required_538_i4 envelope_538_i4 := by
  refine compose HasSnaky 2 childrenC_538_i4 childrenD_538_i4 children_work_538_i4 (4, 6)
    required_538_i4 envelope_538_i4 pivot_mem_538_i4 child_required_sub_538_i4 child_envelope_sub_538_i4 ?_
  intro b hb
  exact common_sub_538_i4 (mem_commonEnvelope childrenD_538_i4 b hb)
def required_538_i5 : Finset Cell := ⟨(([(1, 3), (2, 3), (5, 4), (5, 5), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_538_i5 : Finset Cell := ⟨(([(0, 2), (1, 2), (1, 3), (2, 2), (2, 3), (3, 3), (4, 2), (4, 3), (4, 7), (4, 8), (4, 9), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 1), (6, 2), (6, 3), (6, 4), (6, 7), (6, 8), (6, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_538_i5 : Fin 2 → Finset Cell := ![(placed21 1 (4, 4) required_8), (placed21 7 (6, 7) required_505)]
def childrenD_538_i5 : Fin 2 → Finset Cell := ![(placed21 1 (4, 4) envelope_8), (placed21 7 (6, 7) envelope_505)]
theorem common_sub_538_i5 : commonEnvelope childrenD_538_i5 ⊆ insert (5, 7) required_538_i5 := by decide +kernel
theorem child_required_sub_538_i5 : ∀ j, childrenC_538_i5 j ⊆ insert (5, 7) required_538_i5 := by decide +kernel
theorem child_envelope_sub_538_i5 : ∀ j, childrenD_538_i5 j ⊆ envelope_538_i5 := by decide +kernel
theorem pivot_mem_538_i5 : (5, 7) ∈ envelope_538_i5 := by decide +kernel
theorem children_work_538_i5 : ∀ j, Template HasSnaky 5 (childrenC_538_i5 j) (childrenD_538_i5 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_8 1 (4, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_505 7 (6, 7)).mono (by decide +kernel)
theorem row_works_538_i5 : Template HasSnaky 6 required_538_i5 envelope_538_i5 := by
  refine compose HasSnaky 5 childrenC_538_i5 childrenD_538_i5 children_work_538_i5 (5, 7)
    required_538_i5 envelope_538_i5 pivot_mem_538_i5 child_required_sub_538_i5 child_envelope_sub_538_i5 ?_
  intro b hb
  exact common_sub_538_i5 (mem_commonEnvelope childrenD_538_i5 b hb)
def required_538_i2 : Finset Cell := ⟨(([(1, 3), (1, 6), (2, 3), (2, 6), (4, 5), (5, 5), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_538_i2 : Finset Cell := ⟨(([(0, 2), (1, 2), (1, 3), (1, 6), (2, 2), (2, 3), (2, 6), (3, 3), (3, 6), (3, 7), (4, 1), (4, 2), (4, 3), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 7), (6, 8), (6, 9), (7, 4), (8, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_538_i2 : Fin 4 → Finset Cell := ![(placed21 4 (3, 7) required_136), required_538_i3, required_538_i4, required_538_i5]
def childrenD_538_i2 : Fin 4 → Finset Cell := ![(placed21 4 (3, 7) envelope_136), envelope_538_i3, envelope_538_i4, envelope_538_i5]
theorem common_sub_538_i2 : commonEnvelope childrenD_538_i2 ⊆ insert (5, 4) required_538_i2 := by decide +kernel
theorem child_required_sub_538_i2 : ∀ j, childrenC_538_i2 j ⊆ insert (5, 4) required_538_i2 := by decide +kernel
theorem child_envelope_sub_538_i2 : ∀ j, childrenD_538_i2 j ⊆ envelope_538_i2 := by decide +kernel
theorem pivot_mem_538_i2 : (5, 4) ∈ envelope_538_i2 := by decide +kernel
theorem children_work_538_i2 : ∀ j, Template HasSnaky 6 (childrenC_538_i2 j) (childrenD_538_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_136 4 (3, 7)).mono (by decide +kernel)
  · exact row_works_538_i3.mono (by decide +kernel)
  · exact row_works_538_i4.mono (by decide +kernel)
  · exact row_works_538_i5.mono (by decide +kernel)
theorem row_works_538_i2 : Template HasSnaky 7 required_538_i2 envelope_538_i2 := by
  refine compose HasSnaky 6 childrenC_538_i2 childrenD_538_i2 children_work_538_i2 (5, 4)
    required_538_i2 envelope_538_i2 pivot_mem_538_i2 child_required_sub_538_i2 child_envelope_sub_538_i2 ?_
  intro b hb
  exact common_sub_538_i2 (mem_commonEnvelope childrenD_538_i2 b hb)
def required_538_i6 : Finset Cell := ⟨(([(1, 6), (2, 6), (4, 5), (5, 5), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_538_i6 : Finset Cell := ⟨(([(1, 6), (2, 6), (3, 6), (3, 7), (3, 8), (3, 9), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (9, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_538_i6 : Fin 2 → Finset Cell := ![(placed21 4 (1, 6) required_2), (placed21 0 (3, 2) required_517)]
def childrenD_538_i6 : Fin 2 → Finset Cell := ![(placed21 4 (1, 6) envelope_2), (placed21 0 (3, 2) envelope_517)]
theorem common_sub_538_i6 : commonEnvelope childrenD_538_i6 ⊆ insert (4, 6) required_538_i6 := by decide +kernel
theorem child_required_sub_538_i6 : ∀ j, childrenC_538_i6 j ⊆ insert (4, 6) required_538_i6 := by decide +kernel
theorem child_envelope_sub_538_i6 : ∀ j, childrenD_538_i6 j ⊆ envelope_538_i6 := by decide +kernel
theorem pivot_mem_538_i6 : (4, 6) ∈ envelope_538_i6 := by decide +kernel
theorem children_work_538_i6 : ∀ j, Template HasSnaky 11 (childrenC_538_i6 j) (childrenD_538_i6 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_2 4 (1, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_517 0 (3, 2)).mono (by decide +kernel)
theorem row_works_538_i6 : Template HasSnaky 12 required_538_i6 envelope_538_i6 := by
  refine compose HasSnaky 11 childrenC_538_i6 childrenD_538_i6 children_work_538_i6 (4, 6)
    required_538_i6 envelope_538_i6 pivot_mem_538_i6 child_required_sub_538_i6 child_envelope_sub_538_i6 ?_
  intro b hb
  exact common_sub_538_i6 (mem_commonEnvelope childrenD_538_i6 b hb)
def required_538_i7 : Finset Cell := ⟨(([(1, 6), (2, 6), (4, 5), (5, 5), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_538_i7 : Finset Cell := ⟨(([(1, 6), (1, 8), (1, 9), (2, 6), (2, 8), (2, 9), (3, 6), (3, 7), (3, 8), (3, 9), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (6, 2), (6, 3), (6, 4), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (7, 6), (7, 7), (7, 8), (8, 6), (8, 7), (8, 8), (9, 6), (9, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_538_i7 : Fin 7 → Finset Cell := ![(placed21 3 (2, 8) required_116), (placed21 5 (7, 4) required_180), (placed21 5 (8, 5) required_258), (placed21 4 (1, 9) required_273), (placed21 1 (3, 4) required_275), (placed21 0 (1, 4) required_415), (placed21 2 (8, 2) required_518)]
def childrenD_538_i7 : Fin 7 → Finset Cell := ![(placed21 3 (2, 8) envelope_116), (placed21 5 (7, 4) envelope_180), (placed21 5 (8, 5) envelope_258), (placed21 4 (1, 9) envelope_273), (placed21 1 (3, 4) envelope_275), (placed21 0 (1, 4) envelope_415), (placed21 2 (8, 2) envelope_518)]
theorem common_sub_538_i7 : commonEnvelope childrenD_538_i7 ⊆ insert (5, 7) required_538_i7 := by decide +kernel
theorem child_required_sub_538_i7 : ∀ j, childrenC_538_i7 j ⊆ insert (5, 7) required_538_i7 := by decide +kernel
theorem child_envelope_sub_538_i7 : ∀ j, childrenD_538_i7 j ⊆ envelope_538_i7 := by decide +kernel
theorem pivot_mem_538_i7 : (5, 7) ∈ envelope_538_i7 := by decide +kernel
theorem children_work_538_i7 : ∀ j, Template HasSnaky 8 (childrenC_538_i7 j) (childrenD_538_i7 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_116 3 (2, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_180 5 (7, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_258 5 (8, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_273 4 (1, 9)).mono (by decide +kernel)
  · exact (placed21_template row_works_275 1 (3, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_415 0 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_518 2 (8, 2)).mono (by decide +kernel)
theorem row_works_538_i7 : Template HasSnaky 9 required_538_i7 envelope_538_i7 := by
  refine compose HasSnaky 8 childrenC_538_i7 childrenD_538_i7 children_work_538_i7 (5, 7)
    required_538_i7 envelope_538_i7 pivot_mem_538_i7 child_required_sub_538_i7 child_envelope_sub_538_i7 ?_
  intro b hb
  exact common_sub_538_i7 (mem_commonEnvelope childrenD_538_i7 b hb)
def required_538_i8 : Finset Cell := ⟨(([(1, 6), (2, 6), (4, 5), (5, 5), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_538_i8 : Finset Cell := ⟨(([(1, 6), (2, 6), (3, 6), (3, 7), (4, 5), (4, 6), (4, 7), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (9, 4), (9, 5), (9, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_538_i8 : Fin 2 → Finset Cell := ![(placed21 4 (1, 6) required_2), (placed21 4 (3, 9) required_527)]
def childrenD_538_i8 : Fin 2 → Finset Cell := ![(placed21 4 (1, 6) envelope_2), (placed21 4 (3, 9) envelope_527)]
theorem common_sub_538_i8 : commonEnvelope childrenD_538_i8 ⊆ insert (4, 6) required_538_i8 := by decide +kernel
theorem child_required_sub_538_i8 : ∀ j, childrenC_538_i8 j ⊆ insert (4, 6) required_538_i8 := by decide +kernel
theorem child_envelope_sub_538_i8 : ∀ j, childrenD_538_i8 j ⊆ envelope_538_i8 := by decide +kernel
theorem pivot_mem_538_i8 : (4, 6) ∈ envelope_538_i8 := by decide +kernel
theorem children_work_538_i8 : ∀ j, Template HasSnaky 11 (childrenC_538_i8 j) (childrenD_538_i8 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_2 4 (1, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_527 4 (3, 9)).mono (by decide +kernel)
theorem row_works_538_i8 : Template HasSnaky 12 required_538_i8 envelope_538_i8 := by
  refine compose HasSnaky 11 childrenC_538_i8 childrenD_538_i8 children_work_538_i8 (4, 6)
    required_538_i8 envelope_538_i8 pivot_mem_538_i8 child_required_sub_538_i8 child_envelope_sub_538_i8 ?_
  intro b hb
  exact common_sub_538_i8 (mem_commonEnvelope childrenD_538_i8 b hb)
def required_538_i9 : Finset Cell := ⟨(([(1, 6), (2, 6), (4, 5), (5, 5), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_538_i9 : Finset Cell := ⟨(([(1, 6), (2, 6), (3, 6), (3, 7), (4, 3), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_538_i9 : Fin 2 → Finset Cell := ![(placed21 4 (1, 6) required_2), (placed21 4 (3, 9) required_537)]
def childrenD_538_i9 : Fin 2 → Finset Cell := ![(placed21 4 (1, 6) envelope_2), (placed21 4 (3, 9) envelope_537)]
theorem common_sub_538_i9 : commonEnvelope childrenD_538_i9 ⊆ insert (4, 6) required_538_i9 := by decide +kernel
theorem child_required_sub_538_i9 : ∀ j, childrenC_538_i9 j ⊆ insert (4, 6) required_538_i9 := by decide +kernel
theorem child_envelope_sub_538_i9 : ∀ j, childrenD_538_i9 j ⊆ envelope_538_i9 := by decide +kernel
theorem pivot_mem_538_i9 : (4, 6) ∈ envelope_538_i9 := by decide +kernel
theorem children_work_538_i9 : ∀ j, Template HasSnaky 9 (childrenC_538_i9 j) (childrenD_538_i9 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_2 4 (1, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_537 4 (3, 9)).mono (by decide +kernel)
theorem row_works_538_i9 : Template HasSnaky 10 required_538_i9 envelope_538_i9 := by
  refine compose HasSnaky 9 childrenC_538_i9 childrenD_538_i9 children_work_538_i9 (4, 6)
    required_538_i9 envelope_538_i9 pivot_mem_538_i9 child_required_sub_538_i9 child_envelope_sub_538_i9 ?_
  intro b hb
  exact common_sub_538_i9 (mem_commonEnvelope childrenD_538_i9 b hb)
def required_538 : Finset Cell := ⟨(([(1, 3), (1, 6), (2, 3), (2, 6), (4, 5), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_538 : Finset Cell := ⟨(([(0, 2), (1, 2), (1, 3), (1, 6), (1, 8), (1, 9), (2, 2), (2, 3), (2, 6), (2, 8), (2, 9), (3, 3), (3, 6), (3, 7), (3, 8), (3, 9), (4, 1), (4, 2), (4, 3), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_538 : Fin 10 → Finset Cell := ![(placed21 0 (4, 1) required_459), required_538_i0, required_538_i1, required_538_i2, required_538_i6, required_538_i7, required_538_i8, (placed21 0 (0, 1) required_529), (placed21 4 (3, 10) required_535), required_538_i9]
def childrenD_538 : Fin 10 → Finset Cell := ![(placed21 0 (4, 1) envelope_459), envelope_538_i0, envelope_538_i1, envelope_538_i2, envelope_538_i6, envelope_538_i7, envelope_538_i8, (placed21 0 (0, 1) envelope_529), (placed21 4 (3, 10) envelope_535), envelope_538_i9]
theorem common_sub_538 : commonEnvelope childrenD_538 ⊆ insert (5, 6) required_538 := by decide +kernel
theorem child_required_sub_538 : ∀ j, childrenC_538 j ⊆ insert (5, 6) required_538 := by decide +kernel
theorem child_envelope_sub_538 : ∀ j, childrenD_538 j ⊆ envelope_538 := by decide +kernel
theorem pivot_mem_538 : (5, 6) ∈ envelope_538 := by decide +kernel
theorem children_work_538 : ∀ j, Template HasSnaky 12 (childrenC_538 j) (childrenD_538 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_459 0 (4, 1)).mono (by decide +kernel)
  · exact row_works_538_i0.mono (by decide +kernel)
  · exact row_works_538_i1.mono (by decide +kernel)
  · exact row_works_538_i2.mono (by decide +kernel)
  · exact row_works_538_i6.mono (by decide +kernel)
  · exact row_works_538_i7.mono (by decide +kernel)
  · exact row_works_538_i8.mono (by decide +kernel)
  · exact (placed21_template row_works_529 0 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_535 4 (3, 10)).mono (by decide +kernel)
  · exact row_works_538_i9.mono (by decide +kernel)
theorem row_works_538 : Template HasSnaky 13 required_538 envelope_538 := by
  refine compose HasSnaky 12 childrenC_538 childrenD_538 children_work_538 (5, 6)
    required_538 envelope_538 pivot_mem_538 child_required_sub_538 child_envelope_sub_538 ?_
  intro b hb
  exact common_sub_538 (mem_commonEnvelope childrenD_538 b hb)
def required_552_i1 : Finset Cell := ⟨(([(3, 7), (4, 7), (6, 6), (7, 6), (7, 7), (8, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_552_i1 : Finset Cell := ⟨(([(3, 7), (4, 6), (4, 7), (5, 6), (6, 6), (6, 7), (7, 6), (7, 7), (8, 6), (8, 7), (9, 6), (9, 7), (10, 6), (10, 7), (11, 6), (11, 7), (12, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_552_i1 : Fin 2 → Finset Cell := ![(placed21 2 (7, 6) required_3), (placed21 1 (5, 6) required_389)]
def childrenD_552_i1 : Fin 2 → Finset Cell := ![(placed21 2 (7, 6) envelope_3), (placed21 1 (5, 6) envelope_389)]
theorem common_sub_552_i1 : commonEnvelope childrenD_552_i1 ⊆ insert (5, 6) required_552_i1 := by decide +kernel
theorem child_required_sub_552_i1 : ∀ j, childrenC_552_i1 j ⊆ insert (5, 6) required_552_i1 := by decide +kernel
theorem child_envelope_sub_552_i1 : ∀ j, childrenD_552_i1 j ⊆ envelope_552_i1 := by decide +kernel
theorem pivot_mem_552_i1 : (5, 6) ∈ envelope_552_i1 := by decide +kernel
theorem children_work_552_i1 : ∀ j, Template HasSnaky 5 (childrenC_552_i1 j) (childrenD_552_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_3 2 (7, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_389 1 (5, 6)).mono (by decide +kernel)
theorem row_works_552_i1 : Template HasSnaky 6 required_552_i1 envelope_552_i1 := by
  refine compose HasSnaky 5 childrenC_552_i1 childrenD_552_i1 children_work_552_i1 (5, 6)
    required_552_i1 envelope_552_i1 pivot_mem_552_i1 child_required_sub_552_i1 child_envelope_sub_552_i1 ?_
  intro b hb
  exact common_sub_552_i1 (mem_commonEnvelope childrenD_552_i1 b hb)
def required_552_i0 : Finset Cell := ⟨(([(3, 7), (4, 7), (6, 6), (7, 6), (8, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_552_i0 : Finset Cell := ⟨(([(3, 7), (4, 6), (4, 7), (5, 6), (6, 2), (6, 3), (6, 4), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (6, 12), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (8, 11), (9, 6), (9, 7), (9, 8), (9, 9), (10, 6), (10, 7), (10, 8), (10, 9), (11, 6), (11, 7), (11, 8), (11, 9), (12, 7), (12, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_552_i0 : Fin 5 → Finset Cell := ![(placed21 1 (4, 4) required_544), (placed21 4 (6, 11) required_545), (placed21 0 (6, 2) required_546), required_552_i1, (placed21 0 (6, 1) required_548)]
def childrenD_552_i0 : Fin 5 → Finset Cell := ![(placed21 1 (4, 4) envelope_544), (placed21 4 (6, 11) envelope_545), (placed21 0 (6, 2) envelope_546), envelope_552_i1, (placed21 0 (6, 1) envelope_548)]
theorem common_sub_552_i0 : commonEnvelope childrenD_552_i0 ⊆ insert (7, 7) required_552_i0 := by decide +kernel
theorem child_required_sub_552_i0 : ∀ j, childrenC_552_i0 j ⊆ insert (7, 7) required_552_i0 := by decide +kernel
theorem child_envelope_sub_552_i0 : ∀ j, childrenD_552_i0 j ⊆ envelope_552_i0 := by decide +kernel
theorem pivot_mem_552_i0 : (7, 7) ∈ envelope_552_i0 := by decide +kernel
theorem children_work_552_i0 : ∀ j, Template HasSnaky 10 (childrenC_552_i0 j) (childrenD_552_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_544 1 (4, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_545 4 (6, 11)).mono (by decide +kernel)
  · exact (placed21_template row_works_546 0 (6, 2)).mono (by decide +kernel)
  · exact row_works_552_i1.mono (by decide +kernel)
  · exact (placed21_template row_works_548 0 (6, 1)).mono (by decide +kernel)
theorem row_works_552_i0 : Template HasSnaky 11 required_552_i0 envelope_552_i0 := by
  refine compose HasSnaky 10 childrenC_552_i0 childrenD_552_i0 children_work_552_i0 (7, 7)
    required_552_i0 envelope_552_i0 pivot_mem_552_i0 child_required_sub_552_i0 child_envelope_sub_552_i0 ?_
  intro b hb
  exact common_sub_552_i0 (mem_commonEnvelope childrenD_552_i0 b hb)
def required_552 : Finset Cell := ⟨(([(3, 4), (3, 7), (4, 4), (4, 7), (6, 6), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_552 : Finset Cell := ⟨(([(0, 3), (1, 2), (1, 3), (2, 0), (2, 1), (2, 2), (2, 3), (2, 5), (2, 6), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 6), (4, 7), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (6, 2), (6, 3), (6, 4), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (6, 12), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (8, 11), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (9, 10), (10, 5), (10, 6), (10, 7), (10, 8), (10, 9), (10, 10), (11, 5), (11, 6), (11, 7), (11, 8), (11, 9), (12, 5), (12, 7), (12, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_552 : Fin 6 → Finset Cell := ![(placed21 1 (4, 4) required_188), (placed21 0 (6, 3) required_258), (placed21 4 (3, 10) required_326), (placed21 3 (0, 8) required_543), required_552_i0, (placed21 0 (2, 1) required_551)]
def childrenD_552 : Fin 6 → Finset Cell := ![(placed21 1 (4, 4) envelope_188), (placed21 0 (6, 3) envelope_258), (placed21 4 (3, 10) envelope_326), (placed21 3 (0, 8) envelope_543), envelope_552_i0, (placed21 0 (2, 1) envelope_551)]
theorem common_sub_552 : commonEnvelope childrenD_552 ⊆ insert (8, 6) required_552 := by decide +kernel
theorem child_required_sub_552 : ∀ j, childrenC_552 j ⊆ insert (8, 6) required_552 := by decide +kernel
theorem child_envelope_sub_552 : ∀ j, childrenD_552 j ⊆ envelope_552 := by decide +kernel
theorem pivot_mem_552 : (8, 6) ∈ envelope_552 := by decide +kernel
theorem children_work_552 : ∀ j, Template HasSnaky 12 (childrenC_552 j) (childrenD_552 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_188 1 (4, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_258 0 (6, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_326 4 (3, 10)).mono (by decide +kernel)
  · exact (placed21_template row_works_543 3 (0, 8)).mono (by decide +kernel)
  · exact row_works_552_i0.mono (by decide +kernel)
  · exact (placed21_template row_works_551 0 (2, 1)).mono (by decide +kernel)
theorem row_works_552 : Template HasSnaky 13 required_552 envelope_552 := by
  refine compose HasSnaky 12 childrenC_552 childrenD_552 children_work_552 (8, 6)
    required_552 envelope_552 pivot_mem_552 child_required_sub_552 child_envelope_sub_552 ?_
  intro b hb
  exact common_sub_552 (mem_commonEnvelope childrenD_552 b hb)
def required_555_i0 : Finset Cell := ⟨(([(0, 2), (1, 2), (3, 3), (3, 4), (3, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_555_i0 : Finset Cell := ⟨(([(0, 2), (1, 2), (2, 0), (2, 1), (2, 2), (2, 3), (2, 6), (2, 7), (2, 8), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 2), (4, 3), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_555_i0 : Fin 3 → Finset Cell := ![(placed21 6 (3, 6) required_61), (placed21 0 (2, 2) required_194), (placed21 0 (0, 1) required_224)]
def childrenD_555_i0 : Fin 3 → Finset Cell := ![(placed21 6 (3, 6) envelope_61), (placed21 0 (2, 2) envelope_194), (placed21 0 (0, 1) envelope_224)]
theorem common_sub_555_i0 : commonEnvelope childrenD_555_i0 ⊆ insert (2, 2) required_555_i0 := by decide +kernel
theorem child_required_sub_555_i0 : ∀ j, childrenC_555_i0 j ⊆ insert (2, 2) required_555_i0 := by decide +kernel
theorem child_envelope_sub_555_i0 : ∀ j, childrenD_555_i0 j ⊆ envelope_555_i0 := by decide +kernel
theorem pivot_mem_555_i0 : (2, 2) ∈ envelope_555_i0 := by decide +kernel
theorem children_work_555_i0 : ∀ j, Template HasSnaky 4 (childrenC_555_i0 j) (childrenD_555_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_61 6 (3, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_194 0 (2, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_224 0 (0, 1)).mono (by decide +kernel)
theorem row_works_555_i0 : Template HasSnaky 5 required_555_i0 envelope_555_i0 := by
  refine compose HasSnaky 4 childrenC_555_i0 childrenD_555_i0 children_work_555_i0 (2, 2)
    required_555_i0 envelope_555_i0 pivot_mem_555_i0 child_required_sub_555_i0 child_envelope_sub_555_i0 ?_
  intro b hb
  exact common_sub_555_i0 (mem_commonEnvelope childrenD_555_i0 b hb)
def required_555 : Finset Cell := ⟨(([(0, 2), (1, 2), (3, 4), (3, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_555 : Finset Cell := ⟨(([(0, 2), (1, 2), (2, 0), (2, 1), (2, 2), (2, 3), (2, 6), (2, 7), (2, 8), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, 5), (7, 6), (7, 7), (8, 5), (8, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_555 : Fin 7 → Finset Cell := ![(placed21 6 (4, 7) required_13), (placed21 2 (4, 1) required_14), (placed21 0 (2, 1) required_31), (placed21 7 (5, 6) required_230), (placed21 0 (2, 1) required_367), (placed21 0 (2, 2) required_428), required_555_i0]
def childrenD_555 : Fin 7 → Finset Cell := ![(placed21 6 (4, 7) envelope_13), (placed21 2 (4, 1) envelope_14), (placed21 0 (2, 1) envelope_31), (placed21 7 (5, 6) envelope_230), (placed21 0 (2, 1) envelope_367), (placed21 0 (2, 2) envelope_428), envelope_555_i0]
theorem common_sub_555 : commonEnvelope childrenD_555 ⊆ insert (3, 3) required_555 := by decide +kernel
theorem child_required_sub_555 : ∀ j, childrenC_555 j ⊆ insert (3, 3) required_555 := by decide +kernel
theorem child_envelope_sub_555 : ∀ j, childrenD_555 j ⊆ envelope_555 := by decide +kernel
theorem pivot_mem_555 : (3, 3) ∈ envelope_555 := by decide +kernel
theorem children_work_555 : ∀ j, Template HasSnaky 12 (childrenC_555 j) (childrenD_555 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_13 6 (4, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_14 2 (4, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_31 0 (2, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_230 7 (5, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_367 0 (2, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_428 0 (2, 2)).mono (by decide +kernel)
  · exact row_works_555_i0.mono (by decide +kernel)
theorem row_works_555 : Template HasSnaky 13 required_555 envelope_555 := by
  refine compose HasSnaky 12 childrenC_555 childrenD_555 children_work_555 (3, 3)
    required_555 envelope_555 pivot_mem_555 child_required_sub_555 child_envelope_sub_555 ?_
  intro b hb
  exact common_sub_555 (mem_commonEnvelope childrenD_555 b hb)
def height_462 : ℕ := 13
def childrenH_462 : Fin 7 → ℕ := ![height_13, height_14, height_31, height_189, height_367, height_428, height_457]
theorem height_exact_462 : height_462 = 1 + Finset.univ.sup childrenH_462 := by decide +kernel
theorem required_origin_462 : ∀ x ∈ required_462,
    (∃ j, x ∈ childrenC_462 j) ∨ ∀ j, x ∈ childrenD_462 j := by decide +kernel
theorem required_exact_462 : required_462 =
    ((Finset.univ.biUnion childrenC_462) ∪ commonEnvelope childrenD_462).erase (1, 5) := by
  exact required_eq_combination childrenC_462 childrenD_462 (1, 5) required_462
    (by decide +kernel) child_required_sub_462 common_sub_462 required_origin_462
theorem envelope_origin_462 : ∀ x ∈ envelope_462,
    x = (1, 5) ∨ ∃ j, x ∈ childrenD_462 j := by decide +kernel
theorem envelope_exact_462 : envelope_462 =
    insert (1, 5) (Finset.univ.biUnion childrenD_462) := by
  exact envelope_eq_combination childrenD_462 (1, 5) envelope_462
    pivot_mem_462 child_envelope_sub_462 envelope_origin_462
def checked_462 : CheckedCard where
  required := required_462
  envelope := envelope_462
  height := height_462
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_462
def height_490 : ℕ := 13
def childrenH_490 : Fin 6 → ℕ := ![height_321, height_321, height_485, height_485, height_489, height_489]
theorem height_exact_490 : height_490 = 1 + Finset.univ.sup childrenH_490 := by decide +kernel
theorem required_origin_490 : ∀ x ∈ required_490,
    (∃ j, x ∈ childrenC_490 j) ∨ ∀ j, x ∈ childrenD_490 j := by decide +kernel
theorem required_exact_490 : required_490 =
    ((Finset.univ.biUnion childrenC_490) ∪ commonEnvelope childrenD_490).erase (5, 7) := by
  exact required_eq_combination childrenC_490 childrenD_490 (5, 7) required_490
    (by decide +kernel) child_required_sub_490 common_sub_490 required_origin_490
theorem envelope_origin_490 : ∀ x ∈ envelope_490,
    x = (5, 7) ∨ ∃ j, x ∈ childrenD_490 j := by decide +kernel
theorem envelope_exact_490 : envelope_490 =
    insert (5, 7) (Finset.univ.biUnion childrenD_490) := by
  exact envelope_eq_combination childrenD_490 (5, 7) envelope_490
    pivot_mem_490 child_envelope_sub_490 envelope_origin_490
def checked_490 : CheckedCard where
  required := required_490
  envelope := envelope_490
  height := height_490
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_490
def height_538_i0 : ℕ := 9
def childrenH_538_i0 : Fin 6 → ℕ := ![height_190, height_190, height_258, height_273, height_415, height_507]
theorem height_exact_538_i0 : height_538_i0 = 1 + Finset.univ.sup childrenH_538_i0 := by decide +kernel
theorem required_origin_538_i0 : ∀ x ∈ required_538_i0,
    (∃ j, x ∈ childrenC_538_i0 j) ∨ ∀ j, x ∈ childrenD_538_i0 j := by decide +kernel
theorem required_exact_538_i0 : required_538_i0 =
    ((Finset.univ.biUnion childrenC_538_i0) ∪ commonEnvelope childrenD_538_i0).erase (5, 7) := by
  exact required_eq_combination childrenC_538_i0 childrenD_538_i0 (5, 7) required_538_i0
    (by decide +kernel) child_required_sub_538_i0 common_sub_538_i0 required_origin_538_i0
theorem envelope_origin_538_i0 : ∀ x ∈ envelope_538_i0,
    x = (5, 7) ∨ ∃ j, x ∈ childrenD_538_i0 j := by decide +kernel
theorem envelope_exact_538_i0 : envelope_538_i0 =
    insert (5, 7) (Finset.univ.biUnion childrenD_538_i0) := by
  exact envelope_eq_combination childrenD_538_i0 (5, 7) envelope_538_i0
    pivot_mem_538_i0 child_envelope_sub_538_i0 envelope_origin_538_i0
def checked_538_i0 : CheckedCard where
  required := required_538_i0
  envelope := envelope_538_i0
  height := height_538_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_538_i0
def height_538_i1 : ℕ := 10
def childrenH_538_i1 : Fin 2 → ℕ := ![height_2, height_512]
theorem height_exact_538_i1 : height_538_i1 = 1 + Finset.univ.sup childrenH_538_i1 := by decide +kernel
theorem required_origin_538_i1 : ∀ x ∈ required_538_i1,
    (∃ j, x ∈ childrenC_538_i1 j) ∨ ∀ j, x ∈ childrenD_538_i1 j := by decide +kernel
theorem required_exact_538_i1 : required_538_i1 =
    ((Finset.univ.biUnion childrenC_538_i1) ∪ commonEnvelope childrenD_538_i1).erase (4, 6) := by
  exact required_eq_combination childrenC_538_i1 childrenD_538_i1 (4, 6) required_538_i1
    (by decide +kernel) child_required_sub_538_i1 common_sub_538_i1 required_origin_538_i1
theorem envelope_origin_538_i1 : ∀ x ∈ envelope_538_i1,
    x = (4, 6) ∨ ∃ j, x ∈ childrenD_538_i1 j := by decide +kernel
theorem envelope_exact_538_i1 : envelope_538_i1 =
    insert (4, 6) (Finset.univ.biUnion childrenD_538_i1) := by
  exact envelope_eq_combination childrenD_538_i1 (4, 6) envelope_538_i1
    pivot_mem_538_i1 child_envelope_sub_538_i1 envelope_origin_538_i1
def checked_538_i1 : CheckedCard where
  required := required_538_i1
  envelope := envelope_538_i1
  height := height_538_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_538_i1
def height_538_i3 : ℕ := 5
def childrenH_538_i3 : Fin 3 → ℕ := ![height_7, height_9, height_354]
theorem height_exact_538_i3 : height_538_i3 = 1 + Finset.univ.sup childrenH_538_i3 := by decide +kernel
theorem required_origin_538_i3 : ∀ x ∈ required_538_i3,
    (∃ j, x ∈ childrenC_538_i3 j) ∨ ∀ j, x ∈ childrenD_538_i3 j := by decide +kernel
theorem required_exact_538_i3 : required_538_i3 =
    ((Finset.univ.biUnion childrenC_538_i3) ∪ commonEnvelope childrenD_538_i3).erase (5, 7) := by
  exact required_eq_combination childrenC_538_i3 childrenD_538_i3 (5, 7) required_538_i3
    (by decide +kernel) child_required_sub_538_i3 common_sub_538_i3 required_origin_538_i3
theorem envelope_origin_538_i3 : ∀ x ∈ envelope_538_i3,
    x = (5, 7) ∨ ∃ j, x ∈ childrenD_538_i3 j := by decide +kernel
theorem envelope_exact_538_i3 : envelope_538_i3 =
    insert (5, 7) (Finset.univ.biUnion childrenD_538_i3) := by
  exact envelope_eq_combination childrenD_538_i3 (5, 7) envelope_538_i3
    pivot_mem_538_i3 child_envelope_sub_538_i3 envelope_origin_538_i3
def checked_538_i3 : CheckedCard where
  required := required_538_i3
  envelope := envelope_538_i3
  height := height_538_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_538_i3
def height_538_i4 : ℕ := 3
def childrenH_538_i4 : Fin 2 → ℕ := ![height_2, height_15]
theorem height_exact_538_i4 : height_538_i4 = 1 + Finset.univ.sup childrenH_538_i4 := by decide +kernel
theorem required_origin_538_i4 : ∀ x ∈ required_538_i4,
    (∃ j, x ∈ childrenC_538_i4 j) ∨ ∀ j, x ∈ childrenD_538_i4 j := by decide +kernel
theorem required_exact_538_i4 : required_538_i4 =
    ((Finset.univ.biUnion childrenC_538_i4) ∪ commonEnvelope childrenD_538_i4).erase (4, 6) := by
  exact required_eq_combination childrenC_538_i4 childrenD_538_i4 (4, 6) required_538_i4
    (by decide +kernel) child_required_sub_538_i4 common_sub_538_i4 required_origin_538_i4
theorem envelope_origin_538_i4 : ∀ x ∈ envelope_538_i4,
    x = (4, 6) ∨ ∃ j, x ∈ childrenD_538_i4 j := by decide +kernel
theorem envelope_exact_538_i4 : envelope_538_i4 =
    insert (4, 6) (Finset.univ.biUnion childrenD_538_i4) := by
  exact envelope_eq_combination childrenD_538_i4 (4, 6) envelope_538_i4
    pivot_mem_538_i4 child_envelope_sub_538_i4 envelope_origin_538_i4
def checked_538_i4 : CheckedCard where
  required := required_538_i4
  envelope := envelope_538_i4
  height := height_538_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_538_i4
def height_538_i5 : ℕ := 6
def childrenH_538_i5 : Fin 2 → ℕ := ![height_8, height_505]
theorem height_exact_538_i5 : height_538_i5 = 1 + Finset.univ.sup childrenH_538_i5 := by decide +kernel
theorem required_origin_538_i5 : ∀ x ∈ required_538_i5,
    (∃ j, x ∈ childrenC_538_i5 j) ∨ ∀ j, x ∈ childrenD_538_i5 j := by decide +kernel
theorem required_exact_538_i5 : required_538_i5 =
    ((Finset.univ.biUnion childrenC_538_i5) ∪ commonEnvelope childrenD_538_i5).erase (5, 7) := by
  exact required_eq_combination childrenC_538_i5 childrenD_538_i5 (5, 7) required_538_i5
    (by decide +kernel) child_required_sub_538_i5 common_sub_538_i5 required_origin_538_i5
theorem envelope_origin_538_i5 : ∀ x ∈ envelope_538_i5,
    x = (5, 7) ∨ ∃ j, x ∈ childrenD_538_i5 j := by decide +kernel
theorem envelope_exact_538_i5 : envelope_538_i5 =
    insert (5, 7) (Finset.univ.biUnion childrenD_538_i5) := by
  exact envelope_eq_combination childrenD_538_i5 (5, 7) envelope_538_i5
    pivot_mem_538_i5 child_envelope_sub_538_i5 envelope_origin_538_i5
def checked_538_i5 : CheckedCard where
  required := required_538_i5
  envelope := envelope_538_i5
  height := height_538_i5
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_538_i5
def height_538_i2 : ℕ := 7
def childrenH_538_i2 : Fin 4 → ℕ := ![height_136, height_538_i3, height_538_i4, height_538_i5]
theorem height_exact_538_i2 : height_538_i2 = 1 + Finset.univ.sup childrenH_538_i2 := by decide +kernel
theorem required_origin_538_i2 : ∀ x ∈ required_538_i2,
    (∃ j, x ∈ childrenC_538_i2 j) ∨ ∀ j, x ∈ childrenD_538_i2 j := by decide +kernel
theorem required_exact_538_i2 : required_538_i2 =
    ((Finset.univ.biUnion childrenC_538_i2) ∪ commonEnvelope childrenD_538_i2).erase (5, 4) := by
  exact required_eq_combination childrenC_538_i2 childrenD_538_i2 (5, 4) required_538_i2
    (by decide +kernel) child_required_sub_538_i2 common_sub_538_i2 required_origin_538_i2
theorem envelope_origin_538_i2 : ∀ x ∈ envelope_538_i2,
    x = (5, 4) ∨ ∃ j, x ∈ childrenD_538_i2 j := by decide +kernel
theorem envelope_exact_538_i2 : envelope_538_i2 =
    insert (5, 4) (Finset.univ.biUnion childrenD_538_i2) := by
  exact envelope_eq_combination childrenD_538_i2 (5, 4) envelope_538_i2
    pivot_mem_538_i2 child_envelope_sub_538_i2 envelope_origin_538_i2
def checked_538_i2 : CheckedCard where
  required := required_538_i2
  envelope := envelope_538_i2
  height := height_538_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_538_i2
def height_538_i6 : ℕ := 12
def childrenH_538_i6 : Fin 2 → ℕ := ![height_2, height_517]
theorem height_exact_538_i6 : height_538_i6 = 1 + Finset.univ.sup childrenH_538_i6 := by decide +kernel
theorem required_origin_538_i6 : ∀ x ∈ required_538_i6,
    (∃ j, x ∈ childrenC_538_i6 j) ∨ ∀ j, x ∈ childrenD_538_i6 j := by decide +kernel
theorem required_exact_538_i6 : required_538_i6 =
    ((Finset.univ.biUnion childrenC_538_i6) ∪ commonEnvelope childrenD_538_i6).erase (4, 6) := by
  exact required_eq_combination childrenC_538_i6 childrenD_538_i6 (4, 6) required_538_i6
    (by decide +kernel) child_required_sub_538_i6 common_sub_538_i6 required_origin_538_i6
theorem envelope_origin_538_i6 : ∀ x ∈ envelope_538_i6,
    x = (4, 6) ∨ ∃ j, x ∈ childrenD_538_i6 j := by decide +kernel
theorem envelope_exact_538_i6 : envelope_538_i6 =
    insert (4, 6) (Finset.univ.biUnion childrenD_538_i6) := by
  exact envelope_eq_combination childrenD_538_i6 (4, 6) envelope_538_i6
    pivot_mem_538_i6 child_envelope_sub_538_i6 envelope_origin_538_i6
def checked_538_i6 : CheckedCard where
  required := required_538_i6
  envelope := envelope_538_i6
  height := height_538_i6
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_538_i6
def height_538_i7 : ℕ := 9
def childrenH_538_i7 : Fin 7 → ℕ := ![height_116, height_180, height_258, height_273, height_275, height_415, height_518]
theorem height_exact_538_i7 : height_538_i7 = 1 + Finset.univ.sup childrenH_538_i7 := by decide +kernel
theorem required_origin_538_i7 : ∀ x ∈ required_538_i7,
    (∃ j, x ∈ childrenC_538_i7 j) ∨ ∀ j, x ∈ childrenD_538_i7 j := by decide +kernel
theorem required_exact_538_i7 : required_538_i7 =
    ((Finset.univ.biUnion childrenC_538_i7) ∪ commonEnvelope childrenD_538_i7).erase (5, 7) := by
  exact required_eq_combination childrenC_538_i7 childrenD_538_i7 (5, 7) required_538_i7
    (by decide +kernel) child_required_sub_538_i7 common_sub_538_i7 required_origin_538_i7
theorem envelope_origin_538_i7 : ∀ x ∈ envelope_538_i7,
    x = (5, 7) ∨ ∃ j, x ∈ childrenD_538_i7 j := by decide +kernel
theorem envelope_exact_538_i7 : envelope_538_i7 =
    insert (5, 7) (Finset.univ.biUnion childrenD_538_i7) := by
  exact envelope_eq_combination childrenD_538_i7 (5, 7) envelope_538_i7
    pivot_mem_538_i7 child_envelope_sub_538_i7 envelope_origin_538_i7
def checked_538_i7 : CheckedCard where
  required := required_538_i7
  envelope := envelope_538_i7
  height := height_538_i7
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_538_i7
def height_538_i8 : ℕ := 12
def childrenH_538_i8 : Fin 2 → ℕ := ![height_2, height_527]
theorem height_exact_538_i8 : height_538_i8 = 1 + Finset.univ.sup childrenH_538_i8 := by decide +kernel
theorem required_origin_538_i8 : ∀ x ∈ required_538_i8,
    (∃ j, x ∈ childrenC_538_i8 j) ∨ ∀ j, x ∈ childrenD_538_i8 j := by decide +kernel
theorem required_exact_538_i8 : required_538_i8 =
    ((Finset.univ.biUnion childrenC_538_i8) ∪ commonEnvelope childrenD_538_i8).erase (4, 6) := by
  exact required_eq_combination childrenC_538_i8 childrenD_538_i8 (4, 6) required_538_i8
    (by decide +kernel) child_required_sub_538_i8 common_sub_538_i8 required_origin_538_i8
theorem envelope_origin_538_i8 : ∀ x ∈ envelope_538_i8,
    x = (4, 6) ∨ ∃ j, x ∈ childrenD_538_i8 j := by decide +kernel
theorem envelope_exact_538_i8 : envelope_538_i8 =
    insert (4, 6) (Finset.univ.biUnion childrenD_538_i8) := by
  exact envelope_eq_combination childrenD_538_i8 (4, 6) envelope_538_i8
    pivot_mem_538_i8 child_envelope_sub_538_i8 envelope_origin_538_i8
def checked_538_i8 : CheckedCard where
  required := required_538_i8
  envelope := envelope_538_i8
  height := height_538_i8
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_538_i8
def height_538_i9 : ℕ := 10
def childrenH_538_i9 : Fin 2 → ℕ := ![height_2, height_537]
theorem height_exact_538_i9 : height_538_i9 = 1 + Finset.univ.sup childrenH_538_i9 := by decide +kernel
theorem required_origin_538_i9 : ∀ x ∈ required_538_i9,
    (∃ j, x ∈ childrenC_538_i9 j) ∨ ∀ j, x ∈ childrenD_538_i9 j := by decide +kernel
theorem required_exact_538_i9 : required_538_i9 =
    ((Finset.univ.biUnion childrenC_538_i9) ∪ commonEnvelope childrenD_538_i9).erase (4, 6) := by
  exact required_eq_combination childrenC_538_i9 childrenD_538_i9 (4, 6) required_538_i9
    (by decide +kernel) child_required_sub_538_i9 common_sub_538_i9 required_origin_538_i9
theorem envelope_origin_538_i9 : ∀ x ∈ envelope_538_i9,
    x = (4, 6) ∨ ∃ j, x ∈ childrenD_538_i9 j := by decide +kernel
theorem envelope_exact_538_i9 : envelope_538_i9 =
    insert (4, 6) (Finset.univ.biUnion childrenD_538_i9) := by
  exact envelope_eq_combination childrenD_538_i9 (4, 6) envelope_538_i9
    pivot_mem_538_i9 child_envelope_sub_538_i9 envelope_origin_538_i9
def checked_538_i9 : CheckedCard where
  required := required_538_i9
  envelope := envelope_538_i9
  height := height_538_i9
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_538_i9
def height_538 : ℕ := 13
def childrenH_538 : Fin 10 → ℕ := ![height_459, height_538_i0, height_538_i1, height_538_i2, height_538_i6, height_538_i7, height_538_i8, height_529, height_535, height_538_i9]
theorem height_exact_538 : height_538 = 1 + Finset.univ.sup childrenH_538 := by decide +kernel
theorem required_origin_538 : ∀ x ∈ required_538,
    (∃ j, x ∈ childrenC_538 j) ∨ ∀ j, x ∈ childrenD_538 j := by decide +kernel
theorem required_exact_538 : required_538 =
    ((Finset.univ.biUnion childrenC_538) ∪ commonEnvelope childrenD_538).erase (5, 6) := by
  exact required_eq_combination childrenC_538 childrenD_538 (5, 6) required_538
    (by decide +kernel) child_required_sub_538 common_sub_538 required_origin_538
theorem envelope_origin_538 : ∀ x ∈ envelope_538,
    x = (5, 6) ∨ ∃ j, x ∈ childrenD_538 j := by decide +kernel
theorem envelope_exact_538 : envelope_538 =
    insert (5, 6) (Finset.univ.biUnion childrenD_538) := by
  exact envelope_eq_combination childrenD_538 (5, 6) envelope_538
    pivot_mem_538 child_envelope_sub_538 envelope_origin_538
def checked_538 : CheckedCard where
  required := required_538
  envelope := envelope_538
  height := height_538
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_538
def height_552_i1 : ℕ := 6
def childrenH_552_i1 : Fin 2 → ℕ := ![height_3, height_389]
theorem height_exact_552_i1 : height_552_i1 = 1 + Finset.univ.sup childrenH_552_i1 := by decide +kernel
theorem required_origin_552_i1 : ∀ x ∈ required_552_i1,
    (∃ j, x ∈ childrenC_552_i1 j) ∨ ∀ j, x ∈ childrenD_552_i1 j := by decide +kernel
theorem required_exact_552_i1 : required_552_i1 =
    ((Finset.univ.biUnion childrenC_552_i1) ∪ commonEnvelope childrenD_552_i1).erase (5, 6) := by
  exact required_eq_combination childrenC_552_i1 childrenD_552_i1 (5, 6) required_552_i1
    (by decide +kernel) child_required_sub_552_i1 common_sub_552_i1 required_origin_552_i1
theorem envelope_origin_552_i1 : ∀ x ∈ envelope_552_i1,
    x = (5, 6) ∨ ∃ j, x ∈ childrenD_552_i1 j := by decide +kernel
theorem envelope_exact_552_i1 : envelope_552_i1 =
    insert (5, 6) (Finset.univ.biUnion childrenD_552_i1) := by
  exact envelope_eq_combination childrenD_552_i1 (5, 6) envelope_552_i1
    pivot_mem_552_i1 child_envelope_sub_552_i1 envelope_origin_552_i1
def checked_552_i1 : CheckedCard where
  required := required_552_i1
  envelope := envelope_552_i1
  height := height_552_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_552_i1
def height_552_i0 : ℕ := 11
def childrenH_552_i0 : Fin 5 → ℕ := ![height_544, height_545, height_546, height_552_i1, height_548]
theorem height_exact_552_i0 : height_552_i0 = 1 + Finset.univ.sup childrenH_552_i0 := by decide +kernel
theorem required_origin_552_i0 : ∀ x ∈ required_552_i0,
    (∃ j, x ∈ childrenC_552_i0 j) ∨ ∀ j, x ∈ childrenD_552_i0 j := by decide +kernel
theorem required_exact_552_i0 : required_552_i0 =
    ((Finset.univ.biUnion childrenC_552_i0) ∪ commonEnvelope childrenD_552_i0).erase (7, 7) := by
  exact required_eq_combination childrenC_552_i0 childrenD_552_i0 (7, 7) required_552_i0
    (by decide +kernel) child_required_sub_552_i0 common_sub_552_i0 required_origin_552_i0
theorem envelope_origin_552_i0 : ∀ x ∈ envelope_552_i0,
    x = (7, 7) ∨ ∃ j, x ∈ childrenD_552_i0 j := by decide +kernel
theorem envelope_exact_552_i0 : envelope_552_i0 =
    insert (7, 7) (Finset.univ.biUnion childrenD_552_i0) := by
  exact envelope_eq_combination childrenD_552_i0 (7, 7) envelope_552_i0
    pivot_mem_552_i0 child_envelope_sub_552_i0 envelope_origin_552_i0
def checked_552_i0 : CheckedCard where
  required := required_552_i0
  envelope := envelope_552_i0
  height := height_552_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_552_i0
def height_552 : ℕ := 13
def childrenH_552 : Fin 6 → ℕ := ![height_188, height_258, height_326, height_543, height_552_i0, height_551]
theorem height_exact_552 : height_552 = 1 + Finset.univ.sup childrenH_552 := by decide +kernel
theorem required_origin_552 : ∀ x ∈ required_552,
    (∃ j, x ∈ childrenC_552 j) ∨ ∀ j, x ∈ childrenD_552 j := by decide +kernel
theorem required_exact_552 : required_552 =
    ((Finset.univ.biUnion childrenC_552) ∪ commonEnvelope childrenD_552).erase (8, 6) := by
  exact required_eq_combination childrenC_552 childrenD_552 (8, 6) required_552
    (by decide +kernel) child_required_sub_552 common_sub_552 required_origin_552
theorem envelope_origin_552 : ∀ x ∈ envelope_552,
    x = (8, 6) ∨ ∃ j, x ∈ childrenD_552 j := by decide +kernel
theorem envelope_exact_552 : envelope_552 =
    insert (8, 6) (Finset.univ.biUnion childrenD_552) := by
  exact envelope_eq_combination childrenD_552 (8, 6) envelope_552
    pivot_mem_552 child_envelope_sub_552 envelope_origin_552
def checked_552 : CheckedCard where
  required := required_552
  envelope := envelope_552
  height := height_552
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_552
def height_555_i0 : ℕ := 5
def childrenH_555_i0 : Fin 3 → ℕ := ![height_61, height_194, height_224]
theorem height_exact_555_i0 : height_555_i0 = 1 + Finset.univ.sup childrenH_555_i0 := by decide +kernel
theorem required_origin_555_i0 : ∀ x ∈ required_555_i0,
    (∃ j, x ∈ childrenC_555_i0 j) ∨ ∀ j, x ∈ childrenD_555_i0 j := by decide +kernel
theorem required_exact_555_i0 : required_555_i0 =
    ((Finset.univ.biUnion childrenC_555_i0) ∪ commonEnvelope childrenD_555_i0).erase (2, 2) := by
  exact required_eq_combination childrenC_555_i0 childrenD_555_i0 (2, 2) required_555_i0
    (by decide +kernel) child_required_sub_555_i0 common_sub_555_i0 required_origin_555_i0
theorem envelope_origin_555_i0 : ∀ x ∈ envelope_555_i0,
    x = (2, 2) ∨ ∃ j, x ∈ childrenD_555_i0 j := by decide +kernel
theorem envelope_exact_555_i0 : envelope_555_i0 =
    insert (2, 2) (Finset.univ.biUnion childrenD_555_i0) := by
  exact envelope_eq_combination childrenD_555_i0 (2, 2) envelope_555_i0
    pivot_mem_555_i0 child_envelope_sub_555_i0 envelope_origin_555_i0
def checked_555_i0 : CheckedCard where
  required := required_555_i0
  envelope := envelope_555_i0
  height := height_555_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_555_i0
def height_555 : ℕ := 13
def childrenH_555 : Fin 7 → ℕ := ![height_13, height_14, height_31, height_230, height_367, height_428, height_555_i0]
theorem height_exact_555 : height_555 = 1 + Finset.univ.sup childrenH_555 := by decide +kernel
theorem required_origin_555 : ∀ x ∈ required_555,
    (∃ j, x ∈ childrenC_555 j) ∨ ∀ j, x ∈ childrenD_555 j := by decide +kernel
theorem required_exact_555 : required_555 =
    ((Finset.univ.biUnion childrenC_555) ∪ commonEnvelope childrenD_555).erase (3, 3) := by
  exact required_eq_combination childrenC_555 childrenD_555 (3, 3) required_555
    (by decide +kernel) child_required_sub_555 common_sub_555 required_origin_555
theorem envelope_origin_555 : ∀ x ∈ envelope_555,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_555 j := by decide +kernel
theorem envelope_exact_555 : envelope_555 =
    insert (3, 3) (Finset.univ.biUnion childrenD_555) := by
  exact envelope_eq_combination childrenD_555 (3, 3) envelope_555
    pivot_mem_555 child_envelope_sub_555 envelope_origin_555
def checked_555 : CheckedCard where
  required := required_555
  envelope := envelope_555
  height := height_555
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_555
end SnakyPrototype.Certificate21

end OAI
