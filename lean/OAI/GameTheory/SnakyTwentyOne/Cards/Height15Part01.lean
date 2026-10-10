import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height10Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height10Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height10Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height10Part06
import OAI.GameTheory.SnakyTwentyOne.Cards.Height11Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height12Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height12Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height12Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height13Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height13Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height13Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height13Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height14Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height14Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height14Part03
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_573_i0 : Finset Cell := ⟨(([(0, 3), (3, 3), (3, 4), (3, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_573_i0 : Finset Cell := ⟨(([(0, 3), (0, 5), (1, 3), (1, 5), (1, 6), (2, 2), (2, 3), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, 5), (5, 6), (5, 7), (6, 5), (6, 6), (6, 7), (7, 5), (7, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_573_i0 : Fin 5 → Finset Cell := ![(placed21 1 (2, 3) required_8), (placed21 1 (0, 3) required_115), (placed21 5 (4, 3) required_197), (placed21 0 (0, 2) required_286), (placed21 0 (0, 2) required_339)]
def childrenD_573_i0 : Fin 5 → Finset Cell := ![(placed21 1 (2, 3) envelope_8), (placed21 1 (0, 3) envelope_115), (placed21 5 (4, 3) envelope_197), (placed21 0 (0, 2) envelope_286), (placed21 0 (0, 2) envelope_339)]
theorem common_sub_573_i0 : commonEnvelope childrenD_573_i0 ⊆ insert (3, 5) required_573_i0 := by decide +kernel
theorem child_required_sub_573_i0 : ∀ j, childrenC_573_i0 j ⊆ insert (3, 5) required_573_i0 := by decide +kernel
theorem child_envelope_sub_573_i0 : ∀ j, childrenD_573_i0 j ⊆ envelope_573_i0 := by decide +kernel
theorem pivot_mem_573_i0 : (3, 5) ∈ envelope_573_i0 := by decide +kernel
theorem children_work_573_i0 : ∀ j, Template HasSnaky 7 (childrenC_573_i0 j) (childrenD_573_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_8 1 (2, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_115 1 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_197 5 (4, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_286 0 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_339 0 (0, 2)).mono (by decide +kernel)
theorem row_works_573_i0 : Template HasSnaky 8 required_573_i0 envelope_573_i0 := by
  refine compose HasSnaky 7 childrenC_573_i0 childrenD_573_i0 children_work_573_i0 (3, 5)
    required_573_i0 envelope_573_i0 pivot_mem_573_i0 child_required_sub_573_i0 child_envelope_sub_573_i0 ?_
  intro b hb
  exact common_sub_573_i0 (mem_commonEnvelope childrenD_573_i0 b hb)
def required_573_i1 : Finset Cell := ⟨(([(3, 3), (3, 4), (3, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_573_i1 : Finset Cell := ⟨(([(1, 5), (2, 5), (2, 6), (2, 7), (2, 8), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 4), (5, 5), (5, 6), (5, 7), (6, 5), (6, 6), (6, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_573_i1 : Fin 4 → Finset Cell := ![(placed21 0 (3, 2) required_7), (placed21 1 (2, 3) required_8), (placed21 2 (4, 2) required_9), (placed21 3 (1, 7) required_473)]
def childrenD_573_i1 : Fin 4 → Finset Cell := ![(placed21 0 (3, 2) envelope_7), (placed21 1 (2, 3) envelope_8), (placed21 2 (4, 2) envelope_9), (placed21 3 (1, 7) envelope_473)]
theorem common_sub_573_i1 : commonEnvelope childrenD_573_i1 ⊆ insert (3, 5) required_573_i1 := by decide +kernel
theorem child_required_sub_573_i1 : ∀ j, childrenC_573_i1 j ⊆ insert (3, 5) required_573_i1 := by decide +kernel
theorem child_envelope_sub_573_i1 : ∀ j, childrenD_573_i1 j ⊆ envelope_573_i1 := by decide +kernel
theorem pivot_mem_573_i1 : (3, 5) ∈ envelope_573_i1 := by decide +kernel
theorem children_work_573_i1 : ∀ j, Template HasSnaky 8 (childrenC_573_i1 j) (childrenD_573_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 0 (3, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_8 1 (2, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_9 2 (4, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_473 3 (1, 7)).mono (by decide +kernel)
theorem row_works_573_i1 : Template HasSnaky 9 required_573_i1 envelope_573_i1 := by
  refine compose HasSnaky 8 childrenC_573_i1 childrenD_573_i1 children_work_573_i1 (3, 5)
    required_573_i1 envelope_573_i1 pivot_mem_573_i1 child_required_sub_573_i1 child_envelope_sub_573_i1 ?_
  intro b hb
  exact common_sub_573_i1 (mem_commonEnvelope childrenD_573_i1 b hb)
def required_573_i2 : Finset Cell := ⟨(([(0, 3), (0, 4), (1, 6), (3, 3), (3, 4), (3, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_573_i2 : Finset Cell := ⟨(([(0, 3), (0, 4), (0, 5), (0, 7), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 2), (2, 3), (2, 5), (2, 6), (2, 7), (2, 8), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 2), (4, 3), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 5), (5, 6), (5, 7), (6, 5), (6, 6), (6, 7), (7, 5), (7, 6), (7, 7), (8, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_573_i2 : Fin 4 → Finset Cell := ![(placed21 1 (2, 3) required_8), (placed21 0 (0, 2) required_403), (placed21 0 (0, 3) required_487), (placed21 0 (0, 2) required_492)]
def childrenD_573_i2 : Fin 4 → Finset Cell := ![(placed21 1 (2, 3) envelope_8), (placed21 0 (0, 2) envelope_403), (placed21 0 (0, 3) envelope_487), (placed21 0 (0, 2) envelope_492)]
theorem common_sub_573_i2 : commonEnvelope childrenD_573_i2 ⊆ insert (3, 5) required_573_i2 := by decide +kernel
theorem child_required_sub_573_i2 : ∀ j, childrenC_573_i2 j ⊆ insert (3, 5) required_573_i2 := by decide +kernel
theorem child_envelope_sub_573_i2 : ∀ j, childrenD_573_i2 j ⊆ envelope_573_i2 := by decide +kernel
theorem pivot_mem_573_i2 : (3, 5) ∈ envelope_573_i2 := by decide +kernel
theorem children_work_573_i2 : ∀ j, Template HasSnaky 7 (childrenC_573_i2 j) (childrenD_573_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_8 1 (2, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_403 0 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_487 0 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_492 0 (0, 2)).mono (by decide +kernel)
theorem row_works_573_i2 : Template HasSnaky 8 required_573_i2 envelope_573_i2 := by
  refine compose HasSnaky 7 childrenC_573_i2 childrenD_573_i2 children_work_573_i2 (3, 5)
    required_573_i2 envelope_573_i2 pivot_mem_573_i2 child_required_sub_573_i2 child_envelope_sub_573_i2 ?_
  intro b hb
  exact common_sub_573_i2 (mem_commonEnvelope childrenD_573_i2 b hb)
def required_573_i3 : Finset Cell := ⟨(([(0, 3), (0, 4), (1, 6), (3, 3), (3, 4), (3, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_573_i3 : Finset Cell := ⟨(([(0, 3), (0, 4), (0, 5), (0, 7), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 2), (2, 3), (2, 5), (2, 6), (2, 7), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 5), (5, 6), (5, 7), (6, 5), (6, 6), (6, 7), (7, 5), (7, 6), (7, 7), (8, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_573_i3 : Fin 2 → Finset Cell := ![(placed21 0 (0, 2) required_87), (placed21 0 (0, 3) required_487)]
def childrenD_573_i3 : Fin 2 → Finset Cell := ![(placed21 0 (0, 2) envelope_87), (placed21 0 (0, 3) envelope_487)]
theorem common_sub_573_i3 : commonEnvelope childrenD_573_i3 ⊆ insert (3, 5) required_573_i3 := by decide +kernel
theorem child_required_sub_573_i3 : ∀ j, childrenC_573_i3 j ⊆ insert (3, 5) required_573_i3 := by decide +kernel
theorem child_envelope_sub_573_i3 : ∀ j, childrenD_573_i3 j ⊆ envelope_573_i3 := by decide +kernel
theorem pivot_mem_573_i3 : (3, 5) ∈ envelope_573_i3 := by decide +kernel
theorem children_work_573_i3 : ∀ j, Template HasSnaky 7 (childrenC_573_i3 j) (childrenD_573_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_87 0 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_487 0 (0, 3)).mono (by decide +kernel)
theorem row_works_573_i3 : Template HasSnaky 8 required_573_i3 envelope_573_i3 := by
  refine compose HasSnaky 7 childrenC_573_i3 childrenD_573_i3 children_work_573_i3 (3, 5)
    required_573_i3 envelope_573_i3 pivot_mem_573_i3 child_required_sub_573_i3 child_envelope_sub_573_i3 ?_
  intro b hb
  exact common_sub_573_i3 (mem_commonEnvelope childrenD_573_i3 b hb)
def required_573_i4 : Finset Cell := ⟨(([(0, 3), (0, 4), (1, 6), (3, 3), (3, 4), (3, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_573_i4 : Finset Cell := ⟨(([(0, 3), (0, 4), (0, 5), (0, 7), (0, 8), (0, 9), (0, 10), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, 3), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (3, 3), (3, 4), (3, 6), (3, 7), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, 5), (8, 6), (8, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_573_i4 : Fin 2 → Finset Cell := ![(placed21 0 (0, 3) required_107), required_572]
def childrenD_573_i4 : Fin 2 → Finset Cell := ![(placed21 0 (0, 3) envelope_107), envelope_572]
theorem common_sub_573_i4 : commonEnvelope childrenD_573_i4 ⊆ insert (1, 7) required_573_i4 := by decide +kernel
theorem child_required_sub_573_i4 : ∀ j, childrenC_573_i4 j ⊆ insert (1, 7) required_573_i4 := by decide +kernel
theorem child_envelope_sub_573_i4 : ∀ j, childrenD_573_i4 j ⊆ envelope_573_i4 := by decide +kernel
theorem pivot_mem_573_i4 : (1, 7) ∈ envelope_573_i4 := by decide +kernel
theorem children_work_573_i4 : ∀ j, Template HasSnaky 13 (childrenC_573_i4 j) (childrenD_573_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_107 0 (0, 3)).mono (by decide +kernel)
  · exact row_works_572.mono (by decide +kernel)
theorem row_works_573_i4 : Template HasSnaky 14 required_573_i4 envelope_573_i4 := by
  refine compose HasSnaky 13 childrenC_573_i4 childrenD_573_i4 children_work_573_i4 (1, 7)
    required_573_i4 envelope_573_i4 pivot_mem_573_i4 child_required_sub_573_i4 child_envelope_sub_573_i4 ?_
  intro b hb
  exact common_sub_573_i4 (mem_commonEnvelope childrenD_573_i4 b hb)
def required_573_i5 : Finset Cell := ⟨(([(0, 3), (0, 4), (1, 6), (3, 3), (3, 4), (3, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_573_i5 : Finset Cell := ⟨(([(0, 3), (0, 4), (0, 7), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 2), (2, 3), (2, 6), (2, 7), (2, 8), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 2), (4, 3), (4, 4), (4, 5), (4, 7), (4, 8), (4, 9), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_573_i5 : Fin 4 → Finset Cell := ![(placed21 2 (4, 2) required_9), (placed21 0 (0, 2) required_249), (placed21 7 (5, 6) required_383), (placed21 0 (0, 2) required_403)]
def childrenD_573_i5 : Fin 4 → Finset Cell := ![(placed21 2 (4, 2) envelope_9), (placed21 0 (0, 2) envelope_249), (placed21 7 (5, 6) envelope_383), (placed21 0 (0, 2) envelope_403)]
theorem common_sub_573_i5 : commonEnvelope childrenD_573_i5 ⊆ insert (3, 5) required_573_i5 := by decide +kernel
theorem child_required_sub_573_i5 : ∀ j, childrenC_573_i5 j ⊆ insert (3, 5) required_573_i5 := by decide +kernel
theorem child_envelope_sub_573_i5 : ∀ j, childrenD_573_i5 j ⊆ envelope_573_i5 := by decide +kernel
theorem pivot_mem_573_i5 : (3, 5) ∈ envelope_573_i5 := by decide +kernel
theorem children_work_573_i5 : ∀ j, Template HasSnaky 6 (childrenC_573_i5 j) (childrenD_573_i5 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_9 2 (4, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_249 0 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_383 7 (5, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_403 0 (0, 2)).mono (by decide +kernel)
theorem row_works_573_i5 : Template HasSnaky 7 required_573_i5 envelope_573_i5 := by
  refine compose HasSnaky 6 childrenC_573_i5 childrenD_573_i5 children_work_573_i5 (3, 5)
    required_573_i5 envelope_573_i5 pivot_mem_573_i5 child_required_sub_573_i5 child_envelope_sub_573_i5 ?_
  intro b hb
  exact common_sub_573_i5 (mem_commonEnvelope childrenD_573_i5 b hb)
def required_573 : Finset Cell := ⟨(([(0, 3), (0, 4), (1, 6), (3, 3), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_573 : Finset Cell := ⟨(([(0, 3), (0, 4), (0, 5), (0, 7), (0, 8), (0, 9), (0, 10), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, 2), (2, 3), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, 5), (8, 6), (8, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_573 : Fin 10 → Finset Cell := ![(placed21 0 (0, 2) required_384), (placed21 0 (0, 2) required_385), (placed21 0 (0, 2) required_493), (placed21 0 (0, 2) required_494), required_573_i0, required_573_i1, required_573_i2, required_573_i3, required_573_i4, required_573_i5]
def childrenD_573 : Fin 10 → Finset Cell := ![(placed21 0 (0, 2) envelope_384), (placed21 0 (0, 2) envelope_385), (placed21 0 (0, 2) envelope_493), (placed21 0 (0, 2) envelope_494), envelope_573_i0, envelope_573_i1, envelope_573_i2, envelope_573_i3, envelope_573_i4, envelope_573_i5]
theorem common_sub_573 : commonEnvelope childrenD_573 ⊆ insert (3, 6) required_573 := by decide +kernel
theorem child_required_sub_573 : ∀ j, childrenC_573 j ⊆ insert (3, 6) required_573 := by decide +kernel
theorem child_envelope_sub_573 : ∀ j, childrenD_573 j ⊆ envelope_573 := by decide +kernel
theorem pivot_mem_573 : (3, 6) ∈ envelope_573 := by decide +kernel
theorem children_work_573 : ∀ j, Template HasSnaky 14 (childrenC_573 j) (childrenD_573 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_384 0 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_385 0 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_493 0 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_494 0 (0, 2)).mono (by decide +kernel)
  · exact row_works_573_i0.mono (by decide +kernel)
  · exact row_works_573_i1.mono (by decide +kernel)
  · exact row_works_573_i2.mono (by decide +kernel)
  · exact row_works_573_i3.mono (by decide +kernel)
  · exact row_works_573_i4.mono (by decide +kernel)
  · exact row_works_573_i5.mono (by decide +kernel)
theorem row_works_573 : Template HasSnaky 15 required_573 envelope_573 := by
  refine compose HasSnaky 14 childrenC_573 childrenD_573 children_work_573 (3, 6)
    required_573 envelope_573 pivot_mem_573 child_required_sub_573 child_envelope_sub_573 ?_
  intro b hb
  exact common_sub_573 (mem_commonEnvelope childrenD_573 b hb)
def required_583_i2 : Finset Cell := ⟨(([(3, 5), (3, 8), (4, 8), (5, 6), (6, 6), (7, 6), (8, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_583_i2 : Finset Cell := ⟨(([(2, 7), (2, 9), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 8), (4, 9), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (7, 3), (7, 4), (7, 5), (7, 6), (7, 8), (7, 9), (7, 10), (8, 6), (8, 7), (9, 6), (9, 7), (10, 6), (10, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_583_i2 : Fin 2 → Finset Cell := ![(placed21 1 (5, 6) required_6), (placed21 4 (2, 10) required_576)]
def childrenD_583_i2 : Fin 2 → Finset Cell := ![(placed21 1 (5, 6) envelope_6), (placed21 4 (2, 10) envelope_576)]
theorem common_sub_583_i2 : commonEnvelope childrenD_583_i2 ⊆ insert (9, 6) required_583_i2 := by decide +kernel
theorem child_required_sub_583_i2 : ∀ j, childrenC_583_i2 j ⊆ insert (9, 6) required_583_i2 := by decide +kernel
theorem child_envelope_sub_583_i2 : ∀ j, childrenD_583_i2 j ⊆ envelope_583_i2 := by decide +kernel
theorem pivot_mem_583_i2 : (9, 6) ∈ envelope_583_i2 := by decide +kernel
theorem children_work_583_i2 : ∀ j, Template HasSnaky 7 (childrenC_583_i2 j) (childrenD_583_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_6 1 (5, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_576 4 (2, 10)).mono (by decide +kernel)
theorem row_works_583_i2 : Template HasSnaky 8 required_583_i2 envelope_583_i2 := by
  refine compose HasSnaky 7 childrenC_583_i2 childrenD_583_i2 children_work_583_i2 (9, 6)
    required_583_i2 envelope_583_i2 pivot_mem_583_i2 child_required_sub_583_i2 child_envelope_sub_583_i2 ?_
  intro b hb
  exact common_sub_583_i2 (mem_commonEnvelope childrenD_583_i2 b hb)
def required_583_i3 : Finset Cell := ⟨(([(3, 5), (3, 8), (4, 8), (5, 6), (6, 6), (7, 6), (8, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_583_i3 : Finset Cell := ⟨(([(2, 7), (2, 9), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 8), (4, 9), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (7, 3), (7, 4), (7, 5), (7, 6), (7, 8), (7, 9), (7, 10), (8, 5), (8, 6), (9, 5), (9, 6), (10, 5), (10, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_583_i3 : Fin 2 → Finset Cell := ![(placed21 3 (5, 6) required_6), (placed21 4 (2, 10) required_576)]
def childrenD_583_i3 : Fin 2 → Finset Cell := ![(placed21 3 (5, 6) envelope_6), (placed21 4 (2, 10) envelope_576)]
theorem common_sub_583_i3 : commonEnvelope childrenD_583_i3 ⊆ insert (9, 6) required_583_i3 := by decide +kernel
theorem child_required_sub_583_i3 : ∀ j, childrenC_583_i3 j ⊆ insert (9, 6) required_583_i3 := by decide +kernel
theorem child_envelope_sub_583_i3 : ∀ j, childrenD_583_i3 j ⊆ envelope_583_i3 := by decide +kernel
theorem pivot_mem_583_i3 : (9, 6) ∈ envelope_583_i3 := by decide +kernel
theorem children_work_583_i3 : ∀ j, Template HasSnaky 7 (childrenC_583_i3 j) (childrenD_583_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_6 3 (5, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_576 4 (2, 10)).mono (by decide +kernel)
theorem row_works_583_i3 : Template HasSnaky 8 required_583_i3 envelope_583_i3 := by
  refine compose HasSnaky 7 childrenC_583_i3 childrenD_583_i3 children_work_583_i3 (9, 6)
    required_583_i3 envelope_583_i3 pivot_mem_583_i3 child_required_sub_583_i3 child_envelope_sub_583_i3 ?_
  intro b hb
  exact common_sub_583_i3 (mem_commonEnvelope childrenD_583_i3 b hb)
def required_583_i1 : Finset Cell := ⟨(([(3, 5), (3, 8), (4, 8), (5, 6), (6, 6), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_583_i1 : Finset Cell := ⟨(([(2, 7), (2, 9), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 8), (4, 9), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 8), (7, 9), (7, 10), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (9, 10), (10, 5), (10, 6), (10, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_583_i1 : Fin 4 → Finset Cell := ![(placed21 4 (5, 7) required_8), (placed21 4 (5, 10) required_321), required_583_i2, required_583_i3]
def childrenD_583_i1 : Fin 4 → Finset Cell := ![(placed21 4 (5, 7) envelope_8), (placed21 4 (5, 10) envelope_321), envelope_583_i2, envelope_583_i3]
theorem common_sub_583_i1 : commonEnvelope childrenD_583_i1 ⊆ insert (8, 6) required_583_i1 := by decide +kernel
theorem child_required_sub_583_i1 : ∀ j, childrenC_583_i1 j ⊆ insert (8, 6) required_583_i1 := by decide +kernel
theorem child_envelope_sub_583_i1 : ∀ j, childrenD_583_i1 j ⊆ envelope_583_i1 := by decide +kernel
theorem pivot_mem_583_i1 : (8, 6) ∈ envelope_583_i1 := by decide +kernel
theorem children_work_583_i1 : ∀ j, Template HasSnaky 8 (childrenC_583_i1 j) (childrenD_583_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_8 4 (5, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_321 4 (5, 10)).mono (by decide +kernel)
  · exact row_works_583_i2.mono (by decide +kernel)
  · exact row_works_583_i3.mono (by decide +kernel)
theorem row_works_583_i1 : Template HasSnaky 9 required_583_i1 envelope_583_i1 := by
  refine compose HasSnaky 8 childrenC_583_i1 childrenD_583_i1 children_work_583_i1 (8, 6)
    required_583_i1 envelope_583_i1 pivot_mem_583_i1 child_required_sub_583_i1 child_envelope_sub_583_i1 ?_
  intro b hb
  exact common_sub_583_i1 (mem_commonEnvelope childrenD_583_i1 b hb)
def required_583_i0 : Finset Cell := ⟨(([(3, 5), (3, 8), (4, 5), (4, 8), (6, 6), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_583_i0 : Finset Cell := ⟨(([(2, 7), (2, 9), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 5), (4, 6), (4, 8), (4, 9), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 8), (7, 9), (7, 10), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (9, 10), (10, 5), (10, 6), (10, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_583_i0 : Fin 2 → Finset Cell := ![(placed21 6 (7, 6) required_3), required_583_i1]
def childrenD_583_i0 : Fin 2 → Finset Cell := ![(placed21 6 (7, 6) envelope_3), envelope_583_i1]
theorem common_sub_583_i0 : commonEnvelope childrenD_583_i0 ⊆ insert (5, 6) required_583_i0 := by decide +kernel
theorem child_required_sub_583_i0 : ∀ j, childrenC_583_i0 j ⊆ insert (5, 6) required_583_i0 := by decide +kernel
theorem child_envelope_sub_583_i0 : ∀ j, childrenD_583_i0 j ⊆ envelope_583_i0 := by decide +kernel
theorem pivot_mem_583_i0 : (5, 6) ∈ envelope_583_i0 := by decide +kernel
theorem children_work_583_i0 : ∀ j, Template HasSnaky 9 (childrenC_583_i0 j) (childrenD_583_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_3 6 (7, 6)).mono (by decide +kernel)
  · exact row_works_583_i1.mono (by decide +kernel)
theorem row_works_583_i0 : Template HasSnaky 10 required_583_i0 envelope_583_i0 := by
  refine compose HasSnaky 9 childrenC_583_i0 childrenD_583_i0 children_work_583_i0 (5, 6)
    required_583_i0 envelope_583_i0 pivot_mem_583_i0 child_required_sub_583_i0 child_envelope_sub_583_i0 ?_
  intro b hb
  exact common_sub_583_i0 (mem_commonEnvelope childrenD_583_i0 b hb)
def required_583_i5 : Finset Cell := ⟨(([(3, 5), (3, 8), (4, 5), (4, 8), (6, 6), (6, 8), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_583_i5 : Finset Cell := ⟨(([(2, 7), (2, 9), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 5), (4, 6), (4, 8), (4, 9), (4, 10), (4, 11), (5, 6), (5, 7), (5, 8), (5, 9), (6, 6), (6, 8), (6, 9), (7, 6), (7, 8), (7, 9), (8, 8), (8, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_583_i5 : Fin 3 → Finset Cell := ![(placed21 1 (2, 8) required_7), (placed21 1 (2, 5) required_86), (placed21 1 (2, 5) required_542)]
def childrenD_583_i5 : Fin 3 → Finset Cell := ![(placed21 1 (2, 8) envelope_7), (placed21 1 (2, 5) envelope_86), (placed21 1 (2, 5) envelope_542)]
theorem common_sub_583_i5 : commonEnvelope childrenD_583_i5 ⊆ insert (5, 8) required_583_i5 := by decide +kernel
theorem child_required_sub_583_i5 : ∀ j, childrenC_583_i5 j ⊆ insert (5, 8) required_583_i5 := by decide +kernel
theorem child_envelope_sub_583_i5 : ∀ j, childrenD_583_i5 j ⊆ envelope_583_i5 := by decide +kernel
theorem pivot_mem_583_i5 : (5, 8) ∈ envelope_583_i5 := by decide +kernel
theorem children_work_583_i5 : ∀ j, Template HasSnaky 7 (childrenC_583_i5 j) (childrenD_583_i5 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 1 (2, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_86 1 (2, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_542 1 (2, 5)).mono (by decide +kernel)
theorem row_works_583_i5 : Template HasSnaky 8 required_583_i5 envelope_583_i5 := by
  refine compose HasSnaky 7 childrenC_583_i5 childrenD_583_i5 children_work_583_i5 (5, 8)
    required_583_i5 envelope_583_i5 pivot_mem_583_i5 child_required_sub_583_i5 child_envelope_sub_583_i5 ?_
  intro b hb
  exact common_sub_583_i5 (mem_commonEnvelope childrenD_583_i5 b hb)
def required_583_i6 : Finset Cell := ⟨(([(3, 8), (4, 8), (6, 6), (6, 8), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_583_i6 : Finset Cell := ⟨(([(3, 8), (4, 8), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, 5), (7, 6), (7, 7), (7, 9), (7, 10)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_583_i6 : Fin 3 → Finset Cell := ![(placed21 2 (7, 5) required_48), (placed21 0 (3, 5) required_109), (placed21 2 (7, 5) required_246)]
def childrenD_583_i6 : Fin 3 → Finset Cell := ![(placed21 2 (7, 5) envelope_48), (placed21 0 (3, 5) envelope_109), (placed21 2 (7, 5) envelope_246)]
theorem common_sub_583_i6 : commonEnvelope childrenD_583_i6 ⊆ insert (6, 7) required_583_i6 := by decide +kernel
theorem child_required_sub_583_i6 : ∀ j, childrenC_583_i6 j ⊆ insert (6, 7) required_583_i6 := by decide +kernel
theorem child_envelope_sub_583_i6 : ∀ j, childrenD_583_i6 j ⊆ envelope_583_i6 := by decide +kernel
theorem pivot_mem_583_i6 : (6, 7) ∈ envelope_583_i6 := by decide +kernel
theorem children_work_583_i6 : ∀ j, Template HasSnaky 4 (childrenC_583_i6 j) (childrenD_583_i6 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_48 2 (7, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_109 0 (3, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_246 2 (7, 5)).mono (by decide +kernel)
theorem row_works_583_i6 : Template HasSnaky 5 required_583_i6 envelope_583_i6 := by
  refine compose HasSnaky 4 childrenC_583_i6 childrenD_583_i6 children_work_583_i6 (6, 7)
    required_583_i6 envelope_583_i6 pivot_mem_583_i6 child_required_sub_583_i6 child_envelope_sub_583_i6 ?_
  intro b hb
  exact common_sub_583_i6 (mem_commonEnvelope childrenD_583_i6 b hb)
def required_583_i4 : Finset Cell := ⟨(([(3, 5), (3, 8), (4, 5), (4, 8), (6, 6), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_583_i4 : Finset Cell := ⟨(([(0, 9), (0, 10), (1, 9), (1, 10), (2, 7), (2, 9), (2, 10), (2, 11), (2, 12), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (4, 5), (4, 6), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (5, 12), (5, 13), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (6, 12), (6, 13), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (7, 12), (7, 13), (8, 8), (8, 9), (8, 10), (8, 11), (8, 12), (9, 9), (9, 10), (9, 11), (9, 12), (10, 10), (10, 12)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_583_i4 : Fin 5 → Finset Cell := ![(placed21 2 (7, 5) required_184), (placed21 2 (7, 5) required_423), required_583_i5, (placed21 1 (0, 5) required_572), required_583_i6]
def childrenD_583_i4 : Fin 5 → Finset Cell := ![(placed21 2 (7, 5) envelope_184), (placed21 2 (7, 5) envelope_423), envelope_583_i5, (placed21 1 (0, 5) envelope_572), envelope_583_i6]
theorem common_sub_583_i4 : commonEnvelope childrenD_583_i4 ⊆ insert (6, 8) required_583_i4 := by decide +kernel
theorem child_required_sub_583_i4 : ∀ j, childrenC_583_i4 j ⊆ insert (6, 8) required_583_i4 := by decide +kernel
theorem child_envelope_sub_583_i4 : ∀ j, childrenD_583_i4 j ⊆ envelope_583_i4 := by decide +kernel
theorem pivot_mem_583_i4 : (6, 8) ∈ envelope_583_i4 := by decide +kernel
theorem children_work_583_i4 : ∀ j, Template HasSnaky 13 (childrenC_583_i4 j) (childrenD_583_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_184 2 (7, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_423 2 (7, 5)).mono (by decide +kernel)
  · exact row_works_583_i5.mono (by decide +kernel)
  · exact (placed21_template row_works_572 1 (0, 5)).mono (by decide +kernel)
  · exact row_works_583_i6.mono (by decide +kernel)
theorem row_works_583_i4 : Template HasSnaky 14 required_583_i4 envelope_583_i4 := by
  refine compose HasSnaky 13 childrenC_583_i4 childrenD_583_i4 children_work_583_i4 (6, 8)
    required_583_i4 envelope_583_i4 pivot_mem_583_i4 child_required_sub_583_i4 child_envelope_sub_583_i4 ?_
  intro b hb
  exact common_sub_583_i4 (mem_commonEnvelope childrenD_583_i4 b hb)
def required_583 : Finset Cell := ⟨(([(3, 5), (3, 8), (4, 5), (4, 8), (6, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_583 : Finset Cell := ⟨(([(0, 9), (0, 10), (1, 9), (1, 10), (2, 6), (2, 7), (2, 9), (2, 10), (2, 11), (2, 12), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (4, 5), (4, 6), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (5, 4), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (5, 12), (5, 13), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (6, 12), (6, 13), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (7, 12), (7, 13), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (8, 11), (8, 12), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (9, 10), (9, 11), (9, 12), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (10, 9), (10, 10), (10, 12), (11, 3), (11, 4), (11, 5), (11, 6), (11, 7), (12, 3), (12, 5), (12, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_583 : Fin 8 → Finset Cell := ![(placed21 0 (3, 2) required_401), (placed21 4 (0, 12) required_552), (placed21 0 (3, 2) required_556), (placed21 0 (3, 2) required_575), required_583_i0, (placed21 4 (5, 10) required_579), required_583_i4, (placed21 1 (0, 4) required_582)]
def childrenD_583 : Fin 8 → Finset Cell := ![(placed21 0 (3, 2) envelope_401), (placed21 4 (0, 12) envelope_552), (placed21 0 (3, 2) envelope_556), (placed21 0 (3, 2) envelope_575), envelope_583_i0, (placed21 4 (5, 10) envelope_579), envelope_583_i4, (placed21 1 (0, 4) envelope_582)]
theorem common_sub_583 : commonEnvelope childrenD_583 ⊆ insert (7, 6) required_583 := by decide +kernel
theorem child_required_sub_583 : ∀ j, childrenC_583 j ⊆ insert (7, 6) required_583 := by decide +kernel
theorem child_envelope_sub_583 : ∀ j, childrenD_583 j ⊆ envelope_583 := by decide +kernel
theorem pivot_mem_583 : (7, 6) ∈ envelope_583 := by decide +kernel
theorem children_work_583 : ∀ j, Template HasSnaky 14 (childrenC_583 j) (childrenD_583 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_401 0 (3, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_552 4 (0, 12)).mono (by decide +kernel)
  · exact (placed21_template row_works_556 0 (3, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_575 0 (3, 2)).mono (by decide +kernel)
  · exact row_works_583_i0.mono (by decide +kernel)
  · exact (placed21_template row_works_579 4 (5, 10)).mono (by decide +kernel)
  · exact row_works_583_i4.mono (by decide +kernel)
  · exact (placed21_template row_works_582 1 (0, 4)).mono (by decide +kernel)
theorem row_works_583 : Template HasSnaky 15 required_583 envelope_583 := by
  refine compose HasSnaky 14 childrenC_583 childrenD_583 children_work_583 (7, 6)
    required_583 envelope_583 pivot_mem_583 child_required_sub_583 child_envelope_sub_583 ?_
  intro b hb
  exact common_sub_583 (mem_commonEnvelope childrenD_583 b hb)
def required_648 : Finset Cell := ⟨(([(4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_648 : Finset Cell := ⟨(([(0, 2), (0, 3), (0, 5), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (10, 1), (10, 3), (10, 4), (10, 5), (11, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_648 : Fin 12 → Finset Cell := ![(placed21 0 (1, 1) required_174), (placed21 0 (2, 1) required_475), (placed21 0 (1, 0) required_480), (placed21 2 (7, 0) required_480), (placed21 4 (2, 8) required_483), (placed21 0 (1, 1) required_566), (placed21 0 (2, 1) required_587), (placed21 4 (2, 8) required_587), (placed21 1 (1, 2) required_605), (placed21 0 (2, 0) required_635), required_644, required_647]
def childrenD_648 : Fin 12 → Finset Cell := ![(placed21 0 (1, 1) envelope_174), (placed21 0 (2, 1) envelope_475), (placed21 0 (1, 0) envelope_480), (placed21 2 (7, 0) envelope_480), (placed21 4 (2, 8) envelope_483), (placed21 0 (1, 1) envelope_566), (placed21 0 (2, 1) envelope_587), (placed21 4 (2, 8) envelope_587), (placed21 1 (1, 2) envelope_605), (placed21 0 (2, 0) envelope_635), envelope_644, envelope_647]
theorem common_sub_648 : commonEnvelope childrenD_648 ⊆ insert (4, 4) required_648 := by decide +kernel
theorem child_required_sub_648 : ∀ j, childrenC_648 j ⊆ insert (4, 4) required_648 := by decide +kernel
theorem child_envelope_sub_648 : ∀ j, childrenD_648 j ⊆ envelope_648 := by decide +kernel
theorem pivot_mem_648 : (4, 4) ∈ envelope_648 := by decide +kernel
theorem children_work_648 : ∀ j, Template HasSnaky 14 (childrenC_648 j) (childrenD_648 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_174 0 (1, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_475 0 (2, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_480 0 (1, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_480 2 (7, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_483 4 (2, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_566 0 (1, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_587 0 (2, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_587 4 (2, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_605 1 (1, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_635 0 (2, 0)).mono (by decide +kernel)
  · exact row_works_644.mono (by decide +kernel)
  · exact row_works_647.mono (by decide +kernel)
theorem row_works_648 : Template HasSnaky 15 required_648 envelope_648 := by
  refine compose HasSnaky 14 childrenC_648 childrenD_648 children_work_648 (4, 4)
    required_648 envelope_648 pivot_mem_648 child_required_sub_648 child_envelope_sub_648 ?_
  intro b hb
  exact common_sub_648 (mem_commonEnvelope childrenD_648 b hb)
def required_656_i1 : Finset Cell := ⟨(([(5, 5), (5, 6), (6, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_656_i1 : Finset Cell := ⟨(([(2, 3), (2, 5), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 7), (4, 8), (4, 9), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (9, 3), (9, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_656_i1 : Fin 7 → Finset Cell := ![(placed21 1 (2, 3) required_117), (placed21 3 (3, 7) required_134), (placed21 3 (3, 7) required_180), (placed21 6 (6, 9) required_337), (placed21 6 (8, 9) required_341), (placed21 3 (2, 7) required_435), (placed21 3 (3, 6) required_558)]
def childrenD_656_i1 : Fin 7 → Finset Cell := ![(placed21 1 (2, 3) envelope_117), (placed21 3 (3, 7) envelope_134), (placed21 3 (3, 7) envelope_180), (placed21 6 (6, 9) envelope_337), (placed21 6 (8, 9) envelope_341), (placed21 3 (2, 7) envelope_435), (placed21 3 (3, 6) envelope_558)]
theorem common_sub_656_i1 : commonEnvelope childrenD_656_i1 ⊆ insert (5, 4) required_656_i1 := by decide +kernel
theorem child_required_sub_656_i1 : ∀ j, childrenC_656_i1 j ⊆ insert (5, 4) required_656_i1 := by decide +kernel
theorem child_envelope_sub_656_i1 : ∀ j, childrenD_656_i1 j ⊆ envelope_656_i1 := by decide +kernel
theorem pivot_mem_656_i1 : (5, 4) ∈ envelope_656_i1 := by decide +kernel
theorem children_work_656_i1 : ∀ j, Template HasSnaky 8 (childrenC_656_i1 j) (childrenD_656_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_117 1 (2, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_134 3 (3, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_180 3 (3, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_337 6 (6, 9)).mono (by decide +kernel)
  · exact (placed21_template row_works_341 6 (8, 9)).mono (by decide +kernel)
  · exact (placed21_template row_works_435 3 (2, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_558 3 (3, 6)).mono (by decide +kernel)
theorem row_works_656_i1 : Template HasSnaky 9 required_656_i1 envelope_656_i1 := by
  refine compose HasSnaky 8 childrenC_656_i1 childrenD_656_i1 children_work_656_i1 (5, 4)
    required_656_i1 envelope_656_i1 pivot_mem_656_i1 child_required_sub_656_i1 child_envelope_sub_656_i1 ?_
  intro b hb
  exact common_sub_656_i1 (mem_commonEnvelope childrenD_656_i1 b hb)
def required_656_i2 : Finset Cell := ⟨(([(2, 5), (5, 5), (5, 6), (6, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_656_i2 : Finset Cell := ⟨(([(1, 7), (2, 5), (2, 7), (3, 2), (3, 3), (3, 4), (3, 5), (3, 7), (3, 8), (3, 9), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (8, 4), (8, 5), (8, 6), (9, 4), (9, 5), (9, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_656_i2 : Fin 2 → Finset Cell := ![(placed21 0 (2, 5) required_1), (placed21 1 (1, 2) required_651)]
def childrenD_656_i2 : Fin 2 → Finset Cell := ![(placed21 0 (2, 5) envelope_1), (placed21 1 (1, 2) envelope_651)]
theorem common_sub_656_i2 : commonEnvelope childrenD_656_i2 ⊆ insert (4, 5) required_656_i2 := by decide +kernel
theorem child_required_sub_656_i2 : ∀ j, childrenC_656_i2 j ⊆ insert (4, 5) required_656_i2 := by decide +kernel
theorem child_envelope_sub_656_i2 : ∀ j, childrenD_656_i2 j ⊆ envelope_656_i2 := by decide +kernel
theorem pivot_mem_656_i2 : (4, 5) ∈ envelope_656_i2 := by decide +kernel
theorem children_work_656_i2 : ∀ j, Template HasSnaky 8 (childrenC_656_i2 j) (childrenD_656_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_1 0 (2, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_651 1 (1, 2)).mono (by decide +kernel)
theorem row_works_656_i2 : Template HasSnaky 9 required_656_i2 envelope_656_i2 := by
  refine compose HasSnaky 8 childrenC_656_i2 childrenD_656_i2 children_work_656_i2 (4, 5)
    required_656_i2 envelope_656_i2 pivot_mem_656_i2 child_required_sub_656_i2 child_envelope_sub_656_i2 ?_
  intro b hb
  exact common_sub_656_i2 (mem_commonEnvelope childrenD_656_i2 b hb)
def required_656_i3 : Finset Cell := ⟨(([(2, 5), (5, 5), (5, 6), (6, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_656_i3 : Finset Cell := ⟨(([(2, 5), (3, 4), (3, 5), (3, 7), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_656_i3 : Fin 2 → Finset Cell := ![(placed21 0 (2, 5) required_1), (placed21 4 (3, 9) required_652)]
def childrenD_656_i3 : Fin 2 → Finset Cell := ![(placed21 0 (2, 5) envelope_1), (placed21 4 (3, 9) envelope_652)]
theorem common_sub_656_i3 : commonEnvelope childrenD_656_i3 ⊆ insert (4, 5) required_656_i3 := by decide +kernel
theorem child_required_sub_656_i3 : ∀ j, childrenC_656_i3 j ⊆ insert (4, 5) required_656_i3 := by decide +kernel
theorem child_envelope_sub_656_i3 : ∀ j, childrenD_656_i3 j ⊆ envelope_656_i3 := by decide +kernel
theorem pivot_mem_656_i3 : (4, 5) ∈ envelope_656_i3 := by decide +kernel
theorem children_work_656_i3 : ∀ j, Template HasSnaky 10 (childrenC_656_i3 j) (childrenD_656_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_1 0 (2, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_652 4 (3, 9)).mono (by decide +kernel)
theorem row_works_656_i3 : Template HasSnaky 11 required_656_i3 envelope_656_i3 := by
  refine compose HasSnaky 10 childrenC_656_i3 childrenD_656_i3 children_work_656_i3 (4, 5)
    required_656_i3 envelope_656_i3 pivot_mem_656_i3 child_required_sub_656_i3 child_envelope_sub_656_i3 ?_
  intro b hb
  exact common_sub_656_i3 (mem_commonEnvelope childrenD_656_i3 b hb)
def required_656_i0 : Finset Cell := ⟨(([(2, 5), (5, 6), (6, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_656_i0 : Finset Cell := ⟨(([(1, 7), (2, 3), (2, 5), (2, 7), (3, 2), (3, 3), (3, 4), (3, 5), (3, 7), (3, 8), (3, 9), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (9, 3), (9, 4), (9, 5), (9, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_656_i0 : Fin 8 → Finset Cell := ![(placed21 6 (7, 9) required_248), (placed21 6 (7, 9) required_300), (placed21 6 (8, 9) required_436), (placed21 3 (2, 8) required_449), (placed21 3 (2, 8) required_510), required_656_i1, required_656_i2, required_656_i3]
def childrenD_656_i0 : Fin 8 → Finset Cell := ![(placed21 6 (7, 9) envelope_248), (placed21 6 (7, 9) envelope_300), (placed21 6 (8, 9) envelope_436), (placed21 3 (2, 8) envelope_449), (placed21 3 (2, 8) envelope_510), envelope_656_i1, envelope_656_i2, envelope_656_i3]
theorem common_sub_656_i0 : commonEnvelope childrenD_656_i0 ⊆ insert (5, 5) required_656_i0 := by decide +kernel
theorem child_required_sub_656_i0 : ∀ j, childrenC_656_i0 j ⊆ insert (5, 5) required_656_i0 := by decide +kernel
theorem child_envelope_sub_656_i0 : ∀ j, childrenD_656_i0 j ⊆ envelope_656_i0 := by decide +kernel
theorem pivot_mem_656_i0 : (5, 5) ∈ envelope_656_i0 := by decide +kernel
theorem children_work_656_i0 : ∀ j, Template HasSnaky 11 (childrenC_656_i0 j) (childrenD_656_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_248 6 (7, 9)).mono (by decide +kernel)
  · exact (placed21_template row_works_300 6 (7, 9)).mono (by decide +kernel)
  · exact (placed21_template row_works_436 6 (8, 9)).mono (by decide +kernel)
  · exact (placed21_template row_works_449 3 (2, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_510 3 (2, 8)).mono (by decide +kernel)
  · exact row_works_656_i1.mono (by decide +kernel)
  · exact row_works_656_i2.mono (by decide +kernel)
  · exact row_works_656_i3.mono (by decide +kernel)
theorem row_works_656_i0 : Template HasSnaky 12 required_656_i0 envelope_656_i0 := by
  refine compose HasSnaky 11 childrenC_656_i0 childrenD_656_i0 children_work_656_i0 (5, 5)
    required_656_i0 envelope_656_i0 pivot_mem_656_i0 child_required_sub_656_i0 child_envelope_sub_656_i0 ?_
  intro b hb
  exact common_sub_656_i0 (mem_commonEnvelope childrenD_656_i0 b hb)
def required_656 : Finset Cell := ⟨(([(2, 5), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_656 : Finset Cell := ⟨(([(0, 7), (1, 5), (1, 7), (1, 8), (1, 9), (2, 3), (2, 5), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, 2), (3, 3), (3, 4), (3, 5), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (5, 12), (5, 13), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (6, 12), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (7, 12), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (8, 11), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (9, 10), (9, 11), (9, 12), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (10, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_656 : Fin 11 → Finset Cell := ![(placed21 0 (3, 3) required_508), (placed21 4 (3, 9) required_508), (placed21 0 (3, 3) required_605), (placed21 4 (3, 9) required_605), (placed21 5 (10, 2) required_644), (placed21 5 (10, 2) required_645), (placed21 5 (10, 2) required_647), (placed21 0 (2, 1) required_650), (placed21 4 (2, 11) required_650), required_656_i0, (placed21 5 (9, 3) required_654)]
def childrenD_656 : Fin 11 → Finset Cell := ![(placed21 0 (3, 3) envelope_508), (placed21 4 (3, 9) envelope_508), (placed21 0 (3, 3) envelope_605), (placed21 4 (3, 9) envelope_605), (placed21 5 (10, 2) envelope_644), (placed21 5 (10, 2) envelope_645), (placed21 5 (10, 2) envelope_647), (placed21 0 (2, 1) envelope_650), (placed21 4 (2, 11) envelope_650), envelope_656_i0, (placed21 5 (9, 3) envelope_654)]
theorem common_sub_656 : commonEnvelope childrenD_656 ⊆ insert (6, 6) required_656 := by decide +kernel
theorem child_required_sub_656 : ∀ j, childrenC_656 j ⊆ insert (6, 6) required_656 := by decide +kernel
theorem child_envelope_sub_656 : ∀ j, childrenD_656 j ⊆ envelope_656 := by decide +kernel
theorem pivot_mem_656 : (6, 6) ∈ envelope_656 := by decide +kernel
theorem children_work_656 : ∀ j, Template HasSnaky 14 (childrenC_656 j) (childrenD_656 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_508 0 (3, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_508 4 (3, 9)).mono (by decide +kernel)
  · exact (placed21_template row_works_605 0 (3, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_605 4 (3, 9)).mono (by decide +kernel)
  · exact (placed21_template row_works_644 5 (10, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_645 5 (10, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_647 5 (10, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_650 0 (2, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_650 4 (2, 11)).mono (by decide +kernel)
  · exact row_works_656_i0.mono (by decide +kernel)
  · exact (placed21_template row_works_654 5 (9, 3)).mono (by decide +kernel)
theorem row_works_656 : Template HasSnaky 15 required_656 envelope_656 := by
  refine compose HasSnaky 14 childrenC_656 childrenD_656 children_work_656 (6, 6)
    required_656 envelope_656 pivot_mem_656 child_required_sub_656 child_envelope_sub_656 ?_
  intro b hb
  exact common_sub_656 (mem_commonEnvelope childrenD_656 b hb)
def height_573_i0 : ℕ := 8
def childrenH_573_i0 : Fin 5 → ℕ := ![height_8, height_115, height_197, height_286, height_339]
theorem height_exact_573_i0 : height_573_i0 = 1 + Finset.univ.sup childrenH_573_i0 := by decide +kernel
theorem required_origin_573_i0 : ∀ x ∈ required_573_i0,
    (∃ j, x ∈ childrenC_573_i0 j) ∨ ∀ j, x ∈ childrenD_573_i0 j := by decide +kernel
theorem required_exact_573_i0 : required_573_i0 =
    ((Finset.univ.biUnion childrenC_573_i0) ∪ commonEnvelope childrenD_573_i0).erase (3, 5) := by
  exact required_eq_combination childrenC_573_i0 childrenD_573_i0 (3, 5) required_573_i0
    (by decide +kernel) child_required_sub_573_i0 common_sub_573_i0 required_origin_573_i0
theorem envelope_origin_573_i0 : ∀ x ∈ envelope_573_i0,
    x = (3, 5) ∨ ∃ j, x ∈ childrenD_573_i0 j := by decide +kernel
theorem envelope_exact_573_i0 : envelope_573_i0 =
    insert (3, 5) (Finset.univ.biUnion childrenD_573_i0) := by
  exact envelope_eq_combination childrenD_573_i0 (3, 5) envelope_573_i0
    pivot_mem_573_i0 child_envelope_sub_573_i0 envelope_origin_573_i0
def checked_573_i0 : CheckedCard where
  required := required_573_i0
  envelope := envelope_573_i0
  height := height_573_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_573_i0
def height_573_i1 : ℕ := 9
def childrenH_573_i1 : Fin 4 → ℕ := ![height_7, height_8, height_9, height_473]
theorem height_exact_573_i1 : height_573_i1 = 1 + Finset.univ.sup childrenH_573_i1 := by decide +kernel
theorem required_origin_573_i1 : ∀ x ∈ required_573_i1,
    (∃ j, x ∈ childrenC_573_i1 j) ∨ ∀ j, x ∈ childrenD_573_i1 j := by decide +kernel
theorem required_exact_573_i1 : required_573_i1 =
    ((Finset.univ.biUnion childrenC_573_i1) ∪ commonEnvelope childrenD_573_i1).erase (3, 5) := by
  exact required_eq_combination childrenC_573_i1 childrenD_573_i1 (3, 5) required_573_i1
    (by decide +kernel) child_required_sub_573_i1 common_sub_573_i1 required_origin_573_i1
theorem envelope_origin_573_i1 : ∀ x ∈ envelope_573_i1,
    x = (3, 5) ∨ ∃ j, x ∈ childrenD_573_i1 j := by decide +kernel
theorem envelope_exact_573_i1 : envelope_573_i1 =
    insert (3, 5) (Finset.univ.biUnion childrenD_573_i1) := by
  exact envelope_eq_combination childrenD_573_i1 (3, 5) envelope_573_i1
    pivot_mem_573_i1 child_envelope_sub_573_i1 envelope_origin_573_i1
def checked_573_i1 : CheckedCard where
  required := required_573_i1
  envelope := envelope_573_i1
  height := height_573_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_573_i1
def height_573_i2 : ℕ := 8
def childrenH_573_i2 : Fin 4 → ℕ := ![height_8, height_403, height_487, height_492]
theorem height_exact_573_i2 : height_573_i2 = 1 + Finset.univ.sup childrenH_573_i2 := by decide +kernel
theorem required_origin_573_i2 : ∀ x ∈ required_573_i2,
    (∃ j, x ∈ childrenC_573_i2 j) ∨ ∀ j, x ∈ childrenD_573_i2 j := by decide +kernel
theorem required_exact_573_i2 : required_573_i2 =
    ((Finset.univ.biUnion childrenC_573_i2) ∪ commonEnvelope childrenD_573_i2).erase (3, 5) := by
  exact required_eq_combination childrenC_573_i2 childrenD_573_i2 (3, 5) required_573_i2
    (by decide +kernel) child_required_sub_573_i2 common_sub_573_i2 required_origin_573_i2
theorem envelope_origin_573_i2 : ∀ x ∈ envelope_573_i2,
    x = (3, 5) ∨ ∃ j, x ∈ childrenD_573_i2 j := by decide +kernel
theorem envelope_exact_573_i2 : envelope_573_i2 =
    insert (3, 5) (Finset.univ.biUnion childrenD_573_i2) := by
  exact envelope_eq_combination childrenD_573_i2 (3, 5) envelope_573_i2
    pivot_mem_573_i2 child_envelope_sub_573_i2 envelope_origin_573_i2
def checked_573_i2 : CheckedCard where
  required := required_573_i2
  envelope := envelope_573_i2
  height := height_573_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_573_i2
def height_573_i3 : ℕ := 8
def childrenH_573_i3 : Fin 2 → ℕ := ![height_87, height_487]
theorem height_exact_573_i3 : height_573_i3 = 1 + Finset.univ.sup childrenH_573_i3 := by decide +kernel
theorem required_origin_573_i3 : ∀ x ∈ required_573_i3,
    (∃ j, x ∈ childrenC_573_i3 j) ∨ ∀ j, x ∈ childrenD_573_i3 j := by decide +kernel
theorem required_exact_573_i3 : required_573_i3 =
    ((Finset.univ.biUnion childrenC_573_i3) ∪ commonEnvelope childrenD_573_i3).erase (3, 5) := by
  exact required_eq_combination childrenC_573_i3 childrenD_573_i3 (3, 5) required_573_i3
    (by decide +kernel) child_required_sub_573_i3 common_sub_573_i3 required_origin_573_i3
theorem envelope_origin_573_i3 : ∀ x ∈ envelope_573_i3,
    x = (3, 5) ∨ ∃ j, x ∈ childrenD_573_i3 j := by decide +kernel
theorem envelope_exact_573_i3 : envelope_573_i3 =
    insert (3, 5) (Finset.univ.biUnion childrenD_573_i3) := by
  exact envelope_eq_combination childrenD_573_i3 (3, 5) envelope_573_i3
    pivot_mem_573_i3 child_envelope_sub_573_i3 envelope_origin_573_i3
def checked_573_i3 : CheckedCard where
  required := required_573_i3
  envelope := envelope_573_i3
  height := height_573_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_573_i3
def height_573_i4 : ℕ := 14
def childrenH_573_i4 : Fin 2 → ℕ := ![height_107, height_572]
theorem height_exact_573_i4 : height_573_i4 = 1 + Finset.univ.sup childrenH_573_i4 := by decide +kernel
theorem required_origin_573_i4 : ∀ x ∈ required_573_i4,
    (∃ j, x ∈ childrenC_573_i4 j) ∨ ∀ j, x ∈ childrenD_573_i4 j := by decide +kernel
theorem required_exact_573_i4 : required_573_i4 =
    ((Finset.univ.biUnion childrenC_573_i4) ∪ commonEnvelope childrenD_573_i4).erase (1, 7) := by
  exact required_eq_combination childrenC_573_i4 childrenD_573_i4 (1, 7) required_573_i4
    (by decide +kernel) child_required_sub_573_i4 common_sub_573_i4 required_origin_573_i4
theorem envelope_origin_573_i4 : ∀ x ∈ envelope_573_i4,
    x = (1, 7) ∨ ∃ j, x ∈ childrenD_573_i4 j := by decide +kernel
theorem envelope_exact_573_i4 : envelope_573_i4 =
    insert (1, 7) (Finset.univ.biUnion childrenD_573_i4) := by
  exact envelope_eq_combination childrenD_573_i4 (1, 7) envelope_573_i4
    pivot_mem_573_i4 child_envelope_sub_573_i4 envelope_origin_573_i4
def checked_573_i4 : CheckedCard where
  required := required_573_i4
  envelope := envelope_573_i4
  height := height_573_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_573_i4
def height_573_i5 : ℕ := 7
def childrenH_573_i5 : Fin 4 → ℕ := ![height_9, height_249, height_383, height_403]
theorem height_exact_573_i5 : height_573_i5 = 1 + Finset.univ.sup childrenH_573_i5 := by decide +kernel
theorem required_origin_573_i5 : ∀ x ∈ required_573_i5,
    (∃ j, x ∈ childrenC_573_i5 j) ∨ ∀ j, x ∈ childrenD_573_i5 j := by decide +kernel
theorem required_exact_573_i5 : required_573_i5 =
    ((Finset.univ.biUnion childrenC_573_i5) ∪ commonEnvelope childrenD_573_i5).erase (3, 5) := by
  exact required_eq_combination childrenC_573_i5 childrenD_573_i5 (3, 5) required_573_i5
    (by decide +kernel) child_required_sub_573_i5 common_sub_573_i5 required_origin_573_i5
theorem envelope_origin_573_i5 : ∀ x ∈ envelope_573_i5,
    x = (3, 5) ∨ ∃ j, x ∈ childrenD_573_i5 j := by decide +kernel
theorem envelope_exact_573_i5 : envelope_573_i5 =
    insert (3, 5) (Finset.univ.biUnion childrenD_573_i5) := by
  exact envelope_eq_combination childrenD_573_i5 (3, 5) envelope_573_i5
    pivot_mem_573_i5 child_envelope_sub_573_i5 envelope_origin_573_i5
def checked_573_i5 : CheckedCard where
  required := required_573_i5
  envelope := envelope_573_i5
  height := height_573_i5
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_573_i5
def height_573 : ℕ := 15
def childrenH_573 : Fin 10 → ℕ := ![height_384, height_385, height_493, height_494, height_573_i0, height_573_i1, height_573_i2, height_573_i3, height_573_i4, height_573_i5]
theorem height_exact_573 : height_573 = 1 + Finset.univ.sup childrenH_573 := by decide +kernel
theorem required_origin_573 : ∀ x ∈ required_573,
    (∃ j, x ∈ childrenC_573 j) ∨ ∀ j, x ∈ childrenD_573 j := by decide +kernel
theorem required_exact_573 : required_573 =
    ((Finset.univ.biUnion childrenC_573) ∪ commonEnvelope childrenD_573).erase (3, 6) := by
  exact required_eq_combination childrenC_573 childrenD_573 (3, 6) required_573
    (by decide +kernel) child_required_sub_573 common_sub_573 required_origin_573
theorem envelope_origin_573 : ∀ x ∈ envelope_573,
    x = (3, 6) ∨ ∃ j, x ∈ childrenD_573 j := by decide +kernel
theorem envelope_exact_573 : envelope_573 =
    insert (3, 6) (Finset.univ.biUnion childrenD_573) := by
  exact envelope_eq_combination childrenD_573 (3, 6) envelope_573
    pivot_mem_573 child_envelope_sub_573 envelope_origin_573
def checked_573 : CheckedCard where
  required := required_573
  envelope := envelope_573
  height := height_573
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_573
def height_583_i2 : ℕ := 8
def childrenH_583_i2 : Fin 2 → ℕ := ![height_6, height_576]
theorem height_exact_583_i2 : height_583_i2 = 1 + Finset.univ.sup childrenH_583_i2 := by decide +kernel
theorem required_origin_583_i2 : ∀ x ∈ required_583_i2,
    (∃ j, x ∈ childrenC_583_i2 j) ∨ ∀ j, x ∈ childrenD_583_i2 j := by decide +kernel
theorem required_exact_583_i2 : required_583_i2 =
    ((Finset.univ.biUnion childrenC_583_i2) ∪ commonEnvelope childrenD_583_i2).erase (9, 6) := by
  exact required_eq_combination childrenC_583_i2 childrenD_583_i2 (9, 6) required_583_i2
    (by decide +kernel) child_required_sub_583_i2 common_sub_583_i2 required_origin_583_i2
theorem envelope_origin_583_i2 : ∀ x ∈ envelope_583_i2,
    x = (9, 6) ∨ ∃ j, x ∈ childrenD_583_i2 j := by decide +kernel
theorem envelope_exact_583_i2 : envelope_583_i2 =
    insert (9, 6) (Finset.univ.biUnion childrenD_583_i2) := by
  exact envelope_eq_combination childrenD_583_i2 (9, 6) envelope_583_i2
    pivot_mem_583_i2 child_envelope_sub_583_i2 envelope_origin_583_i2
def checked_583_i2 : CheckedCard where
  required := required_583_i2
  envelope := envelope_583_i2
  height := height_583_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_583_i2
def height_583_i3 : ℕ := 8
def childrenH_583_i3 : Fin 2 → ℕ := ![height_6, height_576]
theorem height_exact_583_i3 : height_583_i3 = 1 + Finset.univ.sup childrenH_583_i3 := by decide +kernel
theorem required_origin_583_i3 : ∀ x ∈ required_583_i3,
    (∃ j, x ∈ childrenC_583_i3 j) ∨ ∀ j, x ∈ childrenD_583_i3 j := by decide +kernel
theorem required_exact_583_i3 : required_583_i3 =
    ((Finset.univ.biUnion childrenC_583_i3) ∪ commonEnvelope childrenD_583_i3).erase (9, 6) := by
  exact required_eq_combination childrenC_583_i3 childrenD_583_i3 (9, 6) required_583_i3
    (by decide +kernel) child_required_sub_583_i3 common_sub_583_i3 required_origin_583_i3
theorem envelope_origin_583_i3 : ∀ x ∈ envelope_583_i3,
    x = (9, 6) ∨ ∃ j, x ∈ childrenD_583_i3 j := by decide +kernel
theorem envelope_exact_583_i3 : envelope_583_i3 =
    insert (9, 6) (Finset.univ.biUnion childrenD_583_i3) := by
  exact envelope_eq_combination childrenD_583_i3 (9, 6) envelope_583_i3
    pivot_mem_583_i3 child_envelope_sub_583_i3 envelope_origin_583_i3
def checked_583_i3 : CheckedCard where
  required := required_583_i3
  envelope := envelope_583_i3
  height := height_583_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_583_i3
def height_583_i1 : ℕ := 9
def childrenH_583_i1 : Fin 4 → ℕ := ![height_8, height_321, height_583_i2, height_583_i3]
theorem height_exact_583_i1 : height_583_i1 = 1 + Finset.univ.sup childrenH_583_i1 := by decide +kernel
theorem required_origin_583_i1 : ∀ x ∈ required_583_i1,
    (∃ j, x ∈ childrenC_583_i1 j) ∨ ∀ j, x ∈ childrenD_583_i1 j := by decide +kernel
theorem required_exact_583_i1 : required_583_i1 =
    ((Finset.univ.biUnion childrenC_583_i1) ∪ commonEnvelope childrenD_583_i1).erase (8, 6) := by
  exact required_eq_combination childrenC_583_i1 childrenD_583_i1 (8, 6) required_583_i1
    (by decide +kernel) child_required_sub_583_i1 common_sub_583_i1 required_origin_583_i1
theorem envelope_origin_583_i1 : ∀ x ∈ envelope_583_i1,
    x = (8, 6) ∨ ∃ j, x ∈ childrenD_583_i1 j := by decide +kernel
theorem envelope_exact_583_i1 : envelope_583_i1 =
    insert (8, 6) (Finset.univ.biUnion childrenD_583_i1) := by
  exact envelope_eq_combination childrenD_583_i1 (8, 6) envelope_583_i1
    pivot_mem_583_i1 child_envelope_sub_583_i1 envelope_origin_583_i1
def checked_583_i1 : CheckedCard where
  required := required_583_i1
  envelope := envelope_583_i1
  height := height_583_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_583_i1
def height_583_i0 : ℕ := 10
def childrenH_583_i0 : Fin 2 → ℕ := ![height_3, height_583_i1]
theorem height_exact_583_i0 : height_583_i0 = 1 + Finset.univ.sup childrenH_583_i0 := by decide +kernel
theorem required_origin_583_i0 : ∀ x ∈ required_583_i0,
    (∃ j, x ∈ childrenC_583_i0 j) ∨ ∀ j, x ∈ childrenD_583_i0 j := by decide +kernel
theorem required_exact_583_i0 : required_583_i0 =
    ((Finset.univ.biUnion childrenC_583_i0) ∪ commonEnvelope childrenD_583_i0).erase (5, 6) := by
  exact required_eq_combination childrenC_583_i0 childrenD_583_i0 (5, 6) required_583_i0
    (by decide +kernel) child_required_sub_583_i0 common_sub_583_i0 required_origin_583_i0
theorem envelope_origin_583_i0 : ∀ x ∈ envelope_583_i0,
    x = (5, 6) ∨ ∃ j, x ∈ childrenD_583_i0 j := by decide +kernel
theorem envelope_exact_583_i0 : envelope_583_i0 =
    insert (5, 6) (Finset.univ.biUnion childrenD_583_i0) := by
  exact envelope_eq_combination childrenD_583_i0 (5, 6) envelope_583_i0
    pivot_mem_583_i0 child_envelope_sub_583_i0 envelope_origin_583_i0
def checked_583_i0 : CheckedCard where
  required := required_583_i0
  envelope := envelope_583_i0
  height := height_583_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_583_i0
def height_583_i5 : ℕ := 8
def childrenH_583_i5 : Fin 3 → ℕ := ![height_7, height_86, height_542]
theorem height_exact_583_i5 : height_583_i5 = 1 + Finset.univ.sup childrenH_583_i5 := by decide +kernel
theorem required_origin_583_i5 : ∀ x ∈ required_583_i5,
    (∃ j, x ∈ childrenC_583_i5 j) ∨ ∀ j, x ∈ childrenD_583_i5 j := by decide +kernel
theorem required_exact_583_i5 : required_583_i5 =
    ((Finset.univ.biUnion childrenC_583_i5) ∪ commonEnvelope childrenD_583_i5).erase (5, 8) := by
  exact required_eq_combination childrenC_583_i5 childrenD_583_i5 (5, 8) required_583_i5
    (by decide +kernel) child_required_sub_583_i5 common_sub_583_i5 required_origin_583_i5
theorem envelope_origin_583_i5 : ∀ x ∈ envelope_583_i5,
    x = (5, 8) ∨ ∃ j, x ∈ childrenD_583_i5 j := by decide +kernel
theorem envelope_exact_583_i5 : envelope_583_i5 =
    insert (5, 8) (Finset.univ.biUnion childrenD_583_i5) := by
  exact envelope_eq_combination childrenD_583_i5 (5, 8) envelope_583_i5
    pivot_mem_583_i5 child_envelope_sub_583_i5 envelope_origin_583_i5
def checked_583_i5 : CheckedCard where
  required := required_583_i5
  envelope := envelope_583_i5
  height := height_583_i5
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_583_i5
def height_583_i6 : ℕ := 5
def childrenH_583_i6 : Fin 3 → ℕ := ![height_48, height_109, height_246]
theorem height_exact_583_i6 : height_583_i6 = 1 + Finset.univ.sup childrenH_583_i6 := by decide +kernel
theorem required_origin_583_i6 : ∀ x ∈ required_583_i6,
    (∃ j, x ∈ childrenC_583_i6 j) ∨ ∀ j, x ∈ childrenD_583_i6 j := by decide +kernel
theorem required_exact_583_i6 : required_583_i6 =
    ((Finset.univ.biUnion childrenC_583_i6) ∪ commonEnvelope childrenD_583_i6).erase (6, 7) := by
  exact required_eq_combination childrenC_583_i6 childrenD_583_i6 (6, 7) required_583_i6
    (by decide +kernel) child_required_sub_583_i6 common_sub_583_i6 required_origin_583_i6
theorem envelope_origin_583_i6 : ∀ x ∈ envelope_583_i6,
    x = (6, 7) ∨ ∃ j, x ∈ childrenD_583_i6 j := by decide +kernel
theorem envelope_exact_583_i6 : envelope_583_i6 =
    insert (6, 7) (Finset.univ.biUnion childrenD_583_i6) := by
  exact envelope_eq_combination childrenD_583_i6 (6, 7) envelope_583_i6
    pivot_mem_583_i6 child_envelope_sub_583_i6 envelope_origin_583_i6
def checked_583_i6 : CheckedCard where
  required := required_583_i6
  envelope := envelope_583_i6
  height := height_583_i6
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_583_i6
def height_583_i4 : ℕ := 14
def childrenH_583_i4 : Fin 5 → ℕ := ![height_184, height_423, height_583_i5, height_572, height_583_i6]
theorem height_exact_583_i4 : height_583_i4 = 1 + Finset.univ.sup childrenH_583_i4 := by decide +kernel
theorem required_origin_583_i4 : ∀ x ∈ required_583_i4,
    (∃ j, x ∈ childrenC_583_i4 j) ∨ ∀ j, x ∈ childrenD_583_i4 j := by decide +kernel
theorem required_exact_583_i4 : required_583_i4 =
    ((Finset.univ.biUnion childrenC_583_i4) ∪ commonEnvelope childrenD_583_i4).erase (6, 8) := by
  exact required_eq_combination childrenC_583_i4 childrenD_583_i4 (6, 8) required_583_i4
    (by decide +kernel) child_required_sub_583_i4 common_sub_583_i4 required_origin_583_i4
theorem envelope_origin_583_i4 : ∀ x ∈ envelope_583_i4,
    x = (6, 8) ∨ ∃ j, x ∈ childrenD_583_i4 j := by decide +kernel
theorem envelope_exact_583_i4 : envelope_583_i4 =
    insert (6, 8) (Finset.univ.biUnion childrenD_583_i4) := by
  exact envelope_eq_combination childrenD_583_i4 (6, 8) envelope_583_i4
    pivot_mem_583_i4 child_envelope_sub_583_i4 envelope_origin_583_i4
def checked_583_i4 : CheckedCard where
  required := required_583_i4
  envelope := envelope_583_i4
  height := height_583_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_583_i4
def height_583 : ℕ := 15
def childrenH_583 : Fin 8 → ℕ := ![height_401, height_552, height_556, height_575, height_583_i0, height_579, height_583_i4, height_582]
theorem height_exact_583 : height_583 = 1 + Finset.univ.sup childrenH_583 := by decide +kernel
theorem required_origin_583 : ∀ x ∈ required_583,
    (∃ j, x ∈ childrenC_583 j) ∨ ∀ j, x ∈ childrenD_583 j := by decide +kernel
theorem required_exact_583 : required_583 =
    ((Finset.univ.biUnion childrenC_583) ∪ commonEnvelope childrenD_583).erase (7, 6) := by
  exact required_eq_combination childrenC_583 childrenD_583 (7, 6) required_583
    (by decide +kernel) child_required_sub_583 common_sub_583 required_origin_583
theorem envelope_origin_583 : ∀ x ∈ envelope_583,
    x = (7, 6) ∨ ∃ j, x ∈ childrenD_583 j := by decide +kernel
theorem envelope_exact_583 : envelope_583 =
    insert (7, 6) (Finset.univ.biUnion childrenD_583) := by
  exact envelope_eq_combination childrenD_583 (7, 6) envelope_583
    pivot_mem_583 child_envelope_sub_583 envelope_origin_583
def checked_583 : CheckedCard where
  required := required_583
  envelope := envelope_583
  height := height_583
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_583
def height_648 : ℕ := 15
def childrenH_648 : Fin 12 → ℕ := ![height_174, height_475, height_480, height_480, height_483, height_566, height_587, height_587, height_605, height_635, height_644, height_647]
theorem height_exact_648 : height_648 = 1 + Finset.univ.sup childrenH_648 := by decide +kernel
theorem required_origin_648 : ∀ x ∈ required_648,
    (∃ j, x ∈ childrenC_648 j) ∨ ∀ j, x ∈ childrenD_648 j := by decide +kernel
theorem required_exact_648 : required_648 =
    ((Finset.univ.biUnion childrenC_648) ∪ commonEnvelope childrenD_648).erase (4, 4) := by
  exact required_eq_combination childrenC_648 childrenD_648 (4, 4) required_648
    (by decide +kernel) child_required_sub_648 common_sub_648 required_origin_648
theorem envelope_origin_648 : ∀ x ∈ envelope_648,
    x = (4, 4) ∨ ∃ j, x ∈ childrenD_648 j := by decide +kernel
theorem envelope_exact_648 : envelope_648 =
    insert (4, 4) (Finset.univ.biUnion childrenD_648) := by
  exact envelope_eq_combination childrenD_648 (4, 4) envelope_648
    pivot_mem_648 child_envelope_sub_648 envelope_origin_648
def checked_648 : CheckedCard where
  required := required_648
  envelope := envelope_648
  height := height_648
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_648
def height_656_i1 : ℕ := 9
def childrenH_656_i1 : Fin 7 → ℕ := ![height_117, height_134, height_180, height_337, height_341, height_435, height_558]
theorem height_exact_656_i1 : height_656_i1 = 1 + Finset.univ.sup childrenH_656_i1 := by decide +kernel
theorem required_origin_656_i1 : ∀ x ∈ required_656_i1,
    (∃ j, x ∈ childrenC_656_i1 j) ∨ ∀ j, x ∈ childrenD_656_i1 j := by decide +kernel
theorem required_exact_656_i1 : required_656_i1 =
    ((Finset.univ.biUnion childrenC_656_i1) ∪ commonEnvelope childrenD_656_i1).erase (5, 4) := by
  exact required_eq_combination childrenC_656_i1 childrenD_656_i1 (5, 4) required_656_i1
    (by decide +kernel) child_required_sub_656_i1 common_sub_656_i1 required_origin_656_i1
theorem envelope_origin_656_i1 : ∀ x ∈ envelope_656_i1,
    x = (5, 4) ∨ ∃ j, x ∈ childrenD_656_i1 j := by decide +kernel
theorem envelope_exact_656_i1 : envelope_656_i1 =
    insert (5, 4) (Finset.univ.biUnion childrenD_656_i1) := by
  exact envelope_eq_combination childrenD_656_i1 (5, 4) envelope_656_i1
    pivot_mem_656_i1 child_envelope_sub_656_i1 envelope_origin_656_i1
def checked_656_i1 : CheckedCard where
  required := required_656_i1
  envelope := envelope_656_i1
  height := height_656_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_656_i1
def height_656_i2 : ℕ := 9
def childrenH_656_i2 : Fin 2 → ℕ := ![height_1, height_651]
theorem height_exact_656_i2 : height_656_i2 = 1 + Finset.univ.sup childrenH_656_i2 := by decide +kernel
theorem required_origin_656_i2 : ∀ x ∈ required_656_i2,
    (∃ j, x ∈ childrenC_656_i2 j) ∨ ∀ j, x ∈ childrenD_656_i2 j := by decide +kernel
theorem required_exact_656_i2 : required_656_i2 =
    ((Finset.univ.biUnion childrenC_656_i2) ∪ commonEnvelope childrenD_656_i2).erase (4, 5) := by
  exact required_eq_combination childrenC_656_i2 childrenD_656_i2 (4, 5) required_656_i2
    (by decide +kernel) child_required_sub_656_i2 common_sub_656_i2 required_origin_656_i2
theorem envelope_origin_656_i2 : ∀ x ∈ envelope_656_i2,
    x = (4, 5) ∨ ∃ j, x ∈ childrenD_656_i2 j := by decide +kernel
theorem envelope_exact_656_i2 : envelope_656_i2 =
    insert (4, 5) (Finset.univ.biUnion childrenD_656_i2) := by
  exact envelope_eq_combination childrenD_656_i2 (4, 5) envelope_656_i2
    pivot_mem_656_i2 child_envelope_sub_656_i2 envelope_origin_656_i2
def checked_656_i2 : CheckedCard where
  required := required_656_i2
  envelope := envelope_656_i2
  height := height_656_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_656_i2
def height_656_i3 : ℕ := 11
def childrenH_656_i3 : Fin 2 → ℕ := ![height_1, height_652]
theorem height_exact_656_i3 : height_656_i3 = 1 + Finset.univ.sup childrenH_656_i3 := by decide +kernel
theorem required_origin_656_i3 : ∀ x ∈ required_656_i3,
    (∃ j, x ∈ childrenC_656_i3 j) ∨ ∀ j, x ∈ childrenD_656_i3 j := by decide +kernel
theorem required_exact_656_i3 : required_656_i3 =
    ((Finset.univ.biUnion childrenC_656_i3) ∪ commonEnvelope childrenD_656_i3).erase (4, 5) := by
  exact required_eq_combination childrenC_656_i3 childrenD_656_i3 (4, 5) required_656_i3
    (by decide +kernel) child_required_sub_656_i3 common_sub_656_i3 required_origin_656_i3
theorem envelope_origin_656_i3 : ∀ x ∈ envelope_656_i3,
    x = (4, 5) ∨ ∃ j, x ∈ childrenD_656_i3 j := by decide +kernel
theorem envelope_exact_656_i3 : envelope_656_i3 =
    insert (4, 5) (Finset.univ.biUnion childrenD_656_i3) := by
  exact envelope_eq_combination childrenD_656_i3 (4, 5) envelope_656_i3
    pivot_mem_656_i3 child_envelope_sub_656_i3 envelope_origin_656_i3
def checked_656_i3 : CheckedCard where
  required := required_656_i3
  envelope := envelope_656_i3
  height := height_656_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_656_i3
def height_656_i0 : ℕ := 12
def childrenH_656_i0 : Fin 8 → ℕ := ![height_248, height_300, height_436, height_449, height_510, height_656_i1, height_656_i2, height_656_i3]
theorem height_exact_656_i0 : height_656_i0 = 1 + Finset.univ.sup childrenH_656_i0 := by decide +kernel
theorem required_origin_656_i0 : ∀ x ∈ required_656_i0,
    (∃ j, x ∈ childrenC_656_i0 j) ∨ ∀ j, x ∈ childrenD_656_i0 j := by decide +kernel
theorem required_exact_656_i0 : required_656_i0 =
    ((Finset.univ.biUnion childrenC_656_i0) ∪ commonEnvelope childrenD_656_i0).erase (5, 5) := by
  exact required_eq_combination childrenC_656_i0 childrenD_656_i0 (5, 5) required_656_i0
    (by decide +kernel) child_required_sub_656_i0 common_sub_656_i0 required_origin_656_i0
theorem envelope_origin_656_i0 : ∀ x ∈ envelope_656_i0,
    x = (5, 5) ∨ ∃ j, x ∈ childrenD_656_i0 j := by decide +kernel
theorem envelope_exact_656_i0 : envelope_656_i0 =
    insert (5, 5) (Finset.univ.biUnion childrenD_656_i0) := by
  exact envelope_eq_combination childrenD_656_i0 (5, 5) envelope_656_i0
    pivot_mem_656_i0 child_envelope_sub_656_i0 envelope_origin_656_i0
def checked_656_i0 : CheckedCard where
  required := required_656_i0
  envelope := envelope_656_i0
  height := height_656_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_656_i0
def height_656 : ℕ := 15
def childrenH_656 : Fin 11 → ℕ := ![height_508, height_508, height_605, height_605, height_644, height_645, height_647, height_650, height_650, height_656_i0, height_654]
theorem height_exact_656 : height_656 = 1 + Finset.univ.sup childrenH_656 := by decide +kernel
theorem required_origin_656 : ∀ x ∈ required_656,
    (∃ j, x ∈ childrenC_656 j) ∨ ∀ j, x ∈ childrenD_656 j := by decide +kernel
theorem required_exact_656 : required_656 =
    ((Finset.univ.biUnion childrenC_656) ∪ commonEnvelope childrenD_656).erase (6, 6) := by
  exact required_eq_combination childrenC_656 childrenD_656 (6, 6) required_656
    (by decide +kernel) child_required_sub_656 common_sub_656 required_origin_656
theorem envelope_origin_656 : ∀ x ∈ envelope_656,
    x = (6, 6) ∨ ∃ j, x ∈ childrenD_656 j := by decide +kernel
theorem envelope_exact_656 : envelope_656 =
    insert (6, 6) (Finset.univ.biUnion childrenD_656) := by
  exact envelope_eq_combination childrenD_656 (6, 6) envelope_656
    pivot_mem_656 child_envelope_sub_656 envelope_origin_656
def checked_656 : CheckedCard where
  required := required_656
  envelope := envelope_656
  height := height_656
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_656
end SnakyPrototype.Certificate21

end OAI
