import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part06
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height10Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height10Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height10Part04
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_517_i0 : Finset Cell := ⟨(([(1, 3), (1, 4), (2, 3), (2, 4), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_517_i0 : Finset Cell := ⟨(([(0, 5), (0, 6), (0, 7), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 4), (3, 5), (3, 6), (4, 4), (4, 5), (5, 4), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_517_i0 : Fin 2 → Finset Cell := ![(placed21 6 (5, 4) required_0), (placed21 1 (0, 3) required_404)]
def childrenD_517_i0 : Fin 2 → Finset Cell := ![(placed21 6 (5, 4) envelope_0), (placed21 1 (0, 3) envelope_404)]
theorem common_sub_517_i0 : commonEnvelope childrenD_517_i0 ⊆ insert (3, 4) required_517_i0 := by decide +kernel
theorem child_required_sub_517_i0 : ∀ j, childrenC_517_i0 j ⊆ insert (3, 4) required_517_i0 := by decide +kernel
theorem child_envelope_sub_517_i0 : ∀ j, childrenD_517_i0 j ⊆ envelope_517_i0 := by decide +kernel
theorem pivot_mem_517_i0 : (3, 4) ∈ envelope_517_i0 := by decide +kernel
theorem children_work_517_i0 : ∀ j, Template HasSnaky 7 (childrenC_517_i0 j) (childrenD_517_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 6 (5, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_404 1 (0, 3)).mono (by decide +kernel)
theorem row_works_517_i0 : Template HasSnaky 8 required_517_i0 envelope_517_i0 := by
  refine compose HasSnaky 7 childrenC_517_i0 childrenD_517_i0 children_work_517_i0 (3, 4)
    required_517_i0 envelope_517_i0 pivot_mem_517_i0 child_required_sub_517_i0 child_envelope_sub_517_i0 ?_
  intro b hb
  exact common_sub_517_i0 (mem_commonEnvelope childrenD_517_i0 b hb)
def required_517_i2 : Finset Cell := ⟨(([(1, 3), (1, 4), (2, 3), (2, 4), (4, 3), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_517_i2 : Finset Cell := ⟨(([(0, 5), (0, 7), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 0), (3, 1), (3, 2), (3, 5), (3, 6), (3, 7), (3, 8), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_517_i2 : Fin 5 → Finset Cell := ![(placed21 6 (5, 7) required_14), (placed21 4 (1, 6) required_79), (placed21 4 (3, 7) required_367), (placed21 2 (5, 2) required_513), (placed21 0 (1, 2) required_516)]
def childrenD_517_i2 : Fin 5 → Finset Cell := ![(placed21 6 (5, 7) envelope_14), (placed21 4 (1, 6) envelope_79), (placed21 4 (3, 7) envelope_367), (placed21 2 (5, 2) envelope_513), (placed21 0 (1, 2) envelope_516)]
theorem common_sub_517_i2 : commonEnvelope childrenD_517_i2 ⊆ insert (4, 5) required_517_i2 := by decide +kernel
theorem child_required_sub_517_i2 : ∀ j, childrenC_517_i2 j ⊆ insert (4, 5) required_517_i2 := by decide +kernel
theorem child_envelope_sub_517_i2 : ∀ j, childrenD_517_i2 j ⊆ envelope_517_i2 := by decide +kernel
theorem pivot_mem_517_i2 : (4, 5) ∈ envelope_517_i2 := by decide +kernel
theorem children_work_517_i2 : ∀ j, Template HasSnaky 8 (childrenC_517_i2 j) (childrenD_517_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_14 6 (5, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_79 4 (1, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_367 4 (3, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_513 2 (5, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_516 0 (1, 2)).mono (by decide +kernel)
theorem row_works_517_i2 : Template HasSnaky 9 required_517_i2 envelope_517_i2 := by
  refine compose HasSnaky 8 childrenC_517_i2 childrenD_517_i2 children_work_517_i2 (4, 5)
    required_517_i2 envelope_517_i2 pivot_mem_517_i2 child_required_sub_517_i2 child_envelope_sub_517_i2 ?_
  intro b hb
  exact common_sub_517_i2 (mem_commonEnvelope childrenD_517_i2 b hb)
def required_517_i1 : Finset Cell := ⟨(([(1, 3), (1, 4), (2, 3), (2, 4), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_517_i1 : Finset Cell := ⟨(([(0, 5), (0, 7), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 0), (3, 1), (3, 2), (3, 3), (3, 5), (3, 6), (3, 7), (3, 8), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_517_i1 : Fin 4 → Finset Cell := ![(placed21 1 (1, 3) required_30), (placed21 0 (1, 0) required_59), (placed21 4 (1, 6) required_346), required_517_i2]
def childrenD_517_i1 : Fin 4 → Finset Cell := ![(placed21 1 (1, 3) envelope_30), (placed21 0 (1, 0) envelope_59), (placed21 4 (1, 6) envelope_346), envelope_517_i2]
theorem common_sub_517_i1 : commonEnvelope childrenD_517_i1 ⊆ insert (4, 3) required_517_i1 := by decide +kernel
theorem child_required_sub_517_i1 : ∀ j, childrenC_517_i1 j ⊆ insert (4, 3) required_517_i1 := by decide +kernel
theorem child_envelope_sub_517_i1 : ∀ j, childrenD_517_i1 j ⊆ envelope_517_i1 := by decide +kernel
theorem pivot_mem_517_i1 : (4, 3) ∈ envelope_517_i1 := by decide +kernel
theorem children_work_517_i1 : ∀ j, Template HasSnaky 9 (childrenC_517_i1 j) (childrenD_517_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_30 1 (1, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_59 0 (1, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_346 4 (1, 6)).mono (by decide +kernel)
  · exact row_works_517_i2.mono (by decide +kernel)
theorem row_works_517_i1 : Template HasSnaky 10 required_517_i1 envelope_517_i1 := by
  refine compose HasSnaky 9 childrenC_517_i1 childrenD_517_i1 children_work_517_i1 (4, 3)
    required_517_i1 envelope_517_i1 pivot_mem_517_i1 child_required_sub_517_i1 child_envelope_sub_517_i1 ?_
  intro b hb
  exact common_sub_517_i1 (mem_commonEnvelope childrenD_517_i1 b hb)
def required_517_i4 : Finset Cell := ⟨(([(1, 4), (2, 4), (4, 3), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_517_i4 : Finset Cell := ⟨(([(1, 4), (1, 6), (2, 4), (2, 5), (2, 6), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 0), (5, 1), (5, 2), (5, 5), (5, 6), (5, 7), (5, 8), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_517_i4 : Fin 4 → Finset Cell := ![(placed21 4 (3, 7) required_14), (placed21 0 (1, 2) required_58), (placed21 4 (1, 6) required_79), (placed21 0 (1, 2) required_429)]
def childrenD_517_i4 : Fin 4 → Finset Cell := ![(placed21 4 (3, 7) envelope_14), (placed21 0 (1, 2) envelope_58), (placed21 4 (1, 6) envelope_79), (placed21 0 (1, 2) envelope_429)]
theorem common_sub_517_i4 : commonEnvelope childrenD_517_i4 ⊆ insert (4, 5) required_517_i4 := by decide +kernel
theorem child_required_sub_517_i4 : ∀ j, childrenC_517_i4 j ⊆ insert (4, 5) required_517_i4 := by decide +kernel
theorem child_envelope_sub_517_i4 : ∀ j, childrenD_517_i4 j ⊆ envelope_517_i4 := by decide +kernel
theorem pivot_mem_517_i4 : (4, 5) ∈ envelope_517_i4 := by decide +kernel
theorem children_work_517_i4 : ∀ j, Template HasSnaky 6 (childrenC_517_i4 j) (childrenD_517_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_14 4 (3, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_58 0 (1, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_79 4 (1, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_429 0 (1, 2)).mono (by decide +kernel)
theorem row_works_517_i4 : Template HasSnaky 7 required_517_i4 envelope_517_i4 := by
  refine compose HasSnaky 6 childrenC_517_i4 childrenD_517_i4 children_work_517_i4 (4, 5)
    required_517_i4 envelope_517_i4 pivot_mem_517_i4 child_required_sub_517_i4 child_envelope_sub_517_i4 ?_
  intro b hb
  exact common_sub_517_i4 (mem_commonEnvelope childrenD_517_i4 b hb)
def required_517_i3 : Finset Cell := ⟨(([(1, 3), (1, 4), (2, 3), (2, 4), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_517_i3 : Finset Cell := ⟨(([(1, 3), (1, 4), (1, 6), (2, 3), (2, 4), (2, 5), (2, 6), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 0), (5, 1), (5, 2), (5, 3), (5, 5), (5, 6), (5, 7), (5, 8), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_517_i3 : Fin 4 → Finset Cell := ![(placed21 3 (1, 4) required_36), (placed21 4 (1, 7) required_59), (placed21 4 (1, 6) required_346), required_517_i4]
def childrenD_517_i3 : Fin 4 → Finset Cell := ![(placed21 3 (1, 4) envelope_36), (placed21 4 (1, 7) envelope_59), (placed21 4 (1, 6) envelope_346), envelope_517_i4]
theorem common_sub_517_i3 : commonEnvelope childrenD_517_i3 ⊆ insert (4, 3) required_517_i3 := by decide +kernel
theorem child_required_sub_517_i3 : ∀ j, childrenC_517_i3 j ⊆ insert (4, 3) required_517_i3 := by decide +kernel
theorem child_envelope_sub_517_i3 : ∀ j, childrenD_517_i3 j ⊆ envelope_517_i3 := by decide +kernel
theorem pivot_mem_517_i3 : (4, 3) ∈ envelope_517_i3 := by decide +kernel
theorem children_work_517_i3 : ∀ j, Template HasSnaky 7 (childrenC_517_i3 j) (childrenD_517_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_36 3 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_59 4 (1, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_346 4 (1, 6)).mono (by decide +kernel)
  · exact row_works_517_i4.mono (by decide +kernel)
theorem row_works_517_i3 : Template HasSnaky 8 required_517_i3 envelope_517_i3 := by
  refine compose HasSnaky 7 childrenC_517_i3 childrenD_517_i3 children_work_517_i3 (4, 3)
    required_517_i3 envelope_517_i3 pivot_mem_517_i3 child_required_sub_517_i3 child_envelope_sub_517_i3 ?_
  intro b hb
  exact common_sub_517_i3 (mem_commonEnvelope childrenD_517_i3 b hb)
def required_517 : Finset Cell := ⟨(([(1, 3), (1, 4), (2, 3), (2, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_517 : Finset Cell := ⟨(([(0, 5), (0, 6), (0, 7), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_517 : Fin 4 → Finset Cell := ![(placed21 3 (1, 4) required_74), required_517_i0, required_517_i1, required_517_i3]
def childrenD_517 : Fin 4 → Finset Cell := ![(placed21 3 (1, 4) envelope_74), envelope_517_i0, envelope_517_i1, envelope_517_i3]
theorem common_sub_517 : commonEnvelope childrenD_517 ⊆ insert (4, 4) required_517 := by decide +kernel
theorem child_required_sub_517 : ∀ j, childrenC_517 j ⊆ insert (4, 4) required_517 := by decide +kernel
theorem child_envelope_sub_517 : ∀ j, childrenD_517 j ⊆ envelope_517 := by decide +kernel
theorem pivot_mem_517 : (4, 4) ∈ envelope_517 := by decide +kernel
theorem children_work_517 : ∀ j, Template HasSnaky 10 (childrenC_517 j) (childrenD_517 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_74 3 (1, 4)).mono (by decide +kernel)
  · exact row_works_517_i0.mono (by decide +kernel)
  · exact row_works_517_i1.mono (by decide +kernel)
  · exact row_works_517_i3.mono (by decide +kernel)
theorem row_works_517 : Template HasSnaky 11 required_517 envelope_517 := by
  refine compose HasSnaky 10 childrenC_517 childrenD_517 children_work_517 (4, 4)
    required_517 envelope_517 pivot_mem_517 child_required_sub_517 child_envelope_sub_517 ?_
  intro b hb
  exact common_sub_517 (mem_commonEnvelope childrenD_517 b hb)
def required_527_i0 : Finset Cell := ⟨(([(1, 3), (1, 4), (2, 2), (2, 3), (2, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_527_i0 : Finset Cell := ⟨(([(1, 2), (1, 3), (1, 4), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 4), (3, 5), (3, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_527_i0 : Fin 2 → Finset Cell := ![(placed21 2 (2, 2) required_23), (placed21 4 (1, 6) required_198)]
def childrenD_527_i0 : Fin 2 → Finset Cell := ![(placed21 2 (2, 2) envelope_23), (placed21 4 (1, 6) envelope_198)]
theorem common_sub_527_i0 : commonEnvelope childrenD_527_i0 ⊆ insert (2, 5) required_527_i0 := by decide +kernel
theorem child_required_sub_527_i0 : ∀ j, childrenC_527_i0 j ⊆ insert (2, 5) required_527_i0 := by decide +kernel
theorem child_envelope_sub_527_i0 : ∀ j, childrenD_527_i0 j ⊆ envelope_527_i0 := by decide +kernel
theorem pivot_mem_527_i0 : (2, 5) ∈ envelope_527_i0 := by decide +kernel
theorem children_work_527_i0 : ∀ j, Template HasSnaky 3 (childrenC_527_i0 j) (childrenD_527_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_23 2 (2, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_198 4 (1, 6)).mono (by decide +kernel)
theorem row_works_527_i0 : Template HasSnaky 4 required_527_i0 envelope_527_i0 := by
  refine compose HasSnaky 3 childrenC_527_i0 childrenD_527_i0 children_work_527_i0 (2, 5)
    required_527_i0 envelope_527_i0 pivot_mem_527_i0 child_required_sub_527_i0 child_envelope_sub_527_i0 ?_
  intro b hb
  exact common_sub_527_i0 (mem_commonEnvelope childrenD_527_i0 b hb)
def required_527_i2 : Finset Cell := ⟨(([(1, 3), (1, 4), (2, 2), (2, 3), (2, 4), (2, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_527_i2 : Finset Cell := ⟨(([(0, 2), (1, 2), (1, 3), (1, 4), (2, 2), (2, 3), (2, 4), (2, 5), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 2), (6, 4), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_527_i2 : Fin 6 → Finset Cell := ![(placed21 4 (1, 6) required_392), (placed21 0 (1, 1) required_417), (placed21 0 (1, 2) required_420), (placed21 0 (1, 1) required_521), (placed21 4 (0, 5) required_522), (placed21 0 (1, 2) required_526)]
def childrenD_527_i2 : Fin 6 → Finset Cell := ![(placed21 4 (1, 6) envelope_392), (placed21 0 (1, 1) envelope_417), (placed21 0 (1, 2) envelope_420), (placed21 0 (1, 1) envelope_521), (placed21 4 (0, 5) envelope_522), (placed21 0 (1, 2) envelope_526)]
theorem common_sub_527_i2 : commonEnvelope childrenD_527_i2 ⊆ insert (3, 3) required_527_i2 := by decide +kernel
theorem child_required_sub_527_i2 : ∀ j, childrenC_527_i2 j ⊆ insert (3, 3) required_527_i2 := by decide +kernel
theorem child_envelope_sub_527_i2 : ∀ j, childrenD_527_i2 j ⊆ envelope_527_i2 := by decide +kernel
theorem pivot_mem_527_i2 : (3, 3) ∈ envelope_527_i2 := by decide +kernel
theorem children_work_527_i2 : ∀ j, Template HasSnaky 8 (childrenC_527_i2 j) (childrenD_527_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_392 4 (1, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_417 0 (1, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_420 0 (1, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_521 0 (1, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_522 4 (0, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_526 0 (1, 2)).mono (by decide +kernel)
theorem row_works_527_i2 : Template HasSnaky 9 required_527_i2 envelope_527_i2 := by
  refine compose HasSnaky 8 childrenC_527_i2 childrenD_527_i2 children_work_527_i2 (3, 3)
    required_527_i2 envelope_527_i2 pivot_mem_527_i2 child_required_sub_527_i2 child_envelope_sub_527_i2 ?_
  intro b hb
  exact common_sub_527_i2 (mem_commonEnvelope childrenD_527_i2 b hb)
def required_527_i1 : Finset Cell := ⟨(([(1, 3), (1, 4), (2, 2), (2, 3), (2, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_527_i1 : Finset Cell := ⟨(([(0, 2), (1, 2), (1, 3), (1, 4), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 2), (6, 4), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_527_i1 : Fin 3 → Finset Cell := ![(placed21 0 (2, 1) required_7), (placed21 2 (2, 2) required_23), required_527_i2]
def childrenD_527_i1 : Fin 3 → Finset Cell := ![(placed21 0 (2, 1) envelope_7), (placed21 2 (2, 2) envelope_23), envelope_527_i2]
theorem common_sub_527_i1 : commonEnvelope childrenD_527_i1 ⊆ insert (2, 5) required_527_i1 := by decide +kernel
theorem child_required_sub_527_i1 : ∀ j, childrenC_527_i1 j ⊆ insert (2, 5) required_527_i1 := by decide +kernel
theorem child_envelope_sub_527_i1 : ∀ j, childrenD_527_i1 j ⊆ envelope_527_i1 := by decide +kernel
theorem pivot_mem_527_i1 : (2, 5) ∈ envelope_527_i1 := by decide +kernel
theorem children_work_527_i1 : ∀ j, Template HasSnaky 9 (childrenC_527_i1 j) (childrenD_527_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 0 (2, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_23 2 (2, 2)).mono (by decide +kernel)
  · exact row_works_527_i2.mono (by decide +kernel)
theorem row_works_527_i1 : Template HasSnaky 10 required_527_i1 envelope_527_i1 := by
  refine compose HasSnaky 9 childrenC_527_i1 childrenD_527_i1 children_work_527_i1 (2, 5)
    required_527_i1 envelope_527_i1 pivot_mem_527_i1 child_required_sub_527_i1 child_envelope_sub_527_i1 ?_
  intro b hb
  exact common_sub_527_i1 (mem_commonEnvelope childrenD_527_i1 b hb)
def required_527 : Finset Cell := ⟨(([(1, 3), (1, 4), (2, 3), (2, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_527 : Finset Cell := ⟨(([(0, 2), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 2), (6, 4), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_527 : Fin 4 → Finset Cell := ![(placed21 0 (1, 0) required_206), required_527_i0, (placed21 4 (1, 5) required_405), required_527_i1]
def childrenD_527 : Fin 4 → Finset Cell := ![(placed21 0 (1, 0) envelope_206), envelope_527_i0, (placed21 4 (1, 5) envelope_405), envelope_527_i1]
theorem common_sub_527 : commonEnvelope childrenD_527 ⊆ insert (2, 2) required_527 := by decide +kernel
theorem child_required_sub_527 : ∀ j, childrenC_527 j ⊆ insert (2, 2) required_527 := by decide +kernel
theorem child_envelope_sub_527 : ∀ j, childrenD_527 j ⊆ envelope_527 := by decide +kernel
theorem pivot_mem_527 : (2, 2) ∈ envelope_527 := by decide +kernel
theorem children_work_527 : ∀ j, Template HasSnaky 10 (childrenC_527 j) (childrenD_527 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_206 0 (1, 0)).mono (by decide +kernel)
  · exact row_works_527_i0.mono (by decide +kernel)
  · exact (placed21_template row_works_405 4 (1, 5)).mono (by decide +kernel)
  · exact row_works_527_i1.mono (by decide +kernel)
theorem row_works_527 : Template HasSnaky 11 required_527 envelope_527 := by
  refine compose HasSnaky 10 childrenC_527 childrenD_527 children_work_527 (2, 2)
    required_527 envelope_527 pivot_mem_527 child_required_sub_527 child_envelope_sub_527 ?_
  intro b hb
  exact common_sub_527 (mem_commonEnvelope childrenD_527 b hb)
def required_550 : Finset Cell := ⟨(([(4, 5), (5, 5), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_550 : Finset Cell := ⟨(([(0, 6), (0, 8), (1, 5), (1, 6), (1, 7), (1, 8), (2, 5), (2, 6), (2, 7), (2, 8), (3, 5), (3, 6), (3, 7), (3, 8), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 1), (6, 2), (6, 3), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (7, 4), (7, 5), (8, 4), (8, 5), (8, 6), (9, 4), (9, 5), (9, 6), (10, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_550 : Fin 5 → Finset Cell := ![(placed21 3 (0, 6) required_390), (placed21 5 (8, 3) required_544), (placed21 6 (6, 10) required_545), (placed21 2 (6, 1) required_546), (placed21 2 (6, 0) required_548)]
def childrenD_550 : Fin 5 → Finset Cell := ![(placed21 3 (0, 6) envelope_390), (placed21 5 (8, 3) envelope_544), (placed21 6 (6, 10) envelope_545), (placed21 2 (6, 1) envelope_546), (placed21 2 (6, 0) envelope_548)]
theorem common_sub_550 : commonEnvelope childrenD_550 ⊆ insert (5, 6) required_550 := by decide +kernel
theorem child_required_sub_550 : ∀ j, childrenC_550 j ⊆ insert (5, 6) required_550 := by decide +kernel
theorem child_envelope_sub_550 : ∀ j, childrenD_550 j ⊆ envelope_550 := by decide +kernel
theorem pivot_mem_550 : (5, 6) ∈ envelope_550 := by decide +kernel
theorem children_work_550 : ∀ j, Template HasSnaky 10 (childrenC_550 j) (childrenD_550 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_390 3 (0, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_544 5 (8, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_545 6 (6, 10)).mono (by decide +kernel)
  · exact (placed21_template row_works_546 2 (6, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_548 2 (6, 0)).mono (by decide +kernel)
theorem row_works_550 : Template HasSnaky 11 required_550 envelope_550 := by
  refine compose HasSnaky 10 childrenC_550 childrenD_550 children_work_550 (5, 6)
    required_550 envelope_550 pivot_mem_550 child_required_sub_550 child_envelope_sub_550 ?_
  intro b hb
  exact common_sub_550 (mem_commonEnvelope childrenD_550 b hb)
def required_567_i4 : Finset Cell := ⟨(([(3, 3), (4, 2), (4, 4), (4, 5), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_567_i4 : Finset Cell := ⟨(([(1, 3), (2, 3), (3, 1), (3, 2), (3, 3), (4, 2), (4, 3), (4, 4), (4, 5), (5, 1), (5, 2), (5, 5), (5, 6), (6, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_567_i4 : Fin 2 → Finset Cell := ![(placed21 1 (4, 2) required_5), (placed21 7 (6, 5) required_92)]
def childrenD_567_i4 : Fin 2 → Finset Cell := ![(placed21 1 (4, 2) envelope_5), (placed21 7 (6, 5) envelope_92)]
theorem common_sub_567_i4 : commonEnvelope childrenD_567_i4 ⊆ insert (4, 3) required_567_i4 := by decide +kernel
theorem child_required_sub_567_i4 : ∀ j, childrenC_567_i4 j ⊆ insert (4, 3) required_567_i4 := by decide +kernel
theorem child_envelope_sub_567_i4 : ∀ j, childrenD_567_i4 j ⊆ envelope_567_i4 := by decide +kernel
theorem pivot_mem_567_i4 : (4, 3) ∈ envelope_567_i4 := by decide +kernel
theorem children_work_567_i4 : ∀ j, Template HasSnaky 4 (childrenC_567_i4 j) (childrenD_567_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 1 (4, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_92 7 (6, 5)).mono (by decide +kernel)
theorem row_works_567_i4 : Template HasSnaky 5 required_567_i4 envelope_567_i4 := by
  refine compose HasSnaky 4 childrenC_567_i4 childrenD_567_i4 children_work_567_i4 (4, 3)
    required_567_i4 envelope_567_i4 pivot_mem_567_i4 child_required_sub_567_i4 child_envelope_sub_567_i4 ?_
  intro b hb
  exact common_sub_567_i4 (mem_commonEnvelope childrenD_567_i4 b hb)
def required_567_i3 : Finset Cell := ⟨(([(3, 3), (3, 4), (3, 5), (4, 4), (4, 5), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_567_i3 : Finset Cell := ⟨(([(1, 3), (2, 3), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 1), (5, 2), (5, 5), (5, 6), (6, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_567_i3 : Fin 3 → Finset Cell := ![(placed21 4 (3, 5) required_94), (placed21 4 (3, 6) required_102), required_567_i4]
def childrenD_567_i3 : Fin 3 → Finset Cell := ![(placed21 4 (3, 5) envelope_94), (placed21 4 (3, 6) envelope_102), envelope_567_i4]
theorem common_sub_567_i3 : commonEnvelope childrenD_567_i3 ⊆ insert (4, 2) required_567_i3 := by decide +kernel
theorem child_required_sub_567_i3 : ∀ j, childrenC_567_i3 j ⊆ insert (4, 2) required_567_i3 := by decide +kernel
theorem child_envelope_sub_567_i3 : ∀ j, childrenD_567_i3 j ⊆ envelope_567_i3 := by decide +kernel
theorem pivot_mem_567_i3 : (4, 2) ∈ envelope_567_i3 := by decide +kernel
theorem children_work_567_i3 : ∀ j, Template HasSnaky 5 (childrenC_567_i3 j) (childrenD_567_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_94 4 (3, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_102 4 (3, 6)).mono (by decide +kernel)
  · exact row_works_567_i4.mono (by decide +kernel)
theorem row_works_567_i3 : Template HasSnaky 6 required_567_i3 envelope_567_i3 := by
  refine compose HasSnaky 5 childrenC_567_i3 childrenD_567_i3 children_work_567_i3 (4, 2)
    required_567_i3 envelope_567_i3 pivot_mem_567_i3 child_required_sub_567_i3 child_envelope_sub_567_i3 ?_
  intro b hb
  exact common_sub_567_i3 (mem_commonEnvelope childrenD_567_i3 b hb)
def required_567_i2 : Finset Cell := ⟨(([(3, 3), (3, 4), (3, 5), (4, 5), (5, 5), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_567_i2 : Finset Cell := ⟨(([(1, 3), (2, 3), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 1), (5, 2), (5, 5), (5, 6), (6, 2), (6, 5), (7, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_567_i2 : Fin 2 → Finset Cell := ![(placed21 6 (7, 5) required_0), required_567_i3]
def childrenD_567_i2 : Fin 2 → Finset Cell := ![(placed21 6 (7, 5) envelope_0), envelope_567_i3]
theorem common_sub_567_i2 : commonEnvelope childrenD_567_i2 ⊆ insert (4, 4) required_567_i2 := by decide +kernel
theorem child_required_sub_567_i2 : ∀ j, childrenC_567_i2 j ⊆ insert (4, 4) required_567_i2 := by decide +kernel
theorem child_envelope_sub_567_i2 : ∀ j, childrenD_567_i2 j ⊆ envelope_567_i2 := by decide +kernel
theorem pivot_mem_567_i2 : (4, 4) ∈ envelope_567_i2 := by decide +kernel
theorem children_work_567_i2 : ∀ j, Template HasSnaky 6 (childrenC_567_i2 j) (childrenD_567_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 6 (7, 5)).mono (by decide +kernel)
  · exact row_works_567_i3.mono (by decide +kernel)
theorem row_works_567_i2 : Template HasSnaky 7 required_567_i2 envelope_567_i2 := by
  refine compose HasSnaky 6 childrenC_567_i2 childrenD_567_i2 children_work_567_i2 (4, 4)
    required_567_i2 envelope_567_i2 pivot_mem_567_i2 child_required_sub_567_i2 child_envelope_sub_567_i2 ?_
  intro b hb
  exact common_sub_567_i2 (mem_commonEnvelope childrenD_567_i2 b hb)
def required_567_i1 : Finset Cell := ⟨(([(3, 3), (3, 4), (3, 5), (4, 5), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_567_i1 : Finset Cell := ⟨(([(1, 3), (1, 6), (2, 3), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 1), (5, 2), (5, 4), (5, 5), (5, 6), (6, 2), (6, 4), (6, 5), (7, 4), (7, 5), (8, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_567_i1 : Fin 3 → Finset Cell := ![(placed21 3 (3, 5) required_16), (placed21 7 (7, 6) required_235), required_567_i2]
def childrenD_567_i1 : Fin 3 → Finset Cell := ![(placed21 3 (3, 5) envelope_16), (placed21 7 (7, 6) envelope_235), envelope_567_i2]
theorem common_sub_567_i1 : commonEnvelope childrenD_567_i1 ⊆ insert (6, 5) required_567_i1 := by decide +kernel
theorem child_required_sub_567_i1 : ∀ j, childrenC_567_i1 j ⊆ insert (6, 5) required_567_i1 := by decide +kernel
theorem child_envelope_sub_567_i1 : ∀ j, childrenD_567_i1 j ⊆ envelope_567_i1 := by decide +kernel
theorem pivot_mem_567_i1 : (6, 5) ∈ envelope_567_i1 := by decide +kernel
theorem children_work_567_i1 : ∀ j, Template HasSnaky 7 (childrenC_567_i1 j) (childrenD_567_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_16 3 (3, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_235 7 (7, 6)).mono (by decide +kernel)
  · exact row_works_567_i2.mono (by decide +kernel)
theorem row_works_567_i1 : Template HasSnaky 8 required_567_i1 envelope_567_i1 := by
  refine compose HasSnaky 7 childrenC_567_i1 childrenD_567_i1 children_work_567_i1 (6, 5)
    required_567_i1 envelope_567_i1 pivot_mem_567_i1 child_required_sub_567_i1 child_envelope_sub_567_i1 ?_
  intro b hb
  exact common_sub_567_i1 (mem_commonEnvelope childrenD_567_i1 b hb)
def required_567_i0 : Finset Cell := ⟨(([(3, 3), (3, 4), (3, 5), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_567_i0 : Finset Cell := ⟨(([(1, 3), (1, 6), (2, 3), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 7), (4, 8), (4, 9), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (8, 4), (8, 5), (8, 6), (9, 4), (9, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_567_i0 : Fin 7 → Finset Cell := ![(placed21 3 (1, 6) required_67), (placed21 4 (2, 7) required_134), (placed21 4 (2, 7) required_180), (placed21 6 (6, 9) required_327), (placed21 1 (1, 2) required_504), (placed21 4 (3, 7) required_558), required_567_i1]
def childrenD_567_i0 : Fin 7 → Finset Cell := ![(placed21 3 (1, 6) envelope_67), (placed21 4 (2, 7) envelope_134), (placed21 4 (2, 7) envelope_180), (placed21 6 (6, 9) envelope_327), (placed21 1 (1, 2) envelope_504), (placed21 4 (3, 7) envelope_558), envelope_567_i1]
theorem common_sub_567_i0 : commonEnvelope childrenD_567_i0 ⊆ insert (5, 5) required_567_i0 := by decide +kernel
theorem child_required_sub_567_i0 : ∀ j, childrenC_567_i0 j ⊆ insert (5, 5) required_567_i0 := by decide +kernel
theorem child_envelope_sub_567_i0 : ∀ j, childrenD_567_i0 j ⊆ envelope_567_i0 := by decide +kernel
theorem pivot_mem_567_i0 : (5, 5) ∈ envelope_567_i0 := by decide +kernel
theorem children_work_567_i0 : ∀ j, Template HasSnaky 9 (childrenC_567_i0 j) (childrenD_567_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_67 3 (1, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_134 4 (2, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_180 4 (2, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_327 6 (6, 9)).mono (by decide +kernel)
  · exact (placed21_template row_works_504 1 (1, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_558 4 (3, 7)).mono (by decide +kernel)
  · exact row_works_567_i1.mono (by decide +kernel)
theorem row_works_567_i0 : Template HasSnaky 10 required_567_i0 envelope_567_i0 := by
  refine compose HasSnaky 9 childrenC_567_i0 childrenD_567_i0 children_work_567_i0 (5, 5)
    required_567_i0 envelope_567_i0 pivot_mem_567_i0 child_required_sub_567_i0 child_envelope_sub_567_i0 ?_
  intro b hb
  exact common_sub_567_i0 (mem_commonEnvelope childrenD_567_i0 b hb)
def required_567 : Finset Cell := ⟨(([(0, 4), (1, 4), (3, 3), (3, 4), (3, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_567 : Finset Cell := ⟨(([(0, 3), (0, 4), (1, 3), (1, 4), (1, 6), (2, 2), (2, 3), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (8, 1), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (9, 4), (9, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_567 : Fin 5 → Finset Cell := ![(placed21 4 (3, 6) required_27), (placed21 0 (3, 2) required_44), (placed21 0 (0, 1) required_560), (placed21 0 (2, 0) required_563), required_567_i0]
def childrenD_567 : Fin 5 → Finset Cell := ![(placed21 4 (3, 6) envelope_27), (placed21 0 (3, 2) envelope_44), (placed21 0 (0, 1) envelope_560), (placed21 0 (2, 0) envelope_563), envelope_567_i0]
theorem common_sub_567 : commonEnvelope childrenD_567 ⊆ insert (4, 5) required_567 := by decide +kernel
theorem child_required_sub_567 : ∀ j, childrenC_567 j ⊆ insert (4, 5) required_567 := by decide +kernel
theorem child_envelope_sub_567 : ∀ j, childrenD_567 j ⊆ envelope_567 := by decide +kernel
theorem pivot_mem_567 : (4, 5) ∈ envelope_567 := by decide +kernel
theorem children_work_567 : ∀ j, Template HasSnaky 10 (childrenC_567 j) (childrenD_567 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_27 4 (3, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_44 0 (3, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_560 0 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_563 0 (2, 0)).mono (by decide +kernel)
  · exact row_works_567_i0.mono (by decide +kernel)
theorem row_works_567 : Template HasSnaky 11 required_567 envelope_567 := by
  refine compose HasSnaky 10 childrenC_567 childrenD_567 children_work_567 (4, 5)
    required_567 envelope_567 pivot_mem_567 child_required_sub_567 child_envelope_sub_567 ?_
  intro b hb
  exact common_sub_567 (mem_commonEnvelope childrenD_567 b hb)
def required_579 : Finset Cell := ⟨(([(1, 4), (2, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_579 : Finset Cell := ⟨(([(0, 2), (0, 3), (0, 4), (0, 6), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 3), (6, 4), (6, 5), (7, 3), (7, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_579 : Fin 9 → Finset Cell := ![(placed21 0 (0, 1) required_118), (placed21 4 (0, 6) required_137), (placed21 0 (0, 1) required_172), (placed21 0 (0, 1) required_173), (placed21 4 (0, 6) required_181), (placed21 4 (0, 7) required_435), (placed21 0 (0, 1) required_507), (placed21 0 (0, 1) required_578), (placed21 4 (0, 7) required_578)]
def childrenD_579 : Fin 9 → Finset Cell := ![(placed21 0 (0, 1) envelope_118), (placed21 4 (0, 6) envelope_137), (placed21 0 (0, 1) envelope_172), (placed21 0 (0, 1) envelope_173), (placed21 4 (0, 6) envelope_181), (placed21 4 (0, 7) envelope_435), (placed21 0 (0, 1) envelope_507), (placed21 0 (0, 1) envelope_578), (placed21 4 (0, 7) envelope_578)]
theorem common_sub_579 : commonEnvelope childrenD_579 ⊆ insert (3, 4) required_579 := by decide +kernel
theorem child_required_sub_579 : ∀ j, childrenC_579 j ⊆ insert (3, 4) required_579 := by decide +kernel
theorem child_envelope_sub_579 : ∀ j, childrenD_579 j ⊆ envelope_579 := by decide +kernel
theorem pivot_mem_579 : (3, 4) ∈ envelope_579 := by decide +kernel
theorem children_work_579 : ∀ j, Template HasSnaky 10 (childrenC_579 j) (childrenD_579 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_118 0 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_137 4 (0, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_172 0 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_173 0 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_181 4 (0, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_435 4 (0, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_507 0 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_578 0 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_578 4 (0, 7)).mono (by decide +kernel)
theorem row_works_579 : Template HasSnaky 11 required_579 envelope_579 := by
  refine compose HasSnaky 10 childrenC_579 childrenD_579 children_work_579 (3, 4)
    required_579 envelope_579 pivot_mem_579 child_required_sub_579 child_envelope_sub_579 ?_
  intro b hb
  exact common_sub_579 (mem_commonEnvelope childrenD_579 b hb)
def required_581 : Finset Cell := ⟨(([(4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_581 : Finset Cell := ⟨(([(0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 0), (3, 1), (3, 2), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 0), (5, 1), (5, 2), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, 4), (7, 5), (7, 6), (7, 7), (8, 4), (8, 5), (8, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_581 : Fin 6 → Finset Cell := ![(placed21 0 (2, 2) required_188), (placed21 2 (6, 2) required_188), (placed21 5 (7, 4) required_258), (placed21 7 (7, 7) required_309), (placed21 1 (1, 3) required_578), (placed21 5 (7, 3) required_578)]
def childrenD_581 : Fin 6 → Finset Cell := ![(placed21 0 (2, 2) envelope_188), (placed21 2 (6, 2) envelope_188), (placed21 5 (7, 4) envelope_258), (placed21 7 (7, 7) envelope_309), (placed21 1 (1, 3) envelope_578), (placed21 5 (7, 3) envelope_578)]
theorem common_sub_581 : commonEnvelope childrenD_581 ⊆ insert (4, 6) required_581 := by decide +kernel
theorem child_required_sub_581 : ∀ j, childrenC_581 j ⊆ insert (4, 6) required_581 := by decide +kernel
theorem child_envelope_sub_581 : ∀ j, childrenD_581 j ⊆ envelope_581 := by decide +kernel
theorem pivot_mem_581 : (4, 6) ∈ envelope_581 := by decide +kernel
theorem children_work_581 : ∀ j, Template HasSnaky 10 (childrenC_581 j) (childrenD_581 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_188 0 (2, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_188 2 (6, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_258 5 (7, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_309 7 (7, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_578 1 (1, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_578 5 (7, 3)).mono (by decide +kernel)
theorem row_works_581 : Template HasSnaky 11 required_581 envelope_581 := by
  refine compose HasSnaky 10 childrenC_581 childrenD_581 children_work_581 (4, 6)
    required_581 envelope_581 pivot_mem_581 child_required_sub_581 child_envelope_sub_581 ?_
  intro b hb
  exact common_sub_581 (mem_commonEnvelope childrenD_581 b hb)
def required_586 : Finset Cell := ⟨(([(1, 2), (2, 2), (3, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_586 : Finset Cell := ⟨(([(0, 1), (0, 3), (0, 4), (0, 5), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (2, 4), (2, 5), (3, 2), (3, 3), (3, 4), (3, 5), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 1), (5, 2), (5, 3), (6, 1), (6, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_586 : Fin 3 → Finset Cell := ![(placed21 0 (1, 1) required_8), required_179, required_585]
def childrenD_586 : Fin 3 → Finset Cell := ![(placed21 0 (1, 1) envelope_8), envelope_179, envelope_585]
theorem common_sub_586 : commonEnvelope childrenD_586 ⊆ insert (4, 2) required_586 := by decide +kernel
theorem child_required_sub_586 : ∀ j, childrenC_586 j ⊆ insert (4, 2) required_586 := by decide +kernel
theorem child_envelope_sub_586 : ∀ j, childrenD_586 j ⊆ envelope_586 := by decide +kernel
theorem pivot_mem_586 : (4, 2) ∈ envelope_586 := by decide +kernel
theorem children_work_586 : ∀ j, Template HasSnaky 10 (childrenC_586 j) (childrenD_586 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_8 0 (1, 1)).mono (by decide +kernel)
  · exact row_works_179.mono (by decide +kernel)
  · exact row_works_585.mono (by decide +kernel)
theorem row_works_586 : Template HasSnaky 11 required_586 envelope_586 := by
  refine compose HasSnaky 10 childrenC_586 childrenD_586 children_work_586 (4, 2)
    required_586 envelope_586 pivot_mem_586 child_required_sub_586 child_envelope_sub_586 ?_
  intro b hb
  exact common_sub_586 (mem_commonEnvelope childrenD_586 b hb)
def required_589 : Finset Cell := ⟨(([(1, 2), (2, 2), (3, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_589 : Finset Cell := ⟨(([(0, 1), (0, 3), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 2), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 4), (3, 5), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (6, 1), (6, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_589 : Fin 4 → Finset Cell := ![(placed21 1 (0, 2) required_7), (placed21 0 (1, 1) required_8), (placed21 3 (0, 3) required_9), (placed21 2 (5, 0) required_585)]
def childrenD_589 : Fin 4 → Finset Cell := ![(placed21 1 (0, 2) envelope_7), (placed21 0 (1, 1) envelope_8), (placed21 3 (0, 3) envelope_9), (placed21 2 (5, 0) envelope_585)]
theorem common_sub_589 : commonEnvelope childrenD_589 ⊆ insert (4, 2) required_589 := by decide +kernel
theorem child_required_sub_589 : ∀ j, childrenC_589 j ⊆ insert (4, 2) required_589 := by decide +kernel
theorem child_envelope_sub_589 : ∀ j, childrenD_589 j ⊆ envelope_589 := by decide +kernel
theorem pivot_mem_589 : (4, 2) ∈ envelope_589 := by decide +kernel
theorem children_work_589 : ∀ j, Template HasSnaky 10 (childrenC_589 j) (childrenD_589 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 1 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_8 0 (1, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_9 3 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_585 2 (5, 0)).mono (by decide +kernel)
theorem row_works_589 : Template HasSnaky 11 required_589 envelope_589 := by
  refine compose HasSnaky 10 childrenC_589 childrenD_589 children_work_589 (4, 2)
    required_589 envelope_589 pivot_mem_589 child_required_sub_589 child_envelope_sub_589 ?_
  intro b hb
  exact common_sub_589 (mem_commonEnvelope childrenD_589 b hb)
def height_517_i0 : ℕ := 8
def childrenH_517_i0 : Fin 2 → ℕ := ![height_0, height_404]
theorem height_exact_517_i0 : height_517_i0 = 1 + Finset.univ.sup childrenH_517_i0 := by decide +kernel
theorem required_origin_517_i0 : ∀ x ∈ required_517_i0,
    (∃ j, x ∈ childrenC_517_i0 j) ∨ ∀ j, x ∈ childrenD_517_i0 j := by decide +kernel
theorem required_exact_517_i0 : required_517_i0 =
    ((Finset.univ.biUnion childrenC_517_i0) ∪ commonEnvelope childrenD_517_i0).erase (3, 4) := by
  exact required_eq_combination childrenC_517_i0 childrenD_517_i0 (3, 4) required_517_i0
    (by decide +kernel) child_required_sub_517_i0 common_sub_517_i0 required_origin_517_i0
theorem envelope_origin_517_i0 : ∀ x ∈ envelope_517_i0,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_517_i0 j := by decide +kernel
theorem envelope_exact_517_i0 : envelope_517_i0 =
    insert (3, 4) (Finset.univ.biUnion childrenD_517_i0) := by
  exact envelope_eq_combination childrenD_517_i0 (3, 4) envelope_517_i0
    pivot_mem_517_i0 child_envelope_sub_517_i0 envelope_origin_517_i0
def checked_517_i0 : CheckedCard where
  required := required_517_i0
  envelope := envelope_517_i0
  height := height_517_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_517_i0
def height_517_i2 : ℕ := 9
def childrenH_517_i2 : Fin 5 → ℕ := ![height_14, height_79, height_367, height_513, height_516]
theorem height_exact_517_i2 : height_517_i2 = 1 + Finset.univ.sup childrenH_517_i2 := by decide +kernel
theorem required_origin_517_i2 : ∀ x ∈ required_517_i2,
    (∃ j, x ∈ childrenC_517_i2 j) ∨ ∀ j, x ∈ childrenD_517_i2 j := by decide +kernel
theorem required_exact_517_i2 : required_517_i2 =
    ((Finset.univ.biUnion childrenC_517_i2) ∪ commonEnvelope childrenD_517_i2).erase (4, 5) := by
  exact required_eq_combination childrenC_517_i2 childrenD_517_i2 (4, 5) required_517_i2
    (by decide +kernel) child_required_sub_517_i2 common_sub_517_i2 required_origin_517_i2
theorem envelope_origin_517_i2 : ∀ x ∈ envelope_517_i2,
    x = (4, 5) ∨ ∃ j, x ∈ childrenD_517_i2 j := by decide +kernel
theorem envelope_exact_517_i2 : envelope_517_i2 =
    insert (4, 5) (Finset.univ.biUnion childrenD_517_i2) := by
  exact envelope_eq_combination childrenD_517_i2 (4, 5) envelope_517_i2
    pivot_mem_517_i2 child_envelope_sub_517_i2 envelope_origin_517_i2
def checked_517_i2 : CheckedCard where
  required := required_517_i2
  envelope := envelope_517_i2
  height := height_517_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_517_i2
def height_517_i1 : ℕ := 10
def childrenH_517_i1 : Fin 4 → ℕ := ![height_30, height_59, height_346, height_517_i2]
theorem height_exact_517_i1 : height_517_i1 = 1 + Finset.univ.sup childrenH_517_i1 := by decide +kernel
theorem required_origin_517_i1 : ∀ x ∈ required_517_i1,
    (∃ j, x ∈ childrenC_517_i1 j) ∨ ∀ j, x ∈ childrenD_517_i1 j := by decide +kernel
theorem required_exact_517_i1 : required_517_i1 =
    ((Finset.univ.biUnion childrenC_517_i1) ∪ commonEnvelope childrenD_517_i1).erase (4, 3) := by
  exact required_eq_combination childrenC_517_i1 childrenD_517_i1 (4, 3) required_517_i1
    (by decide +kernel) child_required_sub_517_i1 common_sub_517_i1 required_origin_517_i1
theorem envelope_origin_517_i1 : ∀ x ∈ envelope_517_i1,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_517_i1 j := by decide +kernel
theorem envelope_exact_517_i1 : envelope_517_i1 =
    insert (4, 3) (Finset.univ.biUnion childrenD_517_i1) := by
  exact envelope_eq_combination childrenD_517_i1 (4, 3) envelope_517_i1
    pivot_mem_517_i1 child_envelope_sub_517_i1 envelope_origin_517_i1
def checked_517_i1 : CheckedCard where
  required := required_517_i1
  envelope := envelope_517_i1
  height := height_517_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_517_i1
def height_517_i4 : ℕ := 7
def childrenH_517_i4 : Fin 4 → ℕ := ![height_14, height_58, height_79, height_429]
theorem height_exact_517_i4 : height_517_i4 = 1 + Finset.univ.sup childrenH_517_i4 := by decide +kernel
theorem required_origin_517_i4 : ∀ x ∈ required_517_i4,
    (∃ j, x ∈ childrenC_517_i4 j) ∨ ∀ j, x ∈ childrenD_517_i4 j := by decide +kernel
theorem required_exact_517_i4 : required_517_i4 =
    ((Finset.univ.biUnion childrenC_517_i4) ∪ commonEnvelope childrenD_517_i4).erase (4, 5) := by
  exact required_eq_combination childrenC_517_i4 childrenD_517_i4 (4, 5) required_517_i4
    (by decide +kernel) child_required_sub_517_i4 common_sub_517_i4 required_origin_517_i4
theorem envelope_origin_517_i4 : ∀ x ∈ envelope_517_i4,
    x = (4, 5) ∨ ∃ j, x ∈ childrenD_517_i4 j := by decide +kernel
theorem envelope_exact_517_i4 : envelope_517_i4 =
    insert (4, 5) (Finset.univ.biUnion childrenD_517_i4) := by
  exact envelope_eq_combination childrenD_517_i4 (4, 5) envelope_517_i4
    pivot_mem_517_i4 child_envelope_sub_517_i4 envelope_origin_517_i4
def checked_517_i4 : CheckedCard where
  required := required_517_i4
  envelope := envelope_517_i4
  height := height_517_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_517_i4
def height_517_i3 : ℕ := 8
def childrenH_517_i3 : Fin 4 → ℕ := ![height_36, height_59, height_346, height_517_i4]
theorem height_exact_517_i3 : height_517_i3 = 1 + Finset.univ.sup childrenH_517_i3 := by decide +kernel
theorem required_origin_517_i3 : ∀ x ∈ required_517_i3,
    (∃ j, x ∈ childrenC_517_i3 j) ∨ ∀ j, x ∈ childrenD_517_i3 j := by decide +kernel
theorem required_exact_517_i3 : required_517_i3 =
    ((Finset.univ.biUnion childrenC_517_i3) ∪ commonEnvelope childrenD_517_i3).erase (4, 3) := by
  exact required_eq_combination childrenC_517_i3 childrenD_517_i3 (4, 3) required_517_i3
    (by decide +kernel) child_required_sub_517_i3 common_sub_517_i3 required_origin_517_i3
theorem envelope_origin_517_i3 : ∀ x ∈ envelope_517_i3,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_517_i3 j := by decide +kernel
theorem envelope_exact_517_i3 : envelope_517_i3 =
    insert (4, 3) (Finset.univ.biUnion childrenD_517_i3) := by
  exact envelope_eq_combination childrenD_517_i3 (4, 3) envelope_517_i3
    pivot_mem_517_i3 child_envelope_sub_517_i3 envelope_origin_517_i3
def checked_517_i3 : CheckedCard where
  required := required_517_i3
  envelope := envelope_517_i3
  height := height_517_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_517_i3
def height_517 : ℕ := 11
def childrenH_517 : Fin 4 → ℕ := ![height_74, height_517_i0, height_517_i1, height_517_i3]
theorem height_exact_517 : height_517 = 1 + Finset.univ.sup childrenH_517 := by decide +kernel
theorem required_origin_517 : ∀ x ∈ required_517,
    (∃ j, x ∈ childrenC_517 j) ∨ ∀ j, x ∈ childrenD_517 j := by decide +kernel
theorem required_exact_517 : required_517 =
    ((Finset.univ.biUnion childrenC_517) ∪ commonEnvelope childrenD_517).erase (4, 4) := by
  exact required_eq_combination childrenC_517 childrenD_517 (4, 4) required_517
    (by decide +kernel) child_required_sub_517 common_sub_517 required_origin_517
theorem envelope_origin_517 : ∀ x ∈ envelope_517,
    x = (4, 4) ∨ ∃ j, x ∈ childrenD_517 j := by decide +kernel
theorem envelope_exact_517 : envelope_517 =
    insert (4, 4) (Finset.univ.biUnion childrenD_517) := by
  exact envelope_eq_combination childrenD_517 (4, 4) envelope_517
    pivot_mem_517 child_envelope_sub_517 envelope_origin_517
def checked_517 : CheckedCard where
  required := required_517
  envelope := envelope_517
  height := height_517
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_517
def height_527_i0 : ℕ := 4
def childrenH_527_i0 : Fin 2 → ℕ := ![height_23, height_198]
theorem height_exact_527_i0 : height_527_i0 = 1 + Finset.univ.sup childrenH_527_i0 := by decide +kernel
theorem required_origin_527_i0 : ∀ x ∈ required_527_i0,
    (∃ j, x ∈ childrenC_527_i0 j) ∨ ∀ j, x ∈ childrenD_527_i0 j := by decide +kernel
theorem required_exact_527_i0 : required_527_i0 =
    ((Finset.univ.biUnion childrenC_527_i0) ∪ commonEnvelope childrenD_527_i0).erase (2, 5) := by
  exact required_eq_combination childrenC_527_i0 childrenD_527_i0 (2, 5) required_527_i0
    (by decide +kernel) child_required_sub_527_i0 common_sub_527_i0 required_origin_527_i0
theorem envelope_origin_527_i0 : ∀ x ∈ envelope_527_i0,
    x = (2, 5) ∨ ∃ j, x ∈ childrenD_527_i0 j := by decide +kernel
theorem envelope_exact_527_i0 : envelope_527_i0 =
    insert (2, 5) (Finset.univ.biUnion childrenD_527_i0) := by
  exact envelope_eq_combination childrenD_527_i0 (2, 5) envelope_527_i0
    pivot_mem_527_i0 child_envelope_sub_527_i0 envelope_origin_527_i0
def checked_527_i0 : CheckedCard where
  required := required_527_i0
  envelope := envelope_527_i0
  height := height_527_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_527_i0
def height_527_i2 : ℕ := 9
def childrenH_527_i2 : Fin 6 → ℕ := ![height_392, height_417, height_420, height_521, height_522, height_526]
theorem height_exact_527_i2 : height_527_i2 = 1 + Finset.univ.sup childrenH_527_i2 := by decide +kernel
theorem required_origin_527_i2 : ∀ x ∈ required_527_i2,
    (∃ j, x ∈ childrenC_527_i2 j) ∨ ∀ j, x ∈ childrenD_527_i2 j := by decide +kernel
theorem required_exact_527_i2 : required_527_i2 =
    ((Finset.univ.biUnion childrenC_527_i2) ∪ commonEnvelope childrenD_527_i2).erase (3, 3) := by
  exact required_eq_combination childrenC_527_i2 childrenD_527_i2 (3, 3) required_527_i2
    (by decide +kernel) child_required_sub_527_i2 common_sub_527_i2 required_origin_527_i2
theorem envelope_origin_527_i2 : ∀ x ∈ envelope_527_i2,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_527_i2 j := by decide +kernel
theorem envelope_exact_527_i2 : envelope_527_i2 =
    insert (3, 3) (Finset.univ.biUnion childrenD_527_i2) := by
  exact envelope_eq_combination childrenD_527_i2 (3, 3) envelope_527_i2
    pivot_mem_527_i2 child_envelope_sub_527_i2 envelope_origin_527_i2
def checked_527_i2 : CheckedCard where
  required := required_527_i2
  envelope := envelope_527_i2
  height := height_527_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_527_i2
def height_527_i1 : ℕ := 10
def childrenH_527_i1 : Fin 3 → ℕ := ![height_7, height_23, height_527_i2]
theorem height_exact_527_i1 : height_527_i1 = 1 + Finset.univ.sup childrenH_527_i1 := by decide +kernel
theorem required_origin_527_i1 : ∀ x ∈ required_527_i1,
    (∃ j, x ∈ childrenC_527_i1 j) ∨ ∀ j, x ∈ childrenD_527_i1 j := by decide +kernel
theorem required_exact_527_i1 : required_527_i1 =
    ((Finset.univ.biUnion childrenC_527_i1) ∪ commonEnvelope childrenD_527_i1).erase (2, 5) := by
  exact required_eq_combination childrenC_527_i1 childrenD_527_i1 (2, 5) required_527_i1
    (by decide +kernel) child_required_sub_527_i1 common_sub_527_i1 required_origin_527_i1
theorem envelope_origin_527_i1 : ∀ x ∈ envelope_527_i1,
    x = (2, 5) ∨ ∃ j, x ∈ childrenD_527_i1 j := by decide +kernel
theorem envelope_exact_527_i1 : envelope_527_i1 =
    insert (2, 5) (Finset.univ.biUnion childrenD_527_i1) := by
  exact envelope_eq_combination childrenD_527_i1 (2, 5) envelope_527_i1
    pivot_mem_527_i1 child_envelope_sub_527_i1 envelope_origin_527_i1
def checked_527_i1 : CheckedCard where
  required := required_527_i1
  envelope := envelope_527_i1
  height := height_527_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_527_i1
def height_527 : ℕ := 11
def childrenH_527 : Fin 4 → ℕ := ![height_206, height_527_i0, height_405, height_527_i1]
theorem height_exact_527 : height_527 = 1 + Finset.univ.sup childrenH_527 := by decide +kernel
theorem required_origin_527 : ∀ x ∈ required_527,
    (∃ j, x ∈ childrenC_527 j) ∨ ∀ j, x ∈ childrenD_527 j := by decide +kernel
theorem required_exact_527 : required_527 =
    ((Finset.univ.biUnion childrenC_527) ∪ commonEnvelope childrenD_527).erase (2, 2) := by
  exact required_eq_combination childrenC_527 childrenD_527 (2, 2) required_527
    (by decide +kernel) child_required_sub_527 common_sub_527 required_origin_527
theorem envelope_origin_527 : ∀ x ∈ envelope_527,
    x = (2, 2) ∨ ∃ j, x ∈ childrenD_527 j := by decide +kernel
theorem envelope_exact_527 : envelope_527 =
    insert (2, 2) (Finset.univ.biUnion childrenD_527) := by
  exact envelope_eq_combination childrenD_527 (2, 2) envelope_527
    pivot_mem_527 child_envelope_sub_527 envelope_origin_527
def checked_527 : CheckedCard where
  required := required_527
  envelope := envelope_527
  height := height_527
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_527
def height_550 : ℕ := 11
def childrenH_550 : Fin 5 → ℕ := ![height_390, height_544, height_545, height_546, height_548]
theorem height_exact_550 : height_550 = 1 + Finset.univ.sup childrenH_550 := by decide +kernel
theorem required_origin_550 : ∀ x ∈ required_550,
    (∃ j, x ∈ childrenC_550 j) ∨ ∀ j, x ∈ childrenD_550 j := by decide +kernel
theorem required_exact_550 : required_550 =
    ((Finset.univ.biUnion childrenC_550) ∪ commonEnvelope childrenD_550).erase (5, 6) := by
  exact required_eq_combination childrenC_550 childrenD_550 (5, 6) required_550
    (by decide +kernel) child_required_sub_550 common_sub_550 required_origin_550
theorem envelope_origin_550 : ∀ x ∈ envelope_550,
    x = (5, 6) ∨ ∃ j, x ∈ childrenD_550 j := by decide +kernel
theorem envelope_exact_550 : envelope_550 =
    insert (5, 6) (Finset.univ.biUnion childrenD_550) := by
  exact envelope_eq_combination childrenD_550 (5, 6) envelope_550
    pivot_mem_550 child_envelope_sub_550 envelope_origin_550
def checked_550 : CheckedCard where
  required := required_550
  envelope := envelope_550
  height := height_550
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_550
def height_567_i4 : ℕ := 5
def childrenH_567_i4 : Fin 2 → ℕ := ![height_5, height_92]
theorem height_exact_567_i4 : height_567_i4 = 1 + Finset.univ.sup childrenH_567_i4 := by decide +kernel
theorem required_origin_567_i4 : ∀ x ∈ required_567_i4,
    (∃ j, x ∈ childrenC_567_i4 j) ∨ ∀ j, x ∈ childrenD_567_i4 j := by decide +kernel
theorem required_exact_567_i4 : required_567_i4 =
    ((Finset.univ.biUnion childrenC_567_i4) ∪ commonEnvelope childrenD_567_i4).erase (4, 3) := by
  exact required_eq_combination childrenC_567_i4 childrenD_567_i4 (4, 3) required_567_i4
    (by decide +kernel) child_required_sub_567_i4 common_sub_567_i4 required_origin_567_i4
theorem envelope_origin_567_i4 : ∀ x ∈ envelope_567_i4,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_567_i4 j := by decide +kernel
theorem envelope_exact_567_i4 : envelope_567_i4 =
    insert (4, 3) (Finset.univ.biUnion childrenD_567_i4) := by
  exact envelope_eq_combination childrenD_567_i4 (4, 3) envelope_567_i4
    pivot_mem_567_i4 child_envelope_sub_567_i4 envelope_origin_567_i4
def checked_567_i4 : CheckedCard where
  required := required_567_i4
  envelope := envelope_567_i4
  height := height_567_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_567_i4
def height_567_i3 : ℕ := 6
def childrenH_567_i3 : Fin 3 → ℕ := ![height_94, height_102, height_567_i4]
theorem height_exact_567_i3 : height_567_i3 = 1 + Finset.univ.sup childrenH_567_i3 := by decide +kernel
theorem required_origin_567_i3 : ∀ x ∈ required_567_i3,
    (∃ j, x ∈ childrenC_567_i3 j) ∨ ∀ j, x ∈ childrenD_567_i3 j := by decide +kernel
theorem required_exact_567_i3 : required_567_i3 =
    ((Finset.univ.biUnion childrenC_567_i3) ∪ commonEnvelope childrenD_567_i3).erase (4, 2) := by
  exact required_eq_combination childrenC_567_i3 childrenD_567_i3 (4, 2) required_567_i3
    (by decide +kernel) child_required_sub_567_i3 common_sub_567_i3 required_origin_567_i3
theorem envelope_origin_567_i3 : ∀ x ∈ envelope_567_i3,
    x = (4, 2) ∨ ∃ j, x ∈ childrenD_567_i3 j := by decide +kernel
theorem envelope_exact_567_i3 : envelope_567_i3 =
    insert (4, 2) (Finset.univ.biUnion childrenD_567_i3) := by
  exact envelope_eq_combination childrenD_567_i3 (4, 2) envelope_567_i3
    pivot_mem_567_i3 child_envelope_sub_567_i3 envelope_origin_567_i3
def checked_567_i3 : CheckedCard where
  required := required_567_i3
  envelope := envelope_567_i3
  height := height_567_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_567_i3
def height_567_i2 : ℕ := 7
def childrenH_567_i2 : Fin 2 → ℕ := ![height_0, height_567_i3]
theorem height_exact_567_i2 : height_567_i2 = 1 + Finset.univ.sup childrenH_567_i2 := by decide +kernel
theorem required_origin_567_i2 : ∀ x ∈ required_567_i2,
    (∃ j, x ∈ childrenC_567_i2 j) ∨ ∀ j, x ∈ childrenD_567_i2 j := by decide +kernel
theorem required_exact_567_i2 : required_567_i2 =
    ((Finset.univ.biUnion childrenC_567_i2) ∪ commonEnvelope childrenD_567_i2).erase (4, 4) := by
  exact required_eq_combination childrenC_567_i2 childrenD_567_i2 (4, 4) required_567_i2
    (by decide +kernel) child_required_sub_567_i2 common_sub_567_i2 required_origin_567_i2
theorem envelope_origin_567_i2 : ∀ x ∈ envelope_567_i2,
    x = (4, 4) ∨ ∃ j, x ∈ childrenD_567_i2 j := by decide +kernel
theorem envelope_exact_567_i2 : envelope_567_i2 =
    insert (4, 4) (Finset.univ.biUnion childrenD_567_i2) := by
  exact envelope_eq_combination childrenD_567_i2 (4, 4) envelope_567_i2
    pivot_mem_567_i2 child_envelope_sub_567_i2 envelope_origin_567_i2
def checked_567_i2 : CheckedCard where
  required := required_567_i2
  envelope := envelope_567_i2
  height := height_567_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_567_i2
def height_567_i1 : ℕ := 8
def childrenH_567_i1 : Fin 3 → ℕ := ![height_16, height_235, height_567_i2]
theorem height_exact_567_i1 : height_567_i1 = 1 + Finset.univ.sup childrenH_567_i1 := by decide +kernel
theorem required_origin_567_i1 : ∀ x ∈ required_567_i1,
    (∃ j, x ∈ childrenC_567_i1 j) ∨ ∀ j, x ∈ childrenD_567_i1 j := by decide +kernel
theorem required_exact_567_i1 : required_567_i1 =
    ((Finset.univ.biUnion childrenC_567_i1) ∪ commonEnvelope childrenD_567_i1).erase (6, 5) := by
  exact required_eq_combination childrenC_567_i1 childrenD_567_i1 (6, 5) required_567_i1
    (by decide +kernel) child_required_sub_567_i1 common_sub_567_i1 required_origin_567_i1
theorem envelope_origin_567_i1 : ∀ x ∈ envelope_567_i1,
    x = (6, 5) ∨ ∃ j, x ∈ childrenD_567_i1 j := by decide +kernel
theorem envelope_exact_567_i1 : envelope_567_i1 =
    insert (6, 5) (Finset.univ.biUnion childrenD_567_i1) := by
  exact envelope_eq_combination childrenD_567_i1 (6, 5) envelope_567_i1
    pivot_mem_567_i1 child_envelope_sub_567_i1 envelope_origin_567_i1
def checked_567_i1 : CheckedCard where
  required := required_567_i1
  envelope := envelope_567_i1
  height := height_567_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_567_i1
def height_567_i0 : ℕ := 10
def childrenH_567_i0 : Fin 7 → ℕ := ![height_67, height_134, height_180, height_327, height_504, height_558, height_567_i1]
theorem height_exact_567_i0 : height_567_i0 = 1 + Finset.univ.sup childrenH_567_i0 := by decide +kernel
theorem required_origin_567_i0 : ∀ x ∈ required_567_i0,
    (∃ j, x ∈ childrenC_567_i0 j) ∨ ∀ j, x ∈ childrenD_567_i0 j := by decide +kernel
theorem required_exact_567_i0 : required_567_i0 =
    ((Finset.univ.biUnion childrenC_567_i0) ∪ commonEnvelope childrenD_567_i0).erase (5, 5) := by
  exact required_eq_combination childrenC_567_i0 childrenD_567_i0 (5, 5) required_567_i0
    (by decide +kernel) child_required_sub_567_i0 common_sub_567_i0 required_origin_567_i0
theorem envelope_origin_567_i0 : ∀ x ∈ envelope_567_i0,
    x = (5, 5) ∨ ∃ j, x ∈ childrenD_567_i0 j := by decide +kernel
theorem envelope_exact_567_i0 : envelope_567_i0 =
    insert (5, 5) (Finset.univ.biUnion childrenD_567_i0) := by
  exact envelope_eq_combination childrenD_567_i0 (5, 5) envelope_567_i0
    pivot_mem_567_i0 child_envelope_sub_567_i0 envelope_origin_567_i0
def checked_567_i0 : CheckedCard where
  required := required_567_i0
  envelope := envelope_567_i0
  height := height_567_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_567_i0
def height_567 : ℕ := 11
def childrenH_567 : Fin 5 → ℕ := ![height_27, height_44, height_560, height_563, height_567_i0]
theorem height_exact_567 : height_567 = 1 + Finset.univ.sup childrenH_567 := by decide +kernel
theorem required_origin_567 : ∀ x ∈ required_567,
    (∃ j, x ∈ childrenC_567 j) ∨ ∀ j, x ∈ childrenD_567 j := by decide +kernel
theorem required_exact_567 : required_567 =
    ((Finset.univ.biUnion childrenC_567) ∪ commonEnvelope childrenD_567).erase (4, 5) := by
  exact required_eq_combination childrenC_567 childrenD_567 (4, 5) required_567
    (by decide +kernel) child_required_sub_567 common_sub_567 required_origin_567
theorem envelope_origin_567 : ∀ x ∈ envelope_567,
    x = (4, 5) ∨ ∃ j, x ∈ childrenD_567 j := by decide +kernel
theorem envelope_exact_567 : envelope_567 =
    insert (4, 5) (Finset.univ.biUnion childrenD_567) := by
  exact envelope_eq_combination childrenD_567 (4, 5) envelope_567
    pivot_mem_567 child_envelope_sub_567 envelope_origin_567
def checked_567 : CheckedCard where
  required := required_567
  envelope := envelope_567
  height := height_567
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_567
def height_579 : ℕ := 11
def childrenH_579 : Fin 9 → ℕ := ![height_118, height_137, height_172, height_173, height_181, height_435, height_507, height_578, height_578]
theorem height_exact_579 : height_579 = 1 + Finset.univ.sup childrenH_579 := by decide +kernel
theorem required_origin_579 : ∀ x ∈ required_579,
    (∃ j, x ∈ childrenC_579 j) ∨ ∀ j, x ∈ childrenD_579 j := by decide +kernel
theorem required_exact_579 : required_579 =
    ((Finset.univ.biUnion childrenC_579) ∪ commonEnvelope childrenD_579).erase (3, 4) := by
  exact required_eq_combination childrenC_579 childrenD_579 (3, 4) required_579
    (by decide +kernel) child_required_sub_579 common_sub_579 required_origin_579
theorem envelope_origin_579 : ∀ x ∈ envelope_579,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_579 j := by decide +kernel
theorem envelope_exact_579 : envelope_579 =
    insert (3, 4) (Finset.univ.biUnion childrenD_579) := by
  exact envelope_eq_combination childrenD_579 (3, 4) envelope_579
    pivot_mem_579 child_envelope_sub_579 envelope_origin_579
def checked_579 : CheckedCard where
  required := required_579
  envelope := envelope_579
  height := height_579
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_579
def height_581 : ℕ := 11
def childrenH_581 : Fin 6 → ℕ := ![height_188, height_188, height_258, height_309, height_578, height_578]
theorem height_exact_581 : height_581 = 1 + Finset.univ.sup childrenH_581 := by decide +kernel
theorem required_origin_581 : ∀ x ∈ required_581,
    (∃ j, x ∈ childrenC_581 j) ∨ ∀ j, x ∈ childrenD_581 j := by decide +kernel
theorem required_exact_581 : required_581 =
    ((Finset.univ.biUnion childrenC_581) ∪ commonEnvelope childrenD_581).erase (4, 6) := by
  exact required_eq_combination childrenC_581 childrenD_581 (4, 6) required_581
    (by decide +kernel) child_required_sub_581 common_sub_581 required_origin_581
theorem envelope_origin_581 : ∀ x ∈ envelope_581,
    x = (4, 6) ∨ ∃ j, x ∈ childrenD_581 j := by decide +kernel
theorem envelope_exact_581 : envelope_581 =
    insert (4, 6) (Finset.univ.biUnion childrenD_581) := by
  exact envelope_eq_combination childrenD_581 (4, 6) envelope_581
    pivot_mem_581 child_envelope_sub_581 envelope_origin_581
def checked_581 : CheckedCard where
  required := required_581
  envelope := envelope_581
  height := height_581
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_581
def height_586 : ℕ := 11
def childrenH_586 : Fin 3 → ℕ := ![height_8, height_179, height_585]
theorem height_exact_586 : height_586 = 1 + Finset.univ.sup childrenH_586 := by decide +kernel
theorem required_origin_586 : ∀ x ∈ required_586,
    (∃ j, x ∈ childrenC_586 j) ∨ ∀ j, x ∈ childrenD_586 j := by decide +kernel
theorem required_exact_586 : required_586 =
    ((Finset.univ.biUnion childrenC_586) ∪ commonEnvelope childrenD_586).erase (4, 2) := by
  exact required_eq_combination childrenC_586 childrenD_586 (4, 2) required_586
    (by decide +kernel) child_required_sub_586 common_sub_586 required_origin_586
theorem envelope_origin_586 : ∀ x ∈ envelope_586,
    x = (4, 2) ∨ ∃ j, x ∈ childrenD_586 j := by decide +kernel
theorem envelope_exact_586 : envelope_586 =
    insert (4, 2) (Finset.univ.biUnion childrenD_586) := by
  exact envelope_eq_combination childrenD_586 (4, 2) envelope_586
    pivot_mem_586 child_envelope_sub_586 envelope_origin_586
def checked_586 : CheckedCard where
  required := required_586
  envelope := envelope_586
  height := height_586
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_586
def height_589 : ℕ := 11
def childrenH_589 : Fin 4 → ℕ := ![height_7, height_8, height_9, height_585]
theorem height_exact_589 : height_589 = 1 + Finset.univ.sup childrenH_589 := by decide +kernel
theorem required_origin_589 : ∀ x ∈ required_589,
    (∃ j, x ∈ childrenC_589 j) ∨ ∀ j, x ∈ childrenD_589 j := by decide +kernel
theorem required_exact_589 : required_589 =
    ((Finset.univ.biUnion childrenC_589) ∪ commonEnvelope childrenD_589).erase (4, 2) := by
  exact required_eq_combination childrenC_589 childrenD_589 (4, 2) required_589
    (by decide +kernel) child_required_sub_589 common_sub_589 required_origin_589
theorem envelope_origin_589 : ∀ x ∈ envelope_589,
    x = (4, 2) ∨ ∃ j, x ∈ childrenD_589 j := by decide +kernel
theorem envelope_exact_589 : envelope_589 =
    insert (4, 2) (Finset.univ.biUnion childrenD_589) := by
  exact envelope_eq_combination childrenD_589 (4, 2) envelope_589
    pivot_mem_589 child_envelope_sub_589 envelope_origin_589
def checked_589 : CheckedCard where
  required := required_589
  envelope := envelope_589
  height := height_589
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_589
end SnakyPrototype.Certificate21

end OAI
