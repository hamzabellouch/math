import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part06
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part06
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height10Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height10Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height11Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height11Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height11Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height11Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height12Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height12Part04
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_591_i0 : Finset Cell := ⟨(([(1, 5), (1, 6), (2, 6), (4, 5), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_591_i0 : Finset Cell := ⟨(([(0, 5), (1, 5), (1, 6), (2, 5), (2, 6), (3, 5), (3, 6), (4, 5), (4, 6), (5, 6), (5, 7), (6, 5), (6, 6), (6, 7), (7, 5), (7, 6), (7, 7), (8, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_591_i0 : Fin 2 → Finset Cell := ![(placed21 6 (4, 6) required_5), (placed21 1 (1, 5) required_265)]
def childrenD_591_i0 : Fin 2 → Finset Cell := ![(placed21 6 (4, 6) envelope_5), (placed21 1 (1, 5) envelope_265)]
theorem common_sub_591_i0 : commonEnvelope childrenD_591_i0 ⊆ insert (3, 6) required_591_i0 := by decide +kernel
theorem child_required_sub_591_i0 : ∀ j, childrenC_591_i0 j ⊆ insert (3, 6) required_591_i0 := by decide +kernel
theorem child_envelope_sub_591_i0 : ∀ j, childrenD_591_i0 j ⊆ envelope_591_i0 := by decide +kernel
theorem pivot_mem_591_i0 : (3, 6) ∈ envelope_591_i0 := by decide +kernel
theorem children_work_591_i0 : ∀ j, Template HasSnaky 5 (childrenC_591_i0 j) (childrenD_591_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 6 (4, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_265 1 (1, 5)).mono (by decide +kernel)
theorem row_works_591_i0 : Template HasSnaky 6 required_591_i0 envelope_591_i0 := by
  refine compose HasSnaky 5 childrenC_591_i0 childrenD_591_i0 children_work_591_i0 (3, 6)
    required_591_i0 envelope_591_i0 pivot_mem_591_i0 child_required_sub_591_i0 child_envelope_sub_591_i0 ?_
  intro b hb
  exact common_sub_591_i0 (mem_commonEnvelope childrenD_591_i0 b hb)
def required_591_i1 : Finset Cell := ⟨(([(1, 5), (1, 6), (2, 6), (4, 5), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_591_i1 : Finset Cell := ⟨(([(0, 5), (1, 3), (1, 5), (1, 6), (2, 3), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 1), (5, 2), (5, 3), (5, 4), (5, 6), (6, 4), (7, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_591_i1 : Fin 5 → Finset Cell := ![(placed21 4 (3, 8) required_12), (placed21 4 (3, 8) required_13), (placed21 4 (3, 8) required_14), (placed21 3 (0, 6) required_289), (placed21 3 (1, 7) required_435)]
def childrenD_591_i1 : Fin 5 → Finset Cell := ![(placed21 4 (3, 8) envelope_12), (placed21 4 (3, 8) envelope_13), (placed21 4 (3, 8) envelope_14), (placed21 3 (0, 6) envelope_289), (placed21 3 (1, 7) envelope_435)]
theorem common_sub_591_i1 : commonEnvelope childrenD_591_i1 ⊆ insert (4, 4) required_591_i1 := by decide +kernel
theorem child_required_sub_591_i1 : ∀ j, childrenC_591_i1 j ⊆ insert (4, 4) required_591_i1 := by decide +kernel
theorem child_envelope_sub_591_i1 : ∀ j, childrenD_591_i1 j ⊆ envelope_591_i1 := by decide +kernel
theorem pivot_mem_591_i1 : (4, 4) ∈ envelope_591_i1 := by decide +kernel
theorem children_work_591_i1 : ∀ j, Template HasSnaky 6 (childrenC_591_i1 j) (childrenD_591_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_12 4 (3, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_13 4 (3, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_14 4 (3, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_289 3 (0, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_435 3 (1, 7)).mono (by decide +kernel)
theorem row_works_591_i1 : Template HasSnaky 7 required_591_i1 envelope_591_i1 := by
  refine compose HasSnaky 6 childrenC_591_i1 childrenD_591_i1 children_work_591_i1 (4, 4)
    required_591_i1 envelope_591_i1 pivot_mem_591_i1 child_required_sub_591_i1 child_envelope_sub_591_i1 ?_
  intro b hb
  exact common_sub_591_i1 (mem_commonEnvelope childrenD_591_i1 b hb)
def required_591_i4 : Finset Cell := ⟨(([(1, 5), (4, 3), (4, 4), (4, 5), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_591_i4 : Finset Cell := ⟨(([(1, 5), (2, 5), (3, 0), (3, 1), (3, 2), (3, 4), (3, 5), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 1), (5, 2), (5, 3), (5, 4), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_591_i4 : Fin 2 → Finset Cell := ![(placed21 4 (3, 6) required_17), (placed21 7 (5, 6) required_80)]
def childrenD_591_i4 : Fin 2 → Finset Cell := ![(placed21 4 (3, 6) envelope_17), (placed21 7 (5, 6) envelope_80)]
theorem common_sub_591_i4 : commonEnvelope childrenD_591_i4 ⊆ insert (3, 5) required_591_i4 := by decide +kernel
theorem child_required_sub_591_i4 : ∀ j, childrenC_591_i4 j ⊆ insert (3, 5) required_591_i4 := by decide +kernel
theorem child_envelope_sub_591_i4 : ∀ j, childrenD_591_i4 j ⊆ envelope_591_i4 := by decide +kernel
theorem pivot_mem_591_i4 : (3, 5) ∈ envelope_591_i4 := by decide +kernel
theorem children_work_591_i4 : ∀ j, Template HasSnaky 4 (childrenC_591_i4 j) (childrenD_591_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_17 4 (3, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_80 7 (5, 6)).mono (by decide +kernel)
theorem row_works_591_i4 : Template HasSnaky 5 required_591_i4 envelope_591_i4 := by
  refine compose HasSnaky 4 childrenC_591_i4 childrenD_591_i4 children_work_591_i4 (3, 5)
    required_591_i4 envelope_591_i4 pivot_mem_591_i4 child_required_sub_591_i4 child_envelope_sub_591_i4 ?_
  intro b hb
  exact common_sub_591_i4 (mem_commonEnvelope childrenD_591_i4 b hb)
def required_591_i3 : Finset Cell := ⟨(([(1, 3), (1, 5), (2, 3), (4, 4), (4, 5), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_591_i3 : Finset Cell := ⟨(([(1, 3), (1, 5), (2, 3), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 1), (5, 2), (5, 3), (5, 4), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_591_i3 : Fin 3 → Finset Cell := ![(placed21 4 (1, 6) required_109), (placed21 7 (5, 6) required_157), required_591_i4]
def childrenD_591_i3 : Fin 3 → Finset Cell := ![(placed21 4 (1, 6) envelope_109), (placed21 7 (5, 6) envelope_157), envelope_591_i4]
theorem common_sub_591_i3 : commonEnvelope childrenD_591_i3 ⊆ insert (4, 3) required_591_i3 := by decide +kernel
theorem child_required_sub_591_i3 : ∀ j, childrenC_591_i3 j ⊆ insert (4, 3) required_591_i3 := by decide +kernel
theorem child_envelope_sub_591_i3 : ∀ j, childrenD_591_i3 j ⊆ envelope_591_i3 := by decide +kernel
theorem pivot_mem_591_i3 : (4, 3) ∈ envelope_591_i3 := by decide +kernel
theorem children_work_591_i3 : ∀ j, Template HasSnaky 5 (childrenC_591_i3 j) (childrenD_591_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_109 4 (1, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_157 7 (5, 6)).mono (by decide +kernel)
  · exact row_works_591_i4.mono (by decide +kernel)
theorem row_works_591_i3 : Template HasSnaky 6 required_591_i3 envelope_591_i3 := by
  refine compose HasSnaky 5 childrenC_591_i3 childrenD_591_i3 children_work_591_i3 (4, 3)
    required_591_i3 envelope_591_i3 pivot_mem_591_i3 child_required_sub_591_i3 child_envelope_sub_591_i3 ?_
  intro b hb
  exact common_sub_591_i3 (mem_commonEnvelope childrenD_591_i3 b hb)
def required_591_i5 : Finset Cell := ⟨(([(1, 3), (2, 3), (4, 4), (4, 5), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_591_i5 : Finset Cell := ⟨(([(1, 3), (2, 3), (3, 0), (3, 1), (3, 2), (3, 3), (3, 7), (3, 8), (3, 9), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 1), (5, 2), (5, 3), (5, 4), (5, 7), (5, 8), (5, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_591_i5 : Fin 3 → Finset Cell := ![(placed21 3 (3, 6) required_8), (placed21 2 (5, 2) required_19), (placed21 4 (1, 6) required_271)]
def childrenD_591_i5 : Fin 3 → Finset Cell := ![(placed21 3 (3, 6) envelope_8), (placed21 2 (5, 2) envelope_19), (placed21 4 (1, 6) envelope_271)]
theorem common_sub_591_i5 : commonEnvelope childrenD_591_i5 ⊆ insert (4, 3) required_591_i5 := by decide +kernel
theorem child_required_sub_591_i5 : ∀ j, childrenC_591_i5 j ⊆ insert (4, 3) required_591_i5 := by decide +kernel
theorem child_envelope_sub_591_i5 : ∀ j, childrenD_591_i5 j ⊆ envelope_591_i5 := by decide +kernel
theorem pivot_mem_591_i5 : (4, 3) ∈ envelope_591_i5 := by decide +kernel
theorem children_work_591_i5 : ∀ j, Template HasSnaky 5 (childrenC_591_i5 j) (childrenD_591_i5 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_8 3 (3, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_19 2 (5, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_271 4 (1, 6)).mono (by decide +kernel)
theorem row_works_591_i5 : Template HasSnaky 6 required_591_i5 envelope_591_i5 := by
  refine compose HasSnaky 5 childrenC_591_i5 childrenD_591_i5 children_work_591_i5 (4, 3)
    required_591_i5 envelope_591_i5 pivot_mem_591_i5 child_required_sub_591_i5 child_envelope_sub_591_i5 ?_
  intro b hb
  exact common_sub_591_i5 (mem_commonEnvelope childrenD_591_i5 b hb)
def required_591_i2 : Finset Cell := ⟨(([(1, 3), (1, 5), (2, 3), (4, 5), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_591_i2 : Finset Cell := ⟨(([(1, 3), (1, 5), (2, 3), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 7), (3, 8), (3, 9), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 1), (5, 2), (5, 3), (5, 4), (5, 6), (5, 7), (5, 8), (5, 9), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_591_i2 : Fin 5 → Finset Cell := ![(placed21 0 (3, 2) required_13), (placed21 0 (1, 2) required_356), required_591_i3, (placed21 1 (2, 3) required_586), required_591_i5]
def childrenD_591_i2 : Fin 5 → Finset Cell := ![(placed21 0 (3, 2) envelope_13), (placed21 0 (1, 2) envelope_356), envelope_591_i3, (placed21 1 (2, 3) envelope_586), envelope_591_i5]
theorem common_sub_591_i2 : commonEnvelope childrenD_591_i2 ⊆ insert (4, 4) required_591_i2 := by decide +kernel
theorem child_required_sub_591_i2 : ∀ j, childrenC_591_i2 j ⊆ insert (4, 4) required_591_i2 := by decide +kernel
theorem child_envelope_sub_591_i2 : ∀ j, childrenD_591_i2 j ⊆ envelope_591_i2 := by decide +kernel
theorem pivot_mem_591_i2 : (4, 4) ∈ envelope_591_i2 := by decide +kernel
theorem children_work_591_i2 : ∀ j, Template HasSnaky 11 (childrenC_591_i2 j) (childrenD_591_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_13 0 (3, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_356 0 (1, 2)).mono (by decide +kernel)
  · exact row_works_591_i3.mono (by decide +kernel)
  · exact (placed21_template row_works_586 1 (2, 3)).mono (by decide +kernel)
  · exact row_works_591_i5.mono (by decide +kernel)
theorem row_works_591_i2 : Template HasSnaky 12 required_591_i2 envelope_591_i2 := by
  refine compose HasSnaky 11 childrenC_591_i2 childrenD_591_i2 children_work_591_i2 (4, 4)
    required_591_i2 envelope_591_i2 pivot_mem_591_i2 child_required_sub_591_i2 child_envelope_sub_591_i2 ?_
  intro b hb
  exact common_sub_591_i2 (mem_commonEnvelope childrenD_591_i2 b hb)
def required_591 : Finset Cell := ⟨(([(1, 3), (1, 5), (1, 6), (2, 3), (2, 6), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_591 : Finset Cell := ⟨(([(0, 5), (1, 3), (1, 5), (1, 6), (1, 8), (2, 3), (2, 5), (2, 6), (2, 8), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 1), (5, 2), (5, 3), (5, 4), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (8, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_591 : Fin 5 → Finset Cell := ![(placed21 1 (0, 5) required_42), (placed21 0 (1, 2) required_430), required_591_i0, required_591_i1, required_591_i2]
def childrenD_591 : Fin 5 → Finset Cell := ![(placed21 1 (0, 5) envelope_42), (placed21 0 (1, 2) envelope_430), envelope_591_i0, envelope_591_i1, envelope_591_i2]
theorem common_sub_591 : commonEnvelope childrenD_591 ⊆ insert (4, 6) required_591 := by decide +kernel
theorem child_required_sub_591 : ∀ j, childrenC_591 j ⊆ insert (4, 6) required_591 := by decide +kernel
theorem child_envelope_sub_591 : ∀ j, childrenD_591 j ⊆ envelope_591 := by decide +kernel
theorem pivot_mem_591 : (4, 6) ∈ envelope_591 := by decide +kernel
theorem children_work_591 : ∀ j, Template HasSnaky 12 (childrenC_591 j) (childrenD_591 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_42 1 (0, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_430 0 (1, 2)).mono (by decide +kernel)
  · exact row_works_591_i0.mono (by decide +kernel)
  · exact row_works_591_i1.mono (by decide +kernel)
  · exact row_works_591_i2.mono (by decide +kernel)
theorem row_works_591 : Template HasSnaky 13 required_591 envelope_591 := by
  refine compose HasSnaky 12 childrenC_591 childrenD_591 children_work_591 (4, 6)
    required_591 envelope_591 pivot_mem_591 child_required_sub_591 child_envelope_sub_591 ?_
  intro b hb
  exact common_sub_591 (mem_commonEnvelope childrenD_591 b hb)
def required_597_i0 : Finset Cell := ⟨(([(2, 5), (3, 5), (5, 3), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_597_i0 : Finset Cell := ⟨(([(2, 5), (3, 5), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 0), (6, 1), (6, 2), (6, 4), (6, 5), (6, 6), (6, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_597_i0 : Fin 3 → Finset Cell := ![(placed21 6 (6, 7) required_13), (placed21 0 (2, 2) required_109), (placed21 0 (2, 2) required_291)]
def childrenD_597_i0 : Fin 3 → Finset Cell := ![(placed21 6 (6, 7) envelope_13), (placed21 0 (2, 2) envelope_109), (placed21 0 (2, 2) envelope_291)]
theorem common_sub_597_i0 : commonEnvelope childrenD_597_i0 ⊆ insert (5, 4) required_597_i0 := by decide +kernel
theorem child_required_sub_597_i0 : ∀ j, childrenC_597_i0 j ⊆ insert (5, 4) required_597_i0 := by decide +kernel
theorem child_envelope_sub_597_i0 : ∀ j, childrenD_597_i0 j ⊆ envelope_597_i0 := by decide +kernel
theorem pivot_mem_597_i0 : (5, 4) ∈ envelope_597_i0 := by decide +kernel
theorem children_work_597_i0 : ∀ j, Template HasSnaky 4 (childrenC_597_i0 j) (childrenD_597_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_13 6 (6, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_109 0 (2, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_291 0 (2, 2)).mono (by decide +kernel)
theorem row_works_597_i0 : Template HasSnaky 5 required_597_i0 envelope_597_i0 := by
  refine compose HasSnaky 4 childrenC_597_i0 childrenD_597_i0 children_work_597_i0 (5, 4)
    required_597_i0 envelope_597_i0 pivot_mem_597_i0 child_required_sub_597_i0 child_envelope_sub_597_i0 ?_
  intro b hb
  exact common_sub_597_i0 (mem_commonEnvelope childrenD_597_i0 b hb)
def required_597_i3 : Finset Cell := ⟨(([(2, 2), (2, 3), (3, 2), (5, 2), (5, 3), (5, 4), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_597_i3 : Finset Cell := ⟨(([(1, 3), (2, 2), (2, 3), (3, 2), (4, 1), (4, 2), (5, 2), (5, 3), (5, 4), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_597_i3 : Fin 2 → Finset Cell := ![(placed21 7 (5, 5) required_5), (placed21 2 (5, 2) required_5)]
def childrenD_597_i3 : Fin 2 → Finset Cell := ![(placed21 7 (5, 5) envelope_5), (placed21 2 (5, 2) envelope_5)]
theorem common_sub_597_i3 : commonEnvelope childrenD_597_i3 ⊆ insert (4, 2) required_597_i3 := by decide +kernel
theorem child_required_sub_597_i3 : ∀ j, childrenC_597_i3 j ⊆ insert (4, 2) required_597_i3 := by decide +kernel
theorem child_envelope_sub_597_i3 : ∀ j, childrenD_597_i3 j ⊆ envelope_597_i3 := by decide +kernel
theorem pivot_mem_597_i3 : (4, 2) ∈ envelope_597_i3 := by decide +kernel
theorem children_work_597_i3 : ∀ j, Template HasSnaky 1 (childrenC_597_i3 j) (childrenD_597_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 7 (5, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_5 2 (5, 2)).mono (by decide +kernel)
theorem row_works_597_i3 : Template HasSnaky 2 required_597_i3 envelope_597_i3 := by
  refine compose HasSnaky 1 childrenC_597_i3 childrenD_597_i3 children_work_597_i3 (4, 2)
    required_597_i3 envelope_597_i3 pivot_mem_597_i3 child_required_sub_597_i3 child_envelope_sub_597_i3 ?_
  intro b hb
  exact common_sub_597_i3 (mem_commonEnvelope childrenD_597_i3 b hb)
def required_597_i2 : Finset Cell := ⟨(([(2, 2), (2, 3), (3, 2), (5, 3), (5, 4), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_597_i2 : Finset Cell := ⟨(([(1, 3), (2, 2), (2, 3), (3, 2), (4, 1), (4, 2), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (6, 0), (6, 1), (6, 2), (6, 4), (6, 5), (6, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_597_i2 : Fin 2 → Finset Cell := ![(placed21 4 (5, 6) required_7), required_597_i3]
def childrenD_597_i2 : Fin 2 → Finset Cell := ![(placed21 4 (5, 6) envelope_7), envelope_597_i3]
theorem common_sub_597_i2 : commonEnvelope childrenD_597_i2 ⊆ insert (5, 2) required_597_i2 := by decide +kernel
theorem child_required_sub_597_i2 : ∀ j, childrenC_597_i2 j ⊆ insert (5, 2) required_597_i2 := by decide +kernel
theorem child_envelope_sub_597_i2 : ∀ j, childrenD_597_i2 j ⊆ envelope_597_i2 := by decide +kernel
theorem pivot_mem_597_i2 : (5, 2) ∈ envelope_597_i2 := by decide +kernel
theorem children_work_597_i2 : ∀ j, Template HasSnaky 3 (childrenC_597_i2 j) (childrenD_597_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 4 (5, 6)).mono (by decide +kernel)
  · exact row_works_597_i3.mono (by decide +kernel)
theorem row_works_597_i2 : Template HasSnaky 4 required_597_i2 envelope_597_i2 := by
  refine compose HasSnaky 3 childrenC_597_i2 childrenD_597_i2 children_work_597_i2 (5, 2)
    required_597_i2 envelope_597_i2 pivot_mem_597_i2 child_required_sub_597_i2 child_envelope_sub_597_i2 ?_
  intro b hb
  exact common_sub_597_i2 (mem_commonEnvelope childrenD_597_i2 b hb)
def required_597_i6 : Finset Cell := ⟨(([(2, 2), (3, 2), (4, 2), (5, 2), (5, 3), (5, 4), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_597_i6 : Finset Cell := ⟨(([(2, 2), (3, 2), (4, 2), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (6, 1), (6, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_597_i6 : Fin 2 → Finset Cell := ![(placed21 4 (2, 2) required_4), (placed21 3 (5, 5) required_4)]
def childrenD_597_i6 : Fin 2 → Finset Cell := ![(placed21 4 (2, 2) envelope_4), (placed21 3 (5, 5) envelope_4)]
theorem common_sub_597_i6 : commonEnvelope childrenD_597_i6 ⊆ insert (6, 1) required_597_i6 := by decide +kernel
theorem child_required_sub_597_i6 : ∀ j, childrenC_597_i6 j ⊆ insert (6, 1) required_597_i6 := by decide +kernel
theorem child_envelope_sub_597_i6 : ∀ j, childrenD_597_i6 j ⊆ envelope_597_i6 := by decide +kernel
theorem pivot_mem_597_i6 : (6, 1) ∈ envelope_597_i6 := by decide +kernel
theorem children_work_597_i6 : ∀ j, Template HasSnaky 1 (childrenC_597_i6 j) (childrenD_597_i6 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_4 4 (2, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_4 3 (5, 5)).mono (by decide +kernel)
theorem row_works_597_i6 : Template HasSnaky 2 required_597_i6 envelope_597_i6 := by
  refine compose HasSnaky 1 childrenC_597_i6 childrenD_597_i6 children_work_597_i6 (6, 1)
    required_597_i6 envelope_597_i6 pivot_mem_597_i6 child_required_sub_597_i6 child_envelope_sub_597_i6 ?_
  intro b hb
  exact common_sub_597_i6 (mem_commonEnvelope childrenD_597_i6 b hb)
def required_597_i5 : Finset Cell := ⟨(([(2, 2), (2, 3), (3, 2), (4, 2), (5, 3), (5, 4), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_597_i5 : Finset Cell := ⟨(([(1, 3), (2, 2), (2, 3), (3, 2), (4, 2), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (6, 1), (6, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_597_i5 : Fin 2 → Finset Cell := ![(placed21 2 (5, 2) required_5), required_597_i6]
def childrenD_597_i5 : Fin 2 → Finset Cell := ![(placed21 2 (5, 2) envelope_5), envelope_597_i6]
theorem common_sub_597_i5 : commonEnvelope childrenD_597_i5 ⊆ insert (5, 2) required_597_i5 := by decide +kernel
theorem child_required_sub_597_i5 : ∀ j, childrenC_597_i5 j ⊆ insert (5, 2) required_597_i5 := by decide +kernel
theorem child_envelope_sub_597_i5 : ∀ j, childrenD_597_i5 j ⊆ envelope_597_i5 := by decide +kernel
theorem pivot_mem_597_i5 : (5, 2) ∈ envelope_597_i5 := by decide +kernel
theorem children_work_597_i5 : ∀ j, Template HasSnaky 2 (childrenC_597_i5 j) (childrenD_597_i5 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 2 (5, 2)).mono (by decide +kernel)
  · exact row_works_597_i6.mono (by decide +kernel)
theorem row_works_597_i5 : Template HasSnaky 3 required_597_i5 envelope_597_i5 := by
  refine compose HasSnaky 2 childrenC_597_i5 childrenD_597_i5 children_work_597_i5 (5, 2)
    required_597_i5 envelope_597_i5 pivot_mem_597_i5 child_required_sub_597_i5 child_envelope_sub_597_i5 ?_
  intro b hb
  exact common_sub_597_i5 (mem_commonEnvelope childrenD_597_i5 b hb)
def required_597_i4 : Finset Cell := ⟨(([(2, 2), (2, 3), (3, 2), (5, 3), (5, 4), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_597_i4 : Finset Cell := ⟨(([(1, 3), (2, 2), (2, 3), (3, 2), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (6, 1), (6, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_597_i4 : Fin 2 → Finset Cell := ![(placed21 6 (5, 6) required_140), required_597_i5]
def childrenD_597_i4 : Fin 2 → Finset Cell := ![(placed21 6 (5, 6) envelope_140), envelope_597_i5]
theorem common_sub_597_i4 : commonEnvelope childrenD_597_i4 ⊆ insert (4, 2) required_597_i4 := by decide +kernel
theorem child_required_sub_597_i4 : ∀ j, childrenC_597_i4 j ⊆ insert (4, 2) required_597_i4 := by decide +kernel
theorem child_envelope_sub_597_i4 : ∀ j, childrenD_597_i4 j ⊆ envelope_597_i4 := by decide +kernel
theorem pivot_mem_597_i4 : (4, 2) ∈ envelope_597_i4 := by decide +kernel
theorem children_work_597_i4 : ∀ j, Template HasSnaky 3 (childrenC_597_i4 j) (childrenD_597_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_140 6 (5, 6)).mono (by decide +kernel)
  · exact row_works_597_i5.mono (by decide +kernel)
theorem row_works_597_i4 : Template HasSnaky 4 required_597_i4 envelope_597_i4 := by
  refine compose HasSnaky 3 childrenC_597_i4 childrenD_597_i4 children_work_597_i4 (4, 2)
    required_597_i4 envelope_597_i4 pivot_mem_597_i4 child_required_sub_597_i4 child_envelope_sub_597_i4 ?_
  intro b hb
  exact common_sub_597_i4 (mem_commonEnvelope childrenD_597_i4 b hb)
def required_597_i1 : Finset Cell := ⟨(([(2, 2), (2, 3), (2, 5), (3, 2), (3, 5), (5, 3), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_597_i1 : Finset Cell := ⟨(([(1, 3), (1, 6), (1, 7), (1, 8), (1, 9), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, 2), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 6), (4, 7), (4, 8), (4, 9), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 0), (6, 1), (6, 2), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, 7), (8, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_597_i1 : Fin 3 → Finset Cell := ![required_597_i2, required_597_i4, (placed21 1 (1, 2) required_596)]
def childrenD_597_i1 : Fin 3 → Finset Cell := ![envelope_597_i2, envelope_597_i4, (placed21 1 (1, 2) envelope_596)]
theorem common_sub_597_i1 : commonEnvelope childrenD_597_i1 ⊆ insert (5, 4) required_597_i1 := by decide +kernel
theorem child_required_sub_597_i1 : ∀ j, childrenC_597_i1 j ⊆ insert (5, 4) required_597_i1 := by decide +kernel
theorem child_envelope_sub_597_i1 : ∀ j, childrenD_597_i1 j ⊆ envelope_597_i1 := by decide +kernel
theorem pivot_mem_597_i1 : (5, 4) ∈ envelope_597_i1 := by decide +kernel
theorem children_work_597_i1 : ∀ j, Template HasSnaky 11 (childrenC_597_i1 j) (childrenD_597_i1 j) := by
  intro j
  fin_cases j
  · exact row_works_597_i2.mono (by decide +kernel)
  · exact row_works_597_i4.mono (by decide +kernel)
  · exact (placed21_template row_works_596 1 (1, 2)).mono (by decide +kernel)
theorem row_works_597_i1 : Template HasSnaky 12 required_597_i1 envelope_597_i1 := by
  refine compose HasSnaky 11 childrenC_597_i1 childrenD_597_i1 children_work_597_i1 (5, 4)
    required_597_i1 envelope_597_i1 pivot_mem_597_i1 child_required_sub_597_i1 child_envelope_sub_597_i1 ?_
  intro b hb
  exact common_sub_597_i1 (mem_commonEnvelope childrenD_597_i1 b hb)
def required_597 : Finset Cell := ⟨(([(2, 2), (2, 3), (2, 5), (3, 2), (3, 5), (5, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_597 : Finset Cell := ⟨(([(0, 7), (1, 3), (1, 4), (1, 6), (1, 7), (1, 8), (1, 9), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, 2), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 0), (6, 1), (6, 2), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, 4), (7, 6), (7, 7), (8, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_597 : Fin 5 → Finset Cell := ![(placed21 1 (1, 2) required_272), (placed21 3 (1, 6) required_290), (placed21 1 (0, 2) required_593), required_597_i0, required_597_i1]
def childrenD_597 : Fin 5 → Finset Cell := ![(placed21 1 (1, 2) envelope_272), (placed21 3 (1, 6) envelope_290), (placed21 1 (0, 2) envelope_593), envelope_597_i0, envelope_597_i1]
theorem common_sub_597 : commonEnvelope childrenD_597 ⊆ insert (5, 5) required_597 := by decide +kernel
theorem child_required_sub_597 : ∀ j, childrenC_597 j ⊆ insert (5, 5) required_597 := by decide +kernel
theorem child_envelope_sub_597 : ∀ j, childrenD_597 j ⊆ envelope_597 := by decide +kernel
theorem pivot_mem_597 : (5, 5) ∈ envelope_597 := by decide +kernel
theorem children_work_597 : ∀ j, Template HasSnaky 12 (childrenC_597 j) (childrenD_597 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_272 1 (1, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_290 3 (1, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_593 1 (0, 2)).mono (by decide +kernel)
  · exact row_works_597_i0.mono (by decide +kernel)
  · exact row_works_597_i1.mono (by decide +kernel)
theorem row_works_597 : Template HasSnaky 13 required_597 envelope_597 := by
  refine compose HasSnaky 12 childrenC_597 childrenD_597 children_work_597 (5, 5)
    required_597 envelope_597 pivot_mem_597 child_required_sub_597 child_envelope_sub_597 ?_
  intro b hb
  exact common_sub_597 (mem_commonEnvelope childrenD_597 b hb)
def required_603_i0 : Finset Cell := ⟨(([(1, 3), (1, 4), (1, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_603_i0 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 5), (0, 6), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 4), (5, 5), (5, 6), (6, 4), (6, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_603_i0 : Fin 4 → Finset Cell := ![(placed21 4 (1, 6) required_7), (placed21 3 (0, 5) required_8), (placed21 6 (2, 6) required_9), (placed21 4 (0, 6) required_427)]
def childrenD_603_i0 : Fin 4 → Finset Cell := ![(placed21 4 (1, 6) envelope_7), (placed21 3 (0, 5) envelope_8), (placed21 6 (2, 6) envelope_9), (placed21 4 (0, 6) envelope_427)]
theorem common_sub_603_i0 : commonEnvelope childrenD_603_i0 ⊆ insert (1, 2) required_603_i0 := by decide +kernel
theorem child_required_sub_603_i0 : ∀ j, childrenC_603_i0 j ⊆ insert (1, 2) required_603_i0 := by decide +kernel
theorem child_envelope_sub_603_i0 : ∀ j, childrenD_603_i0 j ⊆ envelope_603_i0 := by decide +kernel
theorem pivot_mem_603_i0 : (1, 2) ∈ envelope_603_i0 := by decide +kernel
theorem children_work_603_i0 : ∀ j, Template HasSnaky 11 (childrenC_603_i0 j) (childrenD_603_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 4 (1, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_8 3 (0, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_9 6 (2, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_427 4 (0, 6)).mono (by decide +kernel)
theorem row_works_603_i0 : Template HasSnaky 12 required_603_i0 envelope_603_i0 := by
  refine compose HasSnaky 11 childrenC_603_i0 childrenD_603_i0 children_work_603_i0 (1, 2)
    required_603_i0 envelope_603_i0 pivot_mem_603_i0 child_required_sub_603_i0 child_envelope_sub_603_i0 ?_
  intro b hb
  exact common_sub_603_i0 (mem_commonEnvelope childrenD_603_i0 b hb)
def required_603 : Finset Cell := ⟨(([(1, 3), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_603 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 5), (0, 6), (0, 7), (0, 8), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 4), (5, 5), (5, 6), (5, 7), (6, 4), (6, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_603 : Fin 7 → Finset Cell := ![(placed21 2 (2, 1) required_13), (placed21 6 (2, 7) required_14), (placed21 4 (0, 7) required_31), (placed21 2 (2, 1) required_189), (placed21 4 (0, 7) required_367), (placed21 0 (0, 2) required_457), required_603_i0]
def childrenD_603 : Fin 7 → Finset Cell := ![(placed21 2 (2, 1) envelope_13), (placed21 6 (2, 7) envelope_14), (placed21 4 (0, 7) envelope_31), (placed21 2 (2, 1) envelope_189), (placed21 4 (0, 7) envelope_367), (placed21 0 (0, 2) envelope_457), envelope_603_i0]
theorem common_sub_603 : commonEnvelope childrenD_603 ⊆ insert (1, 5) required_603 := by decide +kernel
theorem child_required_sub_603 : ∀ j, childrenC_603 j ⊆ insert (1, 5) required_603 := by decide +kernel
theorem child_envelope_sub_603 : ∀ j, childrenD_603 j ⊆ envelope_603 := by decide +kernel
theorem pivot_mem_603 : (1, 5) ∈ envelope_603 := by decide +kernel
theorem children_work_603 : ∀ j, Template HasSnaky 12 (childrenC_603 j) (childrenD_603 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_13 2 (2, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_14 6 (2, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_31 4 (0, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_189 2 (2, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_367 4 (0, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_457 0 (0, 2)).mono (by decide +kernel)
  · exact row_works_603_i0.mono (by decide +kernel)
theorem row_works_603 : Template HasSnaky 13 required_603 envelope_603 := by
  refine compose HasSnaky 12 childrenC_603 childrenD_603 children_work_603 (1, 5)
    required_603 envelope_603 pivot_mem_603 child_required_sub_603 child_envelope_sub_603 ?_
  intro b hb
  exact common_sub_603 (mem_commonEnvelope childrenD_603 b hb)
def required_634 : Finset Cell := ⟨(([(3, 4), (3, 5), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_634 : Finset Cell := ⟨(([(0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 4), (3, 5), (3, 6), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 0), (6, 1), (6, 2), (6, 3), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_634 : Fin 5 → Finset Cell := ![(placed21 0 (0, 1) required_438), (placed21 0 (0, 1) required_452), (placed21 4 (3, 8) required_587), (placed21 7 (6, 5) required_612), required_633]
def childrenD_634 : Fin 5 → Finset Cell := ![(placed21 0 (0, 1) envelope_438), (placed21 0 (0, 1) envelope_452), (placed21 4 (3, 8) envelope_587), (placed21 7 (6, 5) envelope_612), envelope_633]
theorem common_sub_634 : commonEnvelope childrenD_634 ⊆ insert (5, 5) required_634 := by decide +kernel
theorem child_required_sub_634 : ∀ j, childrenC_634 j ⊆ insert (5, 5) required_634 := by decide +kernel
theorem child_envelope_sub_634 : ∀ j, childrenD_634 j ⊆ envelope_634 := by decide +kernel
theorem pivot_mem_634 : (5, 5) ∈ envelope_634 := by decide +kernel
theorem children_work_634 : ∀ j, Template HasSnaky 12 (childrenC_634 j) (childrenD_634 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_438 0 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_452 0 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_587 4 (3, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_612 7 (6, 5)).mono (by decide +kernel)
  · exact row_works_633.mono (by decide +kernel)
theorem row_works_634 : Template HasSnaky 13 required_634 envelope_634 := by
  refine compose HasSnaky 12 childrenC_634 childrenD_634 children_work_634 (5, 5)
    required_634 envelope_634 pivot_mem_634 child_required_sub_634 child_envelope_sub_634 ?_
  intro b hb
  exact common_sub_634 (mem_commonEnvelope childrenD_634 b hb)
def required_642 : Finset Cell := ⟨(([(1, 4), (1, 5), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_642 : Finset Cell := ⟨(([(0, 5), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_642 : Fin 7 → Finset Cell := ![(placed21 0 (0, 1) required_299), (placed21 0 (0, 1) required_349), (placed21 0 (0, 1) required_476), (placed21 0 (1, 1) required_587), (placed21 4 (1, 8) required_587), (placed21 3 (0, 5) required_612), (placed21 0 (0, 2) required_641)]
def childrenD_642 : Fin 7 → Finset Cell := ![(placed21 0 (0, 1) envelope_299), (placed21 0 (0, 1) envelope_349), (placed21 0 (0, 1) envelope_476), (placed21 0 (1, 1) envelope_587), (placed21 4 (1, 8) envelope_587), (placed21 3 (0, 5) envelope_612), (placed21 0 (0, 2) envelope_641)]
theorem common_sub_642 : commonEnvelope childrenD_642 ⊆ insert (3, 5) required_642 := by decide +kernel
theorem child_required_sub_642 : ∀ j, childrenC_642 j ⊆ insert (3, 5) required_642 := by decide +kernel
theorem child_envelope_sub_642 : ∀ j, childrenD_642 j ⊆ envelope_642 := by decide +kernel
theorem pivot_mem_642 : (3, 5) ∈ envelope_642 := by decide +kernel
theorem children_work_642 : ∀ j, Template HasSnaky 12 (childrenC_642 j) (childrenD_642 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_299 0 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_349 0 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_476 0 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_587 0 (1, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_587 4 (1, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_612 3 (0, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_641 0 (0, 2)).mono (by decide +kernel)
theorem row_works_642 : Template HasSnaky 13 required_642 envelope_642 := by
  refine compose HasSnaky 12 childrenC_642 childrenD_642 children_work_642 (3, 5)
    required_642 envelope_642 pivot_mem_642 child_required_sub_642 child_envelope_sub_642 ?_
  intro b hb
  exact common_sub_642 (mem_commonEnvelope childrenD_642 b hb)
def required_643 : Finset Cell := ⟨(([(1, 4), (1, 5), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_643 : Finset Cell := ⟨(([(0, 4), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_643 : Fin 7 → Finset Cell := ![(placed21 4 (0, 8) required_299), (placed21 4 (0, 8) required_349), (placed21 4 (0, 8) required_476), (placed21 0 (1, 1) required_587), (placed21 4 (1, 8) required_587), (placed21 1 (0, 4) required_612), (placed21 4 (0, 7) required_641)]
def childrenD_643 : Fin 7 → Finset Cell := ![(placed21 4 (0, 8) envelope_299), (placed21 4 (0, 8) envelope_349), (placed21 4 (0, 8) envelope_476), (placed21 0 (1, 1) envelope_587), (placed21 4 (1, 8) envelope_587), (placed21 1 (0, 4) envelope_612), (placed21 4 (0, 7) envelope_641)]
theorem common_sub_643 : commonEnvelope childrenD_643 ⊆ insert (3, 5) required_643 := by decide +kernel
theorem child_required_sub_643 : ∀ j, childrenC_643 j ⊆ insert (3, 5) required_643 := by decide +kernel
theorem child_envelope_sub_643 : ∀ j, childrenD_643 j ⊆ envelope_643 := by decide +kernel
theorem pivot_mem_643 : (3, 5) ∈ envelope_643 := by decide +kernel
theorem children_work_643 : ∀ j, Template HasSnaky 12 (childrenC_643 j) (childrenD_643 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_299 4 (0, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_349 4 (0, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_476 4 (0, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_587 0 (1, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_587 4 (1, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_612 1 (0, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_641 4 (0, 7)).mono (by decide +kernel)
theorem row_works_643 : Template HasSnaky 13 required_643 envelope_643 := by
  refine compose HasSnaky 12 childrenC_643 childrenD_643 children_work_643 (3, 5)
    required_643 envelope_643 pivot_mem_643 child_required_sub_643 child_envelope_sub_643 ?_
  intro b hb
  exact common_sub_643 (mem_commonEnvelope childrenD_643 b hb)
def required_647_i1 : Finset Cell := ⟨(([(4, 4), (4, 5), (5, 4), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_647_i1 : Finset Cell := ⟨(([(1, 4), (1, 5), (1, 6), (2, 4), (2, 5), (2, 6), (3, 4), (3, 5), (3, 6), (3, 7), (4, 2), (4, 3), (4, 4), (4, 5), (5, 4), (5, 5), (6, 5), (6, 6), (7, 5), (7, 6), (8, 5), (8, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_647_i1 : Fin 3 → Finset Cell := ![(placed21 7 (7, 5) required_15), (placed21 5 (8, 4) required_65), (placed21 6 (6, 7) required_282)]
def childrenD_647_i1 : Fin 3 → Finset Cell := ![(placed21 7 (7, 5) envelope_15), (placed21 5 (8, 4) envelope_65), (placed21 6 (6, 7) envelope_282)]
theorem common_sub_647_i1 : commonEnvelope childrenD_647_i1 ⊆ insert (6, 5) required_647_i1 := by decide +kernel
theorem child_required_sub_647_i1 : ∀ j, childrenC_647_i1 j ⊆ insert (6, 5) required_647_i1 := by decide +kernel
theorem child_envelope_sub_647_i1 : ∀ j, childrenD_647_i1 j ⊆ envelope_647_i1 := by decide +kernel
theorem pivot_mem_647_i1 : (6, 5) ∈ envelope_647_i1 := by decide +kernel
theorem children_work_647_i1 : ∀ j, Template HasSnaky 5 (childrenC_647_i1 j) (childrenD_647_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_15 7 (7, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_65 5 (8, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_282 6 (6, 7)).mono (by decide +kernel)
theorem row_works_647_i1 : Template HasSnaky 6 required_647_i1 envelope_647_i1 := by
  refine compose HasSnaky 5 childrenC_647_i1 childrenD_647_i1 children_work_647_i1 (6, 5)
    required_647_i1 envelope_647_i1 pivot_mem_647_i1 child_required_sub_647_i1 child_envelope_sub_647_i1 ?_
  intro b hb
  exact common_sub_647_i1 (mem_commonEnvelope childrenD_647_i1 b hb)
def required_647_i0 : Finset Cell := ⟨(([(4, 4), (4, 5), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_647_i0 : Finset Cell := ⟨(([(1, 2), (1, 4), (1, 5), (1, 6), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 1), (6, 2), (6, 3), (6, 5), (6, 6), (6, 7), (6, 8), (7, 2), (7, 3), (7, 5), (7, 6), (8, 3), (8, 5), (8, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_647_i0 : Fin 4 → Finset Cell := ![(placed21 5 (8, 2) required_600), (placed21 4 (2, 8) required_600), (placed21 1 (1, 1) required_621), required_647_i1]
def childrenD_647_i0 : Fin 4 → Finset Cell := ![(placed21 5 (8, 2) envelope_600), (placed21 4 (2, 8) envelope_600), (placed21 1 (1, 1) envelope_621), envelope_647_i1]
theorem common_sub_647_i0 : commonEnvelope childrenD_647_i0 ⊆ insert (5, 5) required_647_i0 := by decide +kernel
theorem child_required_sub_647_i0 : ∀ j, childrenC_647_i0 j ⊆ insert (5, 5) required_647_i0 := by decide +kernel
theorem child_envelope_sub_647_i0 : ∀ j, childrenD_647_i0 j ⊆ envelope_647_i0 := by decide +kernel
theorem pivot_mem_647_i0 : (5, 5) ∈ envelope_647_i0 := by decide +kernel
theorem children_work_647_i0 : ∀ j, Template HasSnaky 7 (childrenC_647_i0 j) (childrenD_647_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_600 5 (8, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_600 4 (2, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_621 1 (1, 1)).mono (by decide +kernel)
  · exact row_works_647_i1.mono (by decide +kernel)
theorem row_works_647_i0 : Template HasSnaky 8 required_647_i0 envelope_647_i0 := by
  refine compose HasSnaky 7 childrenC_647_i0 childrenD_647_i0 children_work_647_i0 (5, 5)
    required_647_i0 envelope_647_i0 pivot_mem_647_i0 child_required_sub_647_i0 child_envelope_sub_647_i0 ?_
  intro b hb
  exact common_sub_647_i0 (mem_commonEnvelope childrenD_647_i0 b hb)
def required_647 : Finset Cell := ⟨(([(4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_647 : Finset Cell := ⟨(([(0, 2), (0, 3), (0, 5), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (9, 3), (9, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_647 : Fin 9 → Finset Cell := ![(placed21 7 (8, 6) required_399), (placed21 3 (1, 5) required_408), (placed21 3 (1, 5) required_410), (placed21 5 (9, 1) required_480), (placed21 1 (0, 3) required_546), (placed21 3 (1, 6) required_587), (placed21 7 (9, 6) required_635), (placed21 1 (1, 1) required_646), required_647_i0]
def childrenD_647 : Fin 9 → Finset Cell := ![(placed21 7 (8, 6) envelope_399), (placed21 3 (1, 5) envelope_408), (placed21 3 (1, 5) envelope_410), (placed21 5 (9, 1) envelope_480), (placed21 1 (0, 3) envelope_546), (placed21 3 (1, 6) envelope_587), (placed21 7 (9, 6) envelope_635), (placed21 1 (1, 1) envelope_646), envelope_647_i0]
theorem common_sub_647 : commonEnvelope childrenD_647 ⊆ insert (5, 4) required_647 := by decide +kernel
theorem child_required_sub_647 : ∀ j, childrenC_647 j ⊆ insert (5, 4) required_647 := by decide +kernel
theorem child_envelope_sub_647 : ∀ j, childrenD_647 j ⊆ envelope_647 := by decide +kernel
theorem pivot_mem_647 : (5, 4) ∈ envelope_647 := by decide +kernel
theorem children_work_647 : ∀ j, Template HasSnaky 12 (childrenC_647 j) (childrenD_647 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_399 7 (8, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_408 3 (1, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_410 3 (1, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_480 5 (9, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_546 1 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_587 3 (1, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_635 7 (9, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_646 1 (1, 1)).mono (by decide +kernel)
  · exact row_works_647_i0.mono (by decide +kernel)
theorem row_works_647 : Template HasSnaky 13 required_647 envelope_647 := by
  refine compose HasSnaky 12 childrenC_647 childrenD_647 children_work_647 (5, 4)
    required_647 envelope_647 pivot_mem_647 child_required_sub_647 child_envelope_sub_647 ?_
  intro b hb
  exact common_sub_647 (mem_commonEnvelope childrenD_647 b hb)
def height_591_i0 : ℕ := 6
def childrenH_591_i0 : Fin 2 → ℕ := ![height_5, height_265]
theorem height_exact_591_i0 : height_591_i0 = 1 + Finset.univ.sup childrenH_591_i0 := by decide +kernel
theorem required_origin_591_i0 : ∀ x ∈ required_591_i0,
    (∃ j, x ∈ childrenC_591_i0 j) ∨ ∀ j, x ∈ childrenD_591_i0 j := by decide +kernel
theorem required_exact_591_i0 : required_591_i0 =
    ((Finset.univ.biUnion childrenC_591_i0) ∪ commonEnvelope childrenD_591_i0).erase (3, 6) := by
  exact required_eq_combination childrenC_591_i0 childrenD_591_i0 (3, 6) required_591_i0
    (by decide +kernel) child_required_sub_591_i0 common_sub_591_i0 required_origin_591_i0
theorem envelope_origin_591_i0 : ∀ x ∈ envelope_591_i0,
    x = (3, 6) ∨ ∃ j, x ∈ childrenD_591_i0 j := by decide +kernel
theorem envelope_exact_591_i0 : envelope_591_i0 =
    insert (3, 6) (Finset.univ.biUnion childrenD_591_i0) := by
  exact envelope_eq_combination childrenD_591_i0 (3, 6) envelope_591_i0
    pivot_mem_591_i0 child_envelope_sub_591_i0 envelope_origin_591_i0
def checked_591_i0 : CheckedCard where
  required := required_591_i0
  envelope := envelope_591_i0
  height := height_591_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_591_i0
def height_591_i1 : ℕ := 7
def childrenH_591_i1 : Fin 5 → ℕ := ![height_12, height_13, height_14, height_289, height_435]
theorem height_exact_591_i1 : height_591_i1 = 1 + Finset.univ.sup childrenH_591_i1 := by decide +kernel
theorem required_origin_591_i1 : ∀ x ∈ required_591_i1,
    (∃ j, x ∈ childrenC_591_i1 j) ∨ ∀ j, x ∈ childrenD_591_i1 j := by decide +kernel
theorem required_exact_591_i1 : required_591_i1 =
    ((Finset.univ.biUnion childrenC_591_i1) ∪ commonEnvelope childrenD_591_i1).erase (4, 4) := by
  exact required_eq_combination childrenC_591_i1 childrenD_591_i1 (4, 4) required_591_i1
    (by decide +kernel) child_required_sub_591_i1 common_sub_591_i1 required_origin_591_i1
theorem envelope_origin_591_i1 : ∀ x ∈ envelope_591_i1,
    x = (4, 4) ∨ ∃ j, x ∈ childrenD_591_i1 j := by decide +kernel
theorem envelope_exact_591_i1 : envelope_591_i1 =
    insert (4, 4) (Finset.univ.biUnion childrenD_591_i1) := by
  exact envelope_eq_combination childrenD_591_i1 (4, 4) envelope_591_i1
    pivot_mem_591_i1 child_envelope_sub_591_i1 envelope_origin_591_i1
def checked_591_i1 : CheckedCard where
  required := required_591_i1
  envelope := envelope_591_i1
  height := height_591_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_591_i1
def height_591_i4 : ℕ := 5
def childrenH_591_i4 : Fin 2 → ℕ := ![height_17, height_80]
theorem height_exact_591_i4 : height_591_i4 = 1 + Finset.univ.sup childrenH_591_i4 := by decide +kernel
theorem required_origin_591_i4 : ∀ x ∈ required_591_i4,
    (∃ j, x ∈ childrenC_591_i4 j) ∨ ∀ j, x ∈ childrenD_591_i4 j := by decide +kernel
theorem required_exact_591_i4 : required_591_i4 =
    ((Finset.univ.biUnion childrenC_591_i4) ∪ commonEnvelope childrenD_591_i4).erase (3, 5) := by
  exact required_eq_combination childrenC_591_i4 childrenD_591_i4 (3, 5) required_591_i4
    (by decide +kernel) child_required_sub_591_i4 common_sub_591_i4 required_origin_591_i4
theorem envelope_origin_591_i4 : ∀ x ∈ envelope_591_i4,
    x = (3, 5) ∨ ∃ j, x ∈ childrenD_591_i4 j := by decide +kernel
theorem envelope_exact_591_i4 : envelope_591_i4 =
    insert (3, 5) (Finset.univ.biUnion childrenD_591_i4) := by
  exact envelope_eq_combination childrenD_591_i4 (3, 5) envelope_591_i4
    pivot_mem_591_i4 child_envelope_sub_591_i4 envelope_origin_591_i4
def checked_591_i4 : CheckedCard where
  required := required_591_i4
  envelope := envelope_591_i4
  height := height_591_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_591_i4
def height_591_i3 : ℕ := 6
def childrenH_591_i3 : Fin 3 → ℕ := ![height_109, height_157, height_591_i4]
theorem height_exact_591_i3 : height_591_i3 = 1 + Finset.univ.sup childrenH_591_i3 := by decide +kernel
theorem required_origin_591_i3 : ∀ x ∈ required_591_i3,
    (∃ j, x ∈ childrenC_591_i3 j) ∨ ∀ j, x ∈ childrenD_591_i3 j := by decide +kernel
theorem required_exact_591_i3 : required_591_i3 =
    ((Finset.univ.biUnion childrenC_591_i3) ∪ commonEnvelope childrenD_591_i3).erase (4, 3) := by
  exact required_eq_combination childrenC_591_i3 childrenD_591_i3 (4, 3) required_591_i3
    (by decide +kernel) child_required_sub_591_i3 common_sub_591_i3 required_origin_591_i3
theorem envelope_origin_591_i3 : ∀ x ∈ envelope_591_i3,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_591_i3 j := by decide +kernel
theorem envelope_exact_591_i3 : envelope_591_i3 =
    insert (4, 3) (Finset.univ.biUnion childrenD_591_i3) := by
  exact envelope_eq_combination childrenD_591_i3 (4, 3) envelope_591_i3
    pivot_mem_591_i3 child_envelope_sub_591_i3 envelope_origin_591_i3
def checked_591_i3 : CheckedCard where
  required := required_591_i3
  envelope := envelope_591_i3
  height := height_591_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_591_i3
def height_591_i5 : ℕ := 6
def childrenH_591_i5 : Fin 3 → ℕ := ![height_8, height_19, height_271]
theorem height_exact_591_i5 : height_591_i5 = 1 + Finset.univ.sup childrenH_591_i5 := by decide +kernel
theorem required_origin_591_i5 : ∀ x ∈ required_591_i5,
    (∃ j, x ∈ childrenC_591_i5 j) ∨ ∀ j, x ∈ childrenD_591_i5 j := by decide +kernel
theorem required_exact_591_i5 : required_591_i5 =
    ((Finset.univ.biUnion childrenC_591_i5) ∪ commonEnvelope childrenD_591_i5).erase (4, 3) := by
  exact required_eq_combination childrenC_591_i5 childrenD_591_i5 (4, 3) required_591_i5
    (by decide +kernel) child_required_sub_591_i5 common_sub_591_i5 required_origin_591_i5
theorem envelope_origin_591_i5 : ∀ x ∈ envelope_591_i5,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_591_i5 j := by decide +kernel
theorem envelope_exact_591_i5 : envelope_591_i5 =
    insert (4, 3) (Finset.univ.biUnion childrenD_591_i5) := by
  exact envelope_eq_combination childrenD_591_i5 (4, 3) envelope_591_i5
    pivot_mem_591_i5 child_envelope_sub_591_i5 envelope_origin_591_i5
def checked_591_i5 : CheckedCard where
  required := required_591_i5
  envelope := envelope_591_i5
  height := height_591_i5
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_591_i5
def height_591_i2 : ℕ := 12
def childrenH_591_i2 : Fin 5 → ℕ := ![height_13, height_356, height_591_i3, height_586, height_591_i5]
theorem height_exact_591_i2 : height_591_i2 = 1 + Finset.univ.sup childrenH_591_i2 := by decide +kernel
theorem required_origin_591_i2 : ∀ x ∈ required_591_i2,
    (∃ j, x ∈ childrenC_591_i2 j) ∨ ∀ j, x ∈ childrenD_591_i2 j := by decide +kernel
theorem required_exact_591_i2 : required_591_i2 =
    ((Finset.univ.biUnion childrenC_591_i2) ∪ commonEnvelope childrenD_591_i2).erase (4, 4) := by
  exact required_eq_combination childrenC_591_i2 childrenD_591_i2 (4, 4) required_591_i2
    (by decide +kernel) child_required_sub_591_i2 common_sub_591_i2 required_origin_591_i2
theorem envelope_origin_591_i2 : ∀ x ∈ envelope_591_i2,
    x = (4, 4) ∨ ∃ j, x ∈ childrenD_591_i2 j := by decide +kernel
theorem envelope_exact_591_i2 : envelope_591_i2 =
    insert (4, 4) (Finset.univ.biUnion childrenD_591_i2) := by
  exact envelope_eq_combination childrenD_591_i2 (4, 4) envelope_591_i2
    pivot_mem_591_i2 child_envelope_sub_591_i2 envelope_origin_591_i2
def checked_591_i2 : CheckedCard where
  required := required_591_i2
  envelope := envelope_591_i2
  height := height_591_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_591_i2
def height_591 : ℕ := 13
def childrenH_591 : Fin 5 → ℕ := ![height_42, height_430, height_591_i0, height_591_i1, height_591_i2]
theorem height_exact_591 : height_591 = 1 + Finset.univ.sup childrenH_591 := by decide +kernel
theorem required_origin_591 : ∀ x ∈ required_591,
    (∃ j, x ∈ childrenC_591 j) ∨ ∀ j, x ∈ childrenD_591 j := by decide +kernel
theorem required_exact_591 : required_591 =
    ((Finset.univ.biUnion childrenC_591) ∪ commonEnvelope childrenD_591).erase (4, 6) := by
  exact required_eq_combination childrenC_591 childrenD_591 (4, 6) required_591
    (by decide +kernel) child_required_sub_591 common_sub_591 required_origin_591
theorem envelope_origin_591 : ∀ x ∈ envelope_591,
    x = (4, 6) ∨ ∃ j, x ∈ childrenD_591 j := by decide +kernel
theorem envelope_exact_591 : envelope_591 =
    insert (4, 6) (Finset.univ.biUnion childrenD_591) := by
  exact envelope_eq_combination childrenD_591 (4, 6) envelope_591
    pivot_mem_591 child_envelope_sub_591 envelope_origin_591
def checked_591 : CheckedCard where
  required := required_591
  envelope := envelope_591
  height := height_591
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_591
def height_597_i0 : ℕ := 5
def childrenH_597_i0 : Fin 3 → ℕ := ![height_13, height_109, height_291]
theorem height_exact_597_i0 : height_597_i0 = 1 + Finset.univ.sup childrenH_597_i0 := by decide +kernel
theorem required_origin_597_i0 : ∀ x ∈ required_597_i0,
    (∃ j, x ∈ childrenC_597_i0 j) ∨ ∀ j, x ∈ childrenD_597_i0 j := by decide +kernel
theorem required_exact_597_i0 : required_597_i0 =
    ((Finset.univ.biUnion childrenC_597_i0) ∪ commonEnvelope childrenD_597_i0).erase (5, 4) := by
  exact required_eq_combination childrenC_597_i0 childrenD_597_i0 (5, 4) required_597_i0
    (by decide +kernel) child_required_sub_597_i0 common_sub_597_i0 required_origin_597_i0
theorem envelope_origin_597_i0 : ∀ x ∈ envelope_597_i0,
    x = (5, 4) ∨ ∃ j, x ∈ childrenD_597_i0 j := by decide +kernel
theorem envelope_exact_597_i0 : envelope_597_i0 =
    insert (5, 4) (Finset.univ.biUnion childrenD_597_i0) := by
  exact envelope_eq_combination childrenD_597_i0 (5, 4) envelope_597_i0
    pivot_mem_597_i0 child_envelope_sub_597_i0 envelope_origin_597_i0
def checked_597_i0 : CheckedCard where
  required := required_597_i0
  envelope := envelope_597_i0
  height := height_597_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_597_i0
def height_597_i3 : ℕ := 2
def childrenH_597_i3 : Fin 2 → ℕ := ![height_5, height_5]
theorem height_exact_597_i3 : height_597_i3 = 1 + Finset.univ.sup childrenH_597_i3 := by decide +kernel
theorem required_origin_597_i3 : ∀ x ∈ required_597_i3,
    (∃ j, x ∈ childrenC_597_i3 j) ∨ ∀ j, x ∈ childrenD_597_i3 j := by decide +kernel
theorem required_exact_597_i3 : required_597_i3 =
    ((Finset.univ.biUnion childrenC_597_i3) ∪ commonEnvelope childrenD_597_i3).erase (4, 2) := by
  exact required_eq_combination childrenC_597_i3 childrenD_597_i3 (4, 2) required_597_i3
    (by decide +kernel) child_required_sub_597_i3 common_sub_597_i3 required_origin_597_i3
theorem envelope_origin_597_i3 : ∀ x ∈ envelope_597_i3,
    x = (4, 2) ∨ ∃ j, x ∈ childrenD_597_i3 j := by decide +kernel
theorem envelope_exact_597_i3 : envelope_597_i3 =
    insert (4, 2) (Finset.univ.biUnion childrenD_597_i3) := by
  exact envelope_eq_combination childrenD_597_i3 (4, 2) envelope_597_i3
    pivot_mem_597_i3 child_envelope_sub_597_i3 envelope_origin_597_i3
def checked_597_i3 : CheckedCard where
  required := required_597_i3
  envelope := envelope_597_i3
  height := height_597_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_597_i3
def height_597_i2 : ℕ := 4
def childrenH_597_i2 : Fin 2 → ℕ := ![height_7, height_597_i3]
theorem height_exact_597_i2 : height_597_i2 = 1 + Finset.univ.sup childrenH_597_i2 := by decide +kernel
theorem required_origin_597_i2 : ∀ x ∈ required_597_i2,
    (∃ j, x ∈ childrenC_597_i2 j) ∨ ∀ j, x ∈ childrenD_597_i2 j := by decide +kernel
theorem required_exact_597_i2 : required_597_i2 =
    ((Finset.univ.biUnion childrenC_597_i2) ∪ commonEnvelope childrenD_597_i2).erase (5, 2) := by
  exact required_eq_combination childrenC_597_i2 childrenD_597_i2 (5, 2) required_597_i2
    (by decide +kernel) child_required_sub_597_i2 common_sub_597_i2 required_origin_597_i2
theorem envelope_origin_597_i2 : ∀ x ∈ envelope_597_i2,
    x = (5, 2) ∨ ∃ j, x ∈ childrenD_597_i2 j := by decide +kernel
theorem envelope_exact_597_i2 : envelope_597_i2 =
    insert (5, 2) (Finset.univ.biUnion childrenD_597_i2) := by
  exact envelope_eq_combination childrenD_597_i2 (5, 2) envelope_597_i2
    pivot_mem_597_i2 child_envelope_sub_597_i2 envelope_origin_597_i2
def checked_597_i2 : CheckedCard where
  required := required_597_i2
  envelope := envelope_597_i2
  height := height_597_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_597_i2
def height_597_i6 : ℕ := 2
def childrenH_597_i6 : Fin 2 → ℕ := ![height_4, height_4]
theorem height_exact_597_i6 : height_597_i6 = 1 + Finset.univ.sup childrenH_597_i6 := by decide +kernel
theorem required_origin_597_i6 : ∀ x ∈ required_597_i6,
    (∃ j, x ∈ childrenC_597_i6 j) ∨ ∀ j, x ∈ childrenD_597_i6 j := by decide +kernel
theorem required_exact_597_i6 : required_597_i6 =
    ((Finset.univ.biUnion childrenC_597_i6) ∪ commonEnvelope childrenD_597_i6).erase (6, 1) := by
  exact required_eq_combination childrenC_597_i6 childrenD_597_i6 (6, 1) required_597_i6
    (by decide +kernel) child_required_sub_597_i6 common_sub_597_i6 required_origin_597_i6
theorem envelope_origin_597_i6 : ∀ x ∈ envelope_597_i6,
    x = (6, 1) ∨ ∃ j, x ∈ childrenD_597_i6 j := by decide +kernel
theorem envelope_exact_597_i6 : envelope_597_i6 =
    insert (6, 1) (Finset.univ.biUnion childrenD_597_i6) := by
  exact envelope_eq_combination childrenD_597_i6 (6, 1) envelope_597_i6
    pivot_mem_597_i6 child_envelope_sub_597_i6 envelope_origin_597_i6
def checked_597_i6 : CheckedCard where
  required := required_597_i6
  envelope := envelope_597_i6
  height := height_597_i6
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_597_i6
def height_597_i5 : ℕ := 3
def childrenH_597_i5 : Fin 2 → ℕ := ![height_5, height_597_i6]
theorem height_exact_597_i5 : height_597_i5 = 1 + Finset.univ.sup childrenH_597_i5 := by decide +kernel
theorem required_origin_597_i5 : ∀ x ∈ required_597_i5,
    (∃ j, x ∈ childrenC_597_i5 j) ∨ ∀ j, x ∈ childrenD_597_i5 j := by decide +kernel
theorem required_exact_597_i5 : required_597_i5 =
    ((Finset.univ.biUnion childrenC_597_i5) ∪ commonEnvelope childrenD_597_i5).erase (5, 2) := by
  exact required_eq_combination childrenC_597_i5 childrenD_597_i5 (5, 2) required_597_i5
    (by decide +kernel) child_required_sub_597_i5 common_sub_597_i5 required_origin_597_i5
theorem envelope_origin_597_i5 : ∀ x ∈ envelope_597_i5,
    x = (5, 2) ∨ ∃ j, x ∈ childrenD_597_i5 j := by decide +kernel
theorem envelope_exact_597_i5 : envelope_597_i5 =
    insert (5, 2) (Finset.univ.biUnion childrenD_597_i5) := by
  exact envelope_eq_combination childrenD_597_i5 (5, 2) envelope_597_i5
    pivot_mem_597_i5 child_envelope_sub_597_i5 envelope_origin_597_i5
def checked_597_i5 : CheckedCard where
  required := required_597_i5
  envelope := envelope_597_i5
  height := height_597_i5
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_597_i5
def height_597_i4 : ℕ := 4
def childrenH_597_i4 : Fin 2 → ℕ := ![height_140, height_597_i5]
theorem height_exact_597_i4 : height_597_i4 = 1 + Finset.univ.sup childrenH_597_i4 := by decide +kernel
theorem required_origin_597_i4 : ∀ x ∈ required_597_i4,
    (∃ j, x ∈ childrenC_597_i4 j) ∨ ∀ j, x ∈ childrenD_597_i4 j := by decide +kernel
theorem required_exact_597_i4 : required_597_i4 =
    ((Finset.univ.biUnion childrenC_597_i4) ∪ commonEnvelope childrenD_597_i4).erase (4, 2) := by
  exact required_eq_combination childrenC_597_i4 childrenD_597_i4 (4, 2) required_597_i4
    (by decide +kernel) child_required_sub_597_i4 common_sub_597_i4 required_origin_597_i4
theorem envelope_origin_597_i4 : ∀ x ∈ envelope_597_i4,
    x = (4, 2) ∨ ∃ j, x ∈ childrenD_597_i4 j := by decide +kernel
theorem envelope_exact_597_i4 : envelope_597_i4 =
    insert (4, 2) (Finset.univ.biUnion childrenD_597_i4) := by
  exact envelope_eq_combination childrenD_597_i4 (4, 2) envelope_597_i4
    pivot_mem_597_i4 child_envelope_sub_597_i4 envelope_origin_597_i4
def checked_597_i4 : CheckedCard where
  required := required_597_i4
  envelope := envelope_597_i4
  height := height_597_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_597_i4
def height_597_i1 : ℕ := 12
def childrenH_597_i1 : Fin 3 → ℕ := ![height_597_i2, height_597_i4, height_596]
theorem height_exact_597_i1 : height_597_i1 = 1 + Finset.univ.sup childrenH_597_i1 := by decide +kernel
theorem required_origin_597_i1 : ∀ x ∈ required_597_i1,
    (∃ j, x ∈ childrenC_597_i1 j) ∨ ∀ j, x ∈ childrenD_597_i1 j := by decide +kernel
theorem required_exact_597_i1 : required_597_i1 =
    ((Finset.univ.biUnion childrenC_597_i1) ∪ commonEnvelope childrenD_597_i1).erase (5, 4) := by
  exact required_eq_combination childrenC_597_i1 childrenD_597_i1 (5, 4) required_597_i1
    (by decide +kernel) child_required_sub_597_i1 common_sub_597_i1 required_origin_597_i1
theorem envelope_origin_597_i1 : ∀ x ∈ envelope_597_i1,
    x = (5, 4) ∨ ∃ j, x ∈ childrenD_597_i1 j := by decide +kernel
theorem envelope_exact_597_i1 : envelope_597_i1 =
    insert (5, 4) (Finset.univ.biUnion childrenD_597_i1) := by
  exact envelope_eq_combination childrenD_597_i1 (5, 4) envelope_597_i1
    pivot_mem_597_i1 child_envelope_sub_597_i1 envelope_origin_597_i1
def checked_597_i1 : CheckedCard where
  required := required_597_i1
  envelope := envelope_597_i1
  height := height_597_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_597_i1
def height_597 : ℕ := 13
def childrenH_597 : Fin 5 → ℕ := ![height_272, height_290, height_593, height_597_i0, height_597_i1]
theorem height_exact_597 : height_597 = 1 + Finset.univ.sup childrenH_597 := by decide +kernel
theorem required_origin_597 : ∀ x ∈ required_597,
    (∃ j, x ∈ childrenC_597 j) ∨ ∀ j, x ∈ childrenD_597 j := by decide +kernel
theorem required_exact_597 : required_597 =
    ((Finset.univ.biUnion childrenC_597) ∪ commonEnvelope childrenD_597).erase (5, 5) := by
  exact required_eq_combination childrenC_597 childrenD_597 (5, 5) required_597
    (by decide +kernel) child_required_sub_597 common_sub_597 required_origin_597
theorem envelope_origin_597 : ∀ x ∈ envelope_597,
    x = (5, 5) ∨ ∃ j, x ∈ childrenD_597 j := by decide +kernel
theorem envelope_exact_597 : envelope_597 =
    insert (5, 5) (Finset.univ.biUnion childrenD_597) := by
  exact envelope_eq_combination childrenD_597 (5, 5) envelope_597
    pivot_mem_597 child_envelope_sub_597 envelope_origin_597
def checked_597 : CheckedCard where
  required := required_597
  envelope := envelope_597
  height := height_597
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_597
def height_603_i0 : ℕ := 12
def childrenH_603_i0 : Fin 4 → ℕ := ![height_7, height_8, height_9, height_427]
theorem height_exact_603_i0 : height_603_i0 = 1 + Finset.univ.sup childrenH_603_i0 := by decide +kernel
theorem required_origin_603_i0 : ∀ x ∈ required_603_i0,
    (∃ j, x ∈ childrenC_603_i0 j) ∨ ∀ j, x ∈ childrenD_603_i0 j := by decide +kernel
theorem required_exact_603_i0 : required_603_i0 =
    ((Finset.univ.biUnion childrenC_603_i0) ∪ commonEnvelope childrenD_603_i0).erase (1, 2) := by
  exact required_eq_combination childrenC_603_i0 childrenD_603_i0 (1, 2) required_603_i0
    (by decide +kernel) child_required_sub_603_i0 common_sub_603_i0 required_origin_603_i0
theorem envelope_origin_603_i0 : ∀ x ∈ envelope_603_i0,
    x = (1, 2) ∨ ∃ j, x ∈ childrenD_603_i0 j := by decide +kernel
theorem envelope_exact_603_i0 : envelope_603_i0 =
    insert (1, 2) (Finset.univ.biUnion childrenD_603_i0) := by
  exact envelope_eq_combination childrenD_603_i0 (1, 2) envelope_603_i0
    pivot_mem_603_i0 child_envelope_sub_603_i0 envelope_origin_603_i0
def checked_603_i0 : CheckedCard where
  required := required_603_i0
  envelope := envelope_603_i0
  height := height_603_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_603_i0
def height_603 : ℕ := 13
def childrenH_603 : Fin 7 → ℕ := ![height_13, height_14, height_31, height_189, height_367, height_457, height_603_i0]
theorem height_exact_603 : height_603 = 1 + Finset.univ.sup childrenH_603 := by decide +kernel
theorem required_origin_603 : ∀ x ∈ required_603,
    (∃ j, x ∈ childrenC_603 j) ∨ ∀ j, x ∈ childrenD_603 j := by decide +kernel
theorem required_exact_603 : required_603 =
    ((Finset.univ.biUnion childrenC_603) ∪ commonEnvelope childrenD_603).erase (1, 5) := by
  exact required_eq_combination childrenC_603 childrenD_603 (1, 5) required_603
    (by decide +kernel) child_required_sub_603 common_sub_603 required_origin_603
theorem envelope_origin_603 : ∀ x ∈ envelope_603,
    x = (1, 5) ∨ ∃ j, x ∈ childrenD_603 j := by decide +kernel
theorem envelope_exact_603 : envelope_603 =
    insert (1, 5) (Finset.univ.biUnion childrenD_603) := by
  exact envelope_eq_combination childrenD_603 (1, 5) envelope_603
    pivot_mem_603 child_envelope_sub_603 envelope_origin_603
def checked_603 : CheckedCard where
  required := required_603
  envelope := envelope_603
  height := height_603
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_603
def height_634 : ℕ := 13
def childrenH_634 : Fin 5 → ℕ := ![height_438, height_452, height_587, height_612, height_633]
theorem height_exact_634 : height_634 = 1 + Finset.univ.sup childrenH_634 := by decide +kernel
theorem required_origin_634 : ∀ x ∈ required_634,
    (∃ j, x ∈ childrenC_634 j) ∨ ∀ j, x ∈ childrenD_634 j := by decide +kernel
theorem required_exact_634 : required_634 =
    ((Finset.univ.biUnion childrenC_634) ∪ commonEnvelope childrenD_634).erase (5, 5) := by
  exact required_eq_combination childrenC_634 childrenD_634 (5, 5) required_634
    (by decide +kernel) child_required_sub_634 common_sub_634 required_origin_634
theorem envelope_origin_634 : ∀ x ∈ envelope_634,
    x = (5, 5) ∨ ∃ j, x ∈ childrenD_634 j := by decide +kernel
theorem envelope_exact_634 : envelope_634 =
    insert (5, 5) (Finset.univ.biUnion childrenD_634) := by
  exact envelope_eq_combination childrenD_634 (5, 5) envelope_634
    pivot_mem_634 child_envelope_sub_634 envelope_origin_634
def checked_634 : CheckedCard where
  required := required_634
  envelope := envelope_634
  height := height_634
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_634
def height_642 : ℕ := 13
def childrenH_642 : Fin 7 → ℕ := ![height_299, height_349, height_476, height_587, height_587, height_612, height_641]
theorem height_exact_642 : height_642 = 1 + Finset.univ.sup childrenH_642 := by decide +kernel
theorem required_origin_642 : ∀ x ∈ required_642,
    (∃ j, x ∈ childrenC_642 j) ∨ ∀ j, x ∈ childrenD_642 j := by decide +kernel
theorem required_exact_642 : required_642 =
    ((Finset.univ.biUnion childrenC_642) ∪ commonEnvelope childrenD_642).erase (3, 5) := by
  exact required_eq_combination childrenC_642 childrenD_642 (3, 5) required_642
    (by decide +kernel) child_required_sub_642 common_sub_642 required_origin_642
theorem envelope_origin_642 : ∀ x ∈ envelope_642,
    x = (3, 5) ∨ ∃ j, x ∈ childrenD_642 j := by decide +kernel
theorem envelope_exact_642 : envelope_642 =
    insert (3, 5) (Finset.univ.biUnion childrenD_642) := by
  exact envelope_eq_combination childrenD_642 (3, 5) envelope_642
    pivot_mem_642 child_envelope_sub_642 envelope_origin_642
def checked_642 : CheckedCard where
  required := required_642
  envelope := envelope_642
  height := height_642
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_642
def height_643 : ℕ := 13
def childrenH_643 : Fin 7 → ℕ := ![height_299, height_349, height_476, height_587, height_587, height_612, height_641]
theorem height_exact_643 : height_643 = 1 + Finset.univ.sup childrenH_643 := by decide +kernel
theorem required_origin_643 : ∀ x ∈ required_643,
    (∃ j, x ∈ childrenC_643 j) ∨ ∀ j, x ∈ childrenD_643 j := by decide +kernel
theorem required_exact_643 : required_643 =
    ((Finset.univ.biUnion childrenC_643) ∪ commonEnvelope childrenD_643).erase (3, 5) := by
  exact required_eq_combination childrenC_643 childrenD_643 (3, 5) required_643
    (by decide +kernel) child_required_sub_643 common_sub_643 required_origin_643
theorem envelope_origin_643 : ∀ x ∈ envelope_643,
    x = (3, 5) ∨ ∃ j, x ∈ childrenD_643 j := by decide +kernel
theorem envelope_exact_643 : envelope_643 =
    insert (3, 5) (Finset.univ.biUnion childrenD_643) := by
  exact envelope_eq_combination childrenD_643 (3, 5) envelope_643
    pivot_mem_643 child_envelope_sub_643 envelope_origin_643
def checked_643 : CheckedCard where
  required := required_643
  envelope := envelope_643
  height := height_643
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_643
def height_647_i1 : ℕ := 6
def childrenH_647_i1 : Fin 3 → ℕ := ![height_15, height_65, height_282]
theorem height_exact_647_i1 : height_647_i1 = 1 + Finset.univ.sup childrenH_647_i1 := by decide +kernel
theorem required_origin_647_i1 : ∀ x ∈ required_647_i1,
    (∃ j, x ∈ childrenC_647_i1 j) ∨ ∀ j, x ∈ childrenD_647_i1 j := by decide +kernel
theorem required_exact_647_i1 : required_647_i1 =
    ((Finset.univ.biUnion childrenC_647_i1) ∪ commonEnvelope childrenD_647_i1).erase (6, 5) := by
  exact required_eq_combination childrenC_647_i1 childrenD_647_i1 (6, 5) required_647_i1
    (by decide +kernel) child_required_sub_647_i1 common_sub_647_i1 required_origin_647_i1
theorem envelope_origin_647_i1 : ∀ x ∈ envelope_647_i1,
    x = (6, 5) ∨ ∃ j, x ∈ childrenD_647_i1 j := by decide +kernel
theorem envelope_exact_647_i1 : envelope_647_i1 =
    insert (6, 5) (Finset.univ.biUnion childrenD_647_i1) := by
  exact envelope_eq_combination childrenD_647_i1 (6, 5) envelope_647_i1
    pivot_mem_647_i1 child_envelope_sub_647_i1 envelope_origin_647_i1
def checked_647_i1 : CheckedCard where
  required := required_647_i1
  envelope := envelope_647_i1
  height := height_647_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_647_i1
def height_647_i0 : ℕ := 8
def childrenH_647_i0 : Fin 4 → ℕ := ![height_600, height_600, height_621, height_647_i1]
theorem height_exact_647_i0 : height_647_i0 = 1 + Finset.univ.sup childrenH_647_i0 := by decide +kernel
theorem required_origin_647_i0 : ∀ x ∈ required_647_i0,
    (∃ j, x ∈ childrenC_647_i0 j) ∨ ∀ j, x ∈ childrenD_647_i0 j := by decide +kernel
theorem required_exact_647_i0 : required_647_i0 =
    ((Finset.univ.biUnion childrenC_647_i0) ∪ commonEnvelope childrenD_647_i0).erase (5, 5) := by
  exact required_eq_combination childrenC_647_i0 childrenD_647_i0 (5, 5) required_647_i0
    (by decide +kernel) child_required_sub_647_i0 common_sub_647_i0 required_origin_647_i0
theorem envelope_origin_647_i0 : ∀ x ∈ envelope_647_i0,
    x = (5, 5) ∨ ∃ j, x ∈ childrenD_647_i0 j := by decide +kernel
theorem envelope_exact_647_i0 : envelope_647_i0 =
    insert (5, 5) (Finset.univ.biUnion childrenD_647_i0) := by
  exact envelope_eq_combination childrenD_647_i0 (5, 5) envelope_647_i0
    pivot_mem_647_i0 child_envelope_sub_647_i0 envelope_origin_647_i0
def checked_647_i0 : CheckedCard where
  required := required_647_i0
  envelope := envelope_647_i0
  height := height_647_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_647_i0
def height_647 : ℕ := 13
def childrenH_647 : Fin 9 → ℕ := ![height_399, height_408, height_410, height_480, height_546, height_587, height_635, height_646, height_647_i0]
theorem height_exact_647 : height_647 = 1 + Finset.univ.sup childrenH_647 := by decide +kernel
theorem required_origin_647 : ∀ x ∈ required_647,
    (∃ j, x ∈ childrenC_647 j) ∨ ∀ j, x ∈ childrenD_647 j := by decide +kernel
theorem required_exact_647 : required_647 =
    ((Finset.univ.biUnion childrenC_647) ∪ commonEnvelope childrenD_647).erase (5, 4) := by
  exact required_eq_combination childrenC_647 childrenD_647 (5, 4) required_647
    (by decide +kernel) child_required_sub_647 common_sub_647 required_origin_647
theorem envelope_origin_647 : ∀ x ∈ envelope_647,
    x = (5, 4) ∨ ∃ j, x ∈ childrenD_647 j := by decide +kernel
theorem envelope_exact_647 : envelope_647 =
    insert (5, 4) (Finset.univ.biUnion childrenD_647) := by
  exact envelope_eq_combination childrenD_647 (5, 4) envelope_647
    pivot_mem_647 child_envelope_sub_647 envelope_origin_647
def checked_647 : CheckedCard where
  required := required_647
  envelope := envelope_647
  height := height_647
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_647
end SnakyPrototype.Certificate21

end OAI
