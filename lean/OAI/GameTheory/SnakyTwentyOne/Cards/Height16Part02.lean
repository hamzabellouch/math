import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height11Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height13Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height15Part02
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_683_i0 : Finset Cell := ⟨(([(1, 4), (1, 5), (3, 5), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_683_i0 : Finset Cell := ⟨(([(0, 4), (0, 6), (1, 4), (1, 5), (1, 6), (2, 5), (2, 6), (3, 5), (4, 4), (4, 5), (5, 4), (5, 5), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_683_i0 : Fin 2 → Finset Cell := ![(placed21 6 (4, 5) required_5), (placed21 3 (0, 6) required_9)]
def childrenD_683_i0 : Fin 2 → Finset Cell := ![(placed21 6 (4, 5) envelope_5), (placed21 3 (0, 6) envelope_9)]
theorem common_sub_683_i0 : commonEnvelope childrenD_683_i0 ⊆ insert (2, 5) required_683_i0 := by decide +kernel
theorem child_required_sub_683_i0 : ∀ j, childrenC_683_i0 j ⊆ insert (2, 5) required_683_i0 := by decide +kernel
theorem child_envelope_sub_683_i0 : ∀ j, childrenD_683_i0 j ⊆ envelope_683_i0 := by decide +kernel
theorem pivot_mem_683_i0 : (2, 5) ∈ envelope_683_i0 := by decide +kernel
theorem children_work_683_i0 : ∀ j, Template HasSnaky 3 (childrenC_683_i0 j) (childrenD_683_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 6 (4, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_9 3 (0, 6)).mono (by decide +kernel)
theorem row_works_683_i0 : Template HasSnaky 4 required_683_i0 envelope_683_i0 := by
  refine compose HasSnaky 3 childrenC_683_i0 childrenD_683_i0 children_work_683_i0 (2, 5)
    required_683_i0 envelope_683_i0 pivot_mem_683_i0 child_required_sub_683_i0 child_envelope_sub_683_i0 ?_
  intro b hb
  exact common_sub_683_i0 (mem_commonEnvelope childrenD_683_i0 b hb)
def required_683_i1 : Finset Cell := ⟨(([(1, 4), (1, 5), (3, 5), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_683_i1 : Finset Cell := ⟨(([(0, 4), (1, 4), (1, 5), (2, 5), (2, 6), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 4), (5, 6), (5, 7), (5, 8), (5, 9), (6, 7), (7, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_683_i1 : Fin 2 → Finset Cell := ![(placed21 6 (4, 5) required_5), (placed21 0 (1, 2) required_604)]
def childrenD_683_i1 : Fin 2 → Finset Cell := ![(placed21 6 (4, 5) envelope_5), (placed21 0 (1, 2) envelope_604)]
theorem common_sub_683_i1 : commonEnvelope childrenD_683_i1 ⊆ insert (2, 5) required_683_i1 := by decide +kernel
theorem child_required_sub_683_i1 : ∀ j, childrenC_683_i1 j ⊆ insert (2, 5) required_683_i1 := by decide +kernel
theorem child_envelope_sub_683_i1 : ∀ j, childrenD_683_i1 j ⊆ envelope_683_i1 := by decide +kernel
theorem pivot_mem_683_i1 : (2, 5) ∈ envelope_683_i1 := by decide +kernel
theorem children_work_683_i1 : ∀ j, Template HasSnaky 8 (childrenC_683_i1 j) (childrenD_683_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 6 (4, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_604 0 (1, 2)).mono (by decide +kernel)
theorem row_works_683_i1 : Template HasSnaky 9 required_683_i1 envelope_683_i1 := by
  refine compose HasSnaky 8 childrenC_683_i1 childrenD_683_i1 children_work_683_i1 (2, 5)
    required_683_i1 envelope_683_i1 pivot_mem_683_i1 child_required_sub_683_i1 child_envelope_sub_683_i1 ?_
  intro b hb
  exact common_sub_683_i1 (mem_commonEnvelope childrenD_683_i1 b hb)
def required_683 : Finset Cell := ⟨(([(1, 4), (1, 5), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_683 : Finset Cell := ⟨(([(0, 4), (0, 6), (0, 7), (0, 8), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, 3), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_683 : Fin 5 → Finset Cell := ![(placed21 1 (0, 4) required_50), (placed21 1 (0, 4) required_150), required_683_i0, required_683_i1, (placed21 4 (0, 10) required_682)]
def childrenD_683 : Fin 5 → Finset Cell := ![(placed21 1 (0, 4) envelope_50), (placed21 1 (0, 4) envelope_150), envelope_683_i0, envelope_683_i1, (placed21 4 (0, 10) envelope_682)]
theorem common_sub_683 : commonEnvelope childrenD_683 ⊆ insert (3, 5) required_683 := by decide +kernel
theorem child_required_sub_683 : ∀ j, childrenC_683 j ⊆ insert (3, 5) required_683 := by decide +kernel
theorem child_envelope_sub_683 : ∀ j, childrenD_683 j ⊆ envelope_683 := by decide +kernel
theorem pivot_mem_683 : (3, 5) ∈ envelope_683 := by decide +kernel
theorem children_work_683 : ∀ j, Template HasSnaky 15 (childrenC_683 j) (childrenD_683 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_50 1 (0, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_150 1 (0, 4)).mono (by decide +kernel)
  · exact row_works_683_i0.mono (by decide +kernel)
  · exact row_works_683_i1.mono (by decide +kernel)
  · exact (placed21_template row_works_682 4 (0, 10)).mono (by decide +kernel)
theorem row_works_683 : Template HasSnaky 16 required_683 envelope_683 := by
  refine compose HasSnaky 15 childrenC_683 childrenD_683 children_work_683 (3, 5)
    required_683 envelope_683 pivot_mem_683 child_required_sub_683 child_envelope_sub_683 ?_
  intro b hb
  exact common_sub_683 (mem_commonEnvelope childrenD_683 b hb)
def required_706_i2 : Finset Cell := ⟨(([(3, 4), (4, 4), (5, 4), (7, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_706_i2 : Finset Cell := ⟨(([(2, 3), (3, 3), (3, 4), (4, 3), (4, 4), (5, 4), (6, 3), (6, 4), (6, 5), (7, 3), (7, 4), (7, 5), (8, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_706_i2 : Fin 2 → Finset Cell := ![(placed21 4 (3, 4) required_4), (placed21 1 (2, 3) required_9)]
def childrenD_706_i2 : Fin 2 → Finset Cell := ![(placed21 4 (3, 4) envelope_4), (placed21 1 (2, 3) envelope_9)]
theorem common_sub_706_i2 : commonEnvelope childrenD_706_i2 ⊆ insert (6, 4) required_706_i2 := by decide +kernel
theorem child_required_sub_706_i2 : ∀ j, childrenC_706_i2 j ⊆ insert (6, 4) required_706_i2 := by decide +kernel
theorem child_envelope_sub_706_i2 : ∀ j, childrenD_706_i2 j ⊆ envelope_706_i2 := by decide +kernel
theorem pivot_mem_706_i2 : (6, 4) ∈ envelope_706_i2 := by decide +kernel
theorem children_work_706_i2 : ∀ j, Template HasSnaky 3 (childrenC_706_i2 j) (childrenD_706_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_4 4 (3, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_9 1 (2, 3)).mono (by decide +kernel)
theorem row_works_706_i2 : Template HasSnaky 4 required_706_i2 envelope_706_i2 := by
  refine compose HasSnaky 3 childrenC_706_i2 childrenD_706_i2 children_work_706_i2 (6, 4)
    required_706_i2 envelope_706_i2 pivot_mem_706_i2 child_required_sub_706_i2 child_envelope_sub_706_i2 ?_
  intro b hb
  exact common_sub_706_i2 (mem_commonEnvelope childrenD_706_i2 b hb)
def required_706_i3 : Finset Cell := ⟨(([(3, 4), (4, 4), (4, 5), (5, 4), (5, 5), (7, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_706_i3 : Finset Cell := ⟨(([(3, 4), (4, 3), (4, 4), (4, 5), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (6, 3), (6, 5), (6, 6), (7, 3), (7, 5), (8, 3), (8, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_706_i3 : Fin 2 → Finset Cell := ![(placed21 3 (3, 4) required_154), (placed21 4 (3, 6) required_159)]
def childrenD_706_i3 : Fin 2 → Finset Cell := ![(placed21 3 (3, 4) envelope_154), (placed21 4 (3, 6) envelope_159)]
theorem common_sub_706_i3 : commonEnvelope childrenD_706_i3 ⊆ insert (5, 3) required_706_i3 := by decide +kernel
theorem child_required_sub_706_i3 : ∀ j, childrenC_706_i3 j ⊆ insert (5, 3) required_706_i3 := by decide +kernel
theorem child_envelope_sub_706_i3 : ∀ j, childrenD_706_i3 j ⊆ envelope_706_i3 := by decide +kernel
theorem pivot_mem_706_i3 : (5, 3) ∈ envelope_706_i3 := by decide +kernel
theorem children_work_706_i3 : ∀ j, Template HasSnaky 3 (childrenC_706_i3 j) (childrenD_706_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_154 3 (3, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_159 4 (3, 6)).mono (by decide +kernel)
theorem row_works_706_i3 : Template HasSnaky 4 required_706_i3 envelope_706_i3 := by
  refine compose HasSnaky 3 childrenC_706_i3 childrenD_706_i3 children_work_706_i3 (5, 3)
    required_706_i3 envelope_706_i3 pivot_mem_706_i3 child_required_sub_706_i3 child_envelope_sub_706_i3 ?_
  intro b hb
  exact common_sub_706_i3 (mem_commonEnvelope childrenD_706_i3 b hb)
def required_706_i4 : Finset Cell := ⟨(([(4, 4), (4, 5), (5, 4), (5, 5), (7, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_706_i4 : Finset Cell := ⟨(([(3, 4), (4, 4), (4, 5), (5, 4), (5, 5), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_706_i4 : Fin 3 → Finset Cell := ![(placed21 3 (3, 5) required_22), (placed21 2 (8, 2) required_152), (placed21 0 (4, 1) required_166)]
def childrenD_706_i4 : Fin 3 → Finset Cell := ![(placed21 3 (3, 5) envelope_22), (placed21 2 (8, 2) envelope_152), (placed21 0 (4, 1) envelope_166)]
theorem common_sub_706_i4 : commonEnvelope childrenD_706_i4 ⊆ insert (7, 5) required_706_i4 := by decide +kernel
theorem child_required_sub_706_i4 : ∀ j, childrenC_706_i4 j ⊆ insert (7, 5) required_706_i4 := by decide +kernel
theorem child_envelope_sub_706_i4 : ∀ j, childrenD_706_i4 j ⊆ envelope_706_i4 := by decide +kernel
theorem pivot_mem_706_i4 : (7, 5) ∈ envelope_706_i4 := by decide +kernel
theorem children_work_706_i4 : ∀ j, Template HasSnaky 6 (childrenC_706_i4 j) (childrenD_706_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_22 3 (3, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_152 2 (8, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_166 0 (4, 1)).mono (by decide +kernel)
theorem row_works_706_i4 : Template HasSnaky 7 required_706_i4 envelope_706_i4 := by
  refine compose HasSnaky 6 childrenC_706_i4 childrenD_706_i4 children_work_706_i4 (7, 5)
    required_706_i4 envelope_706_i4 pivot_mem_706_i4 child_required_sub_706_i4 child_envelope_sub_706_i4 ?_
  intro b hb
  exact common_sub_706_i4 (mem_commonEnvelope childrenD_706_i4 b hb)
def required_706_i1 : Finset Cell := ⟨(([(3, 4), (4, 4), (4, 5), (5, 4), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_706_i1 : Finset Cell := ⟨(([(2, 3), (3, 3), (3, 4), (4, 3), (4, 4), (4, 5), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_706_i1 : Fin 4 → Finset Cell := ![(placed21 3 (3, 4) required_261), required_706_i2, required_706_i3, required_706_i4]
def childrenD_706_i1 : Fin 4 → Finset Cell := ![(placed21 3 (3, 4) envelope_261), envelope_706_i2, envelope_706_i3, envelope_706_i4]
theorem common_sub_706_i1 : commonEnvelope childrenD_706_i1 ⊆ insert (7, 3) required_706_i1 := by decide +kernel
theorem child_required_sub_706_i1 : ∀ j, childrenC_706_i1 j ⊆ insert (7, 3) required_706_i1 := by decide +kernel
theorem child_envelope_sub_706_i1 : ∀ j, childrenD_706_i1 j ⊆ envelope_706_i1 := by decide +kernel
theorem pivot_mem_706_i1 : (7, 3) ∈ envelope_706_i1 := by decide +kernel
theorem children_work_706_i1 : ∀ j, Template HasSnaky 7 (childrenC_706_i1 j) (childrenD_706_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_261 3 (3, 4)).mono (by decide +kernel)
  · exact row_works_706_i2.mono (by decide +kernel)
  · exact row_works_706_i3.mono (by decide +kernel)
  · exact row_works_706_i4.mono (by decide +kernel)
theorem row_works_706_i1 : Template HasSnaky 8 required_706_i1 envelope_706_i1 := by
  refine compose HasSnaky 7 childrenC_706_i1 childrenD_706_i1 children_work_706_i1 (7, 3)
    required_706_i1 envelope_706_i1 pivot_mem_706_i1 child_required_sub_706_i1 child_envelope_sub_706_i1 ?_
  intro b hb
  exact common_sub_706_i1 (mem_commonEnvelope childrenD_706_i1 b hb)
def required_706_i0 : Finset Cell := ⟨(([(4, 4), (4, 5), (5, 4), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_706_i0 : Finset Cell := ⟨(([(1, 3), (1, 4), (2, 3), (2, 4), (3, 3), (3, 4), (4, 3), (4, 4), (4, 5), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_706_i0 : Fin 3 → Finset Cell := ![(placed21 1 (2, 4) required_15), (placed21 3 (1, 5) required_65), required_706_i1]
def childrenD_706_i0 : Fin 3 → Finset Cell := ![(placed21 1 (2, 4) envelope_15), (placed21 3 (1, 5) envelope_65), envelope_706_i1]
theorem common_sub_706_i0 : commonEnvelope childrenD_706_i0 ⊆ insert (3, 4) required_706_i0 := by decide +kernel
theorem child_required_sub_706_i0 : ∀ j, childrenC_706_i0 j ⊆ insert (3, 4) required_706_i0 := by decide +kernel
theorem child_envelope_sub_706_i0 : ∀ j, childrenD_706_i0 j ⊆ envelope_706_i0 := by decide +kernel
theorem pivot_mem_706_i0 : (3, 4) ∈ envelope_706_i0 := by decide +kernel
theorem children_work_706_i0 : ∀ j, Template HasSnaky 8 (childrenC_706_i0 j) (childrenD_706_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_15 1 (2, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_65 3 (1, 5)).mono (by decide +kernel)
  · exact row_works_706_i1.mono (by decide +kernel)
theorem row_works_706_i0 : Template HasSnaky 9 required_706_i0 envelope_706_i0 := by
  refine compose HasSnaky 8 childrenC_706_i0 childrenD_706_i0 children_work_706_i0 (3, 4)
    required_706_i0 envelope_706_i0 pivot_mem_706_i0 child_required_sub_706_i0 child_envelope_sub_706_i0 ?_
  intro b hb
  exact common_sub_706_i0 (mem_commonEnvelope childrenD_706_i0 b hb)
def required_706_i6 : Finset Cell := ⟨(([(4, 4), (5, 3), (5, 4), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_706_i6 : Finset Cell := ⟨(([(0, 3), (0, 5), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5), (3, 3), (3, 4), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (9, 1), (9, 3), (9, 4), (9, 5), (10, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_706_i6 : Fin 3 → Finset Cell := ![(placed21 1 (0, 3) required_318), (placed21 7 (7, 4) required_334), (placed21 3 (3, 5) required_379)]
def childrenD_706_i6 : Fin 3 → Finset Cell := ![(placed21 1 (0, 3) envelope_318), (placed21 7 (7, 4) envelope_334), (placed21 3 (3, 5) envelope_379)]
theorem common_sub_706_i6 : commonEnvelope childrenD_706_i6 ⊆ insert (3, 3) required_706_i6 := by decide +kernel
theorem child_required_sub_706_i6 : ∀ j, childrenC_706_i6 j ⊆ insert (3, 3) required_706_i6 := by decide +kernel
theorem child_envelope_sub_706_i6 : ∀ j, childrenD_706_i6 j ⊆ envelope_706_i6 := by decide +kernel
theorem pivot_mem_706_i6 : (3, 3) ∈ envelope_706_i6 := by decide +kernel
theorem children_work_706_i6 : ∀ j, Template HasSnaky 7 (childrenC_706_i6 j) (childrenD_706_i6 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_318 1 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_334 7 (7, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_379 3 (3, 5)).mono (by decide +kernel)
theorem row_works_706_i6 : Template HasSnaky 8 required_706_i6 envelope_706_i6 := by
  refine compose HasSnaky 7 childrenC_706_i6 childrenD_706_i6 children_work_706_i6 (3, 3)
    required_706_i6 envelope_706_i6 pivot_mem_706_i6 child_required_sub_706_i6 child_envelope_sub_706_i6 ?_
  intro b hb
  exact common_sub_706_i6 (mem_commonEnvelope childrenD_706_i6 b hb)
def required_706_i7 : Finset Cell := ⟨(([(4, 4), (4, 5), (5, 3), (5, 4), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_706_i7 : Finset Cell := ⟨(([(1, 3), (1, 4), (1, 5), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (4, 2), (4, 3), (4, 4), (4, 5), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (6, 3), (6, 4), (7, 3), (7, 4), (7, 5), (8, 3), (8, 4), (8, 5), (9, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_706_i7 : Fin 3 → Finset Cell := ![(placed21 7 (6, 5) required_66), (placed21 7 (6, 6) required_238), (placed21 3 (2, 5) required_394)]
def childrenD_706_i7 : Fin 3 → Finset Cell := ![(placed21 7 (6, 5) envelope_66), (placed21 7 (6, 6) envelope_238), (placed21 3 (2, 5) envelope_394)]
theorem common_sub_706_i7 : commonEnvelope childrenD_706_i7 ⊆ insert (3, 4) required_706_i7 := by decide +kernel
theorem child_required_sub_706_i7 : ∀ j, childrenC_706_i7 j ⊆ insert (3, 4) required_706_i7 := by decide +kernel
theorem child_envelope_sub_706_i7 : ∀ j, childrenD_706_i7 j ⊆ envelope_706_i7 := by decide +kernel
theorem pivot_mem_706_i7 : (3, 4) ∈ envelope_706_i7 := by decide +kernel
theorem children_work_706_i7 : ∀ j, Template HasSnaky 7 (childrenC_706_i7 j) (childrenD_706_i7 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_66 7 (6, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_238 7 (6, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_394 3 (2, 5)).mono (by decide +kernel)
theorem row_works_706_i7 : Template HasSnaky 8 required_706_i7 envelope_706_i7 := by
  refine compose HasSnaky 7 childrenC_706_i7 childrenD_706_i7 children_work_706_i7 (3, 4)
    required_706_i7 envelope_706_i7 pivot_mem_706_i7 child_required_sub_706_i7 child_envelope_sub_706_i7 ?_
  intro b hb
  exact common_sub_706_i7 (mem_commonEnvelope childrenD_706_i7 b hb)
def required_706_i5 : Finset Cell := ⟨(([(4, 4), (4, 5), (5, 4), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_706_i5 : Finset Cell := ⟨(([(0, 1), (0, 3), (0, 5), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (9, 1), (9, 3), (9, 4), (9, 5), (10, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_706_i5 : Fin 6 → Finset Cell := ![(placed21 7 (7, 5) required_417), (placed21 7 (6, 5) required_420), (placed21 7 (6, 5) required_526), (placed21 3 (0, 6) required_532), required_706_i6, required_706_i7]
def childrenD_706_i5 : Fin 6 → Finset Cell := ![(placed21 7 (7, 5) envelope_417), (placed21 7 (6, 5) envelope_420), (placed21 7 (6, 5) envelope_526), (placed21 3 (0, 6) envelope_532), envelope_706_i6, envelope_706_i7]
theorem common_sub_706_i5 : commonEnvelope childrenD_706_i5 ⊆ insert (5, 3) required_706_i5 := by decide +kernel
theorem child_required_sub_706_i5 : ∀ j, childrenC_706_i5 j ⊆ insert (5, 3) required_706_i5 := by decide +kernel
theorem child_envelope_sub_706_i5 : ∀ j, childrenD_706_i5 j ⊆ envelope_706_i5 := by decide +kernel
theorem pivot_mem_706_i5 : (5, 3) ∈ envelope_706_i5 := by decide +kernel
theorem children_work_706_i5 : ∀ j, Template HasSnaky 8 (childrenC_706_i5 j) (childrenD_706_i5 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_417 7 (7, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_420 7 (6, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_526 7 (6, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_532 3 (0, 6)).mono (by decide +kernel)
  · exact row_works_706_i6.mono (by decide +kernel)
  · exact row_works_706_i7.mono (by decide +kernel)
theorem row_works_706_i5 : Template HasSnaky 9 required_706_i5 envelope_706_i5 := by
  refine compose HasSnaky 8 childrenC_706_i5 childrenD_706_i5 children_work_706_i5 (5, 3)
    required_706_i5 envelope_706_i5 pivot_mem_706_i5 child_required_sub_706_i5 child_envelope_sub_706_i5 ?_
  intro b hb
  exact common_sub_706_i5 (mem_commonEnvelope childrenD_706_i5 b hb)
def required_706_i9 : Finset Cell := ⟨(([(4, 4), (4, 5), (5, 4), (5, 5), (7, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_706_i9 : Finset Cell := ⟨(([(3, 4), (4, 4), (4, 5), (5, 4), (5, 5), (6, 1), (6, 2), (6, 3), (6, 4), (6, 6), (6, 7), (6, 8), (6, 9), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (11, 5), (11, 6), (11, 7), (11, 8), (12, 5), (12, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_706_i9 : Fin 4 → Finset Cell := ![(placed21 1 (4, 4) required_30), (placed21 0 (4, 1) required_59), (placed21 3 (3, 6) required_296), (placed21 0 (6, 1) required_603)]
def childrenD_706_i9 : Fin 4 → Finset Cell := ![(placed21 1 (4, 4) envelope_30), (placed21 0 (4, 1) envelope_59), (placed21 3 (3, 6) envelope_296), (placed21 0 (6, 1) envelope_603)]
theorem common_sub_706_i9 : commonEnvelope childrenD_706_i9 ⊆ insert (7, 4) required_706_i9 := by decide +kernel
theorem child_required_sub_706_i9 : ∀ j, childrenC_706_i9 j ⊆ insert (7, 4) required_706_i9 := by decide +kernel
theorem child_envelope_sub_706_i9 : ∀ j, childrenD_706_i9 j ⊆ envelope_706_i9 := by decide +kernel
theorem pivot_mem_706_i9 : (7, 4) ∈ envelope_706_i9 := by decide +kernel
theorem children_work_706_i9 : ∀ j, Template HasSnaky 13 (childrenC_706_i9 j) (childrenD_706_i9 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_30 1 (4, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_59 0 (4, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_296 3 (3, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_603 0 (6, 1)).mono (by decide +kernel)
theorem row_works_706_i9 : Template HasSnaky 14 required_706_i9 envelope_706_i9 := by
  refine compose HasSnaky 13 childrenC_706_i9 childrenD_706_i9 children_work_706_i9 (7, 4)
    required_706_i9 envelope_706_i9 pivot_mem_706_i9 child_required_sub_706_i9 child_envelope_sub_706_i9 ?_
  intro b hb
  exact common_sub_706_i9 (mem_commonEnvelope childrenD_706_i9 b hb)
def required_706_i8 : Finset Cell := ⟨(([(4, 4), (4, 5), (5, 4), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_706_i8 : Finset Cell := ⟨(([(3, 4), (4, 4), (4, 5), (5, 4), (5, 5), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (11, 5), (11, 6), (11, 7), (11, 8), (12, 5), (12, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_706_i8 : Fin 4 → Finset Cell := ![(placed21 3 (3, 5) required_22), (placed21 3 (4, 5) required_74), (placed21 4 (3, 9) required_325), required_706_i9]
def childrenD_706_i8 : Fin 4 → Finset Cell := ![(placed21 3 (3, 5) envelope_22), (placed21 3 (4, 5) envelope_74), (placed21 4 (3, 9) envelope_325), envelope_706_i9]
theorem common_sub_706_i8 : commonEnvelope childrenD_706_i8 ⊆ insert (7, 5) required_706_i8 := by decide +kernel
theorem child_required_sub_706_i8 : ∀ j, childrenC_706_i8 j ⊆ insert (7, 5) required_706_i8 := by decide +kernel
theorem child_envelope_sub_706_i8 : ∀ j, childrenD_706_i8 j ⊆ envelope_706_i8 := by decide +kernel
theorem pivot_mem_706_i8 : (7, 5) ∈ envelope_706_i8 := by decide +kernel
theorem children_work_706_i8 : ∀ j, Template HasSnaky 14 (childrenC_706_i8 j) (childrenD_706_i8 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_22 3 (3, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_74 3 (4, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_325 4 (3, 9)).mono (by decide +kernel)
  · exact row_works_706_i9.mono (by decide +kernel)
theorem row_works_706_i8 : Template HasSnaky 15 required_706_i8 envelope_706_i8 := by
  refine compose HasSnaky 14 childrenC_706_i8 childrenD_706_i8 children_work_706_i8 (7, 5)
    required_706_i8 envelope_706_i8 pivot_mem_706_i8 child_required_sub_706_i8 child_envelope_sub_706_i8 ?_
  intro b hb
  exact common_sub_706_i8 (mem_commonEnvelope childrenD_706_i8 b hb)
def required_706 : Finset Cell := ⟨(([(4, 5), (5, 4), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_706 : Finset Cell := ⟨(([(0, 1), (0, 3), (0, 5), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (9, 1), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (11, 5), (11, 6), (11, 7), (11, 8), (12, 5), (12, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_706 : Fin 7 → Finset Cell := ![(placed21 7 (8, 6) required_512), (placed21 3 (1, 6) required_517), (placed21 7 (8, 6) required_527), (placed21 7 (8, 6) required_537), required_706_i0, required_706_i5, required_706_i8]
def childrenD_706 : Fin 7 → Finset Cell := ![(placed21 7 (8, 6) envelope_512), (placed21 3 (1, 6) envelope_517), (placed21 7 (8, 6) envelope_527), (placed21 7 (8, 6) envelope_537), envelope_706_i0, envelope_706_i5, envelope_706_i8]
theorem common_sub_706 : commonEnvelope childrenD_706 ⊆ insert (4, 4) required_706 := by decide +kernel
theorem child_required_sub_706 : ∀ j, childrenC_706 j ⊆ insert (4, 4) required_706 := by decide +kernel
theorem child_envelope_sub_706 : ∀ j, childrenD_706 j ⊆ envelope_706 := by decide +kernel
theorem pivot_mem_706 : (4, 4) ∈ envelope_706 := by decide +kernel
theorem children_work_706 : ∀ j, Template HasSnaky 15 (childrenC_706 j) (childrenD_706 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_512 7 (8, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_517 3 (1, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_527 7 (8, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_537 7 (8, 6)).mono (by decide +kernel)
  · exact row_works_706_i0.mono (by decide +kernel)
  · exact row_works_706_i5.mono (by decide +kernel)
  · exact row_works_706_i8.mono (by decide +kernel)
theorem row_works_706 : Template HasSnaky 16 required_706 envelope_706 := by
  refine compose HasSnaky 15 childrenC_706 childrenD_706 children_work_706 (4, 4)
    required_706 envelope_706 pivot_mem_706 child_required_sub_706 child_envelope_sub_706 ?_
  intro b hb
  exact common_sub_706 (mem_commonEnvelope childrenD_706 b hb)
def height_683_i0 : ℕ := 4
def childrenH_683_i0 : Fin 2 → ℕ := ![height_5, height_9]
theorem height_exact_683_i0 : height_683_i0 = 1 + Finset.univ.sup childrenH_683_i0 := by decide +kernel
theorem required_origin_683_i0 : ∀ x ∈ required_683_i0,
    (∃ j, x ∈ childrenC_683_i0 j) ∨ ∀ j, x ∈ childrenD_683_i0 j := by decide +kernel
theorem required_exact_683_i0 : required_683_i0 =
    ((Finset.univ.biUnion childrenC_683_i0) ∪ commonEnvelope childrenD_683_i0).erase (2, 5) := by
  exact required_eq_combination childrenC_683_i0 childrenD_683_i0 (2, 5) required_683_i0
    (by decide +kernel) child_required_sub_683_i0 common_sub_683_i0 required_origin_683_i0
theorem envelope_origin_683_i0 : ∀ x ∈ envelope_683_i0,
    x = (2, 5) ∨ ∃ j, x ∈ childrenD_683_i0 j := by decide +kernel
theorem envelope_exact_683_i0 : envelope_683_i0 =
    insert (2, 5) (Finset.univ.biUnion childrenD_683_i0) := by
  exact envelope_eq_combination childrenD_683_i0 (2, 5) envelope_683_i0
    pivot_mem_683_i0 child_envelope_sub_683_i0 envelope_origin_683_i0
def checked_683_i0 : CheckedCard where
  required := required_683_i0
  envelope := envelope_683_i0
  height := height_683_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_683_i0
def height_683_i1 : ℕ := 9
def childrenH_683_i1 : Fin 2 → ℕ := ![height_5, height_604]
theorem height_exact_683_i1 : height_683_i1 = 1 + Finset.univ.sup childrenH_683_i1 := by decide +kernel
theorem required_origin_683_i1 : ∀ x ∈ required_683_i1,
    (∃ j, x ∈ childrenC_683_i1 j) ∨ ∀ j, x ∈ childrenD_683_i1 j := by decide +kernel
theorem required_exact_683_i1 : required_683_i1 =
    ((Finset.univ.biUnion childrenC_683_i1) ∪ commonEnvelope childrenD_683_i1).erase (2, 5) := by
  exact required_eq_combination childrenC_683_i1 childrenD_683_i1 (2, 5) required_683_i1
    (by decide +kernel) child_required_sub_683_i1 common_sub_683_i1 required_origin_683_i1
theorem envelope_origin_683_i1 : ∀ x ∈ envelope_683_i1,
    x = (2, 5) ∨ ∃ j, x ∈ childrenD_683_i1 j := by decide +kernel
theorem envelope_exact_683_i1 : envelope_683_i1 =
    insert (2, 5) (Finset.univ.biUnion childrenD_683_i1) := by
  exact envelope_eq_combination childrenD_683_i1 (2, 5) envelope_683_i1
    pivot_mem_683_i1 child_envelope_sub_683_i1 envelope_origin_683_i1
def checked_683_i1 : CheckedCard where
  required := required_683_i1
  envelope := envelope_683_i1
  height := height_683_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_683_i1
def height_683 : ℕ := 16
def childrenH_683 : Fin 5 → ℕ := ![height_50, height_150, height_683_i0, height_683_i1, height_682]
theorem height_exact_683 : height_683 = 1 + Finset.univ.sup childrenH_683 := by decide +kernel
theorem required_origin_683 : ∀ x ∈ required_683,
    (∃ j, x ∈ childrenC_683 j) ∨ ∀ j, x ∈ childrenD_683 j := by decide +kernel
theorem required_exact_683 : required_683 =
    ((Finset.univ.biUnion childrenC_683) ∪ commonEnvelope childrenD_683).erase (3, 5) := by
  exact required_eq_combination childrenC_683 childrenD_683 (3, 5) required_683
    (by decide +kernel) child_required_sub_683 common_sub_683 required_origin_683
theorem envelope_origin_683 : ∀ x ∈ envelope_683,
    x = (3, 5) ∨ ∃ j, x ∈ childrenD_683 j := by decide +kernel
theorem envelope_exact_683 : envelope_683 =
    insert (3, 5) (Finset.univ.biUnion childrenD_683) := by
  exact envelope_eq_combination childrenD_683 (3, 5) envelope_683
    pivot_mem_683 child_envelope_sub_683 envelope_origin_683
def checked_683 : CheckedCard where
  required := required_683
  envelope := envelope_683
  height := height_683
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_683
def height_706_i2 : ℕ := 4
def childrenH_706_i2 : Fin 2 → ℕ := ![height_4, height_9]
theorem height_exact_706_i2 : height_706_i2 = 1 + Finset.univ.sup childrenH_706_i2 := by decide +kernel
theorem required_origin_706_i2 : ∀ x ∈ required_706_i2,
    (∃ j, x ∈ childrenC_706_i2 j) ∨ ∀ j, x ∈ childrenD_706_i2 j := by decide +kernel
theorem required_exact_706_i2 : required_706_i2 =
    ((Finset.univ.biUnion childrenC_706_i2) ∪ commonEnvelope childrenD_706_i2).erase (6, 4) := by
  exact required_eq_combination childrenC_706_i2 childrenD_706_i2 (6, 4) required_706_i2
    (by decide +kernel) child_required_sub_706_i2 common_sub_706_i2 required_origin_706_i2
theorem envelope_origin_706_i2 : ∀ x ∈ envelope_706_i2,
    x = (6, 4) ∨ ∃ j, x ∈ childrenD_706_i2 j := by decide +kernel
theorem envelope_exact_706_i2 : envelope_706_i2 =
    insert (6, 4) (Finset.univ.biUnion childrenD_706_i2) := by
  exact envelope_eq_combination childrenD_706_i2 (6, 4) envelope_706_i2
    pivot_mem_706_i2 child_envelope_sub_706_i2 envelope_origin_706_i2
def checked_706_i2 : CheckedCard where
  required := required_706_i2
  envelope := envelope_706_i2
  height := height_706_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_706_i2
def height_706_i3 : ℕ := 4
def childrenH_706_i3 : Fin 2 → ℕ := ![height_154, height_159]
theorem height_exact_706_i3 : height_706_i3 = 1 + Finset.univ.sup childrenH_706_i3 := by decide +kernel
theorem required_origin_706_i3 : ∀ x ∈ required_706_i3,
    (∃ j, x ∈ childrenC_706_i3 j) ∨ ∀ j, x ∈ childrenD_706_i3 j := by decide +kernel
theorem required_exact_706_i3 : required_706_i3 =
    ((Finset.univ.biUnion childrenC_706_i3) ∪ commonEnvelope childrenD_706_i3).erase (5, 3) := by
  exact required_eq_combination childrenC_706_i3 childrenD_706_i3 (5, 3) required_706_i3
    (by decide +kernel) child_required_sub_706_i3 common_sub_706_i3 required_origin_706_i3
theorem envelope_origin_706_i3 : ∀ x ∈ envelope_706_i3,
    x = (5, 3) ∨ ∃ j, x ∈ childrenD_706_i3 j := by decide +kernel
theorem envelope_exact_706_i3 : envelope_706_i3 =
    insert (5, 3) (Finset.univ.biUnion childrenD_706_i3) := by
  exact envelope_eq_combination childrenD_706_i3 (5, 3) envelope_706_i3
    pivot_mem_706_i3 child_envelope_sub_706_i3 envelope_origin_706_i3
def checked_706_i3 : CheckedCard where
  required := required_706_i3
  envelope := envelope_706_i3
  height := height_706_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_706_i3
def height_706_i4 : ℕ := 7
def childrenH_706_i4 : Fin 3 → ℕ := ![height_22, height_152, height_166]
theorem height_exact_706_i4 : height_706_i4 = 1 + Finset.univ.sup childrenH_706_i4 := by decide +kernel
theorem required_origin_706_i4 : ∀ x ∈ required_706_i4,
    (∃ j, x ∈ childrenC_706_i4 j) ∨ ∀ j, x ∈ childrenD_706_i4 j := by decide +kernel
theorem required_exact_706_i4 : required_706_i4 =
    ((Finset.univ.biUnion childrenC_706_i4) ∪ commonEnvelope childrenD_706_i4).erase (7, 5) := by
  exact required_eq_combination childrenC_706_i4 childrenD_706_i4 (7, 5) required_706_i4
    (by decide +kernel) child_required_sub_706_i4 common_sub_706_i4 required_origin_706_i4
theorem envelope_origin_706_i4 : ∀ x ∈ envelope_706_i4,
    x = (7, 5) ∨ ∃ j, x ∈ childrenD_706_i4 j := by decide +kernel
theorem envelope_exact_706_i4 : envelope_706_i4 =
    insert (7, 5) (Finset.univ.biUnion childrenD_706_i4) := by
  exact envelope_eq_combination childrenD_706_i4 (7, 5) envelope_706_i4
    pivot_mem_706_i4 child_envelope_sub_706_i4 envelope_origin_706_i4
def checked_706_i4 : CheckedCard where
  required := required_706_i4
  envelope := envelope_706_i4
  height := height_706_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_706_i4
def height_706_i1 : ℕ := 8
def childrenH_706_i1 : Fin 4 → ℕ := ![height_261, height_706_i2, height_706_i3, height_706_i4]
theorem height_exact_706_i1 : height_706_i1 = 1 + Finset.univ.sup childrenH_706_i1 := by decide +kernel
theorem required_origin_706_i1 : ∀ x ∈ required_706_i1,
    (∃ j, x ∈ childrenC_706_i1 j) ∨ ∀ j, x ∈ childrenD_706_i1 j := by decide +kernel
theorem required_exact_706_i1 : required_706_i1 =
    ((Finset.univ.biUnion childrenC_706_i1) ∪ commonEnvelope childrenD_706_i1).erase (7, 3) := by
  exact required_eq_combination childrenC_706_i1 childrenD_706_i1 (7, 3) required_706_i1
    (by decide +kernel) child_required_sub_706_i1 common_sub_706_i1 required_origin_706_i1
theorem envelope_origin_706_i1 : ∀ x ∈ envelope_706_i1,
    x = (7, 3) ∨ ∃ j, x ∈ childrenD_706_i1 j := by decide +kernel
theorem envelope_exact_706_i1 : envelope_706_i1 =
    insert (7, 3) (Finset.univ.biUnion childrenD_706_i1) := by
  exact envelope_eq_combination childrenD_706_i1 (7, 3) envelope_706_i1
    pivot_mem_706_i1 child_envelope_sub_706_i1 envelope_origin_706_i1
def checked_706_i1 : CheckedCard where
  required := required_706_i1
  envelope := envelope_706_i1
  height := height_706_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_706_i1
def height_706_i0 : ℕ := 9
def childrenH_706_i0 : Fin 3 → ℕ := ![height_15, height_65, height_706_i1]
theorem height_exact_706_i0 : height_706_i0 = 1 + Finset.univ.sup childrenH_706_i0 := by decide +kernel
theorem required_origin_706_i0 : ∀ x ∈ required_706_i0,
    (∃ j, x ∈ childrenC_706_i0 j) ∨ ∀ j, x ∈ childrenD_706_i0 j := by decide +kernel
theorem required_exact_706_i0 : required_706_i0 =
    ((Finset.univ.biUnion childrenC_706_i0) ∪ commonEnvelope childrenD_706_i0).erase (3, 4) := by
  exact required_eq_combination childrenC_706_i0 childrenD_706_i0 (3, 4) required_706_i0
    (by decide +kernel) child_required_sub_706_i0 common_sub_706_i0 required_origin_706_i0
theorem envelope_origin_706_i0 : ∀ x ∈ envelope_706_i0,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_706_i0 j := by decide +kernel
theorem envelope_exact_706_i0 : envelope_706_i0 =
    insert (3, 4) (Finset.univ.biUnion childrenD_706_i0) := by
  exact envelope_eq_combination childrenD_706_i0 (3, 4) envelope_706_i0
    pivot_mem_706_i0 child_envelope_sub_706_i0 envelope_origin_706_i0
def checked_706_i0 : CheckedCard where
  required := required_706_i0
  envelope := envelope_706_i0
  height := height_706_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_706_i0
def height_706_i6 : ℕ := 8
def childrenH_706_i6 : Fin 3 → ℕ := ![height_318, height_334, height_379]
theorem height_exact_706_i6 : height_706_i6 = 1 + Finset.univ.sup childrenH_706_i6 := by decide +kernel
theorem required_origin_706_i6 : ∀ x ∈ required_706_i6,
    (∃ j, x ∈ childrenC_706_i6 j) ∨ ∀ j, x ∈ childrenD_706_i6 j := by decide +kernel
theorem required_exact_706_i6 : required_706_i6 =
    ((Finset.univ.biUnion childrenC_706_i6) ∪ commonEnvelope childrenD_706_i6).erase (3, 3) := by
  exact required_eq_combination childrenC_706_i6 childrenD_706_i6 (3, 3) required_706_i6
    (by decide +kernel) child_required_sub_706_i6 common_sub_706_i6 required_origin_706_i6
theorem envelope_origin_706_i6 : ∀ x ∈ envelope_706_i6,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_706_i6 j := by decide +kernel
theorem envelope_exact_706_i6 : envelope_706_i6 =
    insert (3, 3) (Finset.univ.biUnion childrenD_706_i6) := by
  exact envelope_eq_combination childrenD_706_i6 (3, 3) envelope_706_i6
    pivot_mem_706_i6 child_envelope_sub_706_i6 envelope_origin_706_i6
def checked_706_i6 : CheckedCard where
  required := required_706_i6
  envelope := envelope_706_i6
  height := height_706_i6
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_706_i6
def height_706_i7 : ℕ := 8
def childrenH_706_i7 : Fin 3 → ℕ := ![height_66, height_238, height_394]
theorem height_exact_706_i7 : height_706_i7 = 1 + Finset.univ.sup childrenH_706_i7 := by decide +kernel
theorem required_origin_706_i7 : ∀ x ∈ required_706_i7,
    (∃ j, x ∈ childrenC_706_i7 j) ∨ ∀ j, x ∈ childrenD_706_i7 j := by decide +kernel
theorem required_exact_706_i7 : required_706_i7 =
    ((Finset.univ.biUnion childrenC_706_i7) ∪ commonEnvelope childrenD_706_i7).erase (3, 4) := by
  exact required_eq_combination childrenC_706_i7 childrenD_706_i7 (3, 4) required_706_i7
    (by decide +kernel) child_required_sub_706_i7 common_sub_706_i7 required_origin_706_i7
theorem envelope_origin_706_i7 : ∀ x ∈ envelope_706_i7,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_706_i7 j := by decide +kernel
theorem envelope_exact_706_i7 : envelope_706_i7 =
    insert (3, 4) (Finset.univ.biUnion childrenD_706_i7) := by
  exact envelope_eq_combination childrenD_706_i7 (3, 4) envelope_706_i7
    pivot_mem_706_i7 child_envelope_sub_706_i7 envelope_origin_706_i7
def checked_706_i7 : CheckedCard where
  required := required_706_i7
  envelope := envelope_706_i7
  height := height_706_i7
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_706_i7
def height_706_i5 : ℕ := 9
def childrenH_706_i5 : Fin 6 → ℕ := ![height_417, height_420, height_526, height_532, height_706_i6, height_706_i7]
theorem height_exact_706_i5 : height_706_i5 = 1 + Finset.univ.sup childrenH_706_i5 := by decide +kernel
theorem required_origin_706_i5 : ∀ x ∈ required_706_i5,
    (∃ j, x ∈ childrenC_706_i5 j) ∨ ∀ j, x ∈ childrenD_706_i5 j := by decide +kernel
theorem required_exact_706_i5 : required_706_i5 =
    ((Finset.univ.biUnion childrenC_706_i5) ∪ commonEnvelope childrenD_706_i5).erase (5, 3) := by
  exact required_eq_combination childrenC_706_i5 childrenD_706_i5 (5, 3) required_706_i5
    (by decide +kernel) child_required_sub_706_i5 common_sub_706_i5 required_origin_706_i5
theorem envelope_origin_706_i5 : ∀ x ∈ envelope_706_i5,
    x = (5, 3) ∨ ∃ j, x ∈ childrenD_706_i5 j := by decide +kernel
theorem envelope_exact_706_i5 : envelope_706_i5 =
    insert (5, 3) (Finset.univ.biUnion childrenD_706_i5) := by
  exact envelope_eq_combination childrenD_706_i5 (5, 3) envelope_706_i5
    pivot_mem_706_i5 child_envelope_sub_706_i5 envelope_origin_706_i5
def checked_706_i5 : CheckedCard where
  required := required_706_i5
  envelope := envelope_706_i5
  height := height_706_i5
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_706_i5
def height_706_i9 : ℕ := 14
def childrenH_706_i9 : Fin 4 → ℕ := ![height_30, height_59, height_296, height_603]
theorem height_exact_706_i9 : height_706_i9 = 1 + Finset.univ.sup childrenH_706_i9 := by decide +kernel
theorem required_origin_706_i9 : ∀ x ∈ required_706_i9,
    (∃ j, x ∈ childrenC_706_i9 j) ∨ ∀ j, x ∈ childrenD_706_i9 j := by decide +kernel
theorem required_exact_706_i9 : required_706_i9 =
    ((Finset.univ.biUnion childrenC_706_i9) ∪ commonEnvelope childrenD_706_i9).erase (7, 4) := by
  exact required_eq_combination childrenC_706_i9 childrenD_706_i9 (7, 4) required_706_i9
    (by decide +kernel) child_required_sub_706_i9 common_sub_706_i9 required_origin_706_i9
theorem envelope_origin_706_i9 : ∀ x ∈ envelope_706_i9,
    x = (7, 4) ∨ ∃ j, x ∈ childrenD_706_i9 j := by decide +kernel
theorem envelope_exact_706_i9 : envelope_706_i9 =
    insert (7, 4) (Finset.univ.biUnion childrenD_706_i9) := by
  exact envelope_eq_combination childrenD_706_i9 (7, 4) envelope_706_i9
    pivot_mem_706_i9 child_envelope_sub_706_i9 envelope_origin_706_i9
def checked_706_i9 : CheckedCard where
  required := required_706_i9
  envelope := envelope_706_i9
  height := height_706_i9
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_706_i9
def height_706_i8 : ℕ := 15
def childrenH_706_i8 : Fin 4 → ℕ := ![height_22, height_74, height_325, height_706_i9]
theorem height_exact_706_i8 : height_706_i8 = 1 + Finset.univ.sup childrenH_706_i8 := by decide +kernel
theorem required_origin_706_i8 : ∀ x ∈ required_706_i8,
    (∃ j, x ∈ childrenC_706_i8 j) ∨ ∀ j, x ∈ childrenD_706_i8 j := by decide +kernel
theorem required_exact_706_i8 : required_706_i8 =
    ((Finset.univ.biUnion childrenC_706_i8) ∪ commonEnvelope childrenD_706_i8).erase (7, 5) := by
  exact required_eq_combination childrenC_706_i8 childrenD_706_i8 (7, 5) required_706_i8
    (by decide +kernel) child_required_sub_706_i8 common_sub_706_i8 required_origin_706_i8
theorem envelope_origin_706_i8 : ∀ x ∈ envelope_706_i8,
    x = (7, 5) ∨ ∃ j, x ∈ childrenD_706_i8 j := by decide +kernel
theorem envelope_exact_706_i8 : envelope_706_i8 =
    insert (7, 5) (Finset.univ.biUnion childrenD_706_i8) := by
  exact envelope_eq_combination childrenD_706_i8 (7, 5) envelope_706_i8
    pivot_mem_706_i8 child_envelope_sub_706_i8 envelope_origin_706_i8
def checked_706_i8 : CheckedCard where
  required := required_706_i8
  envelope := envelope_706_i8
  height := height_706_i8
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_706_i8
def height_706 : ℕ := 16
def childrenH_706 : Fin 7 → ℕ := ![height_512, height_517, height_527, height_537, height_706_i0, height_706_i5, height_706_i8]
theorem height_exact_706 : height_706 = 1 + Finset.univ.sup childrenH_706 := by decide +kernel
theorem required_origin_706 : ∀ x ∈ required_706,
    (∃ j, x ∈ childrenC_706 j) ∨ ∀ j, x ∈ childrenD_706 j := by decide +kernel
theorem required_exact_706 : required_706 =
    ((Finset.univ.biUnion childrenC_706) ∪ commonEnvelope childrenD_706).erase (4, 4) := by
  exact required_eq_combination childrenC_706 childrenD_706 (4, 4) required_706
    (by decide +kernel) child_required_sub_706 common_sub_706 required_origin_706
theorem envelope_origin_706 : ∀ x ∈ envelope_706,
    x = (4, 4) ∨ ∃ j, x ∈ childrenD_706 j := by decide +kernel
theorem envelope_exact_706 : envelope_706 =
    insert (4, 4) (Finset.univ.biUnion childrenD_706) := by
  exact envelope_eq_combination childrenD_706 (4, 4) envelope_706
    pivot_mem_706 child_envelope_sub_706 envelope_origin_706
def checked_706 : CheckedCard where
  required := required_706
  envelope := envelope_706
  height := height_706
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_706
end SnakyPrototype.Certificate21

end OAI
