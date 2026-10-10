import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part06
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height10Part06
import OAI.GameTheory.SnakyTwentyOne.Cards.Height12Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height12Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height13Part07
import OAI.GameTheory.SnakyTwentyOne.Cards.Height15Part04
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_724_i0 : Finset Cell := ⟨(([(5, 7), (5, 8), (6, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_724_i0 : Finset Cell := ⟨(([(0, 7), (1, 7), (1, 8), (1, 9), (2, 7), (2, 8), (2, 9), (3, 8), (3, 9), (4, 7), (4, 8), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (6, 12), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (8, 7), (8, 8), (8, 9), (8, 10), (8, 11), (8, 12), (9, 7), (9, 8), (9, 9), (9, 10), (10, 7), (10, 10)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_724_i0 : Fin 4 → Finset Cell := ![(placed21 0 (3, 5) required_57), (placed21 2 (7, 5) required_111), (placed21 5 (10, 7) required_390), (placed21 0 (4, 5) required_397)]
def childrenD_724_i0 : Fin 4 → Finset Cell := ![(placed21 0 (3, 5) envelope_57), (placed21 2 (7, 5) envelope_111), (placed21 5 (10, 7) envelope_390), (placed21 0 (4, 5) envelope_397)]
theorem common_sub_724_i0 : commonEnvelope childrenD_724_i0 ⊆ insert (4, 8) required_724_i0 := by decide +kernel
theorem child_required_sub_724_i0 : ∀ j, childrenC_724_i0 j ⊆ insert (4, 8) required_724_i0 := by decide +kernel
theorem child_envelope_sub_724_i0 : ∀ j, childrenD_724_i0 j ⊆ envelope_724_i0 := by decide +kernel
theorem pivot_mem_724_i0 : (4, 8) ∈ envelope_724_i0 := by decide +kernel
theorem children_work_724_i0 : ∀ j, Template HasSnaky 9 (childrenC_724_i0 j) (childrenD_724_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_57 0 (3, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_111 2 (7, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_390 5 (10, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_397 0 (4, 5)).mono (by decide +kernel)
theorem row_works_724_i0 : Template HasSnaky 10 required_724_i0 envelope_724_i0 := by
  refine compose HasSnaky 9 childrenC_724_i0 childrenD_724_i0 children_work_724_i0 (4, 8)
    required_724_i0 envelope_724_i0 pivot_mem_724_i0 child_required_sub_724_i0 child_envelope_sub_724_i0 ?_
  intro b hb
  exact common_sub_724_i0 (mem_commonEnvelope childrenD_724_i0 b hb)
def required_724_i2 : Finset Cell := ⟨(([(5, 8), (6, 8), (7, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_724_i2 : Finset Cell := ⟨(([(1, 7), (1, 9), (2, 7), (2, 8), (2, 9), (3, 7), (3, 8), (3, 9), (4, 8), (5, 8), (5, 9), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (6, 12), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (8, 7), (8, 9), (8, 10), (8, 11), (8, 12), (9, 10), (10, 10)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_724_i2 : Fin 3 → Finset Cell := ![(placed21 5 (8, 7) required_19), (placed21 7 (8, 9) required_19), (placed21 0 (4, 6) required_395)]
def childrenD_724_i2 : Fin 3 → Finset Cell := ![(placed21 5 (8, 7) envelope_19), (placed21 7 (8, 9) envelope_19), (placed21 0 (4, 6) envelope_395)]
theorem common_sub_724_i2 : commonEnvelope childrenD_724_i2 ⊆ insert (4, 8) required_724_i2 := by decide +kernel
theorem child_required_sub_724_i2 : ∀ j, childrenC_724_i2 j ⊆ insert (4, 8) required_724_i2 := by decide +kernel
theorem child_envelope_sub_724_i2 : ∀ j, childrenD_724_i2 j ⊆ envelope_724_i2 := by decide +kernel
theorem pivot_mem_724_i2 : (4, 8) ∈ envelope_724_i2 := by decide +kernel
theorem children_work_724_i2 : ∀ j, Template HasSnaky 8 (childrenC_724_i2 j) (childrenD_724_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_19 5 (8, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_19 7 (8, 9)).mono (by decide +kernel)
  · exact (placed21_template row_works_395 0 (4, 6)).mono (by decide +kernel)
theorem row_works_724_i2 : Template HasSnaky 9 required_724_i2 envelope_724_i2 := by
  refine compose HasSnaky 8 childrenC_724_i2 childrenD_724_i2 children_work_724_i2 (4, 8)
    required_724_i2 envelope_724_i2 pivot_mem_724_i2 child_required_sub_724_i2 child_envelope_sub_724_i2 ?_
  intro b hb
  exact common_sub_724_i2 (mem_commonEnvelope childrenD_724_i2 b hb)
def required_724_i3 : Finset Cell := ⟨(([(5, 7), (5, 8), (6, 8), (7, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_724_i3 : Finset Cell := ⟨(([(1, 7), (1, 9), (2, 7), (2, 8), (2, 9), (3, 7), (3, 8), (3, 9), (4, 8), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (7, 7), (7, 8), (7, 9), (8, 7), (8, 8), (9, 7), (9, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_724_i3 : Fin 3 → Finset Cell := ![(placed21 5 (8, 7) required_19), (placed21 2 (7, 5) required_231), (placed21 0 (4, 5) required_279)]
def childrenD_724_i3 : Fin 3 → Finset Cell := ![(placed21 5 (8, 7) envelope_19), (placed21 2 (7, 5) envelope_231), (placed21 0 (4, 5) envelope_279)]
theorem common_sub_724_i3 : commonEnvelope childrenD_724_i3 ⊆ insert (4, 8) required_724_i3 := by decide +kernel
theorem child_required_sub_724_i3 : ∀ j, childrenC_724_i3 j ⊆ insert (4, 8) required_724_i3 := by decide +kernel
theorem child_envelope_sub_724_i3 : ∀ j, childrenD_724_i3 j ⊆ envelope_724_i3 := by decide +kernel
theorem pivot_mem_724_i3 : (4, 8) ∈ envelope_724_i3 := by decide +kernel
theorem children_work_724_i3 : ∀ j, Template HasSnaky 5 (childrenC_724_i3 j) (childrenD_724_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_19 5 (8, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_231 2 (7, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_279 0 (4, 5)).mono (by decide +kernel)
theorem row_works_724_i3 : Template HasSnaky 6 required_724_i3 envelope_724_i3 := by
  refine compose HasSnaky 5 childrenC_724_i3 childrenD_724_i3 children_work_724_i3 (4, 8)
    required_724_i3 envelope_724_i3 pivot_mem_724_i3 child_required_sub_724_i3 child_envelope_sub_724_i3 ?_
  intro b hb
  exact common_sub_724_i3 (mem_commonEnvelope childrenD_724_i3 b hb)
def required_724_i4 : Finset Cell := ⟨(([(5, 7), (5, 8), (6, 8), (7, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_724_i4 : Finset Cell := ⟨(([(4, 8), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, 8), (8, 9), (8, 10), (8, 11), (9, 7), (9, 8), (9, 9), (9, 10), (10, 7), (10, 8), (10, 9), (10, 10), (11, 7), (11, 10)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_724_i4 : Fin 2 → Finset Cell := ![(placed21 6 (6, 11) required_53), (placed21 0 (4, 6) required_637)]
def childrenD_724_i4 : Fin 2 → Finset Cell := ![(placed21 6 (6, 11) envelope_53), (placed21 0 (4, 6) envelope_637)]
theorem common_sub_724_i4 : commonEnvelope childrenD_724_i4 ⊆ insert (6, 9) required_724_i4 := by decide +kernel
theorem child_required_sub_724_i4 : ∀ j, childrenC_724_i4 j ⊆ insert (6, 9) required_724_i4 := by decide +kernel
theorem child_envelope_sub_724_i4 : ∀ j, childrenD_724_i4 j ⊆ envelope_724_i4 := by decide +kernel
theorem pivot_mem_724_i4 : (6, 9) ∈ envelope_724_i4 := by decide +kernel
theorem children_work_724_i4 : ∀ j, Template HasSnaky 7 (childrenC_724_i4 j) (childrenD_724_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_53 6 (6, 11)).mono (by decide +kernel)
  · exact (placed21_template row_works_637 0 (4, 6)).mono (by decide +kernel)
theorem row_works_724_i4 : Template HasSnaky 8 required_724_i4 envelope_724_i4 := by
  refine compose HasSnaky 7 childrenC_724_i4 childrenD_724_i4 children_work_724_i4 (6, 9)
    required_724_i4 envelope_724_i4 pivot_mem_724_i4 child_required_sub_724_i4 child_envelope_sub_724_i4 ?_
  intro b hb
  exact common_sub_724_i4 (mem_commonEnvelope childrenD_724_i4 b hb)
def required_724_i1 : Finset Cell := ⟨(([(5, 7), (5, 8), (6, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_724_i1 : Finset Cell := ⟨(([(1, 7), (1, 9), (2, 7), (2, 8), (2, 9), (3, 7), (3, 8), (3, 9), (4, 8), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (6, 12), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (8, 11), (8, 12), (9, 7), (9, 8), (9, 9), (9, 10), (9, 11), (9, 12), (10, 7), (10, 8), (10, 9), (10, 10), (11, 7), (11, 9), (11, 10)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_724_i1 : Fin 6 → Finset Cell := ![(placed21 1 (3, 6) required_188), (placed21 3 (3, 10) required_188), (placed21 0 (5, 5) required_258), required_724_i2, required_724_i3, required_724_i4]
def childrenD_724_i1 : Fin 6 → Finset Cell := ![(placed21 1 (3, 6) envelope_188), (placed21 3 (3, 10) envelope_188), (placed21 0 (5, 5) envelope_258), envelope_724_i2, envelope_724_i3, envelope_724_i4]
theorem common_sub_724_i1 : commonEnvelope childrenD_724_i1 ⊆ insert (7, 8) required_724_i1 := by decide +kernel
theorem child_required_sub_724_i1 : ∀ j, childrenC_724_i1 j ⊆ insert (7, 8) required_724_i1 := by decide +kernel
theorem child_envelope_sub_724_i1 : ∀ j, childrenD_724_i1 j ⊆ envelope_724_i1 := by decide +kernel
theorem pivot_mem_724_i1 : (7, 8) ∈ envelope_724_i1 := by decide +kernel
theorem children_work_724_i1 : ∀ j, Template HasSnaky 9 (childrenC_724_i1 j) (childrenD_724_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_188 1 (3, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_188 3 (3, 10)).mono (by decide +kernel)
  · exact (placed21_template row_works_258 0 (5, 5)).mono (by decide +kernel)
  · exact row_works_724_i2.mono (by decide +kernel)
  · exact row_works_724_i3.mono (by decide +kernel)
  · exact row_works_724_i4.mono (by decide +kernel)
theorem row_works_724_i1 : Template HasSnaky 10 required_724_i1 envelope_724_i1 := by
  refine compose HasSnaky 9 childrenC_724_i1 childrenD_724_i1 children_work_724_i1 (7, 8)
    required_724_i1 envelope_724_i1 pivot_mem_724_i1 child_required_sub_724_i1 child_envelope_sub_724_i1 ?_
  intro b hb
  exact common_sub_724_i1 (mem_commonEnvelope childrenD_724_i1 b hb)
def required_724_i5 : Finset Cell := ⟨(([(5, 7), (5, 8), (6, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_724_i5 : Finset Cell := ⟨(([(0, 4), (0, 6), (0, 11), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 9), (1, 10), (1, 11), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 9), (2, 10), (2, 11), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 9), (3, 10), (3, 11), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 10), (4, 11), (4, 12), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (6, 3), (6, 4), (6, 5), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (6, 12), (6, 13), (6, 14), (6, 15), (7, 4), (7, 5), (7, 6), (7, 8), (7, 9), (7, 10), (7, 11), (7, 12), (7, 13), (7, 14), (8, 4), (8, 5), (8, 6), (8, 8), (8, 9), (8, 10), (8, 11), (8, 12), (8, 13), (8, 14), (9, 4), (9, 5), (9, 6), (9, 9), (9, 10), (9, 11), (9, 12), (9, 13), (10, 4), (10, 9), (10, 11)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_724_i5 : Fin 4 → Finset Cell := ![(placed21 7 (8, 8) required_53), (placed21 1 (2, 7) required_53), (placed21 7 (10, 12) required_720), (placed21 1 (0, 3) required_720)]
def childrenD_724_i5 : Fin 4 → Finset Cell := ![(placed21 7 (8, 8) envelope_53), (placed21 1 (2, 7) envelope_53), (placed21 7 (10, 12) envelope_720), (placed21 1 (0, 3) envelope_720)]
theorem common_sub_724_i5 : commonEnvelope childrenD_724_i5 ⊆ insert (4, 7) required_724_i5 := by decide +kernel
theorem child_required_sub_724_i5 : ∀ j, childrenC_724_i5 j ⊆ insert (4, 7) required_724_i5 := by decide +kernel
theorem child_envelope_sub_724_i5 : ∀ j, childrenD_724_i5 j ⊆ envelope_724_i5 := by decide +kernel
theorem pivot_mem_724_i5 : (4, 7) ∈ envelope_724_i5 := by decide +kernel
theorem children_work_724_i5 : ∀ j, Template HasSnaky 13 (childrenC_724_i5 j) (childrenD_724_i5 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_53 7 (8, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_53 1 (2, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_720 7 (10, 12)).mono (by decide +kernel)
  · exact (placed21_template row_works_720 1 (0, 3)).mono (by decide +kernel)
theorem row_works_724_i5 : Template HasSnaky 14 required_724_i5 envelope_724_i5 := by
  refine compose HasSnaky 13 childrenC_724_i5 childrenD_724_i5 children_work_724_i5 (4, 7)
    required_724_i5 envelope_724_i5 pivot_mem_724_i5 child_required_sub_724_i5 child_envelope_sub_724_i5 ?_
  intro b hb
  exact common_sub_724_i5 (mem_commonEnvelope childrenD_724_i5 b hb)
def required_724_i6 : Finset Cell := ⟨(([(5, 7), (5, 8), (6, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_724_i6 : Finset Cell := ⟨(([(2, 6), (2, 7), (3, 6), (3, 7), (3, 11), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 10), (4, 11), (4, 12), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (7, 12), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (8, 11), (8, 12), (8, 13), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (9, 10), (9, 11), (9, 12), (10, 9), (10, 10), (10, 11)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_724_i6 : Fin 5 → Finset Cell := ![(placed21 0 (4, 4) required_512), (placed21 3 (2, 10) required_600), (placed21 6 (9, 11) required_621), (placed21 1 (3, 6) required_702), (placed21 2 (8, 3) required_714)]
def childrenD_724_i6 : Fin 5 → Finset Cell := ![(placed21 0 (4, 4) envelope_512), (placed21 3 (2, 10) envelope_600), (placed21 6 (9, 11) envelope_621), (placed21 1 (3, 6) envelope_702), (placed21 2 (8, 3) envelope_714)]
theorem common_sub_724_i6 : commonEnvelope childrenD_724_i6 ⊆ insert (6, 7) required_724_i6 := by decide +kernel
theorem child_required_sub_724_i6 : ∀ j, childrenC_724_i6 j ⊆ insert (6, 7) required_724_i6 := by decide +kernel
theorem child_envelope_sub_724_i6 : ∀ j, childrenD_724_i6 j ⊆ envelope_724_i6 := by decide +kernel
theorem pivot_mem_724_i6 : (6, 7) ∈ envelope_724_i6 := by decide +kernel
theorem children_work_724_i6 : ∀ j, Template HasSnaky 10 (childrenC_724_i6 j) (childrenD_724_i6 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_512 0 (4, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_600 3 (2, 10)).mono (by decide +kernel)
  · exact (placed21_template row_works_621 6 (9, 11)).mono (by decide +kernel)
  · exact (placed21_template row_works_702 1 (3, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_714 2 (8, 3)).mono (by decide +kernel)
theorem row_works_724_i6 : Template HasSnaky 11 required_724_i6 envelope_724_i6 := by
  refine compose HasSnaky 10 childrenC_724_i6 childrenD_724_i6 children_work_724_i6 (6, 7)
    required_724_i6 envelope_724_i6 pivot_mem_724_i6 child_required_sub_724_i6 child_envelope_sub_724_i6 ?_
  intro b hb
  exact common_sub_724_i6 (mem_commonEnvelope childrenD_724_i6 b hb)
def required_724_i8 : Finset Cell := ⟨(([(4, 8), (5, 8), (6, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_724_i8 : Finset Cell := ⟨(([(3, 7), (4, 7), (4, 8), (5, 7), (5, 8), (5, 9), (6, 8), (6, 9), (6, 10), (6, 11), (6, 12), (6, 13), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (7, 12), (8, 7), (8, 8), (8, 9), (8, 10), (8, 11), (8, 12), (9, 7), (9, 9), (9, 10), (10, 10)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_724_i8 : Fin 3 → Finset Cell := ![(placed21 3 (3, 8) required_7), (placed21 1 (3, 7) required_9), (placed21 0 (4, 5) required_604)]
def childrenD_724_i8 : Fin 3 → Finset Cell := ![(placed21 3 (3, 8) envelope_7), (placed21 1 (3, 7) envelope_9), (placed21 0 (4, 5) envelope_604)]
theorem common_sub_724_i8 : commonEnvelope childrenD_724_i8 ⊆ insert (7, 8) required_724_i8 := by decide +kernel
theorem child_required_sub_724_i8 : ∀ j, childrenC_724_i8 j ⊆ insert (7, 8) required_724_i8 := by decide +kernel
theorem child_envelope_sub_724_i8 : ∀ j, childrenD_724_i8 j ⊆ envelope_724_i8 := by decide +kernel
theorem pivot_mem_724_i8 : (7, 8) ∈ envelope_724_i8 := by decide +kernel
theorem children_work_724_i8 : ∀ j, Template HasSnaky 8 (childrenC_724_i8 j) (childrenD_724_i8 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 3 (3, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_9 1 (3, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_604 0 (4, 5)).mono (by decide +kernel)
theorem row_works_724_i8 : Template HasSnaky 9 required_724_i8 envelope_724_i8 := by
  refine compose HasSnaky 8 childrenC_724_i8 childrenD_724_i8 children_work_724_i8 (7, 8)
    required_724_i8 envelope_724_i8 pivot_mem_724_i8 child_required_sub_724_i8 child_envelope_sub_724_i8 ?_
  intro b hb
  exact common_sub_724_i8 (mem_commonEnvelope childrenD_724_i8 b hb)
def required_724_i7 : Finset Cell := ⟨(([(5, 7), (5, 8), (6, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_724_i7 : Finset Cell := ⟨(([(0, 7), (1, 7), (1, 8), (1, 9), (2, 7), (2, 8), (2, 9), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (4, 6), (4, 7), (4, 8), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 8), (6, 9), (6, 10), (6, 11), (6, 12), (6, 13), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (7, 12), (8, 7), (8, 8), (8, 9), (8, 10), (8, 11), (8, 12), (9, 7), (9, 9), (9, 10), (10, 10)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_724_i7 : Fin 4 → Finset Cell := ![(placed21 0 (3, 5) required_88), (placed21 2 (7, 5) required_231), (placed21 5 (8, 6) required_267), required_724_i8]
def childrenD_724_i7 : Fin 4 → Finset Cell := ![(placed21 0 (3, 5) envelope_88), (placed21 2 (7, 5) envelope_231), (placed21 5 (8, 6) envelope_267), envelope_724_i8]
theorem common_sub_724_i7 : commonEnvelope childrenD_724_i7 ⊆ insert (4, 8) required_724_i7 := by decide +kernel
theorem child_required_sub_724_i7 : ∀ j, childrenC_724_i7 j ⊆ insert (4, 8) required_724_i7 := by decide +kernel
theorem child_envelope_sub_724_i7 : ∀ j, childrenD_724_i7 j ⊆ envelope_724_i7 := by decide +kernel
theorem pivot_mem_724_i7 : (4, 8) ∈ envelope_724_i7 := by decide +kernel
theorem children_work_724_i7 : ∀ j, Template HasSnaky 9 (childrenC_724_i7 j) (childrenD_724_i7 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_88 0 (3, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_231 2 (7, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_267 5 (8, 6)).mono (by decide +kernel)
  · exact row_works_724_i8.mono (by decide +kernel)
theorem row_works_724_i7 : Template HasSnaky 10 required_724_i7 envelope_724_i7 := by
  refine compose HasSnaky 9 childrenC_724_i7 childrenD_724_i7 children_work_724_i7 (4, 8)
    required_724_i7 envelope_724_i7 pivot_mem_724_i7 child_required_sub_724_i7 child_envelope_sub_724_i7 ?_
  intro b hb
  exact common_sub_724_i7 (mem_commonEnvelope childrenD_724_i7 b hb)
def required_724 : Finset Cell := ⟨(([(5, 7), (5, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_724 : Finset Cell := ⟨(([(0, 4), (0, 5), (0, 6), (0, 7), (0, 11), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 10), (4, 11), (4, 12), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (5, 12), (6, 3), (6, 4), (6, 5), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (6, 12), (6, 13), (6, 14), (6, 15), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (7, 12), (7, 13), (7, 14), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (8, 11), (8, 12), (8, 13), (8, 14), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (9, 10), (9, 11), (9, 12), (9, 13), (10, 4), (10, 7), (10, 8), (10, 9), (10, 10), (10, 11), (11, 7), (11, 9), (11, 10), (11, 11)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_724 : Fin 10 → Finset Cell := ![(placed21 5 (9, 5) required_523), (placed21 5 (9, 5) required_524), (placed21 1 (1, 5) required_677), required_724_i0, required_724_i1, (placed21 7 (10, 10) required_719), required_724_i5, required_724_i6, required_724_i7, (placed21 6 (8, 13) required_723)]
def childrenD_724 : Fin 10 → Finset Cell := ![(placed21 5 (9, 5) envelope_523), (placed21 5 (9, 5) envelope_524), (placed21 1 (1, 5) envelope_677), envelope_724_i0, envelope_724_i1, (placed21 7 (10, 10) envelope_719), envelope_724_i5, envelope_724_i6, envelope_724_i7, (placed21 6 (8, 13) envelope_723)]
theorem common_sub_724 : commonEnvelope childrenD_724 ⊆ insert (6, 8) required_724 := by decide +kernel
theorem child_required_sub_724 : ∀ j, childrenC_724 j ⊆ insert (6, 8) required_724 := by decide +kernel
theorem child_envelope_sub_724 : ∀ j, childrenD_724 j ⊆ envelope_724 := by decide +kernel
theorem pivot_mem_724 : (6, 8) ∈ envelope_724 := by decide +kernel
theorem children_work_724 : ∀ j, Template HasSnaky 15 (childrenC_724 j) (childrenD_724 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_523 5 (9, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_524 5 (9, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_677 1 (1, 5)).mono (by decide +kernel)
  · exact row_works_724_i0.mono (by decide +kernel)
  · exact row_works_724_i1.mono (by decide +kernel)
  · exact (placed21_template row_works_719 7 (10, 10)).mono (by decide +kernel)
  · exact row_works_724_i5.mono (by decide +kernel)
  · exact row_works_724_i6.mono (by decide +kernel)
  · exact row_works_724_i7.mono (by decide +kernel)
  · exact (placed21_template row_works_723 6 (8, 13)).mono (by decide +kernel)
theorem row_works_724 : Template HasSnaky 16 required_724 envelope_724 := by
  refine compose HasSnaky 15 childrenC_724 childrenD_724 children_work_724 (6, 8)
    required_724 envelope_724 pivot_mem_724 child_required_sub_724 child_envelope_sub_724 ?_
  intro b hb
  exact common_sub_724 (mem_commonEnvelope childrenD_724 b hb)
def height_724_i0 : ℕ := 10
def childrenH_724_i0 : Fin 4 → ℕ := ![height_57, height_111, height_390, height_397]
theorem height_exact_724_i0 : height_724_i0 = 1 + Finset.univ.sup childrenH_724_i0 := by decide +kernel
theorem required_origin_724_i0 : ∀ x ∈ required_724_i0,
    (∃ j, x ∈ childrenC_724_i0 j) ∨ ∀ j, x ∈ childrenD_724_i0 j := by decide +kernel
theorem required_exact_724_i0 : required_724_i0 =
    ((Finset.univ.biUnion childrenC_724_i0) ∪ commonEnvelope childrenD_724_i0).erase (4, 8) := by
  exact required_eq_combination childrenC_724_i0 childrenD_724_i0 (4, 8) required_724_i0
    (by decide +kernel) child_required_sub_724_i0 common_sub_724_i0 required_origin_724_i0
theorem envelope_origin_724_i0 : ∀ x ∈ envelope_724_i0,
    x = (4, 8) ∨ ∃ j, x ∈ childrenD_724_i0 j := by decide +kernel
theorem envelope_exact_724_i0 : envelope_724_i0 =
    insert (4, 8) (Finset.univ.biUnion childrenD_724_i0) := by
  exact envelope_eq_combination childrenD_724_i0 (4, 8) envelope_724_i0
    pivot_mem_724_i0 child_envelope_sub_724_i0 envelope_origin_724_i0
def checked_724_i0 : CheckedCard where
  required := required_724_i0
  envelope := envelope_724_i0
  height := height_724_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_724_i0
def height_724_i2 : ℕ := 9
def childrenH_724_i2 : Fin 3 → ℕ := ![height_19, height_19, height_395]
theorem height_exact_724_i2 : height_724_i2 = 1 + Finset.univ.sup childrenH_724_i2 := by decide +kernel
theorem required_origin_724_i2 : ∀ x ∈ required_724_i2,
    (∃ j, x ∈ childrenC_724_i2 j) ∨ ∀ j, x ∈ childrenD_724_i2 j := by decide +kernel
theorem required_exact_724_i2 : required_724_i2 =
    ((Finset.univ.biUnion childrenC_724_i2) ∪ commonEnvelope childrenD_724_i2).erase (4, 8) := by
  exact required_eq_combination childrenC_724_i2 childrenD_724_i2 (4, 8) required_724_i2
    (by decide +kernel) child_required_sub_724_i2 common_sub_724_i2 required_origin_724_i2
theorem envelope_origin_724_i2 : ∀ x ∈ envelope_724_i2,
    x = (4, 8) ∨ ∃ j, x ∈ childrenD_724_i2 j := by decide +kernel
theorem envelope_exact_724_i2 : envelope_724_i2 =
    insert (4, 8) (Finset.univ.biUnion childrenD_724_i2) := by
  exact envelope_eq_combination childrenD_724_i2 (4, 8) envelope_724_i2
    pivot_mem_724_i2 child_envelope_sub_724_i2 envelope_origin_724_i2
def checked_724_i2 : CheckedCard where
  required := required_724_i2
  envelope := envelope_724_i2
  height := height_724_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_724_i2
def height_724_i3 : ℕ := 6
def childrenH_724_i3 : Fin 3 → ℕ := ![height_19, height_231, height_279]
theorem height_exact_724_i3 : height_724_i3 = 1 + Finset.univ.sup childrenH_724_i3 := by decide +kernel
theorem required_origin_724_i3 : ∀ x ∈ required_724_i3,
    (∃ j, x ∈ childrenC_724_i3 j) ∨ ∀ j, x ∈ childrenD_724_i3 j := by decide +kernel
theorem required_exact_724_i3 : required_724_i3 =
    ((Finset.univ.biUnion childrenC_724_i3) ∪ commonEnvelope childrenD_724_i3).erase (4, 8) := by
  exact required_eq_combination childrenC_724_i3 childrenD_724_i3 (4, 8) required_724_i3
    (by decide +kernel) child_required_sub_724_i3 common_sub_724_i3 required_origin_724_i3
theorem envelope_origin_724_i3 : ∀ x ∈ envelope_724_i3,
    x = (4, 8) ∨ ∃ j, x ∈ childrenD_724_i3 j := by decide +kernel
theorem envelope_exact_724_i3 : envelope_724_i3 =
    insert (4, 8) (Finset.univ.biUnion childrenD_724_i3) := by
  exact envelope_eq_combination childrenD_724_i3 (4, 8) envelope_724_i3
    pivot_mem_724_i3 child_envelope_sub_724_i3 envelope_origin_724_i3
def checked_724_i3 : CheckedCard where
  required := required_724_i3
  envelope := envelope_724_i3
  height := height_724_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_724_i3
def height_724_i4 : ℕ := 8
def childrenH_724_i4 : Fin 2 → ℕ := ![height_53, height_637]
theorem height_exact_724_i4 : height_724_i4 = 1 + Finset.univ.sup childrenH_724_i4 := by decide +kernel
theorem required_origin_724_i4 : ∀ x ∈ required_724_i4,
    (∃ j, x ∈ childrenC_724_i4 j) ∨ ∀ j, x ∈ childrenD_724_i4 j := by decide +kernel
theorem required_exact_724_i4 : required_724_i4 =
    ((Finset.univ.biUnion childrenC_724_i4) ∪ commonEnvelope childrenD_724_i4).erase (6, 9) := by
  exact required_eq_combination childrenC_724_i4 childrenD_724_i4 (6, 9) required_724_i4
    (by decide +kernel) child_required_sub_724_i4 common_sub_724_i4 required_origin_724_i4
theorem envelope_origin_724_i4 : ∀ x ∈ envelope_724_i4,
    x = (6, 9) ∨ ∃ j, x ∈ childrenD_724_i4 j := by decide +kernel
theorem envelope_exact_724_i4 : envelope_724_i4 =
    insert (6, 9) (Finset.univ.biUnion childrenD_724_i4) := by
  exact envelope_eq_combination childrenD_724_i4 (6, 9) envelope_724_i4
    pivot_mem_724_i4 child_envelope_sub_724_i4 envelope_origin_724_i4
def checked_724_i4 : CheckedCard where
  required := required_724_i4
  envelope := envelope_724_i4
  height := height_724_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_724_i4
def height_724_i1 : ℕ := 10
def childrenH_724_i1 : Fin 6 → ℕ := ![height_188, height_188, height_258, height_724_i2, height_724_i3, height_724_i4]
theorem height_exact_724_i1 : height_724_i1 = 1 + Finset.univ.sup childrenH_724_i1 := by decide +kernel
theorem required_origin_724_i1 : ∀ x ∈ required_724_i1,
    (∃ j, x ∈ childrenC_724_i1 j) ∨ ∀ j, x ∈ childrenD_724_i1 j := by decide +kernel
theorem required_exact_724_i1 : required_724_i1 =
    ((Finset.univ.biUnion childrenC_724_i1) ∪ commonEnvelope childrenD_724_i1).erase (7, 8) := by
  exact required_eq_combination childrenC_724_i1 childrenD_724_i1 (7, 8) required_724_i1
    (by decide +kernel) child_required_sub_724_i1 common_sub_724_i1 required_origin_724_i1
theorem envelope_origin_724_i1 : ∀ x ∈ envelope_724_i1,
    x = (7, 8) ∨ ∃ j, x ∈ childrenD_724_i1 j := by decide +kernel
theorem envelope_exact_724_i1 : envelope_724_i1 =
    insert (7, 8) (Finset.univ.biUnion childrenD_724_i1) := by
  exact envelope_eq_combination childrenD_724_i1 (7, 8) envelope_724_i1
    pivot_mem_724_i1 child_envelope_sub_724_i1 envelope_origin_724_i1
def checked_724_i1 : CheckedCard where
  required := required_724_i1
  envelope := envelope_724_i1
  height := height_724_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_724_i1
def height_724_i5 : ℕ := 14
def childrenH_724_i5 : Fin 4 → ℕ := ![height_53, height_53, height_720, height_720]
theorem height_exact_724_i5 : height_724_i5 = 1 + Finset.univ.sup childrenH_724_i5 := by decide +kernel
theorem required_origin_724_i5 : ∀ x ∈ required_724_i5,
    (∃ j, x ∈ childrenC_724_i5 j) ∨ ∀ j, x ∈ childrenD_724_i5 j := by decide +kernel
theorem required_exact_724_i5 : required_724_i5 =
    ((Finset.univ.biUnion childrenC_724_i5) ∪ commonEnvelope childrenD_724_i5).erase (4, 7) := by
  exact required_eq_combination childrenC_724_i5 childrenD_724_i5 (4, 7) required_724_i5
    (by decide +kernel) child_required_sub_724_i5 common_sub_724_i5 required_origin_724_i5
theorem envelope_origin_724_i5 : ∀ x ∈ envelope_724_i5,
    x = (4, 7) ∨ ∃ j, x ∈ childrenD_724_i5 j := by decide +kernel
theorem envelope_exact_724_i5 : envelope_724_i5 =
    insert (4, 7) (Finset.univ.biUnion childrenD_724_i5) := by
  exact envelope_eq_combination childrenD_724_i5 (4, 7) envelope_724_i5
    pivot_mem_724_i5 child_envelope_sub_724_i5 envelope_origin_724_i5
def checked_724_i5 : CheckedCard where
  required := required_724_i5
  envelope := envelope_724_i5
  height := height_724_i5
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_724_i5
def height_724_i6 : ℕ := 11
def childrenH_724_i6 : Fin 5 → ℕ := ![height_512, height_600, height_621, height_702, height_714]
theorem height_exact_724_i6 : height_724_i6 = 1 + Finset.univ.sup childrenH_724_i6 := by decide +kernel
theorem required_origin_724_i6 : ∀ x ∈ required_724_i6,
    (∃ j, x ∈ childrenC_724_i6 j) ∨ ∀ j, x ∈ childrenD_724_i6 j := by decide +kernel
theorem required_exact_724_i6 : required_724_i6 =
    ((Finset.univ.biUnion childrenC_724_i6) ∪ commonEnvelope childrenD_724_i6).erase (6, 7) := by
  exact required_eq_combination childrenC_724_i6 childrenD_724_i6 (6, 7) required_724_i6
    (by decide +kernel) child_required_sub_724_i6 common_sub_724_i6 required_origin_724_i6
theorem envelope_origin_724_i6 : ∀ x ∈ envelope_724_i6,
    x = (6, 7) ∨ ∃ j, x ∈ childrenD_724_i6 j := by decide +kernel
theorem envelope_exact_724_i6 : envelope_724_i6 =
    insert (6, 7) (Finset.univ.biUnion childrenD_724_i6) := by
  exact envelope_eq_combination childrenD_724_i6 (6, 7) envelope_724_i6
    pivot_mem_724_i6 child_envelope_sub_724_i6 envelope_origin_724_i6
def checked_724_i6 : CheckedCard where
  required := required_724_i6
  envelope := envelope_724_i6
  height := height_724_i6
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_724_i6
def height_724_i8 : ℕ := 9
def childrenH_724_i8 : Fin 3 → ℕ := ![height_7, height_9, height_604]
theorem height_exact_724_i8 : height_724_i8 = 1 + Finset.univ.sup childrenH_724_i8 := by decide +kernel
theorem required_origin_724_i8 : ∀ x ∈ required_724_i8,
    (∃ j, x ∈ childrenC_724_i8 j) ∨ ∀ j, x ∈ childrenD_724_i8 j := by decide +kernel
theorem required_exact_724_i8 : required_724_i8 =
    ((Finset.univ.biUnion childrenC_724_i8) ∪ commonEnvelope childrenD_724_i8).erase (7, 8) := by
  exact required_eq_combination childrenC_724_i8 childrenD_724_i8 (7, 8) required_724_i8
    (by decide +kernel) child_required_sub_724_i8 common_sub_724_i8 required_origin_724_i8
theorem envelope_origin_724_i8 : ∀ x ∈ envelope_724_i8,
    x = (7, 8) ∨ ∃ j, x ∈ childrenD_724_i8 j := by decide +kernel
theorem envelope_exact_724_i8 : envelope_724_i8 =
    insert (7, 8) (Finset.univ.biUnion childrenD_724_i8) := by
  exact envelope_eq_combination childrenD_724_i8 (7, 8) envelope_724_i8
    pivot_mem_724_i8 child_envelope_sub_724_i8 envelope_origin_724_i8
def checked_724_i8 : CheckedCard where
  required := required_724_i8
  envelope := envelope_724_i8
  height := height_724_i8
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_724_i8
def height_724_i7 : ℕ := 10
def childrenH_724_i7 : Fin 4 → ℕ := ![height_88, height_231, height_267, height_724_i8]
theorem height_exact_724_i7 : height_724_i7 = 1 + Finset.univ.sup childrenH_724_i7 := by decide +kernel
theorem required_origin_724_i7 : ∀ x ∈ required_724_i7,
    (∃ j, x ∈ childrenC_724_i7 j) ∨ ∀ j, x ∈ childrenD_724_i7 j := by decide +kernel
theorem required_exact_724_i7 : required_724_i7 =
    ((Finset.univ.biUnion childrenC_724_i7) ∪ commonEnvelope childrenD_724_i7).erase (4, 8) := by
  exact required_eq_combination childrenC_724_i7 childrenD_724_i7 (4, 8) required_724_i7
    (by decide +kernel) child_required_sub_724_i7 common_sub_724_i7 required_origin_724_i7
theorem envelope_origin_724_i7 : ∀ x ∈ envelope_724_i7,
    x = (4, 8) ∨ ∃ j, x ∈ childrenD_724_i7 j := by decide +kernel
theorem envelope_exact_724_i7 : envelope_724_i7 =
    insert (4, 8) (Finset.univ.biUnion childrenD_724_i7) := by
  exact envelope_eq_combination childrenD_724_i7 (4, 8) envelope_724_i7
    pivot_mem_724_i7 child_envelope_sub_724_i7 envelope_origin_724_i7
def checked_724_i7 : CheckedCard where
  required := required_724_i7
  envelope := envelope_724_i7
  height := height_724_i7
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_724_i7
def height_724 : ℕ := 16
def childrenH_724 : Fin 10 → ℕ := ![height_523, height_524, height_677, height_724_i0, height_724_i1, height_719, height_724_i5, height_724_i6, height_724_i7, height_723]
theorem height_exact_724 : height_724 = 1 + Finset.univ.sup childrenH_724 := by decide +kernel
theorem required_origin_724 : ∀ x ∈ required_724,
    (∃ j, x ∈ childrenC_724 j) ∨ ∀ j, x ∈ childrenD_724 j := by decide +kernel
theorem required_exact_724 : required_724 =
    ((Finset.univ.biUnion childrenC_724) ∪ commonEnvelope childrenD_724).erase (6, 8) := by
  exact required_eq_combination childrenC_724 childrenD_724 (6, 8) required_724
    (by decide +kernel) child_required_sub_724 common_sub_724 required_origin_724
theorem envelope_origin_724 : ∀ x ∈ envelope_724,
    x = (6, 8) ∨ ∃ j, x ∈ childrenD_724 j := by decide +kernel
theorem envelope_exact_724 : envelope_724 =
    insert (6, 8) (Finset.univ.biUnion childrenD_724) := by
  exact envelope_eq_combination childrenD_724 (6, 8) envelope_724
    pivot_mem_724 child_envelope_sub_724 envelope_origin_724
def checked_724 : CheckedCard where
  required := required_724
  envelope := envelope_724
  height := height_724
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_724
end SnakyPrototype.Certificate21

end OAI
