import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part06
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part01
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_594_i0 : Finset Cell := ⟨(([(4, 3), (4, 6), (5, 3), (5, 4), (5, 6), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_594_i0 : Finset Cell := ⟨(([(4, 3), (4, 4), (4, 6), (4, 7), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 4), (6, 5), (6, 7), (6, 8), (6, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_594_i0 : Fin 2 → Finset Cell := ![(placed21 5 (5, 3) required_5), (placed21 0 (4, 3) required_91)]
def childrenD_594_i0 : Fin 2 → Finset Cell := ![(placed21 5 (5, 3) envelope_5), (placed21 0 (4, 3) envelope_91)]
theorem common_sub_594_i0 : commonEnvelope childrenD_594_i0 ⊆ insert (5, 5) required_594_i0 := by decide +kernel
theorem child_required_sub_594_i0 : ∀ j, childrenC_594_i0 j ⊆ insert (5, 5) required_594_i0 := by decide +kernel
theorem child_envelope_sub_594_i0 : ∀ j, childrenD_594_i0 j ⊆ envelope_594_i0 := by decide +kernel
theorem pivot_mem_594_i0 : (5, 5) ∈ envelope_594_i0 := by decide +kernel
theorem children_work_594_i0 : ∀ j, Template HasSnaky 4 (childrenC_594_i0 j) (childrenD_594_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 5 (5, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_91 0 (4, 3)).mono (by decide +kernel)
theorem row_works_594_i0 : Template HasSnaky 5 required_594_i0 envelope_594_i0 := by
  refine compose HasSnaky 4 childrenC_594_i0 childrenD_594_i0 children_work_594_i0 (5, 5)
    required_594_i0 envelope_594_i0 pivot_mem_594_i0 child_required_sub_594_i0 child_envelope_sub_594_i0 ?_
  intro b hb
  exact common_sub_594_i0 (mem_commonEnvelope childrenD_594_i0 b hb)
def required_594_i7 : Finset Cell := ⟨(([(5, 1), (5, 3), (5, 4), (5, 5), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_594_i7 : Finset Cell := ⟨(([(5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (6, 0), (6, 1), (6, 2), (6, 4), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_594_i7 : Fin 2 → Finset Cell := ![(placed21 1 (5, 1) required_5), (placed21 4 (5, 5) required_6)]
def childrenD_594_i7 : Fin 2 → Finset Cell := ![(placed21 1 (5, 1) envelope_5), (placed21 4 (5, 5) envelope_6)]
theorem common_sub_594_i7 : commonEnvelope childrenD_594_i7 ⊆ insert (5, 2) required_594_i7 := by decide +kernel
theorem child_required_sub_594_i7 : ∀ j, childrenC_594_i7 j ⊆ insert (5, 2) required_594_i7 := by decide +kernel
theorem child_envelope_sub_594_i7 : ∀ j, childrenD_594_i7 j ⊆ envelope_594_i7 := by decide +kernel
theorem pivot_mem_594_i7 : (5, 2) ∈ envelope_594_i7 := by decide +kernel
theorem children_work_594_i7 : ∀ j, Template HasSnaky 2 (childrenC_594_i7 j) (childrenD_594_i7 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 1 (5, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_6 4 (5, 5)).mono (by decide +kernel)
theorem row_works_594_i7 : Template HasSnaky 3 required_594_i7 envelope_594_i7 := by
  refine compose HasSnaky 2 childrenC_594_i7 childrenD_594_i7 children_work_594_i7 (5, 2)
    required_594_i7 envelope_594_i7 pivot_mem_594_i7 child_required_sub_594_i7 child_envelope_sub_594_i7 ?_
  intro b hb
  exact common_sub_594_i7 (mem_commonEnvelope childrenD_594_i7 b hb)
def required_594_i6 : Finset Cell := ⟨(([(4, 6), (5, 1), (5, 3), (5, 4), (5, 6), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_594_i6 : Finset Cell := ⟨(([(4, 6), (4, 7), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (6, 0), (6, 1), (6, 2), (6, 4), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_594_i6 : Fin 2 → Finset Cell := ![(placed21 5 (5, 3) required_5), required_594_i7]
def childrenD_594_i6 : Fin 2 → Finset Cell := ![(placed21 5 (5, 3) envelope_5), envelope_594_i7]
theorem common_sub_594_i6 : commonEnvelope childrenD_594_i6 ⊆ insert (5, 5) required_594_i6 := by decide +kernel
theorem child_required_sub_594_i6 : ∀ j, childrenC_594_i6 j ⊆ insert (5, 5) required_594_i6 := by decide +kernel
theorem child_envelope_sub_594_i6 : ∀ j, childrenD_594_i6 j ⊆ envelope_594_i6 := by decide +kernel
theorem pivot_mem_594_i6 : (5, 5) ∈ envelope_594_i6 := by decide +kernel
theorem children_work_594_i6 : ∀ j, Template HasSnaky 3 (childrenC_594_i6 j) (childrenD_594_i6 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 5 (5, 3)).mono (by decide +kernel)
  · exact row_works_594_i7.mono (by decide +kernel)
theorem row_works_594_i6 : Template HasSnaky 4 required_594_i6 envelope_594_i6 := by
  refine compose HasSnaky 3 childrenC_594_i6 childrenD_594_i6 children_work_594_i6 (5, 5)
    required_594_i6 envelope_594_i6 pivot_mem_594_i6 child_required_sub_594_i6 child_envelope_sub_594_i6 ?_
  intro b hb
  exact common_sub_594_i6 (mem_commonEnvelope childrenD_594_i6 b hb)
def required_594_i5 : Finset Cell := ⟨(([(1, 2), (2, 3), (2, 4), (2, 5), (4, 6), (5, 3), (5, 4), (5, 6), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_594_i5 : Finset Cell := ⟨(([(1, 1), (1, 2), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (4, 1), (4, 6), (4, 7), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (6, 0), (6, 1), (6, 2), (6, 4), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_594_i5 : Fin 2 → Finset Cell := ![(placed21 3 (1, 5) required_375), required_594_i6]
def childrenD_594_i5 : Fin 2 → Finset Cell := ![(placed21 3 (1, 5) envelope_375), envelope_594_i6]
theorem common_sub_594_i5 : commonEnvelope childrenD_594_i5 ⊆ insert (5, 1) required_594_i5 := by decide +kernel
theorem child_required_sub_594_i5 : ∀ j, childrenC_594_i5 j ⊆ insert (5, 1) required_594_i5 := by decide +kernel
theorem child_envelope_sub_594_i5 : ∀ j, childrenD_594_i5 j ⊆ envelope_594_i5 := by decide +kernel
theorem pivot_mem_594_i5 : (5, 1) ∈ envelope_594_i5 := by decide +kernel
theorem children_work_594_i5 : ∀ j, Template HasSnaky 4 (childrenC_594_i5 j) (childrenD_594_i5 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_375 3 (1, 5)).mono (by decide +kernel)
  · exact row_works_594_i6.mono (by decide +kernel)
theorem row_works_594_i5 : Template HasSnaky 5 required_594_i5 envelope_594_i5 := by
  refine compose HasSnaky 4 childrenC_594_i5 childrenD_594_i5 children_work_594_i5 (5, 1)
    required_594_i5 envelope_594_i5 pivot_mem_594_i5 child_required_sub_594_i5 child_envelope_sub_594_i5 ?_
  intro b hb
  exact common_sub_594_i5 (mem_commonEnvelope childrenD_594_i5 b hb)
def required_594_i4 : Finset Cell := ⟨(([(2, 3), (2, 4), (2, 5), (2, 6), (4, 6), (5, 3), (5, 4), (5, 6), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_594_i4 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 3), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 0), (3, 1), (3, 2), (4, 1), (4, 6), (4, 7), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (6, 0), (6, 1), (6, 2), (6, 4), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_594_i4 : Fin 2 → Finset Cell := ![(placed21 7 (2, 6) required_4), required_594_i5]
def childrenD_594_i4 : Fin 2 → Finset Cell := ![(placed21 7 (2, 6) envelope_4), envelope_594_i5]
theorem common_sub_594_i4 : commonEnvelope childrenD_594_i4 ⊆ insert (1, 2) required_594_i4 := by decide +kernel
theorem child_required_sub_594_i4 : ∀ j, childrenC_594_i4 j ⊆ insert (1, 2) required_594_i4 := by decide +kernel
theorem child_envelope_sub_594_i4 : ∀ j, childrenD_594_i4 j ⊆ envelope_594_i4 := by decide +kernel
theorem pivot_mem_594_i4 : (1, 2) ∈ envelope_594_i4 := by decide +kernel
theorem children_work_594_i4 : ∀ j, Template HasSnaky 5 (childrenC_594_i4 j) (childrenD_594_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_4 7 (2, 6)).mono (by decide +kernel)
  · exact row_works_594_i5.mono (by decide +kernel)
theorem row_works_594_i4 : Template HasSnaky 6 required_594_i4 envelope_594_i4 := by
  refine compose HasSnaky 5 childrenC_594_i4 childrenD_594_i4 children_work_594_i4 (1, 2)
    required_594_i4 envelope_594_i4 pivot_mem_594_i4 child_required_sub_594_i4 child_envelope_sub_594_i4 ?_
  intro b hb
  exact common_sub_594_i4 (mem_commonEnvelope childrenD_594_i4 b hb)
def required_594_i3 : Finset Cell := ⟨(([(2, 3), (2, 4), (2, 6), (4, 6), (5, 3), (5, 4), (5, 6), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_594_i3 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 3), (1, 5), (1, 6), (1, 7), (1, 8), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 0), (3, 1), (3, 2), (3, 7), (3, 8), (4, 1), (4, 6), (4, 7), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (6, 0), (6, 1), (6, 2), (6, 4), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_594_i3 : Fin 3 → Finset Cell := ![(placed21 6 (2, 7) required_7), (placed21 1 (1, 3) required_208), required_594_i4]
def childrenD_594_i3 : Fin 3 → Finset Cell := ![(placed21 6 (2, 7) envelope_7), (placed21 1 (1, 3) envelope_208), envelope_594_i4]
theorem common_sub_594_i3 : commonEnvelope childrenD_594_i3 ⊆ insert (2, 5) required_594_i3 := by decide +kernel
theorem child_required_sub_594_i3 : ∀ j, childrenC_594_i3 j ⊆ insert (2, 5) required_594_i3 := by decide +kernel
theorem child_envelope_sub_594_i3 : ∀ j, childrenD_594_i3 j ⊆ envelope_594_i3 := by decide +kernel
theorem pivot_mem_594_i3 : (2, 5) ∈ envelope_594_i3 := by decide +kernel
theorem children_work_594_i3 : ∀ j, Template HasSnaky 6 (childrenC_594_i3 j) (childrenD_594_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 6 (2, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_208 1 (1, 3)).mono (by decide +kernel)
  · exact row_works_594_i4.mono (by decide +kernel)
theorem row_works_594_i3 : Template HasSnaky 7 required_594_i3 envelope_594_i3 := by
  refine compose HasSnaky 6 childrenC_594_i3 childrenD_594_i3 children_work_594_i3 (2, 5)
    required_594_i3 envelope_594_i3 pivot_mem_594_i3 child_required_sub_594_i3 child_envelope_sub_594_i3 ?_
  intro b hb
  exact common_sub_594_i3 (mem_commonEnvelope childrenD_594_i3 b hb)
def required_594_i2 : Finset Cell := ⟨(([(2, 4), (2, 6), (4, 3), (4, 6), (5, 3), (5, 4), (5, 6), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_594_i2 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 3), (1, 5), (1, 6), (1, 7), (1, 8), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 0), (3, 1), (3, 2), (3, 3), (3, 7), (3, 8), (4, 1), (4, 3), (4, 6), (4, 7), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (6, 0), (6, 1), (6, 2), (6, 4), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_594_i2 : Fin 2 → Finset Cell := ![(placed21 0 (2, 3) required_1), required_594_i3]
def childrenD_594_i2 : Fin 2 → Finset Cell := ![(placed21 0 (2, 3) envelope_1), envelope_594_i3]
theorem common_sub_594_i2 : commonEnvelope childrenD_594_i2 ⊆ insert (2, 3) required_594_i2 := by decide +kernel
theorem child_required_sub_594_i2 : ∀ j, childrenC_594_i2 j ⊆ insert (2, 3) required_594_i2 := by decide +kernel
theorem child_envelope_sub_594_i2 : ∀ j, childrenD_594_i2 j ⊆ envelope_594_i2 := by decide +kernel
theorem pivot_mem_594_i2 : (2, 3) ∈ envelope_594_i2 := by decide +kernel
theorem children_work_594_i2 : ∀ j, Template HasSnaky 7 (childrenC_594_i2 j) (childrenD_594_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_1 0 (2, 3)).mono (by decide +kernel)
  · exact row_works_594_i3.mono (by decide +kernel)
theorem row_works_594_i2 : Template HasSnaky 8 required_594_i2 envelope_594_i2 := by
  refine compose HasSnaky 7 childrenC_594_i2 childrenD_594_i2 children_work_594_i2 (2, 3)
    required_594_i2 envelope_594_i2 pivot_mem_594_i2 child_required_sub_594_i2 child_envelope_sub_594_i2 ?_
  intro b hb
  exact common_sub_594_i2 (mem_commonEnvelope childrenD_594_i2 b hb)
def required_594_i8 : Finset Cell := ⟨(([(2, 4), (2, 6), (4, 3), (5, 3), (5, 4), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_594_i8 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 3), (1, 5), (1, 6), (1, 7), (1, 8), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 3), (3, 5), (3, 6), (3, 7), (3, 8), (4, 3), (5, 3), (5, 4), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_594_i8 : Fin 2 → Finset Cell := ![(placed21 0 (2, 3) required_1), (placed21 0 (1, 1) required_268)]
def childrenD_594_i8 : Fin 2 → Finset Cell := ![(placed21 0 (2, 3) envelope_1), (placed21 0 (1, 1) envelope_268)]
theorem common_sub_594_i8 : commonEnvelope childrenD_594_i8 ⊆ insert (2, 3) required_594_i8 := by decide +kernel
theorem child_required_sub_594_i8 : ∀ j, childrenC_594_i8 j ⊆ insert (2, 3) required_594_i8 := by decide +kernel
theorem child_envelope_sub_594_i8 : ∀ j, childrenD_594_i8 j ⊆ envelope_594_i8 := by decide +kernel
theorem pivot_mem_594_i8 : (2, 3) ∈ envelope_594_i8 := by decide +kernel
theorem children_work_594_i8 : ∀ j, Template HasSnaky 4 (childrenC_594_i8 j) (childrenD_594_i8 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_1 0 (2, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_268 0 (1, 1)).mono (by decide +kernel)
theorem row_works_594_i8 : Template HasSnaky 5 required_594_i8 envelope_594_i8 := by
  refine compose HasSnaky 4 childrenC_594_i8 childrenD_594_i8 children_work_594_i8 (2, 3)
    required_594_i8 envelope_594_i8 pivot_mem_594_i8 child_required_sub_594_i8 child_envelope_sub_594_i8 ?_
  intro b hb
  exact common_sub_594_i8 (mem_commonEnvelope childrenD_594_i8 b hb)
def required_594_i1 : Finset Cell := ⟨(([(2, 4), (4, 3), (4, 6), (5, 3), (5, 4), (5, 6), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_594_i1 : Finset Cell := ⟨(([(0, 5), (0, 7), (1, 1), (1, 2), (1, 3), (1, 5), (1, 6), (1, 7), (1, 8), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 0), (3, 1), (3, 2), (3, 3), (3, 5), (3, 6), (3, 7), (3, 8), (4, 1), (4, 3), (4, 6), (4, 7), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 0), (6, 1), (6, 2), (6, 4), (6, 5), (6, 7), (6, 8), (7, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_594_i1 : Fin 5 → Finset Cell := ![(placed21 5 (6, 3) required_272), (placed21 7 (6, 7) required_290), required_594_i2, required_594_i8, (placed21 5 (7, 3) required_593)]
def childrenD_594_i1 : Fin 5 → Finset Cell := ![(placed21 5 (6, 3) envelope_272), (placed21 7 (6, 7) envelope_290), envelope_594_i2, envelope_594_i8, (placed21 5 (7, 3) envelope_593)]
theorem common_sub_594_i1 : commonEnvelope childrenD_594_i1 ⊆ insert (2, 6) required_594_i1 := by decide +kernel
theorem child_required_sub_594_i1 : ∀ j, childrenC_594_i1 j ⊆ insert (2, 6) required_594_i1 := by decide +kernel
theorem child_envelope_sub_594_i1 : ∀ j, childrenD_594_i1 j ⊆ envelope_594_i1 := by decide +kernel
theorem pivot_mem_594_i1 : (2, 6) ∈ envelope_594_i1 := by decide +kernel
theorem children_work_594_i1 : ∀ j, Template HasSnaky 8 (childrenC_594_i1 j) (childrenD_594_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_272 5 (6, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_290 7 (6, 7)).mono (by decide +kernel)
  · exact row_works_594_i2.mono (by decide +kernel)
  · exact row_works_594_i8.mono (by decide +kernel)
  · exact (placed21_template row_works_593 5 (7, 3)).mono (by decide +kernel)
theorem row_works_594_i1 : Template HasSnaky 9 required_594_i1 envelope_594_i1 := by
  refine compose HasSnaky 8 childrenC_594_i1 childrenD_594_i1 children_work_594_i1 (2, 6)
    required_594_i1 envelope_594_i1 pivot_mem_594_i1 child_required_sub_594_i1 child_envelope_sub_594_i1 ?_
  intro b hb
  exact common_sub_594_i1 (mem_commonEnvelope childrenD_594_i1 b hb)
def required_594 : Finset Cell := ⟨(([(2, 4), (4, 3), (4, 6), (5, 3), (5, 4), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_594 : Finset Cell := ⟨(([(0, 5), (0, 7), (1, 1), (1, 2), (1, 3), (1, 5), (1, 6), (1, 7), (1, 8), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 0), (3, 1), (3, 2), (3, 3), (3, 5), (3, 6), (3, 7), (3, 8), (4, 1), (4, 3), (4, 4), (4, 6), (4, 7), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 0), (6, 1), (6, 2), (6, 4), (6, 5), (6, 7), (6, 8), (6, 9), (7, 4), (7, 8), (8, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_594 : Fin 3 → Finset Cell := ![(placed21 7 (8, 4) required_53), required_594_i0, required_594_i1]
def childrenD_594 : Fin 3 → Finset Cell := ![(placed21 7 (8, 4) envelope_53), envelope_594_i0, envelope_594_i1]
theorem common_sub_594 : commonEnvelope childrenD_594 ⊆ insert (6, 4) required_594 := by decide +kernel
theorem child_required_sub_594 : ∀ j, childrenC_594 j ⊆ insert (6, 4) required_594 := by decide +kernel
theorem child_envelope_sub_594 : ∀ j, childrenD_594 j ⊆ envelope_594 := by decide +kernel
theorem pivot_mem_594 : (6, 4) ∈ envelope_594 := by decide +kernel
theorem children_work_594 : ∀ j, Template HasSnaky 9 (childrenC_594 j) (childrenD_594 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_53 7 (8, 4)).mono (by decide +kernel)
  · exact row_works_594_i0.mono (by decide +kernel)
  · exact row_works_594_i1.mono (by decide +kernel)
theorem row_works_594 : Template HasSnaky 10 required_594 envelope_594 := by
  refine compose HasSnaky 9 childrenC_594 childrenD_594 children_work_594 (6, 4)
    required_594 envelope_594 pivot_mem_594 child_required_sub_594 child_envelope_sub_594 ?_
  intro b hb
  exact common_sub_594 (mem_commonEnvelope childrenD_594 b hb)
def required_608_i1 : Finset Cell := ⟨(([(1, 2), (4, 4), (4, 5), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_608_i1 : Finset Cell := ⟨(([(1, 2), (2, 2), (3, 1), (3, 2), (3, 3), (3, 7), (3, 8), (3, 9), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 2), (5, 3), (5, 4), (5, 7), (5, 8), (5, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_608_i1 : Fin 2 → Finset Cell := ![(placed21 2 (5, 3) required_18), (placed21 7 (5, 6) required_375)]
def childrenD_608_i1 : Fin 2 → Finset Cell := ![(placed21 2 (5, 3) envelope_18), (placed21 7 (5, 6) envelope_375)]
theorem common_sub_608_i1 : commonEnvelope childrenD_608_i1 ⊆ insert (5, 3) required_608_i1 := by decide +kernel
theorem child_required_sub_608_i1 : ∀ j, childrenC_608_i1 j ⊆ insert (5, 3) required_608_i1 := by decide +kernel
theorem child_envelope_sub_608_i1 : ∀ j, childrenD_608_i1 j ⊆ envelope_608_i1 := by decide +kernel
theorem pivot_mem_608_i1 : (5, 3) ∈ envelope_608_i1 := by decide +kernel
theorem children_work_608_i1 : ∀ j, Template HasSnaky 4 (childrenC_608_i1 j) (childrenD_608_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_18 2 (5, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_375 7 (5, 6)).mono (by decide +kernel)
theorem row_works_608_i1 : Template HasSnaky 5 required_608_i1 envelope_608_i1 := by
  refine compose HasSnaky 4 childrenC_608_i1 childrenD_608_i1 children_work_608_i1 (5, 3)
    required_608_i1 envelope_608_i1 pivot_mem_608_i1 child_required_sub_608_i1 child_envelope_sub_608_i1 ?_
  intro b hb
  exact common_sub_608_i1 (mem_commonEnvelope childrenD_608_i1 b hb)
def required_608_i2 : Finset Cell := ⟨(([(1, 2), (1, 4), (1, 5), (4, 4), (4, 5), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_608_i2 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 4), (2, 5), (2, 6), (3, 5), (4, 4), (4, 5), (4, 6), (5, 4), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_608_i2 : Fin 2 → Finset Cell := ![(placed21 7 (5, 6) required_28), (placed21 6 (2, 6) required_42)]
def childrenD_608_i2 : Fin 2 → Finset Cell := ![(placed21 7 (5, 6) envelope_28), (placed21 6 (2, 6) envelope_42)]
theorem common_sub_608_i2 : commonEnvelope childrenD_608_i2 ⊆ insert (2, 5) required_608_i2 := by decide +kernel
theorem child_required_sub_608_i2 : ∀ j, childrenC_608_i2 j ⊆ insert (2, 5) required_608_i2 := by decide +kernel
theorem child_envelope_sub_608_i2 : ∀ j, childrenD_608_i2 j ⊆ envelope_608_i2 := by decide +kernel
theorem pivot_mem_608_i2 : (2, 5) ∈ envelope_608_i2 := by decide +kernel
theorem children_work_608_i2 : ∀ j, Template HasSnaky 4 (childrenC_608_i2 j) (childrenD_608_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_28 7 (5, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_42 6 (2, 6)).mono (by decide +kernel)
theorem row_works_608_i2 : Template HasSnaky 5 required_608_i2 envelope_608_i2 := by
  refine compose HasSnaky 4 childrenC_608_i2 childrenD_608_i2 children_work_608_i2 (2, 5)
    required_608_i2 envelope_608_i2 pivot_mem_608_i2 child_required_sub_608_i2 child_envelope_sub_608_i2 ?_
  intro b hb
  exact common_sub_608_i2 (mem_commonEnvelope childrenD_608_i2 b hb)
def required_608_i3 : Finset Cell := ⟨(([(1, 2), (1, 4), (1, 5), (4, 4), (4, 5), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_608_i3 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 4), (2, 5), (2, 6), (3, 5), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 6), (5, 7), (5, 8), (5, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_608_i3 : Fin 2 → Finset Cell := ![(placed21 6 (2, 6) required_42), (placed21 0 (1, 3) required_58)]
def childrenD_608_i3 : Fin 2 → Finset Cell := ![(placed21 6 (2, 6) envelope_42), (placed21 0 (1, 3) envelope_58)]
theorem common_sub_608_i3 : commonEnvelope childrenD_608_i3 ⊆ insert (2, 5) required_608_i3 := by decide +kernel
theorem child_required_sub_608_i3 : ∀ j, childrenC_608_i3 j ⊆ insert (2, 5) required_608_i3 := by decide +kernel
theorem child_envelope_sub_608_i3 : ∀ j, childrenD_608_i3 j ⊆ envelope_608_i3 := by decide +kernel
theorem pivot_mem_608_i3 : (2, 5) ∈ envelope_608_i3 := by decide +kernel
theorem children_work_608_i3 : ∀ j, Template HasSnaky 4 (childrenC_608_i3 j) (childrenD_608_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_42 6 (2, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_58 0 (1, 3)).mono (by decide +kernel)
theorem row_works_608_i3 : Template HasSnaky 5 required_608_i3 envelope_608_i3 := by
  refine compose HasSnaky 4 childrenC_608_i3 childrenD_608_i3 children_work_608_i3 (2, 5)
    required_608_i3 envelope_608_i3 pivot_mem_608_i3 child_required_sub_608_i3 child_envelope_sub_608_i3 ?_
  intro b hb
  exact common_sub_608_i3 (mem_commonEnvelope childrenD_608_i3 b hb)
def required_608_i0 : Finset Cell := ⟨(([(1, 4), (1, 5), (4, 4), (4, 5), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_608_i0 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 2), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 5), (3, 7), (3, 8), (3, 9), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 2), (5, 3), (5, 4), (5, 6), (5, 7), (5, 8), (5, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_608_i0 : Fin 3 → Finset Cell := ![required_608_i1, required_608_i2, required_608_i3]
def childrenD_608_i0 : Fin 3 → Finset Cell := ![envelope_608_i1, envelope_608_i2, envelope_608_i3]
theorem common_sub_608_i0 : commonEnvelope childrenD_608_i0 ⊆ insert (1, 2) required_608_i0 := by decide +kernel
theorem child_required_sub_608_i0 : ∀ j, childrenC_608_i0 j ⊆ insert (1, 2) required_608_i0 := by decide +kernel
theorem child_envelope_sub_608_i0 : ∀ j, childrenD_608_i0 j ⊆ envelope_608_i0 := by decide +kernel
theorem pivot_mem_608_i0 : (1, 2) ∈ envelope_608_i0 := by decide +kernel
theorem children_work_608_i0 : ∀ j, Template HasSnaky 5 (childrenC_608_i0 j) (childrenD_608_i0 j) := by
  intro j
  fin_cases j
  · exact row_works_608_i1.mono (by decide +kernel)
  · exact row_works_608_i2.mono (by decide +kernel)
  · exact row_works_608_i3.mono (by decide +kernel)
theorem row_works_608_i0 : Template HasSnaky 6 required_608_i0 envelope_608_i0 := by
  refine compose HasSnaky 5 childrenC_608_i0 childrenD_608_i0 children_work_608_i0 (1, 2)
    required_608_i0 envelope_608_i0 pivot_mem_608_i0 child_required_sub_608_i0 child_envelope_sub_608_i0 ?_
  intro b hb
  exact common_sub_608_i0 (mem_commonEnvelope childrenD_608_i0 b hb)
def required_608 : Finset Cell := ⟨(([(1, 4), (1, 5), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_608 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 7), (0, 8), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 7), (1, 8), (2, 2), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 1), (3, 2), (3, 3), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, 1), (5, 2), (5, 3), (5, 4), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (6, 6), (6, 7), (7, 6), (7, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_608 : Fin 6 → Finset Cell := ![(placed21 4 (3, 8) required_13), (placed21 4 (3, 8) required_31), (placed21 4 (1, 7) required_355), (placed21 0 (1, 2) required_364), (placed21 0 (0, 3) required_434), required_608_i0]
def childrenD_608 : Fin 6 → Finset Cell := ![(placed21 4 (3, 8) envelope_13), (placed21 4 (3, 8) envelope_31), (placed21 4 (1, 7) envelope_355), (placed21 0 (1, 2) envelope_364), (placed21 0 (0, 3) envelope_434), envelope_608_i0]
theorem common_sub_608 : commonEnvelope childrenD_608 ⊆ insert (4, 6) required_608 := by decide +kernel
theorem child_required_sub_608 : ∀ j, childrenC_608 j ⊆ insert (4, 6) required_608 := by decide +kernel
theorem child_envelope_sub_608 : ∀ j, childrenD_608 j ⊆ envelope_608 := by decide +kernel
theorem pivot_mem_608 : (4, 6) ∈ envelope_608 := by decide +kernel
theorem children_work_608 : ∀ j, Template HasSnaky 9 (childrenC_608 j) (childrenD_608 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_13 4 (3, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_31 4 (3, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_355 4 (1, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_364 0 (1, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_434 0 (0, 3)).mono (by decide +kernel)
  · exact row_works_608_i0.mono (by decide +kernel)
theorem row_works_608 : Template HasSnaky 10 required_608 envelope_608 := by
  refine compose HasSnaky 9 childrenC_608 childrenD_608 children_work_608 (4, 6)
    required_608 envelope_608 pivot_mem_608 child_required_sub_608 child_envelope_sub_608 ?_
  intro b hb
  exact common_sub_608 (mem_commonEnvelope childrenD_608 b hb)
def required_616_i1 : Finset Cell := ⟨(([(1, 3), (2, 2), (2, 3), (2, 4), (2, 5), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_616_i1 : Finset Cell := ⟨(([(1, 3), (1, 4), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_616_i1 : Fin 2 → Finset Cell := ![(placed21 0 (2, 2) required_6), (placed21 5 (3, 3) required_123)]
def childrenD_616_i1 : Fin 2 → Finset Cell := ![(placed21 0 (2, 2) envelope_6), (placed21 5 (3, 3) envelope_123)]
theorem common_sub_616_i1 : commonEnvelope childrenD_616_i1 ⊆ insert (2, 6) required_616_i1 := by decide +kernel
theorem child_required_sub_616_i1 : ∀ j, childrenC_616_i1 j ⊆ insert (2, 6) required_616_i1 := by decide +kernel
theorem child_envelope_sub_616_i1 : ∀ j, childrenD_616_i1 j ⊆ envelope_616_i1 := by decide +kernel
theorem pivot_mem_616_i1 : (2, 6) ∈ envelope_616_i1 := by decide +kernel
theorem children_work_616_i1 : ∀ j, Template HasSnaky 2 (childrenC_616_i1 j) (childrenD_616_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_6 0 (2, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_123 5 (3, 3)).mono (by decide +kernel)
theorem row_works_616_i1 : Template HasSnaky 3 required_616_i1 envelope_616_i1 := by
  refine compose HasSnaky 2 childrenC_616_i1 childrenD_616_i1 children_work_616_i1 (2, 6)
    required_616_i1 envelope_616_i1 pivot_mem_616_i1 child_required_sub_616_i1 child_envelope_sub_616_i1 ?_
  intro b hb
  exact common_sub_616_i1 (mem_commonEnvelope childrenD_616_i1 b hb)
def required_616_i0 : Finset Cell := ⟨(([(1, 3), (2, 2), (2, 3), (2, 4), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_616_i0 : Finset Cell := ⟨(([(1, 3), (1, 4), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 1), (4, 2), (4, 5), (4, 6), (5, 2), (5, 5), (6, 2), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_616_i0 : Fin 3 → Finset Cell := ![(placed21 0 (2, 1) required_11), required_616_i1, (placed21 0 (1, 1) required_521)]
def childrenD_616_i0 : Fin 3 → Finset Cell := ![(placed21 0 (2, 1) envelope_11), envelope_616_i1, (placed21 0 (1, 1) envelope_521)]
theorem common_sub_616_i0 : commonEnvelope childrenD_616_i0 ⊆ insert (2, 5) required_616_i0 := by decide +kernel
theorem child_required_sub_616_i0 : ∀ j, childrenC_616_i0 j ⊆ insert (2, 5) required_616_i0 := by decide +kernel
theorem child_envelope_sub_616_i0 : ∀ j, childrenD_616_i0 j ⊆ envelope_616_i0 := by decide +kernel
theorem pivot_mem_616_i0 : (2, 5) ∈ envelope_616_i0 := by decide +kernel
theorem children_work_616_i0 : ∀ j, Template HasSnaky 6 (childrenC_616_i0 j) (childrenD_616_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_11 0 (2, 1)).mono (by decide +kernel)
  · exact row_works_616_i1.mono (by decide +kernel)
  · exact (placed21_template row_works_521 0 (1, 1)).mono (by decide +kernel)
theorem row_works_616_i0 : Template HasSnaky 7 required_616_i0 envelope_616_i0 := by
  refine compose HasSnaky 6 childrenC_616_i0 childrenD_616_i0 children_work_616_i0 (2, 5)
    required_616_i0 envelope_616_i0 pivot_mem_616_i0 child_required_sub_616_i0 child_envelope_sub_616_i0 ?_
  intro b hb
  exact common_sub_616_i0 (mem_commonEnvelope childrenD_616_i0 b hb)
def required_616 : Finset Cell := ⟨(([(1, 3), (2, 2), (2, 3), (2, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_616 : Finset Cell := ⟨(([(0, 4), (1, 3), (1, 4), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 2), (6, 3), (6, 4), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_616 : Fin 7 → Finset Cell := ![(placed21 0 (0, 1) required_345), (placed21 1 (0, 2) required_421), (placed21 0 (0, 1) required_522), (placed21 0 (1, 0) required_530), (placed21 4 (0, 6) required_533), required_534, required_616_i0]
def childrenD_616 : Fin 7 → Finset Cell := ![(placed21 0 (0, 1) envelope_345), (placed21 1 (0, 2) envelope_421), (placed21 0 (0, 1) envelope_522), (placed21 0 (1, 0) envelope_530), (placed21 4 (0, 6) envelope_533), envelope_534, envelope_616_i0]
theorem common_sub_616 : commonEnvelope childrenD_616 ⊆ insert (3, 3) required_616 := by decide +kernel
theorem child_required_sub_616 : ∀ j, childrenC_616 j ⊆ insert (3, 3) required_616 := by decide +kernel
theorem child_envelope_sub_616 : ∀ j, childrenD_616 j ⊆ envelope_616 := by decide +kernel
theorem pivot_mem_616 : (3, 3) ∈ envelope_616 := by decide +kernel
theorem children_work_616 : ∀ j, Template HasSnaky 9 (childrenC_616 j) (childrenD_616 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_345 0 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_421 1 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_522 0 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_530 0 (1, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_533 4 (0, 6)).mono (by decide +kernel)
  · exact row_works_534.mono (by decide +kernel)
  · exact row_works_616_i0.mono (by decide +kernel)
theorem row_works_616 : Template HasSnaky 10 required_616 envelope_616 := by
  refine compose HasSnaky 9 childrenC_616 childrenD_616 children_work_616 (3, 3)
    required_616 envelope_616 pivot_mem_616 child_required_sub_616 child_envelope_sub_616 ?_
  intro b hb
  exact common_sub_616 (mem_commonEnvelope childrenD_616 b hb)
def required_631_i1 : Finset Cell := ⟨(([(3, 3), (3, 4), (3, 5), (4, 2), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_631_i1 : Finset Cell := ⟨(([(0, 2), (1, 2), (2, 1), (2, 2), (2, 5), (2, 6), (3, 2), (3, 3), (3, 4), (3, 5), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 3), (5, 4), (5, 5), (5, 6), (6, 4), (6, 5), (6, 6), (7, 4), (7, 5), (7, 6), (8, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_631_i1 : Fin 2 → Finset Cell := ![(placed21 7 (5, 5) required_45), (placed21 1 (2, 2) required_418)]
def childrenD_631_i1 : Fin 2 → Finset Cell := ![(placed21 7 (5, 5) envelope_45), (placed21 1 (2, 2) envelope_418)]
theorem common_sub_631_i1 : commonEnvelope childrenD_631_i1 ⊆ insert (3, 2) required_631_i1 := by decide +kernel
theorem child_required_sub_631_i1 : ∀ j, childrenC_631_i1 j ⊆ insert (3, 2) required_631_i1 := by decide +kernel
theorem child_envelope_sub_631_i1 : ∀ j, childrenD_631_i1 j ⊆ envelope_631_i1 := by decide +kernel
theorem pivot_mem_631_i1 : (3, 2) ∈ envelope_631_i1 := by decide +kernel
theorem children_work_631_i1 : ∀ j, Template HasSnaky 7 (childrenC_631_i1 j) (childrenD_631_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_45 7 (5, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_418 1 (2, 2)).mono (by decide +kernel)
theorem row_works_631_i1 : Template HasSnaky 8 required_631_i1 envelope_631_i1 := by
  refine compose HasSnaky 7 childrenC_631_i1 childrenD_631_i1 children_work_631_i1 (3, 2)
    required_631_i1 envelope_631_i1 pivot_mem_631_i1 child_required_sub_631_i1 child_envelope_sub_631_i1 ?_
  intro b hb
  exact common_sub_631_i1 (mem_commonEnvelope childrenD_631_i1 b hb)
def required_631_i0 : Finset Cell := ⟨(([(3, 3), (3, 4), (3, 5), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_631_i0 : Finset Cell := ⟨(([(0, 2), (1, 2), (2, 1), (2, 2), (2, 5), (2, 6), (3, 2), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 3), (5, 4), (5, 5), (5, 6), (6, 4), (6, 5), (6, 6), (7, 4), (7, 5), (7, 6), (8, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_631_i0 : Fin 3 → Finset Cell := ![(placed21 4 (3, 5) required_43), (placed21 4 (3, 5) required_51), required_631_i1]
def childrenD_631_i0 : Fin 3 → Finset Cell := ![(placed21 4 (3, 5) envelope_43), (placed21 4 (3, 5) envelope_51), envelope_631_i1]
theorem common_sub_631_i0 : commonEnvelope childrenD_631_i0 ⊆ insert (4, 2) required_631_i0 := by decide +kernel
theorem child_required_sub_631_i0 : ∀ j, childrenC_631_i0 j ⊆ insert (4, 2) required_631_i0 := by decide +kernel
theorem child_envelope_sub_631_i0 : ∀ j, childrenD_631_i0 j ⊆ envelope_631_i0 := by decide +kernel
theorem pivot_mem_631_i0 : (4, 2) ∈ envelope_631_i0 := by decide +kernel
theorem children_work_631_i0 : ∀ j, Template HasSnaky 8 (childrenC_631_i0 j) (childrenD_631_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_43 4 (3, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_51 4 (3, 5)).mono (by decide +kernel)
  · exact row_works_631_i1.mono (by decide +kernel)
theorem row_works_631_i0 : Template HasSnaky 9 required_631_i0 envelope_631_i0 := by
  refine compose HasSnaky 8 childrenC_631_i0 childrenD_631_i0 children_work_631_i0 (4, 2)
    required_631_i0 envelope_631_i0 pivot_mem_631_i0 child_required_sub_631_i0 child_envelope_sub_631_i0 ?_
  intro b hb
  exact common_sub_631_i0 (mem_commonEnvelope childrenD_631_i0 b hb)
def required_631 : Finset Cell := ⟨(([(3, 3), (3, 4), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_631 : Finset Cell := ⟨(([(0, 2), (1, 2), (2, 1), (2, 2), (2, 5), (2, 6), (2, 7), (2, 8), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 3), (5, 4), (5, 5), (5, 6), (6, 4), (6, 5), (6, 6), (7, 4), (7, 5), (7, 6), (8, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_631 : Fin 4 → Finset Cell := ![(placed21 4 (3, 6) required_44), (placed21 4 (3, 6) required_52), (placed21 2 (4, 2) required_63), required_631_i0]
def childrenD_631 : Fin 4 → Finset Cell := ![(placed21 4 (3, 6) envelope_44), (placed21 4 (3, 6) envelope_52), (placed21 2 (4, 2) envelope_63), envelope_631_i0]
theorem common_sub_631 : commonEnvelope childrenD_631 ⊆ insert (3, 5) required_631 := by decide +kernel
theorem child_required_sub_631 : ∀ j, childrenC_631 j ⊆ insert (3, 5) required_631 := by decide +kernel
theorem child_envelope_sub_631 : ∀ j, childrenD_631 j ⊆ envelope_631 := by decide +kernel
theorem pivot_mem_631 : (3, 5) ∈ envelope_631 := by decide +kernel
theorem children_work_631 : ∀ j, Template HasSnaky 9 (childrenC_631 j) (childrenD_631 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_44 4 (3, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_52 4 (3, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_63 2 (4, 2)).mono (by decide +kernel)
  · exact row_works_631_i0.mono (by decide +kernel)
theorem row_works_631 : Template HasSnaky 10 required_631 envelope_631 := by
  refine compose HasSnaky 9 childrenC_631 childrenD_631 children_work_631 (3, 5)
    required_631 envelope_631 pivot_mem_631 child_required_sub_631 child_envelope_sub_631 ?_
  intro b hb
  exact common_sub_631 (mem_commonEnvelope childrenD_631 b hb)
def height_594_i0 : ℕ := 5
def childrenH_594_i0 : Fin 2 → ℕ := ![height_5, height_91]
theorem height_exact_594_i0 : height_594_i0 = 1 + Finset.univ.sup childrenH_594_i0 := by decide +kernel
theorem required_origin_594_i0 : ∀ x ∈ required_594_i0,
    (∃ j, x ∈ childrenC_594_i0 j) ∨ ∀ j, x ∈ childrenD_594_i0 j := by decide +kernel
theorem required_exact_594_i0 : required_594_i0 =
    ((Finset.univ.biUnion childrenC_594_i0) ∪ commonEnvelope childrenD_594_i0).erase (5, 5) := by
  exact required_eq_combination childrenC_594_i0 childrenD_594_i0 (5, 5) required_594_i0
    (by decide +kernel) child_required_sub_594_i0 common_sub_594_i0 required_origin_594_i0
theorem envelope_origin_594_i0 : ∀ x ∈ envelope_594_i0,
    x = (5, 5) ∨ ∃ j, x ∈ childrenD_594_i0 j := by decide +kernel
theorem envelope_exact_594_i0 : envelope_594_i0 =
    insert (5, 5) (Finset.univ.biUnion childrenD_594_i0) := by
  exact envelope_eq_combination childrenD_594_i0 (5, 5) envelope_594_i0
    pivot_mem_594_i0 child_envelope_sub_594_i0 envelope_origin_594_i0
def checked_594_i0 : CheckedCard where
  required := required_594_i0
  envelope := envelope_594_i0
  height := height_594_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_594_i0
def height_594_i7 : ℕ := 3
def childrenH_594_i7 : Fin 2 → ℕ := ![height_5, height_6]
theorem height_exact_594_i7 : height_594_i7 = 1 + Finset.univ.sup childrenH_594_i7 := by decide +kernel
theorem required_origin_594_i7 : ∀ x ∈ required_594_i7,
    (∃ j, x ∈ childrenC_594_i7 j) ∨ ∀ j, x ∈ childrenD_594_i7 j := by decide +kernel
theorem required_exact_594_i7 : required_594_i7 =
    ((Finset.univ.biUnion childrenC_594_i7) ∪ commonEnvelope childrenD_594_i7).erase (5, 2) := by
  exact required_eq_combination childrenC_594_i7 childrenD_594_i7 (5, 2) required_594_i7
    (by decide +kernel) child_required_sub_594_i7 common_sub_594_i7 required_origin_594_i7
theorem envelope_origin_594_i7 : ∀ x ∈ envelope_594_i7,
    x = (5, 2) ∨ ∃ j, x ∈ childrenD_594_i7 j := by decide +kernel
theorem envelope_exact_594_i7 : envelope_594_i7 =
    insert (5, 2) (Finset.univ.biUnion childrenD_594_i7) := by
  exact envelope_eq_combination childrenD_594_i7 (5, 2) envelope_594_i7
    pivot_mem_594_i7 child_envelope_sub_594_i7 envelope_origin_594_i7
def checked_594_i7 : CheckedCard where
  required := required_594_i7
  envelope := envelope_594_i7
  height := height_594_i7
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_594_i7
def height_594_i6 : ℕ := 4
def childrenH_594_i6 : Fin 2 → ℕ := ![height_5, height_594_i7]
theorem height_exact_594_i6 : height_594_i6 = 1 + Finset.univ.sup childrenH_594_i6 := by decide +kernel
theorem required_origin_594_i6 : ∀ x ∈ required_594_i6,
    (∃ j, x ∈ childrenC_594_i6 j) ∨ ∀ j, x ∈ childrenD_594_i6 j := by decide +kernel
theorem required_exact_594_i6 : required_594_i6 =
    ((Finset.univ.biUnion childrenC_594_i6) ∪ commonEnvelope childrenD_594_i6).erase (5, 5) := by
  exact required_eq_combination childrenC_594_i6 childrenD_594_i6 (5, 5) required_594_i6
    (by decide +kernel) child_required_sub_594_i6 common_sub_594_i6 required_origin_594_i6
theorem envelope_origin_594_i6 : ∀ x ∈ envelope_594_i6,
    x = (5, 5) ∨ ∃ j, x ∈ childrenD_594_i6 j := by decide +kernel
theorem envelope_exact_594_i6 : envelope_594_i6 =
    insert (5, 5) (Finset.univ.biUnion childrenD_594_i6) := by
  exact envelope_eq_combination childrenD_594_i6 (5, 5) envelope_594_i6
    pivot_mem_594_i6 child_envelope_sub_594_i6 envelope_origin_594_i6
def checked_594_i6 : CheckedCard where
  required := required_594_i6
  envelope := envelope_594_i6
  height := height_594_i6
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_594_i6
def height_594_i5 : ℕ := 5
def childrenH_594_i5 : Fin 2 → ℕ := ![height_375, height_594_i6]
theorem height_exact_594_i5 : height_594_i5 = 1 + Finset.univ.sup childrenH_594_i5 := by decide +kernel
theorem required_origin_594_i5 : ∀ x ∈ required_594_i5,
    (∃ j, x ∈ childrenC_594_i5 j) ∨ ∀ j, x ∈ childrenD_594_i5 j := by decide +kernel
theorem required_exact_594_i5 : required_594_i5 =
    ((Finset.univ.biUnion childrenC_594_i5) ∪ commonEnvelope childrenD_594_i5).erase (5, 1) := by
  exact required_eq_combination childrenC_594_i5 childrenD_594_i5 (5, 1) required_594_i5
    (by decide +kernel) child_required_sub_594_i5 common_sub_594_i5 required_origin_594_i5
theorem envelope_origin_594_i5 : ∀ x ∈ envelope_594_i5,
    x = (5, 1) ∨ ∃ j, x ∈ childrenD_594_i5 j := by decide +kernel
theorem envelope_exact_594_i5 : envelope_594_i5 =
    insert (5, 1) (Finset.univ.biUnion childrenD_594_i5) := by
  exact envelope_eq_combination childrenD_594_i5 (5, 1) envelope_594_i5
    pivot_mem_594_i5 child_envelope_sub_594_i5 envelope_origin_594_i5
def checked_594_i5 : CheckedCard where
  required := required_594_i5
  envelope := envelope_594_i5
  height := height_594_i5
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_594_i5
def height_594_i4 : ℕ := 6
def childrenH_594_i4 : Fin 2 → ℕ := ![height_4, height_594_i5]
theorem height_exact_594_i4 : height_594_i4 = 1 + Finset.univ.sup childrenH_594_i4 := by decide +kernel
theorem required_origin_594_i4 : ∀ x ∈ required_594_i4,
    (∃ j, x ∈ childrenC_594_i4 j) ∨ ∀ j, x ∈ childrenD_594_i4 j := by decide +kernel
theorem required_exact_594_i4 : required_594_i4 =
    ((Finset.univ.biUnion childrenC_594_i4) ∪ commonEnvelope childrenD_594_i4).erase (1, 2) := by
  exact required_eq_combination childrenC_594_i4 childrenD_594_i4 (1, 2) required_594_i4
    (by decide +kernel) child_required_sub_594_i4 common_sub_594_i4 required_origin_594_i4
theorem envelope_origin_594_i4 : ∀ x ∈ envelope_594_i4,
    x = (1, 2) ∨ ∃ j, x ∈ childrenD_594_i4 j := by decide +kernel
theorem envelope_exact_594_i4 : envelope_594_i4 =
    insert (1, 2) (Finset.univ.biUnion childrenD_594_i4) := by
  exact envelope_eq_combination childrenD_594_i4 (1, 2) envelope_594_i4
    pivot_mem_594_i4 child_envelope_sub_594_i4 envelope_origin_594_i4
def checked_594_i4 : CheckedCard where
  required := required_594_i4
  envelope := envelope_594_i4
  height := height_594_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_594_i4
def height_594_i3 : ℕ := 7
def childrenH_594_i3 : Fin 3 → ℕ := ![height_7, height_208, height_594_i4]
theorem height_exact_594_i3 : height_594_i3 = 1 + Finset.univ.sup childrenH_594_i3 := by decide +kernel
theorem required_origin_594_i3 : ∀ x ∈ required_594_i3,
    (∃ j, x ∈ childrenC_594_i3 j) ∨ ∀ j, x ∈ childrenD_594_i3 j := by decide +kernel
theorem required_exact_594_i3 : required_594_i3 =
    ((Finset.univ.biUnion childrenC_594_i3) ∪ commonEnvelope childrenD_594_i3).erase (2, 5) := by
  exact required_eq_combination childrenC_594_i3 childrenD_594_i3 (2, 5) required_594_i3
    (by decide +kernel) child_required_sub_594_i3 common_sub_594_i3 required_origin_594_i3
theorem envelope_origin_594_i3 : ∀ x ∈ envelope_594_i3,
    x = (2, 5) ∨ ∃ j, x ∈ childrenD_594_i3 j := by decide +kernel
theorem envelope_exact_594_i3 : envelope_594_i3 =
    insert (2, 5) (Finset.univ.biUnion childrenD_594_i3) := by
  exact envelope_eq_combination childrenD_594_i3 (2, 5) envelope_594_i3
    pivot_mem_594_i3 child_envelope_sub_594_i3 envelope_origin_594_i3
def checked_594_i3 : CheckedCard where
  required := required_594_i3
  envelope := envelope_594_i3
  height := height_594_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_594_i3
def height_594_i2 : ℕ := 8
def childrenH_594_i2 : Fin 2 → ℕ := ![height_1, height_594_i3]
theorem height_exact_594_i2 : height_594_i2 = 1 + Finset.univ.sup childrenH_594_i2 := by decide +kernel
theorem required_origin_594_i2 : ∀ x ∈ required_594_i2,
    (∃ j, x ∈ childrenC_594_i2 j) ∨ ∀ j, x ∈ childrenD_594_i2 j := by decide +kernel
theorem required_exact_594_i2 : required_594_i2 =
    ((Finset.univ.biUnion childrenC_594_i2) ∪ commonEnvelope childrenD_594_i2).erase (2, 3) := by
  exact required_eq_combination childrenC_594_i2 childrenD_594_i2 (2, 3) required_594_i2
    (by decide +kernel) child_required_sub_594_i2 common_sub_594_i2 required_origin_594_i2
theorem envelope_origin_594_i2 : ∀ x ∈ envelope_594_i2,
    x = (2, 3) ∨ ∃ j, x ∈ childrenD_594_i2 j := by decide +kernel
theorem envelope_exact_594_i2 : envelope_594_i2 =
    insert (2, 3) (Finset.univ.biUnion childrenD_594_i2) := by
  exact envelope_eq_combination childrenD_594_i2 (2, 3) envelope_594_i2
    pivot_mem_594_i2 child_envelope_sub_594_i2 envelope_origin_594_i2
def checked_594_i2 : CheckedCard where
  required := required_594_i2
  envelope := envelope_594_i2
  height := height_594_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_594_i2
def height_594_i8 : ℕ := 5
def childrenH_594_i8 : Fin 2 → ℕ := ![height_1, height_268]
theorem height_exact_594_i8 : height_594_i8 = 1 + Finset.univ.sup childrenH_594_i8 := by decide +kernel
theorem required_origin_594_i8 : ∀ x ∈ required_594_i8,
    (∃ j, x ∈ childrenC_594_i8 j) ∨ ∀ j, x ∈ childrenD_594_i8 j := by decide +kernel
theorem required_exact_594_i8 : required_594_i8 =
    ((Finset.univ.biUnion childrenC_594_i8) ∪ commonEnvelope childrenD_594_i8).erase (2, 3) := by
  exact required_eq_combination childrenC_594_i8 childrenD_594_i8 (2, 3) required_594_i8
    (by decide +kernel) child_required_sub_594_i8 common_sub_594_i8 required_origin_594_i8
theorem envelope_origin_594_i8 : ∀ x ∈ envelope_594_i8,
    x = (2, 3) ∨ ∃ j, x ∈ childrenD_594_i8 j := by decide +kernel
theorem envelope_exact_594_i8 : envelope_594_i8 =
    insert (2, 3) (Finset.univ.biUnion childrenD_594_i8) := by
  exact envelope_eq_combination childrenD_594_i8 (2, 3) envelope_594_i8
    pivot_mem_594_i8 child_envelope_sub_594_i8 envelope_origin_594_i8
def checked_594_i8 : CheckedCard where
  required := required_594_i8
  envelope := envelope_594_i8
  height := height_594_i8
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_594_i8
def height_594_i1 : ℕ := 9
def childrenH_594_i1 : Fin 5 → ℕ := ![height_272, height_290, height_594_i2, height_594_i8, height_593]
theorem height_exact_594_i1 : height_594_i1 = 1 + Finset.univ.sup childrenH_594_i1 := by decide +kernel
theorem required_origin_594_i1 : ∀ x ∈ required_594_i1,
    (∃ j, x ∈ childrenC_594_i1 j) ∨ ∀ j, x ∈ childrenD_594_i1 j := by decide +kernel
theorem required_exact_594_i1 : required_594_i1 =
    ((Finset.univ.biUnion childrenC_594_i1) ∪ commonEnvelope childrenD_594_i1).erase (2, 6) := by
  exact required_eq_combination childrenC_594_i1 childrenD_594_i1 (2, 6) required_594_i1
    (by decide +kernel) child_required_sub_594_i1 common_sub_594_i1 required_origin_594_i1
theorem envelope_origin_594_i1 : ∀ x ∈ envelope_594_i1,
    x = (2, 6) ∨ ∃ j, x ∈ childrenD_594_i1 j := by decide +kernel
theorem envelope_exact_594_i1 : envelope_594_i1 =
    insert (2, 6) (Finset.univ.biUnion childrenD_594_i1) := by
  exact envelope_eq_combination childrenD_594_i1 (2, 6) envelope_594_i1
    pivot_mem_594_i1 child_envelope_sub_594_i1 envelope_origin_594_i1
def checked_594_i1 : CheckedCard where
  required := required_594_i1
  envelope := envelope_594_i1
  height := height_594_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_594_i1
def height_594 : ℕ := 10
def childrenH_594 : Fin 3 → ℕ := ![height_53, height_594_i0, height_594_i1]
theorem height_exact_594 : height_594 = 1 + Finset.univ.sup childrenH_594 := by decide +kernel
theorem required_origin_594 : ∀ x ∈ required_594,
    (∃ j, x ∈ childrenC_594 j) ∨ ∀ j, x ∈ childrenD_594 j := by decide +kernel
theorem required_exact_594 : required_594 =
    ((Finset.univ.biUnion childrenC_594) ∪ commonEnvelope childrenD_594).erase (6, 4) := by
  exact required_eq_combination childrenC_594 childrenD_594 (6, 4) required_594
    (by decide +kernel) child_required_sub_594 common_sub_594 required_origin_594
theorem envelope_origin_594 : ∀ x ∈ envelope_594,
    x = (6, 4) ∨ ∃ j, x ∈ childrenD_594 j := by decide +kernel
theorem envelope_exact_594 : envelope_594 =
    insert (6, 4) (Finset.univ.biUnion childrenD_594) := by
  exact envelope_eq_combination childrenD_594 (6, 4) envelope_594
    pivot_mem_594 child_envelope_sub_594 envelope_origin_594
def checked_594 : CheckedCard where
  required := required_594
  envelope := envelope_594
  height := height_594
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_594
def height_608_i1 : ℕ := 5
def childrenH_608_i1 : Fin 2 → ℕ := ![height_18, height_375]
theorem height_exact_608_i1 : height_608_i1 = 1 + Finset.univ.sup childrenH_608_i1 := by decide +kernel
theorem required_origin_608_i1 : ∀ x ∈ required_608_i1,
    (∃ j, x ∈ childrenC_608_i1 j) ∨ ∀ j, x ∈ childrenD_608_i1 j := by decide +kernel
theorem required_exact_608_i1 : required_608_i1 =
    ((Finset.univ.biUnion childrenC_608_i1) ∪ commonEnvelope childrenD_608_i1).erase (5, 3) := by
  exact required_eq_combination childrenC_608_i1 childrenD_608_i1 (5, 3) required_608_i1
    (by decide +kernel) child_required_sub_608_i1 common_sub_608_i1 required_origin_608_i1
theorem envelope_origin_608_i1 : ∀ x ∈ envelope_608_i1,
    x = (5, 3) ∨ ∃ j, x ∈ childrenD_608_i1 j := by decide +kernel
theorem envelope_exact_608_i1 : envelope_608_i1 =
    insert (5, 3) (Finset.univ.biUnion childrenD_608_i1) := by
  exact envelope_eq_combination childrenD_608_i1 (5, 3) envelope_608_i1
    pivot_mem_608_i1 child_envelope_sub_608_i1 envelope_origin_608_i1
def checked_608_i1 : CheckedCard where
  required := required_608_i1
  envelope := envelope_608_i1
  height := height_608_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_608_i1
def height_608_i2 : ℕ := 5
def childrenH_608_i2 : Fin 2 → ℕ := ![height_28, height_42]
theorem height_exact_608_i2 : height_608_i2 = 1 + Finset.univ.sup childrenH_608_i2 := by decide +kernel
theorem required_origin_608_i2 : ∀ x ∈ required_608_i2,
    (∃ j, x ∈ childrenC_608_i2 j) ∨ ∀ j, x ∈ childrenD_608_i2 j := by decide +kernel
theorem required_exact_608_i2 : required_608_i2 =
    ((Finset.univ.biUnion childrenC_608_i2) ∪ commonEnvelope childrenD_608_i2).erase (2, 5) := by
  exact required_eq_combination childrenC_608_i2 childrenD_608_i2 (2, 5) required_608_i2
    (by decide +kernel) child_required_sub_608_i2 common_sub_608_i2 required_origin_608_i2
theorem envelope_origin_608_i2 : ∀ x ∈ envelope_608_i2,
    x = (2, 5) ∨ ∃ j, x ∈ childrenD_608_i2 j := by decide +kernel
theorem envelope_exact_608_i2 : envelope_608_i2 =
    insert (2, 5) (Finset.univ.biUnion childrenD_608_i2) := by
  exact envelope_eq_combination childrenD_608_i2 (2, 5) envelope_608_i2
    pivot_mem_608_i2 child_envelope_sub_608_i2 envelope_origin_608_i2
def checked_608_i2 : CheckedCard where
  required := required_608_i2
  envelope := envelope_608_i2
  height := height_608_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_608_i2
def height_608_i3 : ℕ := 5
def childrenH_608_i3 : Fin 2 → ℕ := ![height_42, height_58]
theorem height_exact_608_i3 : height_608_i3 = 1 + Finset.univ.sup childrenH_608_i3 := by decide +kernel
theorem required_origin_608_i3 : ∀ x ∈ required_608_i3,
    (∃ j, x ∈ childrenC_608_i3 j) ∨ ∀ j, x ∈ childrenD_608_i3 j := by decide +kernel
theorem required_exact_608_i3 : required_608_i3 =
    ((Finset.univ.biUnion childrenC_608_i3) ∪ commonEnvelope childrenD_608_i3).erase (2, 5) := by
  exact required_eq_combination childrenC_608_i3 childrenD_608_i3 (2, 5) required_608_i3
    (by decide +kernel) child_required_sub_608_i3 common_sub_608_i3 required_origin_608_i3
theorem envelope_origin_608_i3 : ∀ x ∈ envelope_608_i3,
    x = (2, 5) ∨ ∃ j, x ∈ childrenD_608_i3 j := by decide +kernel
theorem envelope_exact_608_i3 : envelope_608_i3 =
    insert (2, 5) (Finset.univ.biUnion childrenD_608_i3) := by
  exact envelope_eq_combination childrenD_608_i3 (2, 5) envelope_608_i3
    pivot_mem_608_i3 child_envelope_sub_608_i3 envelope_origin_608_i3
def checked_608_i3 : CheckedCard where
  required := required_608_i3
  envelope := envelope_608_i3
  height := height_608_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_608_i3
def height_608_i0 : ℕ := 6
def childrenH_608_i0 : Fin 3 → ℕ := ![height_608_i1, height_608_i2, height_608_i3]
theorem height_exact_608_i0 : height_608_i0 = 1 + Finset.univ.sup childrenH_608_i0 := by decide +kernel
theorem required_origin_608_i0 : ∀ x ∈ required_608_i0,
    (∃ j, x ∈ childrenC_608_i0 j) ∨ ∀ j, x ∈ childrenD_608_i0 j := by decide +kernel
theorem required_exact_608_i0 : required_608_i0 =
    ((Finset.univ.biUnion childrenC_608_i0) ∪ commonEnvelope childrenD_608_i0).erase (1, 2) := by
  exact required_eq_combination childrenC_608_i0 childrenD_608_i0 (1, 2) required_608_i0
    (by decide +kernel) child_required_sub_608_i0 common_sub_608_i0 required_origin_608_i0
theorem envelope_origin_608_i0 : ∀ x ∈ envelope_608_i0,
    x = (1, 2) ∨ ∃ j, x ∈ childrenD_608_i0 j := by decide +kernel
theorem envelope_exact_608_i0 : envelope_608_i0 =
    insert (1, 2) (Finset.univ.biUnion childrenD_608_i0) := by
  exact envelope_eq_combination childrenD_608_i0 (1, 2) envelope_608_i0
    pivot_mem_608_i0 child_envelope_sub_608_i0 envelope_origin_608_i0
def checked_608_i0 : CheckedCard where
  required := required_608_i0
  envelope := envelope_608_i0
  height := height_608_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_608_i0
def height_608 : ℕ := 10
def childrenH_608 : Fin 6 → ℕ := ![height_13, height_31, height_355, height_364, height_434, height_608_i0]
theorem height_exact_608 : height_608 = 1 + Finset.univ.sup childrenH_608 := by decide +kernel
theorem required_origin_608 : ∀ x ∈ required_608,
    (∃ j, x ∈ childrenC_608 j) ∨ ∀ j, x ∈ childrenD_608 j := by decide +kernel
theorem required_exact_608 : required_608 =
    ((Finset.univ.biUnion childrenC_608) ∪ commonEnvelope childrenD_608).erase (4, 6) := by
  exact required_eq_combination childrenC_608 childrenD_608 (4, 6) required_608
    (by decide +kernel) child_required_sub_608 common_sub_608 required_origin_608
theorem envelope_origin_608 : ∀ x ∈ envelope_608,
    x = (4, 6) ∨ ∃ j, x ∈ childrenD_608 j := by decide +kernel
theorem envelope_exact_608 : envelope_608 =
    insert (4, 6) (Finset.univ.biUnion childrenD_608) := by
  exact envelope_eq_combination childrenD_608 (4, 6) envelope_608
    pivot_mem_608 child_envelope_sub_608 envelope_origin_608
def checked_608 : CheckedCard where
  required := required_608
  envelope := envelope_608
  height := height_608
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_608
def height_616_i1 : ℕ := 3
def childrenH_616_i1 : Fin 2 → ℕ := ![height_6, height_123]
theorem height_exact_616_i1 : height_616_i1 = 1 + Finset.univ.sup childrenH_616_i1 := by decide +kernel
theorem required_origin_616_i1 : ∀ x ∈ required_616_i1,
    (∃ j, x ∈ childrenC_616_i1 j) ∨ ∀ j, x ∈ childrenD_616_i1 j := by decide +kernel
theorem required_exact_616_i1 : required_616_i1 =
    ((Finset.univ.biUnion childrenC_616_i1) ∪ commonEnvelope childrenD_616_i1).erase (2, 6) := by
  exact required_eq_combination childrenC_616_i1 childrenD_616_i1 (2, 6) required_616_i1
    (by decide +kernel) child_required_sub_616_i1 common_sub_616_i1 required_origin_616_i1
theorem envelope_origin_616_i1 : ∀ x ∈ envelope_616_i1,
    x = (2, 6) ∨ ∃ j, x ∈ childrenD_616_i1 j := by decide +kernel
theorem envelope_exact_616_i1 : envelope_616_i1 =
    insert (2, 6) (Finset.univ.biUnion childrenD_616_i1) := by
  exact envelope_eq_combination childrenD_616_i1 (2, 6) envelope_616_i1
    pivot_mem_616_i1 child_envelope_sub_616_i1 envelope_origin_616_i1
def checked_616_i1 : CheckedCard where
  required := required_616_i1
  envelope := envelope_616_i1
  height := height_616_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_616_i1
def height_616_i0 : ℕ := 7
def childrenH_616_i0 : Fin 3 → ℕ := ![height_11, height_616_i1, height_521]
theorem height_exact_616_i0 : height_616_i0 = 1 + Finset.univ.sup childrenH_616_i0 := by decide +kernel
theorem required_origin_616_i0 : ∀ x ∈ required_616_i0,
    (∃ j, x ∈ childrenC_616_i0 j) ∨ ∀ j, x ∈ childrenD_616_i0 j := by decide +kernel
theorem required_exact_616_i0 : required_616_i0 =
    ((Finset.univ.biUnion childrenC_616_i0) ∪ commonEnvelope childrenD_616_i0).erase (2, 5) := by
  exact required_eq_combination childrenC_616_i0 childrenD_616_i0 (2, 5) required_616_i0
    (by decide +kernel) child_required_sub_616_i0 common_sub_616_i0 required_origin_616_i0
theorem envelope_origin_616_i0 : ∀ x ∈ envelope_616_i0,
    x = (2, 5) ∨ ∃ j, x ∈ childrenD_616_i0 j := by decide +kernel
theorem envelope_exact_616_i0 : envelope_616_i0 =
    insert (2, 5) (Finset.univ.biUnion childrenD_616_i0) := by
  exact envelope_eq_combination childrenD_616_i0 (2, 5) envelope_616_i0
    pivot_mem_616_i0 child_envelope_sub_616_i0 envelope_origin_616_i0
def checked_616_i0 : CheckedCard where
  required := required_616_i0
  envelope := envelope_616_i0
  height := height_616_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_616_i0
def height_616 : ℕ := 10
def childrenH_616 : Fin 7 → ℕ := ![height_345, height_421, height_522, height_530, height_533, height_534, height_616_i0]
theorem height_exact_616 : height_616 = 1 + Finset.univ.sup childrenH_616 := by decide +kernel
theorem required_origin_616 : ∀ x ∈ required_616,
    (∃ j, x ∈ childrenC_616 j) ∨ ∀ j, x ∈ childrenD_616 j := by decide +kernel
theorem required_exact_616 : required_616 =
    ((Finset.univ.biUnion childrenC_616) ∪ commonEnvelope childrenD_616).erase (3, 3) := by
  exact required_eq_combination childrenC_616 childrenD_616 (3, 3) required_616
    (by decide +kernel) child_required_sub_616 common_sub_616 required_origin_616
theorem envelope_origin_616 : ∀ x ∈ envelope_616,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_616 j := by decide +kernel
theorem envelope_exact_616 : envelope_616 =
    insert (3, 3) (Finset.univ.biUnion childrenD_616) := by
  exact envelope_eq_combination childrenD_616 (3, 3) envelope_616
    pivot_mem_616 child_envelope_sub_616 envelope_origin_616
def checked_616 : CheckedCard where
  required := required_616
  envelope := envelope_616
  height := height_616
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_616
def height_631_i1 : ℕ := 8
def childrenH_631_i1 : Fin 2 → ℕ := ![height_45, height_418]
theorem height_exact_631_i1 : height_631_i1 = 1 + Finset.univ.sup childrenH_631_i1 := by decide +kernel
theorem required_origin_631_i1 : ∀ x ∈ required_631_i1,
    (∃ j, x ∈ childrenC_631_i1 j) ∨ ∀ j, x ∈ childrenD_631_i1 j := by decide +kernel
theorem required_exact_631_i1 : required_631_i1 =
    ((Finset.univ.biUnion childrenC_631_i1) ∪ commonEnvelope childrenD_631_i1).erase (3, 2) := by
  exact required_eq_combination childrenC_631_i1 childrenD_631_i1 (3, 2) required_631_i1
    (by decide +kernel) child_required_sub_631_i1 common_sub_631_i1 required_origin_631_i1
theorem envelope_origin_631_i1 : ∀ x ∈ envelope_631_i1,
    x = (3, 2) ∨ ∃ j, x ∈ childrenD_631_i1 j := by decide +kernel
theorem envelope_exact_631_i1 : envelope_631_i1 =
    insert (3, 2) (Finset.univ.biUnion childrenD_631_i1) := by
  exact envelope_eq_combination childrenD_631_i1 (3, 2) envelope_631_i1
    pivot_mem_631_i1 child_envelope_sub_631_i1 envelope_origin_631_i1
def checked_631_i1 : CheckedCard where
  required := required_631_i1
  envelope := envelope_631_i1
  height := height_631_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_631_i1
def height_631_i0 : ℕ := 9
def childrenH_631_i0 : Fin 3 → ℕ := ![height_43, height_51, height_631_i1]
theorem height_exact_631_i0 : height_631_i0 = 1 + Finset.univ.sup childrenH_631_i0 := by decide +kernel
theorem required_origin_631_i0 : ∀ x ∈ required_631_i0,
    (∃ j, x ∈ childrenC_631_i0 j) ∨ ∀ j, x ∈ childrenD_631_i0 j := by decide +kernel
theorem required_exact_631_i0 : required_631_i0 =
    ((Finset.univ.biUnion childrenC_631_i0) ∪ commonEnvelope childrenD_631_i0).erase (4, 2) := by
  exact required_eq_combination childrenC_631_i0 childrenD_631_i0 (4, 2) required_631_i0
    (by decide +kernel) child_required_sub_631_i0 common_sub_631_i0 required_origin_631_i0
theorem envelope_origin_631_i0 : ∀ x ∈ envelope_631_i0,
    x = (4, 2) ∨ ∃ j, x ∈ childrenD_631_i0 j := by decide +kernel
theorem envelope_exact_631_i0 : envelope_631_i0 =
    insert (4, 2) (Finset.univ.biUnion childrenD_631_i0) := by
  exact envelope_eq_combination childrenD_631_i0 (4, 2) envelope_631_i0
    pivot_mem_631_i0 child_envelope_sub_631_i0 envelope_origin_631_i0
def checked_631_i0 : CheckedCard where
  required := required_631_i0
  envelope := envelope_631_i0
  height := height_631_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_631_i0
def height_631 : ℕ := 10
def childrenH_631 : Fin 4 → ℕ := ![height_44, height_52, height_63, height_631_i0]
theorem height_exact_631 : height_631 = 1 + Finset.univ.sup childrenH_631 := by decide +kernel
theorem required_origin_631 : ∀ x ∈ required_631,
    (∃ j, x ∈ childrenC_631 j) ∨ ∀ j, x ∈ childrenD_631 j := by decide +kernel
theorem required_exact_631 : required_631 =
    ((Finset.univ.biUnion childrenC_631) ∪ commonEnvelope childrenD_631).erase (3, 5) := by
  exact required_eq_combination childrenC_631 childrenD_631 (3, 5) required_631
    (by decide +kernel) child_required_sub_631 common_sub_631 required_origin_631
theorem envelope_origin_631 : ∀ x ∈ envelope_631,
    x = (3, 5) ∨ ∃ j, x ∈ childrenD_631 j := by decide +kernel
theorem envelope_exact_631 : envelope_631 =
    insert (3, 5) (Finset.univ.biUnion childrenD_631) := by
  exact envelope_eq_combination childrenD_631 (3, 5) envelope_631
    pivot_mem_631 child_envelope_sub_631 envelope_origin_631
def checked_631 : CheckedCard where
  required := required_631
  envelope := envelope_631
  height := height_631
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_631
end SnakyPrototype.Certificate21

end OAI
