import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part06
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height10Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height11Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height12Part02
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_564_i2 : Finset Cell := ⟨(([(3, 4), (4, 4), (5, 4), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_564_i2 : Finset Cell := ⟨(([(1, 3), (1, 5), (1, 6), (1, 7), (1, 8), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 4), (4, 5), (4, 6), (5, 4), (5, 5), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_564_i2 : Fin 2 → Finset Cell := ![(placed21 0 (2, 4) required_5), (placed21 2 (5, 3) required_453)]
def childrenD_564_i2 : Fin 2 → Finset Cell := ![(placed21 0 (2, 4) envelope_5), (placed21 2 (5, 3) envelope_453)]
theorem common_sub_564_i2 : commonEnvelope childrenD_564_i2 ⊆ insert (2, 4) required_564_i2 := by decide +kernel
theorem child_required_sub_564_i2 : ∀ j, childrenC_564_i2 j ⊆ insert (2, 4) required_564_i2 := by decide +kernel
theorem child_envelope_sub_564_i2 : ∀ j, childrenD_564_i2 j ⊆ envelope_564_i2 := by decide +kernel
theorem pivot_mem_564_i2 : (2, 4) ∈ envelope_564_i2 := by decide +kernel
theorem children_work_564_i2 : ∀ j, Template HasSnaky 7 (childrenC_564_i2 j) (childrenD_564_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 0 (2, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_453 2 (5, 3)).mono (by decide +kernel)
theorem row_works_564_i2 : Template HasSnaky 8 required_564_i2 envelope_564_i2 := by
  refine compose HasSnaky 7 childrenC_564_i2 childrenD_564_i2 children_work_564_i2 (2, 4)
    required_564_i2 envelope_564_i2 pivot_mem_564_i2 child_required_sub_564_i2 child_envelope_sub_564_i2 ?_
  intro b hb
  exact common_sub_564_i2 (mem_commonEnvelope childrenD_564_i2 b hb)
def required_564_i7 : Finset Cell := ⟨(([(2, 5), (3, 4), (4, 5), (5, 5), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_564_i7 : Finset Cell := ⟨(([(1, 6), (2, 5), (2, 6), (2, 7), (2, 8), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 5), (5, 5), (5, 6), (6, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_564_i7 : Fin 2 → Finset Cell := ![(placed21 0 (2, 5) required_5), (placed21 2 (5, 2) required_55)]
def childrenD_564_i7 : Fin 2 → Finset Cell := ![(placed21 0 (2, 5) envelope_5), (placed21 2 (5, 2) envelope_55)]
theorem common_sub_564_i7 : commonEnvelope childrenD_564_i7 ⊆ insert (3, 5) required_564_i7 := by decide +kernel
theorem child_required_sub_564_i7 : ∀ j, childrenC_564_i7 j ⊆ insert (3, 5) required_564_i7 := by decide +kernel
theorem child_envelope_sub_564_i7 : ∀ j, childrenD_564_i7 j ⊆ envelope_564_i7 := by decide +kernel
theorem pivot_mem_564_i7 : (3, 5) ∈ envelope_564_i7 := by decide +kernel
theorem children_work_564_i7 : ∀ j, Template HasSnaky 4 (childrenC_564_i7 j) (childrenD_564_i7 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 0 (2, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_55 2 (5, 2)).mono (by decide +kernel)
theorem row_works_564_i7 : Template HasSnaky 5 required_564_i7 envelope_564_i7 := by
  refine compose HasSnaky 4 childrenC_564_i7 childrenD_564_i7 children_work_564_i7 (3, 5)
    required_564_i7 envelope_564_i7 pivot_mem_564_i7 child_required_sub_564_i7 child_envelope_sub_564_i7 ?_
  intro b hb
  exact common_sub_564_i7 (mem_commonEnvelope childrenD_564_i7 b hb)
def required_564_i8 : Finset Cell := ⟨(([(2, 5), (3, 4), (4, 4), (4, 5), (5, 4), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_564_i8 : Finset Cell := ⟨(([(1, 3), (1, 5), (1, 6), (1, 7), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 2), (3, 3), (3, 4), (3, 6), (3, 7), (4, 4), (4, 5), (4, 6), (5, 4), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_564_i8 : Fin 2 → Finset Cell := ![(placed21 2 (5, 4) required_5), (placed21 2 (5, 2) required_342)]
def childrenD_564_i8 : Fin 2 → Finset Cell := ![(placed21 2 (5, 4) envelope_5), (placed21 2 (5, 2) envelope_342)]
theorem common_sub_564_i8 : commonEnvelope childrenD_564_i8 ⊆ insert (2, 4) required_564_i8 := by decide +kernel
theorem child_required_sub_564_i8 : ∀ j, childrenC_564_i8 j ⊆ insert (2, 4) required_564_i8 := by decide +kernel
theorem child_envelope_sub_564_i8 : ∀ j, childrenD_564_i8 j ⊆ envelope_564_i8 := by decide +kernel
theorem pivot_mem_564_i8 : (2, 4) ∈ envelope_564_i8 := by decide +kernel
theorem children_work_564_i8 : ∀ j, Template HasSnaky 5 (childrenC_564_i8 j) (childrenD_564_i8 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 2 (5, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_342 2 (5, 2)).mono (by decide +kernel)
theorem row_works_564_i8 : Template HasSnaky 6 required_564_i8 envelope_564_i8 := by
  refine compose HasSnaky 5 childrenC_564_i8 childrenD_564_i8 children_work_564_i8 (2, 4)
    required_564_i8 envelope_564_i8 pivot_mem_564_i8 child_required_sub_564_i8 child_envelope_sub_564_i8 ?_
  intro b hb
  exact common_sub_564_i8 (mem_commonEnvelope childrenD_564_i8 b hb)
def required_564_i6 : Finset Cell := ⟨(([(3, 4), (4, 4), (4, 5), (5, 4), (5, 5), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_564_i6 : Finset Cell := ⟨(([(1, 3), (1, 5), (1, 6), (1, 7), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 4), (4, 5), (4, 6), (5, 4), (5, 5), (5, 6), (6, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_564_i6 : Fin 3 → Finset Cell := ![(placed21 5 (6, 4) required_102), required_564_i7, required_564_i8]
def childrenD_564_i6 : Fin 3 → Finset Cell := ![(placed21 5 (6, 4) envelope_102), envelope_564_i7, envelope_564_i8]
theorem common_sub_564_i6 : commonEnvelope childrenD_564_i6 ⊆ insert (2, 5) required_564_i6 := by decide +kernel
theorem child_required_sub_564_i6 : ∀ j, childrenC_564_i6 j ⊆ insert (2, 5) required_564_i6 := by decide +kernel
theorem child_envelope_sub_564_i6 : ∀ j, childrenD_564_i6 j ⊆ envelope_564_i6 := by decide +kernel
theorem pivot_mem_564_i6 : (2, 5) ∈ envelope_564_i6 := by decide +kernel
theorem children_work_564_i6 : ∀ j, Template HasSnaky 6 (childrenC_564_i6 j) (childrenD_564_i6 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_102 5 (6, 4)).mono (by decide +kernel)
  · exact row_works_564_i7.mono (by decide +kernel)
  · exact row_works_564_i8.mono (by decide +kernel)
theorem row_works_564_i6 : Template HasSnaky 7 required_564_i6 envelope_564_i6 := by
  refine compose HasSnaky 6 childrenC_564_i6 childrenD_564_i6 children_work_564_i6 (2, 5)
    required_564_i6 envelope_564_i6 pivot_mem_564_i6 child_required_sub_564_i6 child_envelope_sub_564_i6 ?_
  intro b hb
  exact common_sub_564_i6 (mem_commonEnvelope childrenD_564_i6 b hb)
def required_564_i5 : Finset Cell := ⟨(([(3, 4), (4, 4), (5, 4), (5, 5), (5, 6), (5, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_564_i5 : Finset Cell := ⟨(([(1, 3), (1, 5), (1, 6), (1, 7), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 4), (4, 5), (4, 6), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_564_i5 : Fin 2 → Finset Cell := ![(placed21 7 (5, 8) required_0), required_564_i6]
def childrenD_564_i5 : Fin 2 → Finset Cell := ![(placed21 7 (5, 8) envelope_0), envelope_564_i6]
theorem common_sub_564_i5 : commonEnvelope childrenD_564_i5 ⊆ insert (4, 5) required_564_i5 := by decide +kernel
theorem child_required_sub_564_i5 : ∀ j, childrenC_564_i5 j ⊆ insert (4, 5) required_564_i5 := by decide +kernel
theorem child_envelope_sub_564_i5 : ∀ j, childrenD_564_i5 j ⊆ envelope_564_i5 := by decide +kernel
theorem pivot_mem_564_i5 : (4, 5) ∈ envelope_564_i5 := by decide +kernel
theorem children_work_564_i5 : ∀ j, Template HasSnaky 7 (childrenC_564_i5 j) (childrenD_564_i5 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 7 (5, 8)).mono (by decide +kernel)
  · exact row_works_564_i6.mono (by decide +kernel)
theorem row_works_564_i5 : Template HasSnaky 8 required_564_i5 envelope_564_i5 := by
  refine compose HasSnaky 7 childrenC_564_i5 childrenD_564_i5 children_work_564_i5 (4, 5)
    required_564_i5 envelope_564_i5 pivot_mem_564_i5 child_required_sub_564_i5 child_envelope_sub_564_i5 ?_
  intro b hb
  exact common_sub_564_i5 (mem_commonEnvelope childrenD_564_i5 b hb)
def required_564_i4 : Finset Cell := ⟨(([(3, 4), (4, 4), (5, 4), (5, 5), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_564_i4 : Finset Cell := ⟨(([(1, 3), (1, 5), (1, 6), (1, 7), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 2), (6, 3), (6, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_564_i4 : Fin 3 → Finset Cell := ![(placed21 2 (5, 4) required_16), (placed21 6 (6, 8) required_235), required_564_i5]
def childrenD_564_i4 : Fin 3 → Finset Cell := ![(placed21 2 (5, 4) envelope_16), (placed21 6 (6, 8) envelope_235), envelope_564_i5]
theorem common_sub_564_i4 : commonEnvelope childrenD_564_i4 ⊆ insert (5, 7) required_564_i4 := by decide +kernel
theorem child_required_sub_564_i4 : ∀ j, childrenC_564_i4 j ⊆ insert (5, 7) required_564_i4 := by decide +kernel
theorem child_envelope_sub_564_i4 : ∀ j, childrenD_564_i4 j ⊆ envelope_564_i4 := by decide +kernel
theorem pivot_mem_564_i4 : (5, 7) ∈ envelope_564_i4 := by decide +kernel
theorem children_work_564_i4 : ∀ j, Template HasSnaky 8 (childrenC_564_i4 j) (childrenD_564_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_16 2 (5, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_235 6 (6, 8)).mono (by decide +kernel)
  · exact row_works_564_i5.mono (by decide +kernel)
theorem row_works_564_i4 : Template HasSnaky 9 required_564_i4 envelope_564_i4 := by
  refine compose HasSnaky 8 childrenC_564_i4 childrenD_564_i4 children_work_564_i4 (5, 7)
    required_564_i4 envelope_564_i4 pivot_mem_564_i4 child_required_sub_564_i4 child_envelope_sub_564_i4 ?_
  intro b hb
  exact common_sub_564_i4 (mem_commonEnvelope childrenD_564_i4 b hb)
def required_564_i3 : Finset Cell := ⟨(([(3, 4), (4, 4), (5, 4), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_564_i3 : Finset Cell := ⟨(([(0, 5), (1, 3), (1, 5), (1, 6), (1, 7), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 2), (6, 3), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, 5), (7, 6), (7, 7), (8, 5), (8, 6), (8, 7), (9, 5), (9, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_564_i3 : Fin 7 → Finset Cell := ![(placed21 2 (6, 2) required_67), (placed21 5 (7, 3) required_134), (placed21 5 (7, 3) required_180), (placed21 7 (9, 7) required_327), (placed21 0 (2, 2) required_504), (placed21 5 (7, 4) required_558), required_564_i4]
def childrenD_564_i3 : Fin 7 → Finset Cell := ![(placed21 2 (6, 2) envelope_67), (placed21 5 (7, 3) envelope_134), (placed21 5 (7, 3) envelope_180), (placed21 7 (9, 7) envelope_327), (placed21 0 (2, 2) envelope_504), (placed21 5 (7, 4) envelope_558), envelope_564_i4]
theorem common_sub_564_i3 : commonEnvelope childrenD_564_i3 ⊆ insert (5, 6) required_564_i3 := by decide +kernel
theorem child_required_sub_564_i3 : ∀ j, childrenC_564_i3 j ⊆ insert (5, 6) required_564_i3 := by decide +kernel
theorem child_envelope_sub_564_i3 : ∀ j, childrenD_564_i3 j ⊆ envelope_564_i3 := by decide +kernel
theorem pivot_mem_564_i3 : (5, 6) ∈ envelope_564_i3 := by decide +kernel
theorem children_work_564_i3 : ∀ j, Template HasSnaky 9 (childrenC_564_i3 j) (childrenD_564_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_67 2 (6, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_134 5 (7, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_180 5 (7, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_327 7 (9, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_504 0 (2, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_558 5 (7, 4)).mono (by decide +kernel)
  · exact row_works_564_i4.mono (by decide +kernel)
theorem row_works_564_i3 : Template HasSnaky 10 required_564_i3 envelope_564_i3 := by
  refine compose HasSnaky 9 childrenC_564_i3 childrenD_564_i3 children_work_564_i3 (5, 6)
    required_564_i3 envelope_564_i3 pivot_mem_564_i3 child_required_sub_564_i3 child_envelope_sub_564_i3 ?_
  intro b hb
  exact common_sub_564_i3 (mem_commonEnvelope childrenD_564_i3 b hb)
def required_564_i1 : Finset Cell := ⟨(([(3, 4), (4, 1), (4, 2), (4, 4), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_564_i1 : Finset Cell := ⟨(([(0, 5), (1, 3), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 1), (4, 2), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 2), (6, 3), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (8, 5), (8, 6), (8, 7), (9, 5), (9, 6), (9, 7), (10, 5), (10, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_564_i1 : Fin 5 → Finset Cell := ![(placed21 1 (2, 4) required_44), required_564_i2, required_564_i3, (placed21 1 (1, 1) required_560), (placed21 1 (0, 3) required_563)]
def childrenD_564_i1 : Fin 5 → Finset Cell := ![(placed21 1 (2, 4) envelope_44), envelope_564_i2, envelope_564_i3, (placed21 1 (1, 1) envelope_560), (placed21 1 (0, 3) envelope_563)]
theorem common_sub_564_i1 : commonEnvelope childrenD_564_i1 ⊆ insert (5, 5) required_564_i1 := by decide +kernel
theorem child_required_sub_564_i1 : ∀ j, childrenC_564_i1 j ⊆ insert (5, 5) required_564_i1 := by decide +kernel
theorem child_envelope_sub_564_i1 : ∀ j, childrenD_564_i1 j ⊆ envelope_564_i1 := by decide +kernel
theorem pivot_mem_564_i1 : (5, 5) ∈ envelope_564_i1 := by decide +kernel
theorem children_work_564_i1 : ∀ j, Template HasSnaky 10 (childrenC_564_i1 j) (childrenD_564_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_44 1 (2, 4)).mono (by decide +kernel)
  · exact row_works_564_i2.mono (by decide +kernel)
  · exact row_works_564_i3.mono (by decide +kernel)
  · exact (placed21_template row_works_560 1 (1, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_563 1 (0, 3)).mono (by decide +kernel)
theorem row_works_564_i1 : Template HasSnaky 11 required_564_i1 envelope_564_i1 := by
  refine compose HasSnaky 10 childrenC_564_i1 childrenD_564_i1 children_work_564_i1 (5, 5)
    required_564_i1 envelope_564_i1 pivot_mem_564_i1 child_required_sub_564_i1 child_envelope_sub_564_i1 ?_
  intro b hb
  exact common_sub_564_i1 (mem_commonEnvelope childrenD_564_i1 b hb)
def required_564_i0 : Finset Cell := ⟨(([(3, 4), (4, 1), (4, 2), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_564_i0 : Finset Cell := ⟨(([(0, 5), (1, 3), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 1), (4, 2), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (8, 3), (8, 5), (8, 6), (8, 7), (9, 5), (9, 6), (9, 7), (10, 5), (10, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_564_i0 : Fin 6 → Finset Cell := ![(placed21 1 (1, 3) required_12), (placed21 3 (1, 5) required_12), (placed21 1 (2, 1) required_79), (placed21 1 (1, 2) required_135), (placed21 3 (1, 6) required_182), required_564_i1]
def childrenD_564_i0 : Fin 6 → Finset Cell := ![(placed21 1 (1, 3) envelope_12), (placed21 3 (1, 5) envelope_12), (placed21 1 (2, 1) envelope_79), (placed21 1 (1, 2) envelope_135), (placed21 3 (1, 6) envelope_182), envelope_564_i1]
theorem common_sub_564_i0 : commonEnvelope childrenD_564_i0 ⊆ insert (5, 4) required_564_i0 := by decide +kernel
theorem child_required_sub_564_i0 : ∀ j, childrenC_564_i0 j ⊆ insert (5, 4) required_564_i0 := by decide +kernel
theorem child_envelope_sub_564_i0 : ∀ j, childrenD_564_i0 j ⊆ envelope_564_i0 := by decide +kernel
theorem pivot_mem_564_i0 : (5, 4) ∈ envelope_564_i0 := by decide +kernel
theorem children_work_564_i0 : ∀ j, Template HasSnaky 11 (childrenC_564_i0 j) (childrenD_564_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_12 1 (1, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_12 3 (1, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_79 1 (2, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_135 1 (1, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_182 3 (1, 6)).mono (by decide +kernel)
  · exact row_works_564_i1.mono (by decide +kernel)
theorem row_works_564_i0 : Template HasSnaky 12 required_564_i0 envelope_564_i0 := by
  refine compose HasSnaky 11 childrenC_564_i0 childrenD_564_i0 children_work_564_i0 (5, 4)
    required_564_i0 envelope_564_i0 pivot_mem_564_i0 child_required_sub_564_i0 child_envelope_sub_564_i0 ?_
  intro b hb
  exact common_sub_564_i0 (mem_commonEnvelope childrenD_564_i0 b hb)
def required_564 : Finset Cell := ⟨(([(1, 1), (1, 2), (3, 4), (4, 1), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_564 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 5), (1, 1), (1, 2), (1, 3), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, 1), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (8, 3), (8, 5), (8, 6), (8, 7), (9, 5), (9, 6), (9, 7), (10, 5), (10, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_564 : Fin 4 → Finset Cell := ![(placed21 1 (1, 1) required_119), (placed21 2 (4, 0) required_497), required_498, required_564_i0]
def childrenD_564 : Fin 4 → Finset Cell := ![(placed21 1 (1, 1) envelope_119), (placed21 2 (4, 0) envelope_497), envelope_498, envelope_564_i0]
theorem common_sub_564 : commonEnvelope childrenD_564 ⊆ insert (4, 4) required_564 := by decide +kernel
theorem child_required_sub_564 : ∀ j, childrenC_564 j ⊆ insert (4, 4) required_564 := by decide +kernel
theorem child_envelope_sub_564 : ∀ j, childrenD_564 j ⊆ envelope_564 := by decide +kernel
theorem pivot_mem_564 : (4, 4) ∈ envelope_564 := by decide +kernel
theorem children_work_564 : ∀ j, Template HasSnaky 12 (childrenC_564 j) (childrenD_564 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_119 1 (1, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_497 2 (4, 0)).mono (by decide +kernel)
  · exact row_works_498.mono (by decide +kernel)
  · exact row_works_564_i0.mono (by decide +kernel)
theorem row_works_564 : Template HasSnaky 13 required_564 envelope_564 := by
  refine compose HasSnaky 12 childrenC_564 childrenD_564 children_work_564 (4, 4)
    required_564 envelope_564 pivot_mem_564 child_required_sub_564 child_envelope_sub_564 ?_
  intro b hb
  exact common_sub_564 (mem_commonEnvelope childrenD_564 b hb)
def required_568_i0 : Finset Cell := ⟨(([(1, 1), (1, 2), (3, 4), (4, 1), (4, 2), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_568_i0 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 4), (0, 5), (1, 1), (1, 2), (1, 4), (1, 5), (2, 1), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 3), (5, 4), (5, 5), (6, 3), (6, 4), (7, 3), (7, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_568_i0 : Fin 2 → Finset Cell := ![(placed21 5 (7, 1) required_255), (placed21 2 (4, 0) required_496)]
def childrenD_568_i0 : Fin 2 → Finset Cell := ![(placed21 5 (7, 1) envelope_255), (placed21 2 (4, 0) envelope_496)]
theorem common_sub_568_i0 : commonEnvelope childrenD_568_i0 ⊆ insert (4, 3) required_568_i0 := by decide +kernel
theorem child_required_sub_568_i0 : ∀ j, childrenC_568_i0 j ⊆ insert (4, 3) required_568_i0 := by decide +kernel
theorem child_envelope_sub_568_i0 : ∀ j, childrenD_568_i0 j ⊆ envelope_568_i0 := by decide +kernel
theorem pivot_mem_568_i0 : (4, 3) ∈ envelope_568_i0 := by decide +kernel
theorem children_work_568_i0 : ∀ j, Template HasSnaky 6 (childrenC_568_i0 j) (childrenD_568_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_255 5 (7, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_496 2 (4, 0)).mono (by decide +kernel)
theorem row_works_568_i0 : Template HasSnaky 7 required_568_i0 envelope_568_i0 := by
  refine compose HasSnaky 6 childrenC_568_i0 childrenD_568_i0 children_work_568_i0 (4, 3)
    required_568_i0 envelope_568_i0 pivot_mem_568_i0 child_required_sub_568_i0 child_envelope_sub_568_i0 ?_
  intro b hb
  exact common_sub_568_i0 (mem_commonEnvelope childrenD_568_i0 b hb)
def required_568_i3 : Finset Cell := ⟨(([(3, 4), (3, 5), (4, 1), (4, 2), (4, 4), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_568_i3 : Finset Cell := ⟨(([(2, 3), (3, 2), (3, 3), (3, 4), (3, 5), (4, 1), (4, 2), (4, 4), (4, 5), (5, 4), (6, 3), (6, 4), (7, 3), (7, 4), (8, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_568_i3 : Fin 2 → Finset Cell := ![(placed21 4 (3, 5) required_24), (placed21 3 (2, 5) required_77)]
def childrenD_568_i3 : Fin 2 → Finset Cell := ![(placed21 4 (3, 5) envelope_24), (placed21 3 (2, 5) envelope_77)]
theorem common_sub_568_i3 : commonEnvelope childrenD_568_i3 ⊆ insert (6, 4) required_568_i3 := by decide +kernel
theorem child_required_sub_568_i3 : ∀ j, childrenC_568_i3 j ⊆ insert (6, 4) required_568_i3 := by decide +kernel
theorem child_envelope_sub_568_i3 : ∀ j, childrenD_568_i3 j ⊆ envelope_568_i3 := by decide +kernel
theorem pivot_mem_568_i3 : (6, 4) ∈ envelope_568_i3 := by decide +kernel
theorem children_work_568_i3 : ∀ j, Template HasSnaky 3 (childrenC_568_i3 j) (childrenD_568_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_24 4 (3, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_77 3 (2, 5)).mono (by decide +kernel)
theorem row_works_568_i3 : Template HasSnaky 4 required_568_i3 envelope_568_i3 := by
  refine compose HasSnaky 3 childrenC_568_i3 childrenD_568_i3 children_work_568_i3 (6, 4)
    required_568_i3 envelope_568_i3 pivot_mem_568_i3 child_required_sub_568_i3 child_envelope_sub_568_i3 ?_
  intro b hb
  exact common_sub_568_i3 (mem_commonEnvelope childrenD_568_i3 b hb)
def required_568_i6 : Finset Cell := ⟨(([(3, 3), (3, 4), (3, 5), (3, 6), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_568_i6 : Finset Cell := ⟨(([(0, 5), (1, 5), (2, 3), (2, 4), (2, 5), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 4), (4, 6), (4, 7), (4, 8), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_568_i6 : Fin 2 → Finset Cell := ![(placed21 0 (3, 3) required_6), (placed21 5 (5, 3) required_132)]
def childrenD_568_i6 : Fin 2 → Finset Cell := ![(placed21 0 (3, 3) envelope_6), (placed21 5 (5, 3) envelope_132)]
theorem common_sub_568_i6 : commonEnvelope childrenD_568_i6 ⊆ insert (3, 7) required_568_i6 := by decide +kernel
theorem child_required_sub_568_i6 : ∀ j, childrenC_568_i6 j ⊆ insert (3, 7) required_568_i6 := by decide +kernel
theorem child_envelope_sub_568_i6 : ∀ j, childrenD_568_i6 j ⊆ envelope_568_i6 := by decide +kernel
theorem pivot_mem_568_i6 : (3, 7) ∈ envelope_568_i6 := by decide +kernel
theorem children_work_568_i6 : ∀ j, Template HasSnaky 4 (childrenC_568_i6 j) (childrenD_568_i6 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_6 0 (3, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_132 5 (5, 3)).mono (by decide +kernel)
theorem row_works_568_i6 : Template HasSnaky 5 required_568_i6 envelope_568_i6 := by
  refine compose HasSnaky 4 childrenC_568_i6 childrenD_568_i6 children_work_568_i6 (3, 7)
    required_568_i6 envelope_568_i6 pivot_mem_568_i6 child_required_sub_568_i6 child_envelope_sub_568_i6 ?_
  intro b hb
  exact common_sub_568_i6 (mem_commonEnvelope childrenD_568_i6 b hb)
def required_568_i7 : Finset Cell := ⟨(([(3, 3), (3, 4), (3, 5), (3, 6), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_568_i7 : Finset Cell := ⟨(([(2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_568_i7 : Fin 2 → Finset Cell := ![(placed21 2 (3, 3) required_6), (placed21 2 (4, 3) required_124)]
def childrenD_568_i7 : Fin 2 → Finset Cell := ![(placed21 2 (3, 3) envelope_6), (placed21 2 (4, 3) envelope_124)]
theorem common_sub_568_i7 : commonEnvelope childrenD_568_i7 ⊆ insert (3, 7) required_568_i7 := by decide +kernel
theorem child_required_sub_568_i7 : ∀ j, childrenC_568_i7 j ⊆ insert (3, 7) required_568_i7 := by decide +kernel
theorem child_envelope_sub_568_i7 : ∀ j, childrenD_568_i7 j ⊆ envelope_568_i7 := by decide +kernel
theorem pivot_mem_568_i7 : (3, 7) ∈ envelope_568_i7 := by decide +kernel
theorem children_work_568_i7 : ∀ j, Template HasSnaky 3 (childrenC_568_i7 j) (childrenD_568_i7 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_6 2 (3, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_124 2 (4, 3)).mono (by decide +kernel)
theorem row_works_568_i7 : Template HasSnaky 4 required_568_i7 envelope_568_i7 := by
  refine compose HasSnaky 3 childrenC_568_i7 childrenD_568_i7 children_work_568_i7 (3, 7)
    required_568_i7 envelope_568_i7 pivot_mem_568_i7 child_required_sub_568_i7 child_envelope_sub_568_i7 ?_
  intro b hb
  exact common_sub_568_i7 (mem_commonEnvelope childrenD_568_i7 b hb)
def required_568_i5 : Finset Cell := ⟨(([(3, 3), (3, 4), (3, 5), (4, 4), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_568_i5 : Finset Cell := ⟨(([(0, 5), (0, 6), (1, 5), (1, 6), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 4), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_568_i5 : Fin 4 → Finset Cell := ![(placed21 5 (4, 3) required_8), (placed21 2 (5, 3) required_387), required_568_i6, required_568_i7]
def childrenD_568_i5 : Fin 4 → Finset Cell := ![(placed21 5 (4, 3) envelope_8), (placed21 2 (5, 3) envelope_387), envelope_568_i6, envelope_568_i7]
theorem common_sub_568_i5 : commonEnvelope childrenD_568_i5 ⊆ insert (3, 6) required_568_i5 := by decide +kernel
theorem child_required_sub_568_i5 : ∀ j, childrenC_568_i5 j ⊆ insert (3, 6) required_568_i5 := by decide +kernel
theorem child_envelope_sub_568_i5 : ∀ j, childrenD_568_i5 j ⊆ envelope_568_i5 := by decide +kernel
theorem pivot_mem_568_i5 : (3, 6) ∈ envelope_568_i5 := by decide +kernel
theorem children_work_568_i5 : ∀ j, Template HasSnaky 6 (childrenC_568_i5 j) (childrenD_568_i5 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_8 5 (4, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_387 2 (5, 3)).mono (by decide +kernel)
  · exact row_works_568_i6.mono (by decide +kernel)
  · exact row_works_568_i7.mono (by decide +kernel)
theorem row_works_568_i5 : Template HasSnaky 7 required_568_i5 envelope_568_i5 := by
  refine compose HasSnaky 6 childrenC_568_i5 childrenD_568_i5 children_work_568_i5 (3, 6)
    required_568_i5 envelope_568_i5 pivot_mem_568_i5 child_required_sub_568_i5 child_envelope_sub_568_i5 ?_
  intro b hb
  exact common_sub_568_i5 (mem_commonEnvelope childrenD_568_i5 b hb)
def required_568_i4 : Finset Cell := ⟨(([(3, 4), (3, 5), (4, 1), (4, 2), (4, 4), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_568_i4 : Finset Cell := ⟨(([(0, 5), (0, 6), (1, 5), (1, 6), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 1), (4, 2), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 4), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_568_i4 : Fin 2 → Finset Cell := ![(placed21 3 (3, 5) required_3), required_568_i5]
def childrenD_568_i4 : Fin 2 → Finset Cell := ![(placed21 3 (3, 5) envelope_3), envelope_568_i5]
theorem common_sub_568_i4 : commonEnvelope childrenD_568_i4 ⊆ insert (3, 3) required_568_i4 := by decide +kernel
theorem child_required_sub_568_i4 : ∀ j, childrenC_568_i4 j ⊆ insert (3, 3) required_568_i4 := by decide +kernel
theorem child_envelope_sub_568_i4 : ∀ j, childrenD_568_i4 j ⊆ envelope_568_i4 := by decide +kernel
theorem pivot_mem_568_i4 : (3, 3) ∈ envelope_568_i4 := by decide +kernel
theorem children_work_568_i4 : ∀ j, Template HasSnaky 7 (childrenC_568_i4 j) (childrenD_568_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_3 3 (3, 5)).mono (by decide +kernel)
  · exact row_works_568_i5.mono (by decide +kernel)
theorem row_works_568_i4 : Template HasSnaky 8 required_568_i4 envelope_568_i4 := by
  refine compose HasSnaky 7 childrenC_568_i4 childrenD_568_i4 children_work_568_i4 (3, 3)
    required_568_i4 envelope_568_i4 pivot_mem_568_i4 child_required_sub_568_i4 child_envelope_sub_568_i4 ?_
  intro b hb
  exact common_sub_568_i4 (mem_commonEnvelope childrenD_568_i4 b hb)
def required_568_i2 : Finset Cell := ⟨(([(3, 4), (4, 1), (4, 2), (4, 4), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_568_i2 : Finset Cell := ⟨(([(0, 5), (0, 6), (1, 5), (1, 6), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 1), (4, 2), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 4), (5, 5), (6, 3), (6, 4), (7, 3), (7, 4), (8, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_568_i2 : Fin 3 → Finset Cell := ![(placed21 5 (6, 4) required_52), required_568_i3, required_568_i4]
def childrenD_568_i2 : Fin 3 → Finset Cell := ![(placed21 5 (6, 4) envelope_52), envelope_568_i3, envelope_568_i4]
theorem common_sub_568_i2 : commonEnvelope childrenD_568_i2 ⊆ insert (3, 5) required_568_i2 := by decide +kernel
theorem child_required_sub_568_i2 : ∀ j, childrenC_568_i2 j ⊆ insert (3, 5) required_568_i2 := by decide +kernel
theorem child_envelope_sub_568_i2 : ∀ j, childrenD_568_i2 j ⊆ envelope_568_i2 := by decide +kernel
theorem pivot_mem_568_i2 : (3, 5) ∈ envelope_568_i2 := by decide +kernel
theorem children_work_568_i2 : ∀ j, Template HasSnaky 8 (childrenC_568_i2 j) (childrenD_568_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_52 5 (6, 4)).mono (by decide +kernel)
  · exact row_works_568_i3.mono (by decide +kernel)
  · exact row_works_568_i4.mono (by decide +kernel)
theorem row_works_568_i2 : Template HasSnaky 9 required_568_i2 envelope_568_i2 := by
  refine compose HasSnaky 8 childrenC_568_i2 childrenD_568_i2 children_work_568_i2 (3, 5)
    required_568_i2 envelope_568_i2 pivot_mem_568_i2 child_required_sub_568_i2 child_envelope_sub_568_i2 ?_
  intro b hb
  exact common_sub_568_i2 (mem_commonEnvelope childrenD_568_i2 b hb)
def required_568_i1 : Finset Cell := ⟨(([(3, 4), (4, 1), (4, 2), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_568_i1 : Finset Cell := ⟨(([(0, 5), (0, 6), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 1), (4, 2), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (9, 4), (9, 5), (9, 6), (9, 7), (10, 5), (10, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_568_i1 : Fin 6 → Finset Cell := ![(placed21 1 (2, 1) required_79), (placed21 3 (1, 5) required_189), (placed21 3 (0, 7) required_518), required_568_i2, (placed21 4 (1, 7) required_565), (placed21 1 (0, 1) required_567)]
def childrenD_568_i1 : Fin 6 → Finset Cell := ![(placed21 1 (2, 1) envelope_79), (placed21 3 (1, 5) envelope_189), (placed21 3 (0, 7) envelope_518), envelope_568_i2, (placed21 4 (1, 7) envelope_565), (placed21 1 (0, 1) envelope_567)]
theorem common_sub_568_i1 : commonEnvelope childrenD_568_i1 ⊆ insert (5, 4) required_568_i1 := by decide +kernel
theorem child_required_sub_568_i1 : ∀ j, childrenC_568_i1 j ⊆ insert (5, 4) required_568_i1 := by decide +kernel
theorem child_envelope_sub_568_i1 : ∀ j, childrenD_568_i1 j ⊆ envelope_568_i1 := by decide +kernel
theorem pivot_mem_568_i1 : (5, 4) ∈ envelope_568_i1 := by decide +kernel
theorem children_work_568_i1 : ∀ j, Template HasSnaky 11 (childrenC_568_i1 j) (childrenD_568_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_79 1 (2, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_189 3 (1, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_518 3 (0, 7)).mono (by decide +kernel)
  · exact row_works_568_i2.mono (by decide +kernel)
  · exact (placed21_template row_works_565 4 (1, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_567 1 (0, 1)).mono (by decide +kernel)
theorem row_works_568_i1 : Template HasSnaky 12 required_568_i1 envelope_568_i1 := by
  refine compose HasSnaky 11 childrenC_568_i1 childrenD_568_i1 children_work_568_i1 (5, 4)
    required_568_i1 envelope_568_i1 pivot_mem_568_i1 child_required_sub_568_i1 child_envelope_sub_568_i1 ?_
  intro b hb
  exact common_sub_568_i1 (mem_commonEnvelope childrenD_568_i1 b hb)
def required_568 : Finset Cell := ⟨(([(1, 1), (1, 2), (3, 4), (4, 1), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_568 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 4), (0, 5), (0, 6), (1, 1), (1, 2), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, 1), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (9, 4), (9, 5), (9, 6), (9, 7), (10, 5), (10, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_568 : Fin 4 → Finset Cell := ![(placed21 1 (1, 1) required_110), (placed21 2 (4, 0) required_497), required_568_i0, required_568_i1]
def childrenD_568 : Fin 4 → Finset Cell := ![(placed21 1 (1, 1) envelope_110), (placed21 2 (4, 0) envelope_497), envelope_568_i0, envelope_568_i1]
theorem common_sub_568 : commonEnvelope childrenD_568 ⊆ insert (4, 4) required_568 := by decide +kernel
theorem child_required_sub_568 : ∀ j, childrenC_568 j ⊆ insert (4, 4) required_568 := by decide +kernel
theorem child_envelope_sub_568 : ∀ j, childrenD_568 j ⊆ envelope_568 := by decide +kernel
theorem pivot_mem_568 : (4, 4) ∈ envelope_568 := by decide +kernel
theorem children_work_568 : ∀ j, Template HasSnaky 12 (childrenC_568 j) (childrenD_568 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_110 1 (1, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_497 2 (4, 0)).mono (by decide +kernel)
  · exact row_works_568_i0.mono (by decide +kernel)
  · exact row_works_568_i1.mono (by decide +kernel)
theorem row_works_568 : Template HasSnaky 13 required_568 envelope_568 := by
  refine compose HasSnaky 12 childrenC_568 childrenD_568 children_work_568 (4, 4)
    required_568 envelope_568 pivot_mem_568 child_required_sub_568 child_envelope_sub_568 ?_
  intro b hb
  exact common_sub_568 (mem_commonEnvelope childrenD_568 b hb)
def required_572_i0 : Finset Cell := ⟨(([(1, 6), (1, 7), (3, 3), (3, 4), (3, 6), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_572_i0 : Finset Cell := ⟨(([(0, 7), (1, 6), (1, 7), (2, 6), (3, 3), (3, 4), (3, 6), (4, 4), (4, 5), (4, 6), (4, 7), (5, 5), (5, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_572_i0 : Fin 2 → Finset Cell := ![(placed21 2 (4, 6) required_5), (placed21 4 (1, 7) required_78)]
def childrenD_572_i0 : Fin 2 → Finset Cell := ![(placed21 2 (4, 6) envelope_5), (placed21 4 (1, 7) envelope_78)]
theorem common_sub_572_i0 : commonEnvelope childrenD_572_i0 ⊆ insert (2, 6) required_572_i0 := by decide +kernel
theorem child_required_sub_572_i0 : ∀ j, childrenC_572_i0 j ⊆ insert (2, 6) required_572_i0 := by decide +kernel
theorem child_envelope_sub_572_i0 : ∀ j, childrenD_572_i0 j ⊆ envelope_572_i0 := by decide +kernel
theorem pivot_mem_572_i0 : (2, 6) ∈ envelope_572_i0 := by decide +kernel
theorem children_work_572_i0 : ∀ j, Template HasSnaky 3 (childrenC_572_i0 j) (childrenD_572_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 2 (4, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_78 4 (1, 7)).mono (by decide +kernel)
theorem row_works_572_i0 : Template HasSnaky 4 required_572_i0 envelope_572_i0 := by
  refine compose HasSnaky 3 childrenC_572_i0 childrenD_572_i0 children_work_572_i0 (2, 6)
    required_572_i0 envelope_572_i0 pivot_mem_572_i0 child_required_sub_572_i0 child_envelope_sub_572_i0 ?_
  intro b hb
  exact common_sub_572_i0 (mem_commonEnvelope childrenD_572_i0 b hb)
def required_572 : Finset Cell := ⟨(([(0, 3), (1, 6), (1, 7), (3, 3), (3, 4), (3, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_572 : Finset Cell := ⟨(([(0, 3), (0, 7), (1, 3), (1, 6), (1, 7), (2, 3), (2, 6), (2, 7), (3, 3), (3, 4), (3, 6), (3, 7), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, 5), (8, 6), (8, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_572 : Fin 4 → Finset Cell := ![(placed21 3 (0, 7) required_97), (placed21 1 (0, 6) required_98), required_572_i0, required_571]
def childrenD_572 : Fin 4 → Finset Cell := ![(placed21 3 (0, 7) envelope_97), (placed21 1 (0, 6) envelope_98), envelope_572_i0, envelope_571]
theorem common_sub_572 : commonEnvelope childrenD_572 ⊆ insert (4, 6) required_572 := by decide +kernel
theorem child_required_sub_572 : ∀ j, childrenC_572 j ⊆ insert (4, 6) required_572 := by decide +kernel
theorem child_envelope_sub_572 : ∀ j, childrenD_572 j ⊆ envelope_572 := by decide +kernel
theorem pivot_mem_572 : (4, 6) ∈ envelope_572 := by decide +kernel
theorem children_work_572 : ∀ j, Template HasSnaky 12 (childrenC_572 j) (childrenD_572 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_97 3 (0, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_98 1 (0, 6)).mono (by decide +kernel)
  · exact row_works_572_i0.mono (by decide +kernel)
  · exact row_works_571.mono (by decide +kernel)
theorem row_works_572 : Template HasSnaky 13 required_572 envelope_572 := by
  refine compose HasSnaky 12 childrenC_572 childrenD_572 children_work_572 (4, 6)
    required_572 envelope_572 pivot_mem_572 child_required_sub_572 child_envelope_sub_572 ?_
  intro b hb
  exact common_sub_572 (mem_commonEnvelope childrenD_572 b hb)
def required_590 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 3), (4, 1), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_590 : Finset Cell := ⟨(([(0, 2), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 0), (5, 1), (5, 3), (5, 4), (5, 5), (5, 6), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_590 : Fin 2 → Finset Cell := ![(placed21 0 (1, 0) required_52), required_588]
def childrenD_590 : Fin 2 → Finset Cell := ![(placed21 0 (1, 0) envelope_52), envelope_588]
theorem common_sub_590 : commonEnvelope childrenD_590 ⊆ insert (2, 3) required_590 := by decide +kernel
theorem child_required_sub_590 : ∀ j, childrenC_590 j ⊆ insert (2, 3) required_590 := by decide +kernel
theorem child_envelope_sub_590 : ∀ j, childrenD_590 j ⊆ envelope_590 := by decide +kernel
theorem pivot_mem_590 : (2, 3) ∈ envelope_590 := by decide +kernel
theorem children_work_590 : ∀ j, Template HasSnaky 12 (childrenC_590 j) (childrenD_590 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_52 0 (1, 0)).mono (by decide +kernel)
  · exact row_works_588.mono (by decide +kernel)
theorem row_works_590 : Template HasSnaky 13 required_590 envelope_590 := by
  refine compose HasSnaky 12 childrenC_590 childrenD_590 children_work_590 (2, 3)
    required_590 envelope_590 pivot_mem_590 child_required_sub_590 child_envelope_sub_590 ?_
  intro b hb
  exact common_sub_590 (mem_commonEnvelope childrenD_590 b hb)
def height_564_i2 : ℕ := 8
def childrenH_564_i2 : Fin 2 → ℕ := ![height_5, height_453]
theorem height_exact_564_i2 : height_564_i2 = 1 + Finset.univ.sup childrenH_564_i2 := by decide +kernel
theorem required_origin_564_i2 : ∀ x ∈ required_564_i2,
    (∃ j, x ∈ childrenC_564_i2 j) ∨ ∀ j, x ∈ childrenD_564_i2 j := by decide +kernel
theorem required_exact_564_i2 : required_564_i2 =
    ((Finset.univ.biUnion childrenC_564_i2) ∪ commonEnvelope childrenD_564_i2).erase (2, 4) := by
  exact required_eq_combination childrenC_564_i2 childrenD_564_i2 (2, 4) required_564_i2
    (by decide +kernel) child_required_sub_564_i2 common_sub_564_i2 required_origin_564_i2
theorem envelope_origin_564_i2 : ∀ x ∈ envelope_564_i2,
    x = (2, 4) ∨ ∃ j, x ∈ childrenD_564_i2 j := by decide +kernel
theorem envelope_exact_564_i2 : envelope_564_i2 =
    insert (2, 4) (Finset.univ.biUnion childrenD_564_i2) := by
  exact envelope_eq_combination childrenD_564_i2 (2, 4) envelope_564_i2
    pivot_mem_564_i2 child_envelope_sub_564_i2 envelope_origin_564_i2
def checked_564_i2 : CheckedCard where
  required := required_564_i2
  envelope := envelope_564_i2
  height := height_564_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_564_i2
def height_564_i7 : ℕ := 5
def childrenH_564_i7 : Fin 2 → ℕ := ![height_5, height_55]
theorem height_exact_564_i7 : height_564_i7 = 1 + Finset.univ.sup childrenH_564_i7 := by decide +kernel
theorem required_origin_564_i7 : ∀ x ∈ required_564_i7,
    (∃ j, x ∈ childrenC_564_i7 j) ∨ ∀ j, x ∈ childrenD_564_i7 j := by decide +kernel
theorem required_exact_564_i7 : required_564_i7 =
    ((Finset.univ.biUnion childrenC_564_i7) ∪ commonEnvelope childrenD_564_i7).erase (3, 5) := by
  exact required_eq_combination childrenC_564_i7 childrenD_564_i7 (3, 5) required_564_i7
    (by decide +kernel) child_required_sub_564_i7 common_sub_564_i7 required_origin_564_i7
theorem envelope_origin_564_i7 : ∀ x ∈ envelope_564_i7,
    x = (3, 5) ∨ ∃ j, x ∈ childrenD_564_i7 j := by decide +kernel
theorem envelope_exact_564_i7 : envelope_564_i7 =
    insert (3, 5) (Finset.univ.biUnion childrenD_564_i7) := by
  exact envelope_eq_combination childrenD_564_i7 (3, 5) envelope_564_i7
    pivot_mem_564_i7 child_envelope_sub_564_i7 envelope_origin_564_i7
def checked_564_i7 : CheckedCard where
  required := required_564_i7
  envelope := envelope_564_i7
  height := height_564_i7
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_564_i7
def height_564_i8 : ℕ := 6
def childrenH_564_i8 : Fin 2 → ℕ := ![height_5, height_342]
theorem height_exact_564_i8 : height_564_i8 = 1 + Finset.univ.sup childrenH_564_i8 := by decide +kernel
theorem required_origin_564_i8 : ∀ x ∈ required_564_i8,
    (∃ j, x ∈ childrenC_564_i8 j) ∨ ∀ j, x ∈ childrenD_564_i8 j := by decide +kernel
theorem required_exact_564_i8 : required_564_i8 =
    ((Finset.univ.biUnion childrenC_564_i8) ∪ commonEnvelope childrenD_564_i8).erase (2, 4) := by
  exact required_eq_combination childrenC_564_i8 childrenD_564_i8 (2, 4) required_564_i8
    (by decide +kernel) child_required_sub_564_i8 common_sub_564_i8 required_origin_564_i8
theorem envelope_origin_564_i8 : ∀ x ∈ envelope_564_i8,
    x = (2, 4) ∨ ∃ j, x ∈ childrenD_564_i8 j := by decide +kernel
theorem envelope_exact_564_i8 : envelope_564_i8 =
    insert (2, 4) (Finset.univ.biUnion childrenD_564_i8) := by
  exact envelope_eq_combination childrenD_564_i8 (2, 4) envelope_564_i8
    pivot_mem_564_i8 child_envelope_sub_564_i8 envelope_origin_564_i8
def checked_564_i8 : CheckedCard where
  required := required_564_i8
  envelope := envelope_564_i8
  height := height_564_i8
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_564_i8
def height_564_i6 : ℕ := 7
def childrenH_564_i6 : Fin 3 → ℕ := ![height_102, height_564_i7, height_564_i8]
theorem height_exact_564_i6 : height_564_i6 = 1 + Finset.univ.sup childrenH_564_i6 := by decide +kernel
theorem required_origin_564_i6 : ∀ x ∈ required_564_i6,
    (∃ j, x ∈ childrenC_564_i6 j) ∨ ∀ j, x ∈ childrenD_564_i6 j := by decide +kernel
theorem required_exact_564_i6 : required_564_i6 =
    ((Finset.univ.biUnion childrenC_564_i6) ∪ commonEnvelope childrenD_564_i6).erase (2, 5) := by
  exact required_eq_combination childrenC_564_i6 childrenD_564_i6 (2, 5) required_564_i6
    (by decide +kernel) child_required_sub_564_i6 common_sub_564_i6 required_origin_564_i6
theorem envelope_origin_564_i6 : ∀ x ∈ envelope_564_i6,
    x = (2, 5) ∨ ∃ j, x ∈ childrenD_564_i6 j := by decide +kernel
theorem envelope_exact_564_i6 : envelope_564_i6 =
    insert (2, 5) (Finset.univ.biUnion childrenD_564_i6) := by
  exact envelope_eq_combination childrenD_564_i6 (2, 5) envelope_564_i6
    pivot_mem_564_i6 child_envelope_sub_564_i6 envelope_origin_564_i6
def checked_564_i6 : CheckedCard where
  required := required_564_i6
  envelope := envelope_564_i6
  height := height_564_i6
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_564_i6
def height_564_i5 : ℕ := 8
def childrenH_564_i5 : Fin 2 → ℕ := ![height_0, height_564_i6]
theorem height_exact_564_i5 : height_564_i5 = 1 + Finset.univ.sup childrenH_564_i5 := by decide +kernel
theorem required_origin_564_i5 : ∀ x ∈ required_564_i5,
    (∃ j, x ∈ childrenC_564_i5 j) ∨ ∀ j, x ∈ childrenD_564_i5 j := by decide +kernel
theorem required_exact_564_i5 : required_564_i5 =
    ((Finset.univ.biUnion childrenC_564_i5) ∪ commonEnvelope childrenD_564_i5).erase (4, 5) := by
  exact required_eq_combination childrenC_564_i5 childrenD_564_i5 (4, 5) required_564_i5
    (by decide +kernel) child_required_sub_564_i5 common_sub_564_i5 required_origin_564_i5
theorem envelope_origin_564_i5 : ∀ x ∈ envelope_564_i5,
    x = (4, 5) ∨ ∃ j, x ∈ childrenD_564_i5 j := by decide +kernel
theorem envelope_exact_564_i5 : envelope_564_i5 =
    insert (4, 5) (Finset.univ.biUnion childrenD_564_i5) := by
  exact envelope_eq_combination childrenD_564_i5 (4, 5) envelope_564_i5
    pivot_mem_564_i5 child_envelope_sub_564_i5 envelope_origin_564_i5
def checked_564_i5 : CheckedCard where
  required := required_564_i5
  envelope := envelope_564_i5
  height := height_564_i5
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_564_i5
def height_564_i4 : ℕ := 9
def childrenH_564_i4 : Fin 3 → ℕ := ![height_16, height_235, height_564_i5]
theorem height_exact_564_i4 : height_564_i4 = 1 + Finset.univ.sup childrenH_564_i4 := by decide +kernel
theorem required_origin_564_i4 : ∀ x ∈ required_564_i4,
    (∃ j, x ∈ childrenC_564_i4 j) ∨ ∀ j, x ∈ childrenD_564_i4 j := by decide +kernel
theorem required_exact_564_i4 : required_564_i4 =
    ((Finset.univ.biUnion childrenC_564_i4) ∪ commonEnvelope childrenD_564_i4).erase (5, 7) := by
  exact required_eq_combination childrenC_564_i4 childrenD_564_i4 (5, 7) required_564_i4
    (by decide +kernel) child_required_sub_564_i4 common_sub_564_i4 required_origin_564_i4
theorem envelope_origin_564_i4 : ∀ x ∈ envelope_564_i4,
    x = (5, 7) ∨ ∃ j, x ∈ childrenD_564_i4 j := by decide +kernel
theorem envelope_exact_564_i4 : envelope_564_i4 =
    insert (5, 7) (Finset.univ.biUnion childrenD_564_i4) := by
  exact envelope_eq_combination childrenD_564_i4 (5, 7) envelope_564_i4
    pivot_mem_564_i4 child_envelope_sub_564_i4 envelope_origin_564_i4
def checked_564_i4 : CheckedCard where
  required := required_564_i4
  envelope := envelope_564_i4
  height := height_564_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_564_i4
def height_564_i3 : ℕ := 10
def childrenH_564_i3 : Fin 7 → ℕ := ![height_67, height_134, height_180, height_327, height_504, height_558, height_564_i4]
theorem height_exact_564_i3 : height_564_i3 = 1 + Finset.univ.sup childrenH_564_i3 := by decide +kernel
theorem required_origin_564_i3 : ∀ x ∈ required_564_i3,
    (∃ j, x ∈ childrenC_564_i3 j) ∨ ∀ j, x ∈ childrenD_564_i3 j := by decide +kernel
theorem required_exact_564_i3 : required_564_i3 =
    ((Finset.univ.biUnion childrenC_564_i3) ∪ commonEnvelope childrenD_564_i3).erase (5, 6) := by
  exact required_eq_combination childrenC_564_i3 childrenD_564_i3 (5, 6) required_564_i3
    (by decide +kernel) child_required_sub_564_i3 common_sub_564_i3 required_origin_564_i3
theorem envelope_origin_564_i3 : ∀ x ∈ envelope_564_i3,
    x = (5, 6) ∨ ∃ j, x ∈ childrenD_564_i3 j := by decide +kernel
theorem envelope_exact_564_i3 : envelope_564_i3 =
    insert (5, 6) (Finset.univ.biUnion childrenD_564_i3) := by
  exact envelope_eq_combination childrenD_564_i3 (5, 6) envelope_564_i3
    pivot_mem_564_i3 child_envelope_sub_564_i3 envelope_origin_564_i3
def checked_564_i3 : CheckedCard where
  required := required_564_i3
  envelope := envelope_564_i3
  height := height_564_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_564_i3
def height_564_i1 : ℕ := 11
def childrenH_564_i1 : Fin 5 → ℕ := ![height_44, height_564_i2, height_564_i3, height_560, height_563]
theorem height_exact_564_i1 : height_564_i1 = 1 + Finset.univ.sup childrenH_564_i1 := by decide +kernel
theorem required_origin_564_i1 : ∀ x ∈ required_564_i1,
    (∃ j, x ∈ childrenC_564_i1 j) ∨ ∀ j, x ∈ childrenD_564_i1 j := by decide +kernel
theorem required_exact_564_i1 : required_564_i1 =
    ((Finset.univ.biUnion childrenC_564_i1) ∪ commonEnvelope childrenD_564_i1).erase (5, 5) := by
  exact required_eq_combination childrenC_564_i1 childrenD_564_i1 (5, 5) required_564_i1
    (by decide +kernel) child_required_sub_564_i1 common_sub_564_i1 required_origin_564_i1
theorem envelope_origin_564_i1 : ∀ x ∈ envelope_564_i1,
    x = (5, 5) ∨ ∃ j, x ∈ childrenD_564_i1 j := by decide +kernel
theorem envelope_exact_564_i1 : envelope_564_i1 =
    insert (5, 5) (Finset.univ.biUnion childrenD_564_i1) := by
  exact envelope_eq_combination childrenD_564_i1 (5, 5) envelope_564_i1
    pivot_mem_564_i1 child_envelope_sub_564_i1 envelope_origin_564_i1
def checked_564_i1 : CheckedCard where
  required := required_564_i1
  envelope := envelope_564_i1
  height := height_564_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_564_i1
def height_564_i0 : ℕ := 12
def childrenH_564_i0 : Fin 6 → ℕ := ![height_12, height_12, height_79, height_135, height_182, height_564_i1]
theorem height_exact_564_i0 : height_564_i0 = 1 + Finset.univ.sup childrenH_564_i0 := by decide +kernel
theorem required_origin_564_i0 : ∀ x ∈ required_564_i0,
    (∃ j, x ∈ childrenC_564_i0 j) ∨ ∀ j, x ∈ childrenD_564_i0 j := by decide +kernel
theorem required_exact_564_i0 : required_564_i0 =
    ((Finset.univ.biUnion childrenC_564_i0) ∪ commonEnvelope childrenD_564_i0).erase (5, 4) := by
  exact required_eq_combination childrenC_564_i0 childrenD_564_i0 (5, 4) required_564_i0
    (by decide +kernel) child_required_sub_564_i0 common_sub_564_i0 required_origin_564_i0
theorem envelope_origin_564_i0 : ∀ x ∈ envelope_564_i0,
    x = (5, 4) ∨ ∃ j, x ∈ childrenD_564_i0 j := by decide +kernel
theorem envelope_exact_564_i0 : envelope_564_i0 =
    insert (5, 4) (Finset.univ.biUnion childrenD_564_i0) := by
  exact envelope_eq_combination childrenD_564_i0 (5, 4) envelope_564_i0
    pivot_mem_564_i0 child_envelope_sub_564_i0 envelope_origin_564_i0
def checked_564_i0 : CheckedCard where
  required := required_564_i0
  envelope := envelope_564_i0
  height := height_564_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_564_i0
def height_564 : ℕ := 13
def childrenH_564 : Fin 4 → ℕ := ![height_119, height_497, height_498, height_564_i0]
theorem height_exact_564 : height_564 = 1 + Finset.univ.sup childrenH_564 := by decide +kernel
theorem required_origin_564 : ∀ x ∈ required_564,
    (∃ j, x ∈ childrenC_564 j) ∨ ∀ j, x ∈ childrenD_564 j := by decide +kernel
theorem required_exact_564 : required_564 =
    ((Finset.univ.biUnion childrenC_564) ∪ commonEnvelope childrenD_564).erase (4, 4) := by
  exact required_eq_combination childrenC_564 childrenD_564 (4, 4) required_564
    (by decide +kernel) child_required_sub_564 common_sub_564 required_origin_564
theorem envelope_origin_564 : ∀ x ∈ envelope_564,
    x = (4, 4) ∨ ∃ j, x ∈ childrenD_564 j := by decide +kernel
theorem envelope_exact_564 : envelope_564 =
    insert (4, 4) (Finset.univ.biUnion childrenD_564) := by
  exact envelope_eq_combination childrenD_564 (4, 4) envelope_564
    pivot_mem_564 child_envelope_sub_564 envelope_origin_564
def checked_564 : CheckedCard where
  required := required_564
  envelope := envelope_564
  height := height_564
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_564
def height_568_i0 : ℕ := 7
def childrenH_568_i0 : Fin 2 → ℕ := ![height_255, height_496]
theorem height_exact_568_i0 : height_568_i0 = 1 + Finset.univ.sup childrenH_568_i0 := by decide +kernel
theorem required_origin_568_i0 : ∀ x ∈ required_568_i0,
    (∃ j, x ∈ childrenC_568_i0 j) ∨ ∀ j, x ∈ childrenD_568_i0 j := by decide +kernel
theorem required_exact_568_i0 : required_568_i0 =
    ((Finset.univ.biUnion childrenC_568_i0) ∪ commonEnvelope childrenD_568_i0).erase (4, 3) := by
  exact required_eq_combination childrenC_568_i0 childrenD_568_i0 (4, 3) required_568_i0
    (by decide +kernel) child_required_sub_568_i0 common_sub_568_i0 required_origin_568_i0
theorem envelope_origin_568_i0 : ∀ x ∈ envelope_568_i0,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_568_i0 j := by decide +kernel
theorem envelope_exact_568_i0 : envelope_568_i0 =
    insert (4, 3) (Finset.univ.biUnion childrenD_568_i0) := by
  exact envelope_eq_combination childrenD_568_i0 (4, 3) envelope_568_i0
    pivot_mem_568_i0 child_envelope_sub_568_i0 envelope_origin_568_i0
def checked_568_i0 : CheckedCard where
  required := required_568_i0
  envelope := envelope_568_i0
  height := height_568_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_568_i0
def height_568_i3 : ℕ := 4
def childrenH_568_i3 : Fin 2 → ℕ := ![height_24, height_77]
theorem height_exact_568_i3 : height_568_i3 = 1 + Finset.univ.sup childrenH_568_i3 := by decide +kernel
theorem required_origin_568_i3 : ∀ x ∈ required_568_i3,
    (∃ j, x ∈ childrenC_568_i3 j) ∨ ∀ j, x ∈ childrenD_568_i3 j := by decide +kernel
theorem required_exact_568_i3 : required_568_i3 =
    ((Finset.univ.biUnion childrenC_568_i3) ∪ commonEnvelope childrenD_568_i3).erase (6, 4) := by
  exact required_eq_combination childrenC_568_i3 childrenD_568_i3 (6, 4) required_568_i3
    (by decide +kernel) child_required_sub_568_i3 common_sub_568_i3 required_origin_568_i3
theorem envelope_origin_568_i3 : ∀ x ∈ envelope_568_i3,
    x = (6, 4) ∨ ∃ j, x ∈ childrenD_568_i3 j := by decide +kernel
theorem envelope_exact_568_i3 : envelope_568_i3 =
    insert (6, 4) (Finset.univ.biUnion childrenD_568_i3) := by
  exact envelope_eq_combination childrenD_568_i3 (6, 4) envelope_568_i3
    pivot_mem_568_i3 child_envelope_sub_568_i3 envelope_origin_568_i3
def checked_568_i3 : CheckedCard where
  required := required_568_i3
  envelope := envelope_568_i3
  height := height_568_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_568_i3
def height_568_i6 : ℕ := 5
def childrenH_568_i6 : Fin 2 → ℕ := ![height_6, height_132]
theorem height_exact_568_i6 : height_568_i6 = 1 + Finset.univ.sup childrenH_568_i6 := by decide +kernel
theorem required_origin_568_i6 : ∀ x ∈ required_568_i6,
    (∃ j, x ∈ childrenC_568_i6 j) ∨ ∀ j, x ∈ childrenD_568_i6 j := by decide +kernel
theorem required_exact_568_i6 : required_568_i6 =
    ((Finset.univ.biUnion childrenC_568_i6) ∪ commonEnvelope childrenD_568_i6).erase (3, 7) := by
  exact required_eq_combination childrenC_568_i6 childrenD_568_i6 (3, 7) required_568_i6
    (by decide +kernel) child_required_sub_568_i6 common_sub_568_i6 required_origin_568_i6
theorem envelope_origin_568_i6 : ∀ x ∈ envelope_568_i6,
    x = (3, 7) ∨ ∃ j, x ∈ childrenD_568_i6 j := by decide +kernel
theorem envelope_exact_568_i6 : envelope_568_i6 =
    insert (3, 7) (Finset.univ.biUnion childrenD_568_i6) := by
  exact envelope_eq_combination childrenD_568_i6 (3, 7) envelope_568_i6
    pivot_mem_568_i6 child_envelope_sub_568_i6 envelope_origin_568_i6
def checked_568_i6 : CheckedCard where
  required := required_568_i6
  envelope := envelope_568_i6
  height := height_568_i6
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_568_i6
def height_568_i7 : ℕ := 4
def childrenH_568_i7 : Fin 2 → ℕ := ![height_6, height_124]
theorem height_exact_568_i7 : height_568_i7 = 1 + Finset.univ.sup childrenH_568_i7 := by decide +kernel
theorem required_origin_568_i7 : ∀ x ∈ required_568_i7,
    (∃ j, x ∈ childrenC_568_i7 j) ∨ ∀ j, x ∈ childrenD_568_i7 j := by decide +kernel
theorem required_exact_568_i7 : required_568_i7 =
    ((Finset.univ.biUnion childrenC_568_i7) ∪ commonEnvelope childrenD_568_i7).erase (3, 7) := by
  exact required_eq_combination childrenC_568_i7 childrenD_568_i7 (3, 7) required_568_i7
    (by decide +kernel) child_required_sub_568_i7 common_sub_568_i7 required_origin_568_i7
theorem envelope_origin_568_i7 : ∀ x ∈ envelope_568_i7,
    x = (3, 7) ∨ ∃ j, x ∈ childrenD_568_i7 j := by decide +kernel
theorem envelope_exact_568_i7 : envelope_568_i7 =
    insert (3, 7) (Finset.univ.biUnion childrenD_568_i7) := by
  exact envelope_eq_combination childrenD_568_i7 (3, 7) envelope_568_i7
    pivot_mem_568_i7 child_envelope_sub_568_i7 envelope_origin_568_i7
def checked_568_i7 : CheckedCard where
  required := required_568_i7
  envelope := envelope_568_i7
  height := height_568_i7
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_568_i7
def height_568_i5 : ℕ := 7
def childrenH_568_i5 : Fin 4 → ℕ := ![height_8, height_387, height_568_i6, height_568_i7]
theorem height_exact_568_i5 : height_568_i5 = 1 + Finset.univ.sup childrenH_568_i5 := by decide +kernel
theorem required_origin_568_i5 : ∀ x ∈ required_568_i5,
    (∃ j, x ∈ childrenC_568_i5 j) ∨ ∀ j, x ∈ childrenD_568_i5 j := by decide +kernel
theorem required_exact_568_i5 : required_568_i5 =
    ((Finset.univ.biUnion childrenC_568_i5) ∪ commonEnvelope childrenD_568_i5).erase (3, 6) := by
  exact required_eq_combination childrenC_568_i5 childrenD_568_i5 (3, 6) required_568_i5
    (by decide +kernel) child_required_sub_568_i5 common_sub_568_i5 required_origin_568_i5
theorem envelope_origin_568_i5 : ∀ x ∈ envelope_568_i5,
    x = (3, 6) ∨ ∃ j, x ∈ childrenD_568_i5 j := by decide +kernel
theorem envelope_exact_568_i5 : envelope_568_i5 =
    insert (3, 6) (Finset.univ.biUnion childrenD_568_i5) := by
  exact envelope_eq_combination childrenD_568_i5 (3, 6) envelope_568_i5
    pivot_mem_568_i5 child_envelope_sub_568_i5 envelope_origin_568_i5
def checked_568_i5 : CheckedCard where
  required := required_568_i5
  envelope := envelope_568_i5
  height := height_568_i5
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_568_i5
def height_568_i4 : ℕ := 8
def childrenH_568_i4 : Fin 2 → ℕ := ![height_3, height_568_i5]
theorem height_exact_568_i4 : height_568_i4 = 1 + Finset.univ.sup childrenH_568_i4 := by decide +kernel
theorem required_origin_568_i4 : ∀ x ∈ required_568_i4,
    (∃ j, x ∈ childrenC_568_i4 j) ∨ ∀ j, x ∈ childrenD_568_i4 j := by decide +kernel
theorem required_exact_568_i4 : required_568_i4 =
    ((Finset.univ.biUnion childrenC_568_i4) ∪ commonEnvelope childrenD_568_i4).erase (3, 3) := by
  exact required_eq_combination childrenC_568_i4 childrenD_568_i4 (3, 3) required_568_i4
    (by decide +kernel) child_required_sub_568_i4 common_sub_568_i4 required_origin_568_i4
theorem envelope_origin_568_i4 : ∀ x ∈ envelope_568_i4,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_568_i4 j := by decide +kernel
theorem envelope_exact_568_i4 : envelope_568_i4 =
    insert (3, 3) (Finset.univ.biUnion childrenD_568_i4) := by
  exact envelope_eq_combination childrenD_568_i4 (3, 3) envelope_568_i4
    pivot_mem_568_i4 child_envelope_sub_568_i4 envelope_origin_568_i4
def checked_568_i4 : CheckedCard where
  required := required_568_i4
  envelope := envelope_568_i4
  height := height_568_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_568_i4
def height_568_i2 : ℕ := 9
def childrenH_568_i2 : Fin 3 → ℕ := ![height_52, height_568_i3, height_568_i4]
theorem height_exact_568_i2 : height_568_i2 = 1 + Finset.univ.sup childrenH_568_i2 := by decide +kernel
theorem required_origin_568_i2 : ∀ x ∈ required_568_i2,
    (∃ j, x ∈ childrenC_568_i2 j) ∨ ∀ j, x ∈ childrenD_568_i2 j := by decide +kernel
theorem required_exact_568_i2 : required_568_i2 =
    ((Finset.univ.biUnion childrenC_568_i2) ∪ commonEnvelope childrenD_568_i2).erase (3, 5) := by
  exact required_eq_combination childrenC_568_i2 childrenD_568_i2 (3, 5) required_568_i2
    (by decide +kernel) child_required_sub_568_i2 common_sub_568_i2 required_origin_568_i2
theorem envelope_origin_568_i2 : ∀ x ∈ envelope_568_i2,
    x = (3, 5) ∨ ∃ j, x ∈ childrenD_568_i2 j := by decide +kernel
theorem envelope_exact_568_i2 : envelope_568_i2 =
    insert (3, 5) (Finset.univ.biUnion childrenD_568_i2) := by
  exact envelope_eq_combination childrenD_568_i2 (3, 5) envelope_568_i2
    pivot_mem_568_i2 child_envelope_sub_568_i2 envelope_origin_568_i2
def checked_568_i2 : CheckedCard where
  required := required_568_i2
  envelope := envelope_568_i2
  height := height_568_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_568_i2
def height_568_i1 : ℕ := 12
def childrenH_568_i1 : Fin 6 → ℕ := ![height_79, height_189, height_518, height_568_i2, height_565, height_567]
theorem height_exact_568_i1 : height_568_i1 = 1 + Finset.univ.sup childrenH_568_i1 := by decide +kernel
theorem required_origin_568_i1 : ∀ x ∈ required_568_i1,
    (∃ j, x ∈ childrenC_568_i1 j) ∨ ∀ j, x ∈ childrenD_568_i1 j := by decide +kernel
theorem required_exact_568_i1 : required_568_i1 =
    ((Finset.univ.biUnion childrenC_568_i1) ∪ commonEnvelope childrenD_568_i1).erase (5, 4) := by
  exact required_eq_combination childrenC_568_i1 childrenD_568_i1 (5, 4) required_568_i1
    (by decide +kernel) child_required_sub_568_i1 common_sub_568_i1 required_origin_568_i1
theorem envelope_origin_568_i1 : ∀ x ∈ envelope_568_i1,
    x = (5, 4) ∨ ∃ j, x ∈ childrenD_568_i1 j := by decide +kernel
theorem envelope_exact_568_i1 : envelope_568_i1 =
    insert (5, 4) (Finset.univ.biUnion childrenD_568_i1) := by
  exact envelope_eq_combination childrenD_568_i1 (5, 4) envelope_568_i1
    pivot_mem_568_i1 child_envelope_sub_568_i1 envelope_origin_568_i1
def checked_568_i1 : CheckedCard where
  required := required_568_i1
  envelope := envelope_568_i1
  height := height_568_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_568_i1
def height_568 : ℕ := 13
def childrenH_568 : Fin 4 → ℕ := ![height_110, height_497, height_568_i0, height_568_i1]
theorem height_exact_568 : height_568 = 1 + Finset.univ.sup childrenH_568 := by decide +kernel
theorem required_origin_568 : ∀ x ∈ required_568,
    (∃ j, x ∈ childrenC_568 j) ∨ ∀ j, x ∈ childrenD_568 j := by decide +kernel
theorem required_exact_568 : required_568 =
    ((Finset.univ.biUnion childrenC_568) ∪ commonEnvelope childrenD_568).erase (4, 4) := by
  exact required_eq_combination childrenC_568 childrenD_568 (4, 4) required_568
    (by decide +kernel) child_required_sub_568 common_sub_568 required_origin_568
theorem envelope_origin_568 : ∀ x ∈ envelope_568,
    x = (4, 4) ∨ ∃ j, x ∈ childrenD_568 j := by decide +kernel
theorem envelope_exact_568 : envelope_568 =
    insert (4, 4) (Finset.univ.biUnion childrenD_568) := by
  exact envelope_eq_combination childrenD_568 (4, 4) envelope_568
    pivot_mem_568 child_envelope_sub_568 envelope_origin_568
def checked_568 : CheckedCard where
  required := required_568
  envelope := envelope_568
  height := height_568
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_568
def height_572_i0 : ℕ := 4
def childrenH_572_i0 : Fin 2 → ℕ := ![height_5, height_78]
theorem height_exact_572_i0 : height_572_i0 = 1 + Finset.univ.sup childrenH_572_i0 := by decide +kernel
theorem required_origin_572_i0 : ∀ x ∈ required_572_i0,
    (∃ j, x ∈ childrenC_572_i0 j) ∨ ∀ j, x ∈ childrenD_572_i0 j := by decide +kernel
theorem required_exact_572_i0 : required_572_i0 =
    ((Finset.univ.biUnion childrenC_572_i0) ∪ commonEnvelope childrenD_572_i0).erase (2, 6) := by
  exact required_eq_combination childrenC_572_i0 childrenD_572_i0 (2, 6) required_572_i0
    (by decide +kernel) child_required_sub_572_i0 common_sub_572_i0 required_origin_572_i0
theorem envelope_origin_572_i0 : ∀ x ∈ envelope_572_i0,
    x = (2, 6) ∨ ∃ j, x ∈ childrenD_572_i0 j := by decide +kernel
theorem envelope_exact_572_i0 : envelope_572_i0 =
    insert (2, 6) (Finset.univ.biUnion childrenD_572_i0) := by
  exact envelope_eq_combination childrenD_572_i0 (2, 6) envelope_572_i0
    pivot_mem_572_i0 child_envelope_sub_572_i0 envelope_origin_572_i0
def checked_572_i0 : CheckedCard where
  required := required_572_i0
  envelope := envelope_572_i0
  height := height_572_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_572_i0
def height_572 : ℕ := 13
def childrenH_572 : Fin 4 → ℕ := ![height_97, height_98, height_572_i0, height_571]
theorem height_exact_572 : height_572 = 1 + Finset.univ.sup childrenH_572 := by decide +kernel
theorem required_origin_572 : ∀ x ∈ required_572,
    (∃ j, x ∈ childrenC_572 j) ∨ ∀ j, x ∈ childrenD_572 j := by decide +kernel
theorem required_exact_572 : required_572 =
    ((Finset.univ.biUnion childrenC_572) ∪ commonEnvelope childrenD_572).erase (4, 6) := by
  exact required_eq_combination childrenC_572 childrenD_572 (4, 6) required_572
    (by decide +kernel) child_required_sub_572 common_sub_572 required_origin_572
theorem envelope_origin_572 : ∀ x ∈ envelope_572,
    x = (4, 6) ∨ ∃ j, x ∈ childrenD_572 j := by decide +kernel
theorem envelope_exact_572 : envelope_572 =
    insert (4, 6) (Finset.univ.biUnion childrenD_572) := by
  exact envelope_eq_combination childrenD_572 (4, 6) envelope_572
    pivot_mem_572 child_envelope_sub_572 envelope_origin_572
def checked_572 : CheckedCard where
  required := required_572
  envelope := envelope_572
  height := height_572
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_572
def height_590 : ℕ := 13
def childrenH_590 : Fin 2 → ℕ := ![height_52, height_588]
theorem height_exact_590 : height_590 = 1 + Finset.univ.sup childrenH_590 := by decide +kernel
theorem required_origin_590 : ∀ x ∈ required_590,
    (∃ j, x ∈ childrenC_590 j) ∨ ∀ j, x ∈ childrenD_590 j := by decide +kernel
theorem required_exact_590 : required_590 =
    ((Finset.univ.biUnion childrenC_590) ∪ commonEnvelope childrenD_590).erase (2, 3) := by
  exact required_eq_combination childrenC_590 childrenD_590 (2, 3) required_590
    (by decide +kernel) child_required_sub_590 common_sub_590 required_origin_590
theorem envelope_origin_590 : ∀ x ∈ envelope_590,
    x = (2, 3) ∨ ∃ j, x ∈ childrenD_590 j := by decide +kernel
theorem envelope_exact_590 : envelope_590 =
    insert (2, 3) (Finset.univ.biUnion childrenD_590) := by
  exact envelope_eq_combination childrenD_590 (2, 3) envelope_590
    pivot_mem_590 child_envelope_sub_590 envelope_origin_590
def checked_590 : CheckedCard where
  required := required_590
  envelope := envelope_590
  height := height_590
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_590
end SnakyPrototype.Certificate21

end OAI
