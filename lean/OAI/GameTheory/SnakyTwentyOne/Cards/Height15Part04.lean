import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part01
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_719_i5 : Finset Cell := ⟨(([(3, 5), (3, 6), (4, 5), (4, 6), (4, 7), (4, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_719_i5 : Finset Cell := ⟨(([(3, 5), (3, 6), (3, 8), (3, 9), (4, 5), (4, 6), (4, 7), (4, 8), (5, 4), (5, 5), (5, 7), (5, 8), (5, 9), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_719_i5 : Fin 2 → Finset Cell := ![(placed21 5 (4, 5) required_5), (placed21 0 (3, 4) required_412)]
def childrenD_719_i5 : Fin 2 → Finset Cell := ![(placed21 5 (4, 5) envelope_5), (placed21 0 (3, 4) envelope_412)]
theorem common_sub_719_i5 : commonEnvelope childrenD_719_i5 ⊆ insert (3, 8) required_719_i5 := by decide +kernel
theorem child_required_sub_719_i5 : ∀ j, childrenC_719_i5 j ⊆ insert (3, 8) required_719_i5 := by decide +kernel
theorem child_envelope_sub_719_i5 : ∀ j, childrenD_719_i5 j ⊆ envelope_719_i5 := by decide +kernel
theorem pivot_mem_719_i5 : (3, 8) ∈ envelope_719_i5 := by decide +kernel
theorem children_work_719_i5 : ∀ j, Template HasSnaky 8 (childrenC_719_i5 j) (childrenD_719_i5 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 5 (4, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_412 0 (3, 4)).mono (by decide +kernel)
theorem row_works_719_i5 : Template HasSnaky 9 required_719_i5 envelope_719_i5 := by
  refine compose HasSnaky 8 childrenC_719_i5 childrenD_719_i5 children_work_719_i5 (3, 8)
    required_719_i5 envelope_719_i5 pivot_mem_719_i5 child_required_sub_719_i5 child_envelope_sub_719_i5 ?_
  intro b hb
  exact common_sub_719_i5 (mem_commonEnvelope childrenD_719_i5 b hb)
def required_719_i4 : Finset Cell := ⟨(([(3, 5), (3, 6), (4, 6), (4, 7), (4, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_719_i4 : Finset Cell := ⟨(([(1, 7), (1, 8), (1, 9), (2, 6), (2, 7), (2, 8), (2, 9), (3, 5), (3, 6), (3, 8), (3, 9), (4, 5), (4, 6), (4, 7), (4, 8), (5, 4), (5, 5), (5, 7), (5, 8), (5, 9), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_719_i4 : Fin 3 → Finset Cell := ![(placed21 3 (2, 8) required_45), (placed21 5 (6, 5) required_343), required_719_i5]
def childrenD_719_i4 : Fin 3 → Finset Cell := ![(placed21 3 (2, 8) envelope_45), (placed21 5 (6, 5) envelope_343), envelope_719_i5]
theorem common_sub_719_i4 : commonEnvelope childrenD_719_i4 ⊆ insert (4, 5) required_719_i4 := by decide +kernel
theorem child_required_sub_719_i4 : ∀ j, childrenC_719_i4 j ⊆ insert (4, 5) required_719_i4 := by decide +kernel
theorem child_envelope_sub_719_i4 : ∀ j, childrenD_719_i4 j ⊆ envelope_719_i4 := by decide +kernel
theorem pivot_mem_719_i4 : (4, 5) ∈ envelope_719_i4 := by decide +kernel
theorem children_work_719_i4 : ∀ j, Template HasSnaky 9 (childrenC_719_i4 j) (childrenD_719_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_45 3 (2, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_343 5 (6, 5)).mono (by decide +kernel)
  · exact row_works_719_i5.mono (by decide +kernel)
theorem row_works_719_i4 : Template HasSnaky 10 required_719_i4 envelope_719_i4 := by
  refine compose HasSnaky 9 childrenC_719_i4 childrenD_719_i4 children_work_719_i4 (4, 5)
    required_719_i4 envelope_719_i4 pivot_mem_719_i4 child_required_sub_719_i4 child_envelope_sub_719_i4 ?_
  intro b hb
  exact common_sub_719_i4 (mem_commonEnvelope childrenD_719_i4 b hb)
def required_719_i3 : Finset Cell := ⟨(([(3, 5), (3, 6), (4, 6), (4, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_719_i3 : Finset Cell := ⟨(([(1, 7), (1, 8), (1, 9), (2, 6), (2, 7), (2, 8), (2, 9), (3, 5), (3, 6), (3, 8), (3, 9), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 4), (5, 5), (5, 7), (5, 8), (5, 9), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_719_i3 : Fin 2 → Finset Cell := ![(placed21 7 (4, 9) required_0), required_719_i4]
def childrenD_719_i3 : Fin 2 → Finset Cell := ![(placed21 7 (4, 9) envelope_0), envelope_719_i4]
theorem common_sub_719_i3 : commonEnvelope childrenD_719_i3 ⊆ insert (4, 8) required_719_i3 := by decide +kernel
theorem child_required_sub_719_i3 : ∀ j, childrenC_719_i3 j ⊆ insert (4, 8) required_719_i3 := by decide +kernel
theorem child_envelope_sub_719_i3 : ∀ j, childrenD_719_i3 j ⊆ envelope_719_i3 := by decide +kernel
theorem pivot_mem_719_i3 : (4, 8) ∈ envelope_719_i3 := by decide +kernel
theorem children_work_719_i3 : ∀ j, Template HasSnaky 10 (childrenC_719_i3 j) (childrenD_719_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 7 (4, 9)).mono (by decide +kernel)
  · exact row_works_719_i4.mono (by decide +kernel)
theorem row_works_719_i3 : Template HasSnaky 11 required_719_i3 envelope_719_i3 := by
  refine compose HasSnaky 10 childrenC_719_i3 childrenD_719_i3 children_work_719_i3 (4, 8)
    required_719_i3 envelope_719_i3 pivot_mem_719_i3 child_required_sub_719_i3 child_envelope_sub_719_i3 ?_
  intro b hb
  exact common_sub_719_i3 (mem_commonEnvelope childrenD_719_i3 b hb)
def required_719_i2 : Finset Cell := ⟨(([(3, 3), (3, 5), (3, 6), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_719_i2 : Finset Cell := ⟨(([(1, 7), (1, 8), (1, 9), (2, 6), (2, 7), (2, 8), (2, 9), (3, 3), (3, 4), (3, 5), (3, 6), (3, 8), (3, 9), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 4), (5, 5), (5, 7), (5, 8), (5, 9), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_719_i2 : Fin 2 → Finset Cell := ![(placed21 1 (3, 3) required_1), required_719_i3]
def childrenD_719_i2 : Fin 2 → Finset Cell := ![(placed21 1 (3, 3) envelope_1), envelope_719_i3]
theorem common_sub_719_i2 : commonEnvelope childrenD_719_i2 ⊆ insert (4, 7) required_719_i2 := by decide +kernel
theorem child_required_sub_719_i2 : ∀ j, childrenC_719_i2 j ⊆ insert (4, 7) required_719_i2 := by decide +kernel
theorem child_envelope_sub_719_i2 : ∀ j, childrenD_719_i2 j ⊆ envelope_719_i2 := by decide +kernel
theorem pivot_mem_719_i2 : (4, 7) ∈ envelope_719_i2 := by decide +kernel
theorem children_work_719_i2 : ∀ j, Template HasSnaky 11 (childrenC_719_i2 j) (childrenD_719_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_1 1 (3, 3)).mono (by decide +kernel)
  · exact row_works_719_i3.mono (by decide +kernel)
theorem row_works_719_i2 : Template HasSnaky 12 required_719_i2 envelope_719_i2 := by
  refine compose HasSnaky 11 childrenC_719_i2 childrenD_719_i2 children_work_719_i2 (4, 7)
    required_719_i2 envelope_719_i2 pivot_mem_719_i2 child_required_sub_719_i2 child_envelope_sub_719_i2 ?_
  intro b hb
  exact common_sub_719_i2 (mem_commonEnvelope childrenD_719_i2 b hb)
def required_719_i1 : Finset Cell := ⟨(([(2, 5), (3, 3), (3, 5), (3, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_719_i1 : Finset Cell := ⟨(([(0, 5), (1, 5), (1, 7), (1, 8), (1, 9), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, 3), (3, 4), (3, 5), (3, 6), (3, 8), (3, 9), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_719_i1 : Fin 4 → Finset Cell := ![(placed21 1 (0, 5) required_53), (placed21 7 (6, 6) required_53), (placed21 7 (5, 6) required_209), required_719_i2]
def childrenD_719_i1 : Fin 4 → Finset Cell := ![(placed21 1 (0, 5) envelope_53), (placed21 7 (6, 6) envelope_53), (placed21 7 (5, 6) envelope_209), envelope_719_i2]
theorem common_sub_719_i1 : commonEnvelope childrenD_719_i1 ⊆ insert (4, 6) required_719_i1 := by decide +kernel
theorem child_required_sub_719_i1 : ∀ j, childrenC_719_i1 j ⊆ insert (4, 6) required_719_i1 := by decide +kernel
theorem child_envelope_sub_719_i1 : ∀ j, childrenD_719_i1 j ⊆ envelope_719_i1 := by decide +kernel
theorem pivot_mem_719_i1 : (4, 6) ∈ envelope_719_i1 := by decide +kernel
theorem children_work_719_i1 : ∀ j, Template HasSnaky 12 (childrenC_719_i1 j) (childrenD_719_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_53 1 (0, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_53 7 (6, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_209 7 (5, 6)).mono (by decide +kernel)
  · exact row_works_719_i2.mono (by decide +kernel)
theorem row_works_719_i1 : Template HasSnaky 13 required_719_i1 envelope_719_i1 := by
  refine compose HasSnaky 12 childrenC_719_i1 childrenD_719_i1 children_work_719_i1 (4, 6)
    required_719_i1 envelope_719_i1 pivot_mem_719_i1 child_required_sub_719_i1 child_envelope_sub_719_i1 ?_
  intro b hb
  exact common_sub_719_i1 (mem_commonEnvelope childrenD_719_i1 b hb)
def required_719_i0 : Finset Cell := ⟨(([(2, 4), (2, 5), (3, 3), (3, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_719_i0 : Finset Cell := ⟨(([(0, 5), (1, 5), (1, 7), (1, 8), (1, 9), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_719_i0 : Fin 4 → Finset Cell := ![(placed21 0 (2, 2) required_53), (placed21 6 (3, 8) required_53), (placed21 6 (3, 7) required_209), required_719_i1]
def childrenD_719_i0 : Fin 4 → Finset Cell := ![(placed21 0 (2, 2) envelope_53), (placed21 6 (3, 8) envelope_53), (placed21 6 (3, 7) envelope_209), envelope_719_i1]
theorem common_sub_719_i0 : commonEnvelope childrenD_719_i0 ⊆ insert (3, 6) required_719_i0 := by decide +kernel
theorem child_required_sub_719_i0 : ∀ j, childrenC_719_i0 j ⊆ insert (3, 6) required_719_i0 := by decide +kernel
theorem child_envelope_sub_719_i0 : ∀ j, childrenD_719_i0 j ⊆ envelope_719_i0 := by decide +kernel
theorem pivot_mem_719_i0 : (3, 6) ∈ envelope_719_i0 := by decide +kernel
theorem children_work_719_i0 : ∀ j, Template HasSnaky 13 (childrenC_719_i0 j) (childrenD_719_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_53 0 (2, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_53 6 (3, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_209 6 (3, 7)).mono (by decide +kernel)
  · exact row_works_719_i1.mono (by decide +kernel)
theorem row_works_719_i0 : Template HasSnaky 14 required_719_i0 envelope_719_i0 := by
  refine compose HasSnaky 13 childrenC_719_i0 childrenD_719_i0 children_work_719_i0 (3, 6)
    required_719_i0 envelope_719_i0 pivot_mem_719_i0 child_required_sub_719_i0 child_envelope_sub_719_i0 ?_
  intro b hb
  exact common_sub_719_i0 (mem_commonEnvelope childrenD_719_i0 b hb)
def required_719_i6 : Finset Cell := ⟨(([(2, 4), (2, 5), (3, 3), (3, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_719_i6 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 5), (1, 1), (1, 2), (1, 5), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 1), (4, 2), (4, 3), (4, 5), (4, 6), (4, 7), (4, 8), (5, 3), (5, 6), (6, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_719_i6 : Fin 3 → Finset Cell := ![(placed21 0 (2, 1) required_65), (placed21 1 (0, 3) required_301), (placed21 7 (5, 5) required_417)]
def childrenD_719_i6 : Fin 3 → Finset Cell := ![(placed21 0 (2, 1) envelope_65), (placed21 1 (0, 3) envelope_301), (placed21 7 (5, 5) envelope_417)]
theorem common_sub_719_i6 : commonEnvelope childrenD_719_i6 ⊆ insert (3, 4) required_719_i6 := by decide +kernel
theorem child_required_sub_719_i6 : ∀ j, childrenC_719_i6 j ⊆ insert (3, 4) required_719_i6 := by decide +kernel
theorem child_envelope_sub_719_i6 : ∀ j, childrenD_719_i6 j ⊆ envelope_719_i6 := by decide +kernel
theorem pivot_mem_719_i6 : (3, 4) ∈ envelope_719_i6 := by decide +kernel
theorem children_work_719_i6 : ∀ j, Template HasSnaky 6 (childrenC_719_i6 j) (childrenD_719_i6 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_65 0 (2, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_301 1 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_417 7 (5, 5)).mono (by decide +kernel)
theorem row_works_719_i6 : Template HasSnaky 7 required_719_i6 envelope_719_i6 := by
  refine compose HasSnaky 6 childrenC_719_i6 childrenD_719_i6 children_work_719_i6 (3, 4)
    required_719_i6 envelope_719_i6 pivot_mem_719_i6 child_required_sub_719_i6 child_envelope_sub_719_i6 ?_
  intro b hb
  exact common_sub_719_i6 (mem_commonEnvelope childrenD_719_i6 b hb)
def required_719_i7 : Finset Cell := ⟨(([(2, 4), (2, 5), (3, 3), (3, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_719_i7 : Finset Cell := ⟨(([(1, 5), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 1), (4, 2), (4, 3), (4, 6), (4, 7), (4, 8), (5, 6), (6, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_719_i7 : Fin 3 → Finset Cell := ![(placed21 2 (3, 2) required_15), (placed21 0 (2, 1) required_65), (placed21 1 (1, 3) required_72)]
def childrenD_719_i7 : Fin 3 → Finset Cell := ![(placed21 2 (3, 2) envelope_15), (placed21 0 (2, 1) envelope_65), (placed21 1 (1, 3) envelope_72)]
theorem common_sub_719_i7 : commonEnvelope childrenD_719_i7 ⊆ insert (3, 4) required_719_i7 := by decide +kernel
theorem child_required_sub_719_i7 : ∀ j, childrenC_719_i7 j ⊆ insert (3, 4) required_719_i7 := by decide +kernel
theorem child_envelope_sub_719_i7 : ∀ j, childrenD_719_i7 j ⊆ envelope_719_i7 := by decide +kernel
theorem pivot_mem_719_i7 : (3, 4) ∈ envelope_719_i7 := by decide +kernel
theorem children_work_719_i7 : ∀ j, Template HasSnaky 5 (childrenC_719_i7 j) (childrenD_719_i7 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_15 2 (3, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_65 0 (2, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_72 1 (1, 3)).mono (by decide +kernel)
theorem row_works_719_i7 : Template HasSnaky 6 required_719_i7 envelope_719_i7 := by
  refine compose HasSnaky 5 childrenC_719_i7 childrenD_719_i7 children_work_719_i7 (3, 4)
    required_719_i7 envelope_719_i7 pivot_mem_719_i7 child_required_sub_719_i7 child_envelope_sub_719_i7 ?_
  intro b hb
  exact common_sub_719_i7 (mem_commonEnvelope childrenD_719_i7 b hb)
def required_719 : Finset Cell := ⟨(([(2, 4), (2, 5), (3, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_719 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 5), (1, 0), (1, 1), (1, 2), (1, 5), (1, 7), (1, 8), (1, 9), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (4, 1), (4, 2), (4, 3), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_719 : Fin 5 → Finset Cell := ![(placed21 2 (3, 0) required_318), (placed21 4 (2, 7) required_334), required_719_i0, required_719_i6, required_719_i7]
def childrenD_719 : Fin 5 → Finset Cell := ![(placed21 2 (3, 0) envelope_318), (placed21 4 (2, 7) envelope_334), envelope_719_i0, envelope_719_i6, envelope_719_i7]
theorem common_sub_719 : commonEnvelope childrenD_719 ⊆ insert (3, 3) required_719 := by decide +kernel
theorem child_required_sub_719 : ∀ j, childrenC_719 j ⊆ insert (3, 3) required_719 := by decide +kernel
theorem child_envelope_sub_719 : ∀ j, childrenD_719 j ⊆ envelope_719 := by decide +kernel
theorem pivot_mem_719 : (3, 3) ∈ envelope_719 := by decide +kernel
theorem children_work_719 : ∀ j, Template HasSnaky 14 (childrenC_719 j) (childrenD_719 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_318 2 (3, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_334 4 (2, 7)).mono (by decide +kernel)
  · exact row_works_719_i0.mono (by decide +kernel)
  · exact row_works_719_i6.mono (by decide +kernel)
  · exact row_works_719_i7.mono (by decide +kernel)
theorem row_works_719 : Template HasSnaky 15 required_719 envelope_719 := by
  refine compose HasSnaky 14 childrenC_719 childrenD_719 children_work_719 (3, 3)
    required_719 envelope_719 pivot_mem_719 child_required_sub_719 child_envelope_sub_719 ?_
  intro b hb
  exact common_sub_719 (mem_commonEnvelope childrenD_719 b hb)
def height_719_i5 : ℕ := 9
def childrenH_719_i5 : Fin 2 → ℕ := ![height_5, height_412]
theorem height_exact_719_i5 : height_719_i5 = 1 + Finset.univ.sup childrenH_719_i5 := by decide +kernel
theorem required_origin_719_i5 : ∀ x ∈ required_719_i5,
    (∃ j, x ∈ childrenC_719_i5 j) ∨ ∀ j, x ∈ childrenD_719_i5 j := by decide +kernel
theorem required_exact_719_i5 : required_719_i5 =
    ((Finset.univ.biUnion childrenC_719_i5) ∪ commonEnvelope childrenD_719_i5).erase (3, 8) := by
  exact required_eq_combination childrenC_719_i5 childrenD_719_i5 (3, 8) required_719_i5
    (by decide +kernel) child_required_sub_719_i5 common_sub_719_i5 required_origin_719_i5
theorem envelope_origin_719_i5 : ∀ x ∈ envelope_719_i5,
    x = (3, 8) ∨ ∃ j, x ∈ childrenD_719_i5 j := by decide +kernel
theorem envelope_exact_719_i5 : envelope_719_i5 =
    insert (3, 8) (Finset.univ.biUnion childrenD_719_i5) := by
  exact envelope_eq_combination childrenD_719_i5 (3, 8) envelope_719_i5
    pivot_mem_719_i5 child_envelope_sub_719_i5 envelope_origin_719_i5
def checked_719_i5 : CheckedCard where
  required := required_719_i5
  envelope := envelope_719_i5
  height := height_719_i5
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_719_i5
def height_719_i4 : ℕ := 10
def childrenH_719_i4 : Fin 3 → ℕ := ![height_45, height_343, height_719_i5]
theorem height_exact_719_i4 : height_719_i4 = 1 + Finset.univ.sup childrenH_719_i4 := by decide +kernel
theorem required_origin_719_i4 : ∀ x ∈ required_719_i4,
    (∃ j, x ∈ childrenC_719_i4 j) ∨ ∀ j, x ∈ childrenD_719_i4 j := by decide +kernel
theorem required_exact_719_i4 : required_719_i4 =
    ((Finset.univ.biUnion childrenC_719_i4) ∪ commonEnvelope childrenD_719_i4).erase (4, 5) := by
  exact required_eq_combination childrenC_719_i4 childrenD_719_i4 (4, 5) required_719_i4
    (by decide +kernel) child_required_sub_719_i4 common_sub_719_i4 required_origin_719_i4
theorem envelope_origin_719_i4 : ∀ x ∈ envelope_719_i4,
    x = (4, 5) ∨ ∃ j, x ∈ childrenD_719_i4 j := by decide +kernel
theorem envelope_exact_719_i4 : envelope_719_i4 =
    insert (4, 5) (Finset.univ.biUnion childrenD_719_i4) := by
  exact envelope_eq_combination childrenD_719_i4 (4, 5) envelope_719_i4
    pivot_mem_719_i4 child_envelope_sub_719_i4 envelope_origin_719_i4
def checked_719_i4 : CheckedCard where
  required := required_719_i4
  envelope := envelope_719_i4
  height := height_719_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_719_i4
def height_719_i3 : ℕ := 11
def childrenH_719_i3 : Fin 2 → ℕ := ![height_0, height_719_i4]
theorem height_exact_719_i3 : height_719_i3 = 1 + Finset.univ.sup childrenH_719_i3 := by decide +kernel
theorem required_origin_719_i3 : ∀ x ∈ required_719_i3,
    (∃ j, x ∈ childrenC_719_i3 j) ∨ ∀ j, x ∈ childrenD_719_i3 j := by decide +kernel
theorem required_exact_719_i3 : required_719_i3 =
    ((Finset.univ.biUnion childrenC_719_i3) ∪ commonEnvelope childrenD_719_i3).erase (4, 8) := by
  exact required_eq_combination childrenC_719_i3 childrenD_719_i3 (4, 8) required_719_i3
    (by decide +kernel) child_required_sub_719_i3 common_sub_719_i3 required_origin_719_i3
theorem envelope_origin_719_i3 : ∀ x ∈ envelope_719_i3,
    x = (4, 8) ∨ ∃ j, x ∈ childrenD_719_i3 j := by decide +kernel
theorem envelope_exact_719_i3 : envelope_719_i3 =
    insert (4, 8) (Finset.univ.biUnion childrenD_719_i3) := by
  exact envelope_eq_combination childrenD_719_i3 (4, 8) envelope_719_i3
    pivot_mem_719_i3 child_envelope_sub_719_i3 envelope_origin_719_i3
def checked_719_i3 : CheckedCard where
  required := required_719_i3
  envelope := envelope_719_i3
  height := height_719_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_719_i3
def height_719_i2 : ℕ := 12
def childrenH_719_i2 : Fin 2 → ℕ := ![height_1, height_719_i3]
theorem height_exact_719_i2 : height_719_i2 = 1 + Finset.univ.sup childrenH_719_i2 := by decide +kernel
theorem required_origin_719_i2 : ∀ x ∈ required_719_i2,
    (∃ j, x ∈ childrenC_719_i2 j) ∨ ∀ j, x ∈ childrenD_719_i2 j := by decide +kernel
theorem required_exact_719_i2 : required_719_i2 =
    ((Finset.univ.biUnion childrenC_719_i2) ∪ commonEnvelope childrenD_719_i2).erase (4, 7) := by
  exact required_eq_combination childrenC_719_i2 childrenD_719_i2 (4, 7) required_719_i2
    (by decide +kernel) child_required_sub_719_i2 common_sub_719_i2 required_origin_719_i2
theorem envelope_origin_719_i2 : ∀ x ∈ envelope_719_i2,
    x = (4, 7) ∨ ∃ j, x ∈ childrenD_719_i2 j := by decide +kernel
theorem envelope_exact_719_i2 : envelope_719_i2 =
    insert (4, 7) (Finset.univ.biUnion childrenD_719_i2) := by
  exact envelope_eq_combination childrenD_719_i2 (4, 7) envelope_719_i2
    pivot_mem_719_i2 child_envelope_sub_719_i2 envelope_origin_719_i2
def checked_719_i2 : CheckedCard where
  required := required_719_i2
  envelope := envelope_719_i2
  height := height_719_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_719_i2
def height_719_i1 : ℕ := 13
def childrenH_719_i1 : Fin 4 → ℕ := ![height_53, height_53, height_209, height_719_i2]
theorem height_exact_719_i1 : height_719_i1 = 1 + Finset.univ.sup childrenH_719_i1 := by decide +kernel
theorem required_origin_719_i1 : ∀ x ∈ required_719_i1,
    (∃ j, x ∈ childrenC_719_i1 j) ∨ ∀ j, x ∈ childrenD_719_i1 j := by decide +kernel
theorem required_exact_719_i1 : required_719_i1 =
    ((Finset.univ.biUnion childrenC_719_i1) ∪ commonEnvelope childrenD_719_i1).erase (4, 6) := by
  exact required_eq_combination childrenC_719_i1 childrenD_719_i1 (4, 6) required_719_i1
    (by decide +kernel) child_required_sub_719_i1 common_sub_719_i1 required_origin_719_i1
theorem envelope_origin_719_i1 : ∀ x ∈ envelope_719_i1,
    x = (4, 6) ∨ ∃ j, x ∈ childrenD_719_i1 j := by decide +kernel
theorem envelope_exact_719_i1 : envelope_719_i1 =
    insert (4, 6) (Finset.univ.biUnion childrenD_719_i1) := by
  exact envelope_eq_combination childrenD_719_i1 (4, 6) envelope_719_i1
    pivot_mem_719_i1 child_envelope_sub_719_i1 envelope_origin_719_i1
def checked_719_i1 : CheckedCard where
  required := required_719_i1
  envelope := envelope_719_i1
  height := height_719_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_719_i1
def height_719_i0 : ℕ := 14
def childrenH_719_i0 : Fin 4 → ℕ := ![height_53, height_53, height_209, height_719_i1]
theorem height_exact_719_i0 : height_719_i0 = 1 + Finset.univ.sup childrenH_719_i0 := by decide +kernel
theorem required_origin_719_i0 : ∀ x ∈ required_719_i0,
    (∃ j, x ∈ childrenC_719_i0 j) ∨ ∀ j, x ∈ childrenD_719_i0 j := by decide +kernel
theorem required_exact_719_i0 : required_719_i0 =
    ((Finset.univ.biUnion childrenC_719_i0) ∪ commonEnvelope childrenD_719_i0).erase (3, 6) := by
  exact required_eq_combination childrenC_719_i0 childrenD_719_i0 (3, 6) required_719_i0
    (by decide +kernel) child_required_sub_719_i0 common_sub_719_i0 required_origin_719_i0
theorem envelope_origin_719_i0 : ∀ x ∈ envelope_719_i0,
    x = (3, 6) ∨ ∃ j, x ∈ childrenD_719_i0 j := by decide +kernel
theorem envelope_exact_719_i0 : envelope_719_i0 =
    insert (3, 6) (Finset.univ.biUnion childrenD_719_i0) := by
  exact envelope_eq_combination childrenD_719_i0 (3, 6) envelope_719_i0
    pivot_mem_719_i0 child_envelope_sub_719_i0 envelope_origin_719_i0
def checked_719_i0 : CheckedCard where
  required := required_719_i0
  envelope := envelope_719_i0
  height := height_719_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_719_i0
def height_719_i6 : ℕ := 7
def childrenH_719_i6 : Fin 3 → ℕ := ![height_65, height_301, height_417]
theorem height_exact_719_i6 : height_719_i6 = 1 + Finset.univ.sup childrenH_719_i6 := by decide +kernel
theorem required_origin_719_i6 : ∀ x ∈ required_719_i6,
    (∃ j, x ∈ childrenC_719_i6 j) ∨ ∀ j, x ∈ childrenD_719_i6 j := by decide +kernel
theorem required_exact_719_i6 : required_719_i6 =
    ((Finset.univ.biUnion childrenC_719_i6) ∪ commonEnvelope childrenD_719_i6).erase (3, 4) := by
  exact required_eq_combination childrenC_719_i6 childrenD_719_i6 (3, 4) required_719_i6
    (by decide +kernel) child_required_sub_719_i6 common_sub_719_i6 required_origin_719_i6
theorem envelope_origin_719_i6 : ∀ x ∈ envelope_719_i6,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_719_i6 j := by decide +kernel
theorem envelope_exact_719_i6 : envelope_719_i6 =
    insert (3, 4) (Finset.univ.biUnion childrenD_719_i6) := by
  exact envelope_eq_combination childrenD_719_i6 (3, 4) envelope_719_i6
    pivot_mem_719_i6 child_envelope_sub_719_i6 envelope_origin_719_i6
def checked_719_i6 : CheckedCard where
  required := required_719_i6
  envelope := envelope_719_i6
  height := height_719_i6
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_719_i6
def height_719_i7 : ℕ := 6
def childrenH_719_i7 : Fin 3 → ℕ := ![height_15, height_65, height_72]
theorem height_exact_719_i7 : height_719_i7 = 1 + Finset.univ.sup childrenH_719_i7 := by decide +kernel
theorem required_origin_719_i7 : ∀ x ∈ required_719_i7,
    (∃ j, x ∈ childrenC_719_i7 j) ∨ ∀ j, x ∈ childrenD_719_i7 j := by decide +kernel
theorem required_exact_719_i7 : required_719_i7 =
    ((Finset.univ.biUnion childrenC_719_i7) ∪ commonEnvelope childrenD_719_i7).erase (3, 4) := by
  exact required_eq_combination childrenC_719_i7 childrenD_719_i7 (3, 4) required_719_i7
    (by decide +kernel) child_required_sub_719_i7 common_sub_719_i7 required_origin_719_i7
theorem envelope_origin_719_i7 : ∀ x ∈ envelope_719_i7,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_719_i7 j := by decide +kernel
theorem envelope_exact_719_i7 : envelope_719_i7 =
    insert (3, 4) (Finset.univ.biUnion childrenD_719_i7) := by
  exact envelope_eq_combination childrenD_719_i7 (3, 4) envelope_719_i7
    pivot_mem_719_i7 child_envelope_sub_719_i7 envelope_origin_719_i7
def checked_719_i7 : CheckedCard where
  required := required_719_i7
  envelope := envelope_719_i7
  height := height_719_i7
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_719_i7
def height_719 : ℕ := 15
def childrenH_719 : Fin 5 → ℕ := ![height_318, height_334, height_719_i0, height_719_i6, height_719_i7]
theorem height_exact_719 : height_719 = 1 + Finset.univ.sup childrenH_719 := by decide +kernel
theorem required_origin_719 : ∀ x ∈ required_719,
    (∃ j, x ∈ childrenC_719 j) ∨ ∀ j, x ∈ childrenD_719 j := by decide +kernel
theorem required_exact_719 : required_719 =
    ((Finset.univ.biUnion childrenC_719) ∪ commonEnvelope childrenD_719).erase (3, 3) := by
  exact required_eq_combination childrenC_719 childrenD_719 (3, 3) required_719
    (by decide +kernel) child_required_sub_719 common_sub_719 required_origin_719
theorem envelope_origin_719 : ∀ x ∈ envelope_719,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_719 j := by decide +kernel
theorem envelope_exact_719 : envelope_719 =
    insert (3, 3) (Finset.univ.biUnion childrenD_719) := by
  exact envelope_eq_combination childrenD_719 (3, 3) envelope_719
    pivot_mem_719 child_envelope_sub_719 envelope_origin_719
def checked_719 : CheckedCard where
  required := required_719
  envelope := envelope_719
  height := height_719
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_719
end SnakyPrototype.Certificate21

end OAI
