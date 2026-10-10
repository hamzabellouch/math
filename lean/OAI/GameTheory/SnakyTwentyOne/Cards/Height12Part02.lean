import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height10Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height11Part02
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_551_i7 : Finset Cell := ⟨(([(1, 3), (2, 3), (2, 5), (2, 6), (4, 3), (5, 3), (6, 3), (7, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_551_i7 : Finset Cell := ⟨(([(0, 2), (0, 4), (1, 2), (1, 3), (1, 4), (1, 5), (2, 2), (2, 3), (2, 5), (2, 6), (3, 2), (3, 3), (4, 2), (4, 3), (5, 3), (6, 3), (7, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_551_i7 : Fin 2 → Finset Cell := ![(placed21 7 (7, 3) required_6), (placed21 2 (4, 2) required_78)]
def childrenD_551_i7 : Fin 2 → Finset Cell := ![(placed21 7 (7, 3) envelope_6), (placed21 2 (4, 2) envelope_78)]
theorem common_sub_551_i7 : commonEnvelope childrenD_551_i7 ⊆ insert (3, 3) required_551_i7 := by decide +kernel
theorem child_required_sub_551_i7 : ∀ j, childrenC_551_i7 j ⊆ insert (3, 3) required_551_i7 := by decide +kernel
theorem child_envelope_sub_551_i7 : ∀ j, childrenD_551_i7 j ⊆ envelope_551_i7 := by decide +kernel
theorem pivot_mem_551_i7 : (3, 3) ∈ envelope_551_i7 := by decide +kernel
theorem children_work_551_i7 : ∀ j, Template HasSnaky 3 (childrenC_551_i7 j) (childrenD_551_i7 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_6 7 (7, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_78 2 (4, 2)).mono (by decide +kernel)
theorem row_works_551_i7 : Template HasSnaky 4 required_551_i7 envelope_551_i7 := by
  refine compose HasSnaky 3 childrenC_551_i7 childrenD_551_i7 children_work_551_i7 (3, 3)
    required_551_i7 envelope_551_i7 pivot_mem_551_i7 child_required_sub_551_i7 child_envelope_sub_551_i7 ?_
  intro b hb
  exact common_sub_551_i7 (mem_commonEnvelope childrenD_551_i7 b hb)
def required_551_i8 : Finset Cell := ⟨(([(1, 3), (2, 3), (4, 3), (5, 3), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_551_i8 : Finset Cell := ⟨(([(0, 2), (1, 2), (1, 3), (2, 2), (2, 3), (3, 3), (4, 3), (5, 3), (5, 4), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_551_i8 : Fin 2 → Finset Cell := ![(placed21 0 (2, 3) required_4), (placed21 7 (5, 3) required_6)]
def childrenD_551_i8 : Fin 2 → Finset Cell := ![(placed21 0 (2, 3) envelope_4), (placed21 7 (5, 3) envelope_6)]
theorem common_sub_551_i8 : commonEnvelope childrenD_551_i8 ⊆ insert (3, 3) required_551_i8 := by decide +kernel
theorem child_required_sub_551_i8 : ∀ j, childrenC_551_i8 j ⊆ insert (3, 3) required_551_i8 := by decide +kernel
theorem child_envelope_sub_551_i8 : ∀ j, childrenD_551_i8 j ⊆ envelope_551_i8 := by decide +kernel
theorem pivot_mem_551_i8 : (3, 3) ∈ envelope_551_i8 := by decide +kernel
theorem children_work_551_i8 : ∀ j, Template HasSnaky 2 (childrenC_551_i8 j) (childrenD_551_i8 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_4 0 (2, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_6 7 (5, 3)).mono (by decide +kernel)
theorem row_works_551_i8 : Template HasSnaky 3 required_551_i8 envelope_551_i8 := by
  refine compose HasSnaky 2 childrenC_551_i8 childrenD_551_i8 children_work_551_i8 (3, 3)
    required_551_i8 envelope_551_i8 pivot_mem_551_i8 child_required_sub_551_i8 child_envelope_sub_551_i8 ?_
  intro b hb
  exact common_sub_551_i8 (mem_commonEnvelope childrenD_551_i8 b hb)
def required_551_i6 : Finset Cell := ⟨(([(1, 3), (2, 3), (2, 5), (2, 6), (5, 3), (5, 5), (5, 6), (6, 3), (6, 4), (7, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_551_i6 : Finset Cell := ⟨(([(0, 2), (0, 4), (1, 2), (1, 3), (1, 4), (1, 5), (2, 2), (2, 3), (2, 5), (2, 6), (3, 2), (3, 3), (4, 2), (4, 3), (5, 3), (5, 4), (5, 5), (5, 6), (6, 3), (6, 4), (7, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_551_i6 : Fin 3 → Finset Cell := ![(placed21 2 (7, 2) required_25), required_551_i7, required_551_i8]
def childrenD_551_i6 : Fin 3 → Finset Cell := ![(placed21 2 (7, 2) envelope_25), envelope_551_i7, envelope_551_i8]
theorem common_sub_551_i6 : commonEnvelope childrenD_551_i6 ⊆ insert (4, 3) required_551_i6 := by decide +kernel
theorem child_required_sub_551_i6 : ∀ j, childrenC_551_i6 j ⊆ insert (4, 3) required_551_i6 := by decide +kernel
theorem child_envelope_sub_551_i6 : ∀ j, childrenD_551_i6 j ⊆ envelope_551_i6 := by decide +kernel
theorem pivot_mem_551_i6 : (4, 3) ∈ envelope_551_i6 := by decide +kernel
theorem children_work_551_i6 : ∀ j, Template HasSnaky 4 (childrenC_551_i6 j) (childrenD_551_i6 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_25 2 (7, 2)).mono (by decide +kernel)
  · exact row_works_551_i7.mono (by decide +kernel)
  · exact row_works_551_i8.mono (by decide +kernel)
theorem row_works_551_i6 : Template HasSnaky 5 required_551_i6 envelope_551_i6 := by
  refine compose HasSnaky 4 childrenC_551_i6 childrenD_551_i6 children_work_551_i6 (4, 3)
    required_551_i6 envelope_551_i6 pivot_mem_551_i6 child_required_sub_551_i6 child_envelope_sub_551_i6 ?_
  intro b hb
  exact common_sub_551_i6 (mem_commonEnvelope childrenD_551_i6 b hb)
def required_551_i5 : Finset Cell := ⟨(([(1, 3), (2, 3), (2, 5), (2, 6), (5, 3), (5, 5), (5, 6), (6, 3), (6, 4), (6, 5), (6, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_551_i5 : Finset Cell := ⟨(([(0, 2), (0, 4), (1, 2), (1, 3), (1, 4), (1, 5), (2, 2), (2, 3), (2, 5), (2, 6), (3, 2), (3, 3), (4, 2), (4, 3), (5, 3), (5, 4), (5, 5), (5, 6), (6, 3), (6, 4), (6, 5), (6, 6), (7, 2), (7, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_551_i5 : Fin 2 → Finset Cell := ![(placed21 3 (6, 6) required_5), required_551_i6]
def childrenD_551_i5 : Fin 2 → Finset Cell := ![(placed21 3 (6, 6) envelope_5), envelope_551_i6]
theorem common_sub_551_i5 : commonEnvelope childrenD_551_i5 ⊆ insert (7, 3) required_551_i5 := by decide +kernel
theorem child_required_sub_551_i5 : ∀ j, childrenC_551_i5 j ⊆ insert (7, 3) required_551_i5 := by decide +kernel
theorem child_envelope_sub_551_i5 : ∀ j, childrenD_551_i5 j ⊆ envelope_551_i5 := by decide +kernel
theorem pivot_mem_551_i5 : (7, 3) ∈ envelope_551_i5 := by decide +kernel
theorem children_work_551_i5 : ∀ j, Template HasSnaky 5 (childrenC_551_i5 j) (childrenD_551_i5 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 3 (6, 6)).mono (by decide +kernel)
  · exact row_works_551_i6.mono (by decide +kernel)
theorem row_works_551_i5 : Template HasSnaky 6 required_551_i5 envelope_551_i5 := by
  refine compose HasSnaky 5 childrenC_551_i5 childrenD_551_i5 children_work_551_i5 (7, 3)
    required_551_i5 envelope_551_i5 pivot_mem_551_i5 child_required_sub_551_i5 child_envelope_sub_551_i5 ?_
  intro b hb
  exact common_sub_551_i5 (mem_commonEnvelope childrenD_551_i5 b hb)
def required_551_i4 : Finset Cell := ⟨(([(1, 3), (2, 3), (2, 5), (2, 6), (5, 5), (5, 6), (6, 3), (6, 4), (6, 5), (6, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_551_i4 : Finset Cell := ⟨(([(0, 2), (0, 4), (1, 2), (1, 3), (1, 4), (1, 5), (2, 2), (2, 3), (2, 5), (2, 6), (3, 2), (3, 3), (4, 2), (4, 3), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (6, 3), (6, 4), (6, 5), (6, 6), (7, 2), (7, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_551_i4 : Fin 2 → Finset Cell := ![(placed21 7 (6, 6) required_5), required_551_i5]
def childrenD_551_i4 : Fin 2 → Finset Cell := ![(placed21 7 (6, 6) envelope_5), envelope_551_i5]
theorem common_sub_551_i4 : commonEnvelope childrenD_551_i4 ⊆ insert (5, 3) required_551_i4 := by decide +kernel
theorem child_required_sub_551_i4 : ∀ j, childrenC_551_i4 j ⊆ insert (5, 3) required_551_i4 := by decide +kernel
theorem child_envelope_sub_551_i4 : ∀ j, childrenD_551_i4 j ⊆ envelope_551_i4 := by decide +kernel
theorem pivot_mem_551_i4 : (5, 3) ∈ envelope_551_i4 := by decide +kernel
theorem children_work_551_i4 : ∀ j, Template HasSnaky 6 (childrenC_551_i4 j) (childrenD_551_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 7 (6, 6)).mono (by decide +kernel)
  · exact row_works_551_i5.mono (by decide +kernel)
theorem row_works_551_i4 : Template HasSnaky 7 required_551_i4 envelope_551_i4 := by
  refine compose HasSnaky 6 childrenC_551_i4 childrenD_551_i4 children_work_551_i4 (5, 3)
    required_551_i4 envelope_551_i4 pivot_mem_551_i4 child_required_sub_551_i4 child_envelope_sub_551_i4 ?_
  intro b hb
  exact common_sub_551_i4 (mem_commonEnvelope childrenD_551_i4 b hb)
def required_551_i3 : Finset Cell := ⟨(([(1, 3), (2, 3), (2, 6), (4, 5), (5, 5), (5, 6), (6, 3), (6, 4), (6, 5), (6, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_551_i3 : Finset Cell := ⟨(([(0, 2), (0, 4), (1, 2), (1, 3), (1, 4), (1, 5), (2, 2), (2, 3), (2, 5), (2, 6), (3, 2), (3, 3), (3, 5), (4, 2), (4, 3), (4, 5), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (6, 3), (6, 4), (6, 5), (6, 6), (7, 2), (7, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_551_i3 : Fin 2 → Finset Cell := ![(placed21 0 (2, 5) required_1), required_551_i4]
def childrenD_551_i3 : Fin 2 → Finset Cell := ![(placed21 0 (2, 5) envelope_1), envelope_551_i4]
theorem common_sub_551_i3 : commonEnvelope childrenD_551_i3 ⊆ insert (2, 5) required_551_i3 := by decide +kernel
theorem child_required_sub_551_i3 : ∀ j, childrenC_551_i3 j ⊆ insert (2, 5) required_551_i3 := by decide +kernel
theorem child_envelope_sub_551_i3 : ∀ j, childrenD_551_i3 j ⊆ envelope_551_i3 := by decide +kernel
theorem pivot_mem_551_i3 : (2, 5) ∈ envelope_551_i3 := by decide +kernel
theorem children_work_551_i3 : ∀ j, Template HasSnaky 7 (childrenC_551_i3 j) (childrenD_551_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_1 0 (2, 5)).mono (by decide +kernel)
  · exact row_works_551_i4.mono (by decide +kernel)
theorem row_works_551_i3 : Template HasSnaky 8 required_551_i3 envelope_551_i3 := by
  refine compose HasSnaky 7 childrenC_551_i3 childrenD_551_i3 children_work_551_i3 (2, 5)
    required_551_i3 envelope_551_i3 pivot_mem_551_i3 child_required_sub_551_i3 child_envelope_sub_551_i3 ?_
  intro b hb
  exact common_sub_551_i3 (mem_commonEnvelope childrenD_551_i3 b hb)
def required_551_i2 : Finset Cell := ⟨(([(1, 3), (2, 3), (2, 6), (4, 5), (5, 5), (6, 3), (6, 4), (6, 5), (6, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_551_i2 : Finset Cell := ⟨(([(0, 2), (0, 4), (1, 2), (1, 3), (1, 4), (1, 5), (2, 2), (2, 3), (2, 5), (2, 6), (3, 2), (3, 3), (3, 5), (4, 2), (4, 3), (4, 5), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 3), (6, 4), (6, 5), (6, 6), (7, 2), (7, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_551_i2 : Fin 2 → Finset Cell := ![(placed21 5 (6, 3) required_5), required_551_i3]
def childrenD_551_i2 : Fin 2 → Finset Cell := ![(placed21 5 (6, 3) envelope_5), envelope_551_i3]
theorem common_sub_551_i2 : commonEnvelope childrenD_551_i2 ⊆ insert (5, 6) required_551_i2 := by decide +kernel
theorem child_required_sub_551_i2 : ∀ j, childrenC_551_i2 j ⊆ insert (5, 6) required_551_i2 := by decide +kernel
theorem child_envelope_sub_551_i2 : ∀ j, childrenD_551_i2 j ⊆ envelope_551_i2 := by decide +kernel
theorem pivot_mem_551_i2 : (5, 6) ∈ envelope_551_i2 := by decide +kernel
theorem children_work_551_i2 : ∀ j, Template HasSnaky 8 (childrenC_551_i2 j) (childrenD_551_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 5 (6, 3)).mono (by decide +kernel)
  · exact row_works_551_i3.mono (by decide +kernel)
theorem row_works_551_i2 : Template HasSnaky 9 required_551_i2 envelope_551_i2 := by
  refine compose HasSnaky 8 childrenC_551_i2 childrenD_551_i2 children_work_551_i2 (5, 6)
    required_551_i2 envelope_551_i2 pivot_mem_551_i2 child_required_sub_551_i2 child_envelope_sub_551_i2 ?_
  intro b hb
  exact common_sub_551_i2 (mem_commonEnvelope childrenD_551_i2 b hb)
def required_551_i1 : Finset Cell := ⟨(([(1, 3), (2, 3), (2, 6), (4, 5), (5, 5), (6, 3), (6, 4), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_551_i1 : Finset Cell := ⟨(([(0, 2), (0, 4), (1, 2), (1, 3), (1, 4), (1, 5), (2, 2), (2, 3), (2, 5), (2, 6), (3, 2), (3, 3), (3, 5), (4, 2), (4, 3), (4, 5), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (7, 2), (7, 3), (7, 7), (7, 8), (7, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_551_i1 : Fin 4 → Finset Cell := ![(placed21 0 (5, 2) required_19), (placed21 0 (5, 2) required_84), (placed21 1 (5, 3) required_314), required_551_i2]
def childrenD_551_i1 : Fin 4 → Finset Cell := ![(placed21 0 (5, 2) envelope_19), (placed21 0 (5, 2) envelope_84), (placed21 1 (5, 3) envelope_314), envelope_551_i2]
theorem common_sub_551_i1 : commonEnvelope childrenD_551_i1 ⊆ insert (6, 6) required_551_i1 := by decide +kernel
theorem child_required_sub_551_i1 : ∀ j, childrenC_551_i1 j ⊆ insert (6, 6) required_551_i1 := by decide +kernel
theorem child_envelope_sub_551_i1 : ∀ j, childrenD_551_i1 j ⊆ envelope_551_i1 := by decide +kernel
theorem pivot_mem_551_i1 : (6, 6) ∈ envelope_551_i1 := by decide +kernel
theorem children_work_551_i1 : ∀ j, Template HasSnaky 9 (childrenC_551_i1 j) (childrenD_551_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_19 0 (5, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_84 0 (5, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_314 1 (5, 3)).mono (by decide +kernel)
  · exact row_works_551_i2.mono (by decide +kernel)
theorem row_works_551_i1 : Template HasSnaky 10 required_551_i1 envelope_551_i1 := by
  refine compose HasSnaky 9 childrenC_551_i1 childrenD_551_i1 children_work_551_i1 (6, 6)
    required_551_i1 envelope_551_i1 pivot_mem_551_i1 child_required_sub_551_i1 child_envelope_sub_551_i1 ?_
  intro b hb
  exact common_sub_551_i1 (mem_commonEnvelope childrenD_551_i1 b hb)
def required_551_i0 : Finset Cell := ⟨(([(1, 3), (2, 3), (2, 6), (4, 5), (5, 5), (6, 4), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_551_i0 : Finset Cell := ⟨(([(0, 2), (0, 4), (1, 2), (1, 3), (1, 4), (1, 5), (2, 2), (2, 3), (2, 5), (2, 6), (3, 2), (3, 3), (3, 5), (4, 2), (4, 3), (4, 5), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (7, 0), (7, 1), (7, 2), (7, 3), (7, 7), (7, 8), (7, 9)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_551_i0 : Fin 4 → Finset Cell := ![(placed21 4 (5, 6) required_10), (placed21 2 (6, 2) required_44), (placed21 4 (5, 6) required_63), required_551_i1]
def childrenD_551_i0 : Fin 4 → Finset Cell := ![(placed21 4 (5, 6) envelope_10), (placed21 2 (6, 2) envelope_44), (placed21 4 (5, 6) envelope_63), envelope_551_i1]
theorem common_sub_551_i0 : commonEnvelope childrenD_551_i0 ⊆ insert (6, 3) required_551_i0 := by decide +kernel
theorem child_required_sub_551_i0 : ∀ j, childrenC_551_i0 j ⊆ insert (6, 3) required_551_i0 := by decide +kernel
theorem child_envelope_sub_551_i0 : ∀ j, childrenD_551_i0 j ⊆ envelope_551_i0 := by decide +kernel
theorem pivot_mem_551_i0 : (6, 3) ∈ envelope_551_i0 := by decide +kernel
theorem children_work_551_i0 : ∀ j, Template HasSnaky 10 (childrenC_551_i0 j) (childrenD_551_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_10 4 (5, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_44 2 (6, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_63 4 (5, 6)).mono (by decide +kernel)
  · exact row_works_551_i1.mono (by decide +kernel)
theorem row_works_551_i0 : Template HasSnaky 11 required_551_i0 envelope_551_i0 := by
  refine compose HasSnaky 10 childrenC_551_i0 childrenD_551_i0 children_work_551_i0 (6, 3)
    required_551_i0 envelope_551_i0 pivot_mem_551_i0 child_required_sub_551_i0 child_envelope_sub_551_i0 ?_
  intro b hb
  exact common_sub_551_i0 (mem_commonEnvelope childrenD_551_i0 b hb)
def required_551 : Finset Cell := ⟨(([(1, 3), (2, 3), (2, 6), (4, 5), (5, 5), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_551 : Finset Cell := ⟨(([(0, 2), (0, 4), (1, 2), (1, 3), (1, 4), (1, 5), (2, 2), (2, 3), (2, 5), (2, 6), (3, 2), (3, 3), (3, 5), (4, 2), (4, 3), (4, 5), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 7), (7, 8), (7, 9), (8, 4), (9, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_551 : Fin 3 → Finset Cell := ![(placed21 3 (3, 5) required_52), (placed21 0 (3, 1) required_523), required_551_i0]
def childrenD_551 : Fin 3 → Finset Cell := ![(placed21 3 (3, 5) envelope_52), (placed21 0 (3, 1) envelope_523), envelope_551_i0]
theorem common_sub_551 : commonEnvelope childrenD_551 ⊆ insert (6, 4) required_551 := by decide +kernel
theorem child_required_sub_551 : ∀ j, childrenC_551 j ⊆ insert (6, 4) required_551 := by decide +kernel
theorem child_envelope_sub_551 : ∀ j, childrenD_551 j ⊆ envelope_551 := by decide +kernel
theorem pivot_mem_551 : (6, 4) ∈ envelope_551 := by decide +kernel
theorem children_work_551 : ∀ j, Template HasSnaky 11 (childrenC_551 j) (childrenD_551 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_52 3 (3, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_523 0 (3, 1)).mono (by decide +kernel)
  · exact row_works_551_i0.mono (by decide +kernel)
theorem row_works_551 : Template HasSnaky 12 required_551 envelope_551 := by
  refine compose HasSnaky 11 childrenC_551 childrenD_551 children_work_551 (6, 4)
    required_551 envelope_551 pivot_mem_551 child_required_sub_551 child_envelope_sub_551 ?_
  intro b hb
  exact common_sub_551 (mem_commonEnvelope childrenD_551 b hb)
def required_571_i1 : Finset Cell := ⟨(([(0, 3), (3, 3), (3, 4), (3, 6), (4, 4), (4, 6), (4, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_571_i1 : Finset Cell := ⟨(([(0, 3), (1, 3), (2, 3), (2, 7), (3, 3), (3, 4), (3, 6), (3, 7), (4, 4), (4, 6), (4, 7), (4, 8), (4, 9), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, 5), (8, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_571_i1 : Fin 4 → Finset Cell := ![(placed21 1 (0, 3) required_287), (placed21 1 (0, 3) required_288), (placed21 0 (2, 4) required_345), (placed21 1 (2, 5) required_457)]
def childrenD_571_i1 : Fin 4 → Finset Cell := ![(placed21 1 (0, 3) envelope_287), (placed21 1 (0, 3) envelope_288), (placed21 0 (2, 4) envelope_345), (placed21 1 (2, 5) envelope_457)]
theorem common_sub_571_i1 : commonEnvelope childrenD_571_i1 ⊆ insert (5, 6) required_571_i1 := by decide +kernel
theorem child_required_sub_571_i1 : ∀ j, childrenC_571_i1 j ⊆ insert (5, 6) required_571_i1 := by decide +kernel
theorem child_envelope_sub_571_i1 : ∀ j, childrenD_571_i1 j ⊆ envelope_571_i1 := by decide +kernel
theorem pivot_mem_571_i1 : (5, 6) ∈ envelope_571_i1 := by decide +kernel
theorem children_work_571_i1 : ∀ j, Template HasSnaky 9 (childrenC_571_i1 j) (childrenD_571_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_287 1 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_288 1 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_345 0 (2, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_457 1 (2, 5)).mono (by decide +kernel)
theorem row_works_571_i1 : Template HasSnaky 10 required_571_i1 envelope_571_i1 := by
  refine compose HasSnaky 9 childrenC_571_i1 childrenD_571_i1 children_work_571_i1 (5, 6)
    required_571_i1 envelope_571_i1 pivot_mem_571_i1 child_required_sub_571_i1 child_envelope_sub_571_i1 ?_
  intro b hb
  exact common_sub_571_i1 (mem_commonEnvelope childrenD_571_i1 b hb)
def required_571_i0 : Finset Cell := ⟨(([(0, 3), (3, 3), (3, 4), (3, 6), (4, 4), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_571_i0 : Finset Cell := ⟨(([(0, 3), (1, 3), (2, 3), (2, 7), (3, 3), (3, 4), (3, 6), (3, 7), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, 5), (8, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_571_i0 : Fin 2 → Finset Cell := ![(placed21 7 (4, 7) required_2), required_571_i1]
def childrenD_571_i0 : Fin 2 → Finset Cell := ![(placed21 7 (4, 7) envelope_2), envelope_571_i1]
theorem common_sub_571_i0 : commonEnvelope childrenD_571_i0 ⊆ insert (4, 7) required_571_i0 := by decide +kernel
theorem child_required_sub_571_i0 : ∀ j, childrenC_571_i0 j ⊆ insert (4, 7) required_571_i0 := by decide +kernel
theorem child_envelope_sub_571_i0 : ∀ j, childrenD_571_i0 j ⊆ envelope_571_i0 := by decide +kernel
theorem pivot_mem_571_i0 : (4, 7) ∈ envelope_571_i0 := by decide +kernel
theorem children_work_571_i0 : ∀ j, Template HasSnaky 10 (childrenC_571_i0 j) (childrenD_571_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_2 7 (4, 7)).mono (by decide +kernel)
  · exact row_works_571_i1.mono (by decide +kernel)
theorem row_works_571_i0 : Template HasSnaky 11 required_571_i0 envelope_571_i0 := by
  refine compose HasSnaky 10 childrenC_571_i0 childrenD_571_i0 children_work_571_i0 (4, 7)
    required_571_i0 envelope_571_i0 pivot_mem_571_i0 child_required_sub_571_i0 child_envelope_sub_571_i0 ?_
  intro b hb
  exact common_sub_571_i0 (mem_commonEnvelope childrenD_571_i0 b hb)
def required_571_i3 : Finset Cell := ⟨(([(3, 6), (4, 4), (4, 5), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_571_i3 : Finset Cell := ⟨(([(3, 6), (3, 7), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 4), (5, 5), (5, 6), (5, 7), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (7, 5), (7, 6), (7, 7), (8, 5), (8, 6), (8, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_571_i3 : Fin 2 → Finset Cell := ![(placed21 5 (4, 3) required_5), (placed21 4 (3, 9) required_446)]
def childrenD_571_i3 : Fin 2 → Finset Cell := ![(placed21 5 (4, 3) envelope_5), (placed21 4 (3, 9) envelope_446)]
theorem common_sub_571_i3 : commonEnvelope childrenD_571_i3 ⊆ insert (4, 3) required_571_i3 := by decide +kernel
theorem child_required_sub_571_i3 : ∀ j, childrenC_571_i3 j ⊆ insert (4, 3) required_571_i3 := by decide +kernel
theorem child_envelope_sub_571_i3 : ∀ j, childrenD_571_i3 j ⊆ envelope_571_i3 := by decide +kernel
theorem pivot_mem_571_i3 : (4, 3) ∈ envelope_571_i3 := by decide +kernel
theorem children_work_571_i3 : ∀ j, Template HasSnaky 7 (childrenC_571_i3 j) (childrenD_571_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 5 (4, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_446 4 (3, 9)).mono (by decide +kernel)
theorem row_works_571_i3 : Template HasSnaky 8 required_571_i3 envelope_571_i3 := by
  refine compose HasSnaky 7 childrenC_571_i3 childrenD_571_i3 children_work_571_i3 (4, 3)
    required_571_i3 envelope_571_i3 pivot_mem_571_i3 child_required_sub_571_i3 child_envelope_sub_571_i3 ?_
  intro b hb
  exact common_sub_571_i3 (mem_commonEnvelope childrenD_571_i3 b hb)
def required_571_i2 : Finset Cell := ⟨(([(3, 3), (3, 4), (3, 6), (4, 4), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_571_i2 : Finset Cell := ⟨(([(3, 3), (3, 4), (3, 6), (3, 7), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 4), (5, 5), (5, 6), (5, 7), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (7, 5), (7, 6), (7, 7), (8, 5), (8, 6), (8, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_571_i2 : Fin 2 → Finset Cell := ![(placed21 7 (4, 7) required_0), required_571_i3]
def childrenD_571_i2 : Fin 2 → Finset Cell := ![(placed21 7 (4, 7) envelope_0), envelope_571_i3]
theorem common_sub_571_i2 : commonEnvelope childrenD_571_i2 ⊆ insert (4, 5) required_571_i2 := by decide +kernel
theorem child_required_sub_571_i2 : ∀ j, childrenC_571_i2 j ⊆ insert (4, 5) required_571_i2 := by decide +kernel
theorem child_envelope_sub_571_i2 : ∀ j, childrenD_571_i2 j ⊆ envelope_571_i2 := by decide +kernel
theorem pivot_mem_571_i2 : (4, 5) ∈ envelope_571_i2 := by decide +kernel
theorem children_work_571_i2 : ∀ j, Template HasSnaky 8 (childrenC_571_i2 j) (childrenD_571_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 7 (4, 7)).mono (by decide +kernel)
  · exact row_works_571_i3.mono (by decide +kernel)
theorem row_works_571_i2 : Template HasSnaky 9 required_571_i2 envelope_571_i2 := by
  refine compose HasSnaky 8 childrenC_571_i2 childrenD_571_i2 children_work_571_i2 (4, 5)
    required_571_i2 envelope_571_i2 pivot_mem_571_i2 child_required_sub_571_i2 child_envelope_sub_571_i2 ?_
  intro b hb
  exact common_sub_571_i2 (mem_commonEnvelope childrenD_571_i2 b hb)
def required_571_i5 : Finset Cell := ⟨(([(0, 3), (3, 3), (3, 4), (3, 6), (4, 4), (4, 5), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_571_i5 : Finset Cell := ⟨(([(0, 3), (1, 3), (2, 3), (3, 3), (3, 4), (3, 6), (3, 7), (4, 3), (4, 4), (4, 5), (4, 6), (5, 1), (5, 2), (5, 3), (5, 4), (6, 2), (6, 3), (6, 4), (7, 2), (7, 3), (7, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_571_i5 : Fin 2 → Finset Cell := ![(placed21 5 (4, 3) required_5), (placed21 0 (0, 1) required_283)]
def childrenD_571_i5 : Fin 2 → Finset Cell := ![(placed21 5 (4, 3) envelope_5), (placed21 0 (0, 1) envelope_283)]
theorem common_sub_571_i5 : commonEnvelope childrenD_571_i5 ⊆ insert (4, 3) required_571_i5 := by decide +kernel
theorem child_required_sub_571_i5 : ∀ j, childrenC_571_i5 j ⊆ insert (4, 3) required_571_i5 := by decide +kernel
theorem child_envelope_sub_571_i5 : ∀ j, childrenD_571_i5 j ⊆ envelope_571_i5 := by decide +kernel
theorem pivot_mem_571_i5 : (4, 3) ∈ envelope_571_i5 := by decide +kernel
theorem children_work_571_i5 : ∀ j, Template HasSnaky 6 (childrenC_571_i5 j) (childrenD_571_i5 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 5 (4, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_283 0 (0, 1)).mono (by decide +kernel)
theorem row_works_571_i5 : Template HasSnaky 7 required_571_i5 envelope_571_i5 := by
  refine compose HasSnaky 6 childrenC_571_i5 childrenD_571_i5 children_work_571_i5 (4, 3)
    required_571_i5 envelope_571_i5 pivot_mem_571_i5 child_required_sub_571_i5 child_envelope_sub_571_i5 ?_
  intro b hb
  exact common_sub_571_i5 (mem_commonEnvelope childrenD_571_i5 b hb)
def required_571_i4 : Finset Cell := ⟨(([(0, 3), (3, 3), (3, 4), (3, 6), (4, 4), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_571_i4 : Finset Cell := ⟨(([(0, 3), (1, 3), (2, 3), (3, 3), (3, 4), (3, 6), (3, 7), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 1), (5, 2), (5, 3), (5, 4), (6, 2), (6, 3), (6, 4), (7, 2), (7, 3), (7, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_571_i4 : Fin 2 → Finset Cell := ![(placed21 7 (4, 7) required_0), required_571_i5]
def childrenD_571_i4 : Fin 2 → Finset Cell := ![(placed21 7 (4, 7) envelope_0), envelope_571_i5]
theorem common_sub_571_i4 : commonEnvelope childrenD_571_i4 ⊆ insert (4, 5) required_571_i4 := by decide +kernel
theorem child_required_sub_571_i4 : ∀ j, childrenC_571_i4 j ⊆ insert (4, 5) required_571_i4 := by decide +kernel
theorem child_envelope_sub_571_i4 : ∀ j, childrenD_571_i4 j ⊆ envelope_571_i4 := by decide +kernel
theorem pivot_mem_571_i4 : (4, 5) ∈ envelope_571_i4 := by decide +kernel
theorem children_work_571_i4 : ∀ j, Template HasSnaky 7 (childrenC_571_i4 j) (childrenD_571_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 7 (4, 7)).mono (by decide +kernel)
  · exact row_works_571_i5.mono (by decide +kernel)
theorem row_works_571_i4 : Template HasSnaky 8 required_571_i4 envelope_571_i4 := by
  refine compose HasSnaky 7 childrenC_571_i4 childrenD_571_i4 children_work_571_i4 (4, 5)
    required_571_i4 envelope_571_i4 pivot_mem_571_i4 child_required_sub_571_i4 child_envelope_sub_571_i4 ?_
  intro b hb
  exact common_sub_571_i4 (mem_commonEnvelope childrenD_571_i4 b hb)
def required_571_i9 : Finset Cell := ⟨(([(2, 3), (3, 3), (3, 4), (4, 3), (4, 4), (4, 5), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_571_i9 : Finset Cell := ⟨(([(2, 3), (3, 3), (3, 4), (4, 3), (4, 4), (4, 5), (4, 6), (5, 2), (5, 3), (5, 4), (6, 3), (6, 4), (7, 3), (7, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_571_i9 : Fin 2 → Finset Cell := ![(placed21 3 (4, 6) required_5), (placed21 1 (2, 3) required_29)]
def childrenD_571_i9 : Fin 2 → Finset Cell := ![(placed21 3 (4, 6) envelope_5), (placed21 1 (2, 3) envelope_29)]
theorem common_sub_571_i9 : commonEnvelope childrenD_571_i9 ⊆ insert (5, 3) required_571_i9 := by decide +kernel
theorem child_required_sub_571_i9 : ∀ j, childrenC_571_i9 j ⊆ insert (5, 3) required_571_i9 := by decide +kernel
theorem child_envelope_sub_571_i9 : ∀ j, childrenD_571_i9 j ⊆ envelope_571_i9 := by decide +kernel
theorem pivot_mem_571_i9 : (5, 3) ∈ envelope_571_i9 := by decide +kernel
theorem children_work_571_i9 : ∀ j, Template HasSnaky 3 (childrenC_571_i9 j) (childrenD_571_i9 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 3 (4, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_29 1 (2, 3)).mono (by decide +kernel)
theorem row_works_571_i9 : Template HasSnaky 4 required_571_i9 envelope_571_i9 := by
  refine compose HasSnaky 3 childrenC_571_i9 childrenD_571_i9 children_work_571_i9 (5, 3)
    required_571_i9 envelope_571_i9 pivot_mem_571_i9 child_required_sub_571_i9 child_envelope_sub_571_i9 ?_
  intro b hb
  exact common_sub_571_i9 (mem_commonEnvelope childrenD_571_i9 b hb)
def required_571_i8 : Finset Cell := ⟨(([(2, 3), (3, 3), (3, 4), (3, 6), (4, 4), (4, 5), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_571_i8 : Finset Cell := ⟨(([(2, 3), (3, 3), (3, 4), (3, 6), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (8, 5), (8, 6), (8, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_571_i8 : Fin 3 → Finset Cell := ![(placed21 4 (4, 7) required_7), required_571_i9, (placed21 4 (3, 9) required_446)]
def childrenD_571_i8 : Fin 3 → Finset Cell := ![(placed21 4 (4, 7) envelope_7), envelope_571_i9, (placed21 4 (3, 9) envelope_446)]
theorem common_sub_571_i8 : commonEnvelope childrenD_571_i8 ⊆ insert (4, 3) required_571_i8 := by decide +kernel
theorem child_required_sub_571_i8 : ∀ j, childrenC_571_i8 j ⊆ insert (4, 3) required_571_i8 := by decide +kernel
theorem child_envelope_sub_571_i8 : ∀ j, childrenD_571_i8 j ⊆ envelope_571_i8 := by decide +kernel
theorem pivot_mem_571_i8 : (4, 3) ∈ envelope_571_i8 := by decide +kernel
theorem children_work_571_i8 : ∀ j, Template HasSnaky 7 (childrenC_571_i8 j) (childrenD_571_i8 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 4 (4, 7)).mono (by decide +kernel)
  · exact row_works_571_i9.mono (by decide +kernel)
  · exact (placed21_template row_works_446 4 (3, 9)).mono (by decide +kernel)
theorem row_works_571_i8 : Template HasSnaky 8 required_571_i8 envelope_571_i8 := by
  refine compose HasSnaky 7 childrenC_571_i8 childrenD_571_i8 children_work_571_i8 (4, 3)
    required_571_i8 envelope_571_i8 pivot_mem_571_i8 child_required_sub_571_i8 child_envelope_sub_571_i8 ?_
  intro b hb
  exact common_sub_571_i8 (mem_commonEnvelope childrenD_571_i8 b hb)
def required_571_i7 : Finset Cell := ⟨(([(2, 3), (3, 3), (3, 4), (3, 6), (4, 4), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_571_i7 : Finset Cell := ⟨(([(2, 3), (3, 3), (3, 4), (3, 6), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (8, 5), (8, 6), (8, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_571_i7 : Fin 2 → Finset Cell := ![(placed21 7 (4, 7) required_0), required_571_i8]
def childrenD_571_i7 : Fin 2 → Finset Cell := ![(placed21 7 (4, 7) envelope_0), envelope_571_i8]
theorem common_sub_571_i7 : commonEnvelope childrenD_571_i7 ⊆ insert (4, 5) required_571_i7 := by decide +kernel
theorem child_required_sub_571_i7 : ∀ j, childrenC_571_i7 j ⊆ insert (4, 5) required_571_i7 := by decide +kernel
theorem child_envelope_sub_571_i7 : ∀ j, childrenD_571_i7 j ⊆ envelope_571_i7 := by decide +kernel
theorem pivot_mem_571_i7 : (4, 5) ∈ envelope_571_i7 := by decide +kernel
theorem children_work_571_i7 : ∀ j, Template HasSnaky 8 (childrenC_571_i7 j) (childrenD_571_i7 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 7 (4, 7)).mono (by decide +kernel)
  · exact row_works_571_i8.mono (by decide +kernel)
theorem row_works_571_i7 : Template HasSnaky 9 required_571_i7 envelope_571_i7 := by
  refine compose HasSnaky 8 childrenC_571_i7 childrenD_571_i7 children_work_571_i7 (4, 5)
    required_571_i7 envelope_571_i7 pivot_mem_571_i7 child_required_sub_571_i7 child_envelope_sub_571_i7 ?_
  intro b hb
  exact common_sub_571_i7 (mem_commonEnvelope childrenD_571_i7 b hb)
def required_571_i6 : Finset Cell := ⟨(([(0, 3), (3, 3), (3, 4), (3, 6), (4, 4), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_571_i6 : Finset Cell := ⟨(([(0, 3), (1, 3), (2, 3), (3, 3), (3, 4), (3, 6), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (8, 5), (8, 6), (8, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_571_i6 : Fin 2 → Finset Cell := ![(placed21 0 (0, 3) required_1), required_571_i7]
def childrenD_571_i6 : Fin 2 → Finset Cell := ![(placed21 0 (0, 3) envelope_1), envelope_571_i7]
theorem common_sub_571_i6 : commonEnvelope childrenD_571_i6 ⊆ insert (2, 3) required_571_i6 := by decide +kernel
theorem child_required_sub_571_i6 : ∀ j, childrenC_571_i6 j ⊆ insert (2, 3) required_571_i6 := by decide +kernel
theorem child_envelope_sub_571_i6 : ∀ j, childrenD_571_i6 j ⊆ envelope_571_i6 := by decide +kernel
theorem pivot_mem_571_i6 : (2, 3) ∈ envelope_571_i6 := by decide +kernel
theorem children_work_571_i6 : ∀ j, Template HasSnaky 9 (childrenC_571_i6 j) (childrenD_571_i6 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_1 0 (0, 3)).mono (by decide +kernel)
  · exact row_works_571_i7.mono (by decide +kernel)
theorem row_works_571_i6 : Template HasSnaky 10 required_571_i6 envelope_571_i6 := by
  refine compose HasSnaky 9 childrenC_571_i6 childrenD_571_i6 children_work_571_i6 (2, 3)
    required_571_i6 envelope_571_i6 pivot_mem_571_i6 child_required_sub_571_i6 child_envelope_sub_571_i6 ?_
  intro b hb
  exact common_sub_571_i6 (mem_commonEnvelope childrenD_571_i6 b hb)
def required_571 : Finset Cell := ⟨(([(0, 3), (3, 3), (3, 4), (3, 6), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_571 : Finset Cell := ⟨(([(0, 3), (1, 3), (2, 3), (2, 7), (3, 3), (3, 4), (3, 6), (3, 7), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, 5), (8, 6), (8, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_571 : Fin 7 → Finset Cell := ![(placed21 4 (3, 7) required_250), (placed21 0 (0, 1) required_569), required_571_i0, required_571_i2, required_571_i4, required_570, required_571_i6]
def childrenD_571 : Fin 7 → Finset Cell := ![(placed21 4 (3, 7) envelope_250), (placed21 0 (0, 1) envelope_569), envelope_571_i0, envelope_571_i2, envelope_571_i4, envelope_570, envelope_571_i6]
theorem common_sub_571 : commonEnvelope childrenD_571 ⊆ insert (4, 4) required_571 := by decide +kernel
theorem child_required_sub_571 : ∀ j, childrenC_571 j ⊆ insert (4, 4) required_571 := by decide +kernel
theorem child_envelope_sub_571 : ∀ j, childrenD_571 j ⊆ envelope_571 := by decide +kernel
theorem pivot_mem_571 : (4, 4) ∈ envelope_571 := by decide +kernel
theorem children_work_571 : ∀ j, Template HasSnaky 11 (childrenC_571 j) (childrenD_571 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_250 4 (3, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_569 0 (0, 1)).mono (by decide +kernel)
  · exact row_works_571_i0.mono (by decide +kernel)
  · exact row_works_571_i2.mono (by decide +kernel)
  · exact row_works_571_i4.mono (by decide +kernel)
  · exact row_works_570.mono (by decide +kernel)
  · exact row_works_571_i6.mono (by decide +kernel)
theorem row_works_571 : Template HasSnaky 12 required_571 envelope_571 := by
  refine compose HasSnaky 11 childrenC_571 childrenD_571 children_work_571 (4, 4)
    required_571 envelope_571 pivot_mem_571 child_required_sub_571 child_envelope_sub_571 ?_
  intro b hb
  exact common_sub_571 (mem_commonEnvelope childrenD_571 b hb)
def required_587 : Finset Cell := ⟨(([(2, 3), (2, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_587 : Finset Cell := ⟨(([(0, 4), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 0), (3, 1), (3, 2), (3, 3), (3, 5), (3, 6), (3, 7), (3, 8), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_587 : Fin 6 → Finset Cell := ![(placed21 0 (1, 1) required_12), (placed21 2 (3, 1) required_12), (placed21 4 (1, 7) required_12), (placed21 6 (3, 7) required_12), (placed21 1 (0, 2) required_586), (placed21 3 (0, 6) required_586)]
def childrenD_587 : Fin 6 → Finset Cell := ![(placed21 0 (1, 1) envelope_12), (placed21 2 (3, 1) envelope_12), (placed21 4 (1, 7) envelope_12), (placed21 6 (3, 7) envelope_12), (placed21 1 (0, 2) envelope_586), (placed21 3 (0, 6) envelope_586)]
theorem common_sub_587 : commonEnvelope childrenD_587 ⊆ insert (2, 5) required_587 := by decide +kernel
theorem child_required_sub_587 : ∀ j, childrenC_587 j ⊆ insert (2, 5) required_587 := by decide +kernel
theorem child_envelope_sub_587 : ∀ j, childrenD_587 j ⊆ envelope_587 := by decide +kernel
theorem pivot_mem_587 : (2, 5) ∈ envelope_587 := by decide +kernel
theorem children_work_587 : ∀ j, Template HasSnaky 11 (childrenC_587 j) (childrenD_587 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_12 0 (1, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_12 2 (3, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_12 4 (1, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_12 6 (3, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_586 1 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_586 3 (0, 6)).mono (by decide +kernel)
theorem row_works_587 : Template HasSnaky 12 required_587 envelope_587 := by
  refine compose HasSnaky 11 childrenC_587 childrenD_587 children_work_587 (2, 5)
    required_587 envelope_587 pivot_mem_587 child_required_sub_587 child_envelope_sub_587 ?_
  intro b hb
  exact common_sub_587 (mem_commonEnvelope childrenD_587 b hb)
def required_588 : Finset Cell := ⟨(([(1, 2), (1, 3), (2, 3), (4, 1), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_588 : Finset Cell := ⟨(([(0, 2), (1, 2), (1, 3), (2, 2), (2, 3), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 0), (5, 1), (5, 3), (5, 4), (5, 5), (5, 6), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_588 : Fin 4 → Finset Cell := ![(placed21 1 (0, 2) required_42), (placed21 3 (0, 3) required_289), (placed21 0 (1, 0) required_291), (placed21 1 (2, 0) required_586)]
def childrenD_588 : Fin 4 → Finset Cell := ![(placed21 1 (0, 2) envelope_42), (placed21 3 (0, 3) envelope_289), (placed21 0 (1, 0) envelope_291), (placed21 1 (2, 0) envelope_586)]
theorem common_sub_588 : commonEnvelope childrenD_588 ⊆ insert (4, 3) required_588 := by decide +kernel
theorem child_required_sub_588 : ∀ j, childrenC_588 j ⊆ insert (4, 3) required_588 := by decide +kernel
theorem child_envelope_sub_588 : ∀ j, childrenD_588 j ⊆ envelope_588 := by decide +kernel
theorem pivot_mem_588 : (4, 3) ∈ envelope_588 := by decide +kernel
theorem children_work_588 : ∀ j, Template HasSnaky 11 (childrenC_588 j) (childrenD_588 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_42 1 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_289 3 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_291 0 (1, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_586 1 (2, 0)).mono (by decide +kernel)
theorem row_works_588 : Template HasSnaky 12 required_588 envelope_588 := by
  refine compose HasSnaky 11 childrenC_588 childrenD_588 children_work_588 (4, 3)
    required_588 envelope_588 pivot_mem_588 child_required_sub_588 child_envelope_sub_588 ?_
  intro b hb
  exact common_sub_588 (mem_commonEnvelope childrenD_588 b hb)
def height_551_i7 : ℕ := 4
def childrenH_551_i7 : Fin 2 → ℕ := ![height_6, height_78]
theorem height_exact_551_i7 : height_551_i7 = 1 + Finset.univ.sup childrenH_551_i7 := by decide +kernel
theorem required_origin_551_i7 : ∀ x ∈ required_551_i7,
    (∃ j, x ∈ childrenC_551_i7 j) ∨ ∀ j, x ∈ childrenD_551_i7 j := by decide +kernel
theorem required_exact_551_i7 : required_551_i7 =
    ((Finset.univ.biUnion childrenC_551_i7) ∪ commonEnvelope childrenD_551_i7).erase (3, 3) := by
  exact required_eq_combination childrenC_551_i7 childrenD_551_i7 (3, 3) required_551_i7
    (by decide +kernel) child_required_sub_551_i7 common_sub_551_i7 required_origin_551_i7
theorem envelope_origin_551_i7 : ∀ x ∈ envelope_551_i7,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_551_i7 j := by decide +kernel
theorem envelope_exact_551_i7 : envelope_551_i7 =
    insert (3, 3) (Finset.univ.biUnion childrenD_551_i7) := by
  exact envelope_eq_combination childrenD_551_i7 (3, 3) envelope_551_i7
    pivot_mem_551_i7 child_envelope_sub_551_i7 envelope_origin_551_i7
def checked_551_i7 : CheckedCard where
  required := required_551_i7
  envelope := envelope_551_i7
  height := height_551_i7
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_551_i7
def height_551_i8 : ℕ := 3
def childrenH_551_i8 : Fin 2 → ℕ := ![height_4, height_6]
theorem height_exact_551_i8 : height_551_i8 = 1 + Finset.univ.sup childrenH_551_i8 := by decide +kernel
theorem required_origin_551_i8 : ∀ x ∈ required_551_i8,
    (∃ j, x ∈ childrenC_551_i8 j) ∨ ∀ j, x ∈ childrenD_551_i8 j := by decide +kernel
theorem required_exact_551_i8 : required_551_i8 =
    ((Finset.univ.biUnion childrenC_551_i8) ∪ commonEnvelope childrenD_551_i8).erase (3, 3) := by
  exact required_eq_combination childrenC_551_i8 childrenD_551_i8 (3, 3) required_551_i8
    (by decide +kernel) child_required_sub_551_i8 common_sub_551_i8 required_origin_551_i8
theorem envelope_origin_551_i8 : ∀ x ∈ envelope_551_i8,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_551_i8 j := by decide +kernel
theorem envelope_exact_551_i8 : envelope_551_i8 =
    insert (3, 3) (Finset.univ.biUnion childrenD_551_i8) := by
  exact envelope_eq_combination childrenD_551_i8 (3, 3) envelope_551_i8
    pivot_mem_551_i8 child_envelope_sub_551_i8 envelope_origin_551_i8
def checked_551_i8 : CheckedCard where
  required := required_551_i8
  envelope := envelope_551_i8
  height := height_551_i8
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_551_i8
def height_551_i6 : ℕ := 5
def childrenH_551_i6 : Fin 3 → ℕ := ![height_25, height_551_i7, height_551_i8]
theorem height_exact_551_i6 : height_551_i6 = 1 + Finset.univ.sup childrenH_551_i6 := by decide +kernel
theorem required_origin_551_i6 : ∀ x ∈ required_551_i6,
    (∃ j, x ∈ childrenC_551_i6 j) ∨ ∀ j, x ∈ childrenD_551_i6 j := by decide +kernel
theorem required_exact_551_i6 : required_551_i6 =
    ((Finset.univ.biUnion childrenC_551_i6) ∪ commonEnvelope childrenD_551_i6).erase (4, 3) := by
  exact required_eq_combination childrenC_551_i6 childrenD_551_i6 (4, 3) required_551_i6
    (by decide +kernel) child_required_sub_551_i6 common_sub_551_i6 required_origin_551_i6
theorem envelope_origin_551_i6 : ∀ x ∈ envelope_551_i6,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_551_i6 j := by decide +kernel
theorem envelope_exact_551_i6 : envelope_551_i6 =
    insert (4, 3) (Finset.univ.biUnion childrenD_551_i6) := by
  exact envelope_eq_combination childrenD_551_i6 (4, 3) envelope_551_i6
    pivot_mem_551_i6 child_envelope_sub_551_i6 envelope_origin_551_i6
def checked_551_i6 : CheckedCard where
  required := required_551_i6
  envelope := envelope_551_i6
  height := height_551_i6
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_551_i6
def height_551_i5 : ℕ := 6
def childrenH_551_i5 : Fin 2 → ℕ := ![height_5, height_551_i6]
theorem height_exact_551_i5 : height_551_i5 = 1 + Finset.univ.sup childrenH_551_i5 := by decide +kernel
theorem required_origin_551_i5 : ∀ x ∈ required_551_i5,
    (∃ j, x ∈ childrenC_551_i5 j) ∨ ∀ j, x ∈ childrenD_551_i5 j := by decide +kernel
theorem required_exact_551_i5 : required_551_i5 =
    ((Finset.univ.biUnion childrenC_551_i5) ∪ commonEnvelope childrenD_551_i5).erase (7, 3) := by
  exact required_eq_combination childrenC_551_i5 childrenD_551_i5 (7, 3) required_551_i5
    (by decide +kernel) child_required_sub_551_i5 common_sub_551_i5 required_origin_551_i5
theorem envelope_origin_551_i5 : ∀ x ∈ envelope_551_i5,
    x = (7, 3) ∨ ∃ j, x ∈ childrenD_551_i5 j := by decide +kernel
theorem envelope_exact_551_i5 : envelope_551_i5 =
    insert (7, 3) (Finset.univ.biUnion childrenD_551_i5) := by
  exact envelope_eq_combination childrenD_551_i5 (7, 3) envelope_551_i5
    pivot_mem_551_i5 child_envelope_sub_551_i5 envelope_origin_551_i5
def checked_551_i5 : CheckedCard where
  required := required_551_i5
  envelope := envelope_551_i5
  height := height_551_i5
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_551_i5
def height_551_i4 : ℕ := 7
def childrenH_551_i4 : Fin 2 → ℕ := ![height_5, height_551_i5]
theorem height_exact_551_i4 : height_551_i4 = 1 + Finset.univ.sup childrenH_551_i4 := by decide +kernel
theorem required_origin_551_i4 : ∀ x ∈ required_551_i4,
    (∃ j, x ∈ childrenC_551_i4 j) ∨ ∀ j, x ∈ childrenD_551_i4 j := by decide +kernel
theorem required_exact_551_i4 : required_551_i4 =
    ((Finset.univ.biUnion childrenC_551_i4) ∪ commonEnvelope childrenD_551_i4).erase (5, 3) := by
  exact required_eq_combination childrenC_551_i4 childrenD_551_i4 (5, 3) required_551_i4
    (by decide +kernel) child_required_sub_551_i4 common_sub_551_i4 required_origin_551_i4
theorem envelope_origin_551_i4 : ∀ x ∈ envelope_551_i4,
    x = (5, 3) ∨ ∃ j, x ∈ childrenD_551_i4 j := by decide +kernel
theorem envelope_exact_551_i4 : envelope_551_i4 =
    insert (5, 3) (Finset.univ.biUnion childrenD_551_i4) := by
  exact envelope_eq_combination childrenD_551_i4 (5, 3) envelope_551_i4
    pivot_mem_551_i4 child_envelope_sub_551_i4 envelope_origin_551_i4
def checked_551_i4 : CheckedCard where
  required := required_551_i4
  envelope := envelope_551_i4
  height := height_551_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_551_i4
def height_551_i3 : ℕ := 8
def childrenH_551_i3 : Fin 2 → ℕ := ![height_1, height_551_i4]
theorem height_exact_551_i3 : height_551_i3 = 1 + Finset.univ.sup childrenH_551_i3 := by decide +kernel
theorem required_origin_551_i3 : ∀ x ∈ required_551_i3,
    (∃ j, x ∈ childrenC_551_i3 j) ∨ ∀ j, x ∈ childrenD_551_i3 j := by decide +kernel
theorem required_exact_551_i3 : required_551_i3 =
    ((Finset.univ.biUnion childrenC_551_i3) ∪ commonEnvelope childrenD_551_i3).erase (2, 5) := by
  exact required_eq_combination childrenC_551_i3 childrenD_551_i3 (2, 5) required_551_i3
    (by decide +kernel) child_required_sub_551_i3 common_sub_551_i3 required_origin_551_i3
theorem envelope_origin_551_i3 : ∀ x ∈ envelope_551_i3,
    x = (2, 5) ∨ ∃ j, x ∈ childrenD_551_i3 j := by decide +kernel
theorem envelope_exact_551_i3 : envelope_551_i3 =
    insert (2, 5) (Finset.univ.biUnion childrenD_551_i3) := by
  exact envelope_eq_combination childrenD_551_i3 (2, 5) envelope_551_i3
    pivot_mem_551_i3 child_envelope_sub_551_i3 envelope_origin_551_i3
def checked_551_i3 : CheckedCard where
  required := required_551_i3
  envelope := envelope_551_i3
  height := height_551_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_551_i3
def height_551_i2 : ℕ := 9
def childrenH_551_i2 : Fin 2 → ℕ := ![height_5, height_551_i3]
theorem height_exact_551_i2 : height_551_i2 = 1 + Finset.univ.sup childrenH_551_i2 := by decide +kernel
theorem required_origin_551_i2 : ∀ x ∈ required_551_i2,
    (∃ j, x ∈ childrenC_551_i2 j) ∨ ∀ j, x ∈ childrenD_551_i2 j := by decide +kernel
theorem required_exact_551_i2 : required_551_i2 =
    ((Finset.univ.biUnion childrenC_551_i2) ∪ commonEnvelope childrenD_551_i2).erase (5, 6) := by
  exact required_eq_combination childrenC_551_i2 childrenD_551_i2 (5, 6) required_551_i2
    (by decide +kernel) child_required_sub_551_i2 common_sub_551_i2 required_origin_551_i2
theorem envelope_origin_551_i2 : ∀ x ∈ envelope_551_i2,
    x = (5, 6) ∨ ∃ j, x ∈ childrenD_551_i2 j := by decide +kernel
theorem envelope_exact_551_i2 : envelope_551_i2 =
    insert (5, 6) (Finset.univ.biUnion childrenD_551_i2) := by
  exact envelope_eq_combination childrenD_551_i2 (5, 6) envelope_551_i2
    pivot_mem_551_i2 child_envelope_sub_551_i2 envelope_origin_551_i2
def checked_551_i2 : CheckedCard where
  required := required_551_i2
  envelope := envelope_551_i2
  height := height_551_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_551_i2
def height_551_i1 : ℕ := 10
def childrenH_551_i1 : Fin 4 → ℕ := ![height_19, height_84, height_314, height_551_i2]
theorem height_exact_551_i1 : height_551_i1 = 1 + Finset.univ.sup childrenH_551_i1 := by decide +kernel
theorem required_origin_551_i1 : ∀ x ∈ required_551_i1,
    (∃ j, x ∈ childrenC_551_i1 j) ∨ ∀ j, x ∈ childrenD_551_i1 j := by decide +kernel
theorem required_exact_551_i1 : required_551_i1 =
    ((Finset.univ.biUnion childrenC_551_i1) ∪ commonEnvelope childrenD_551_i1).erase (6, 6) := by
  exact required_eq_combination childrenC_551_i1 childrenD_551_i1 (6, 6) required_551_i1
    (by decide +kernel) child_required_sub_551_i1 common_sub_551_i1 required_origin_551_i1
theorem envelope_origin_551_i1 : ∀ x ∈ envelope_551_i1,
    x = (6, 6) ∨ ∃ j, x ∈ childrenD_551_i1 j := by decide +kernel
theorem envelope_exact_551_i1 : envelope_551_i1 =
    insert (6, 6) (Finset.univ.biUnion childrenD_551_i1) := by
  exact envelope_eq_combination childrenD_551_i1 (6, 6) envelope_551_i1
    pivot_mem_551_i1 child_envelope_sub_551_i1 envelope_origin_551_i1
def checked_551_i1 : CheckedCard where
  required := required_551_i1
  envelope := envelope_551_i1
  height := height_551_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_551_i1
def height_551_i0 : ℕ := 11
def childrenH_551_i0 : Fin 4 → ℕ := ![height_10, height_44, height_63, height_551_i1]
theorem height_exact_551_i0 : height_551_i0 = 1 + Finset.univ.sup childrenH_551_i0 := by decide +kernel
theorem required_origin_551_i0 : ∀ x ∈ required_551_i0,
    (∃ j, x ∈ childrenC_551_i0 j) ∨ ∀ j, x ∈ childrenD_551_i0 j := by decide +kernel
theorem required_exact_551_i0 : required_551_i0 =
    ((Finset.univ.biUnion childrenC_551_i0) ∪ commonEnvelope childrenD_551_i0).erase (6, 3) := by
  exact required_eq_combination childrenC_551_i0 childrenD_551_i0 (6, 3) required_551_i0
    (by decide +kernel) child_required_sub_551_i0 common_sub_551_i0 required_origin_551_i0
theorem envelope_origin_551_i0 : ∀ x ∈ envelope_551_i0,
    x = (6, 3) ∨ ∃ j, x ∈ childrenD_551_i0 j := by decide +kernel
theorem envelope_exact_551_i0 : envelope_551_i0 =
    insert (6, 3) (Finset.univ.biUnion childrenD_551_i0) := by
  exact envelope_eq_combination childrenD_551_i0 (6, 3) envelope_551_i0
    pivot_mem_551_i0 child_envelope_sub_551_i0 envelope_origin_551_i0
def checked_551_i0 : CheckedCard where
  required := required_551_i0
  envelope := envelope_551_i0
  height := height_551_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_551_i0
def height_551 : ℕ := 12
def childrenH_551 : Fin 3 → ℕ := ![height_52, height_523, height_551_i0]
theorem height_exact_551 : height_551 = 1 + Finset.univ.sup childrenH_551 := by decide +kernel
theorem required_origin_551 : ∀ x ∈ required_551,
    (∃ j, x ∈ childrenC_551 j) ∨ ∀ j, x ∈ childrenD_551 j := by decide +kernel
theorem required_exact_551 : required_551 =
    ((Finset.univ.biUnion childrenC_551) ∪ commonEnvelope childrenD_551).erase (6, 4) := by
  exact required_eq_combination childrenC_551 childrenD_551 (6, 4) required_551
    (by decide +kernel) child_required_sub_551 common_sub_551 required_origin_551
theorem envelope_origin_551 : ∀ x ∈ envelope_551,
    x = (6, 4) ∨ ∃ j, x ∈ childrenD_551 j := by decide +kernel
theorem envelope_exact_551 : envelope_551 =
    insert (6, 4) (Finset.univ.biUnion childrenD_551) := by
  exact envelope_eq_combination childrenD_551 (6, 4) envelope_551
    pivot_mem_551 child_envelope_sub_551 envelope_origin_551
def checked_551 : CheckedCard where
  required := required_551
  envelope := envelope_551
  height := height_551
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_551
def height_571_i1 : ℕ := 10
def childrenH_571_i1 : Fin 4 → ℕ := ![height_287, height_288, height_345, height_457]
theorem height_exact_571_i1 : height_571_i1 = 1 + Finset.univ.sup childrenH_571_i1 := by decide +kernel
theorem required_origin_571_i1 : ∀ x ∈ required_571_i1,
    (∃ j, x ∈ childrenC_571_i1 j) ∨ ∀ j, x ∈ childrenD_571_i1 j := by decide +kernel
theorem required_exact_571_i1 : required_571_i1 =
    ((Finset.univ.biUnion childrenC_571_i1) ∪ commonEnvelope childrenD_571_i1).erase (5, 6) := by
  exact required_eq_combination childrenC_571_i1 childrenD_571_i1 (5, 6) required_571_i1
    (by decide +kernel) child_required_sub_571_i1 common_sub_571_i1 required_origin_571_i1
theorem envelope_origin_571_i1 : ∀ x ∈ envelope_571_i1,
    x = (5, 6) ∨ ∃ j, x ∈ childrenD_571_i1 j := by decide +kernel
theorem envelope_exact_571_i1 : envelope_571_i1 =
    insert (5, 6) (Finset.univ.biUnion childrenD_571_i1) := by
  exact envelope_eq_combination childrenD_571_i1 (5, 6) envelope_571_i1
    pivot_mem_571_i1 child_envelope_sub_571_i1 envelope_origin_571_i1
def checked_571_i1 : CheckedCard where
  required := required_571_i1
  envelope := envelope_571_i1
  height := height_571_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_571_i1
def height_571_i0 : ℕ := 11
def childrenH_571_i0 : Fin 2 → ℕ := ![height_2, height_571_i1]
theorem height_exact_571_i0 : height_571_i0 = 1 + Finset.univ.sup childrenH_571_i0 := by decide +kernel
theorem required_origin_571_i0 : ∀ x ∈ required_571_i0,
    (∃ j, x ∈ childrenC_571_i0 j) ∨ ∀ j, x ∈ childrenD_571_i0 j := by decide +kernel
theorem required_exact_571_i0 : required_571_i0 =
    ((Finset.univ.biUnion childrenC_571_i0) ∪ commonEnvelope childrenD_571_i0).erase (4, 7) := by
  exact required_eq_combination childrenC_571_i0 childrenD_571_i0 (4, 7) required_571_i0
    (by decide +kernel) child_required_sub_571_i0 common_sub_571_i0 required_origin_571_i0
theorem envelope_origin_571_i0 : ∀ x ∈ envelope_571_i0,
    x = (4, 7) ∨ ∃ j, x ∈ childrenD_571_i0 j := by decide +kernel
theorem envelope_exact_571_i0 : envelope_571_i0 =
    insert (4, 7) (Finset.univ.biUnion childrenD_571_i0) := by
  exact envelope_eq_combination childrenD_571_i0 (4, 7) envelope_571_i0
    pivot_mem_571_i0 child_envelope_sub_571_i0 envelope_origin_571_i0
def checked_571_i0 : CheckedCard where
  required := required_571_i0
  envelope := envelope_571_i0
  height := height_571_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_571_i0
def height_571_i3 : ℕ := 8
def childrenH_571_i3 : Fin 2 → ℕ := ![height_5, height_446]
theorem height_exact_571_i3 : height_571_i3 = 1 + Finset.univ.sup childrenH_571_i3 := by decide +kernel
theorem required_origin_571_i3 : ∀ x ∈ required_571_i3,
    (∃ j, x ∈ childrenC_571_i3 j) ∨ ∀ j, x ∈ childrenD_571_i3 j := by decide +kernel
theorem required_exact_571_i3 : required_571_i3 =
    ((Finset.univ.biUnion childrenC_571_i3) ∪ commonEnvelope childrenD_571_i3).erase (4, 3) := by
  exact required_eq_combination childrenC_571_i3 childrenD_571_i3 (4, 3) required_571_i3
    (by decide +kernel) child_required_sub_571_i3 common_sub_571_i3 required_origin_571_i3
theorem envelope_origin_571_i3 : ∀ x ∈ envelope_571_i3,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_571_i3 j := by decide +kernel
theorem envelope_exact_571_i3 : envelope_571_i3 =
    insert (4, 3) (Finset.univ.biUnion childrenD_571_i3) := by
  exact envelope_eq_combination childrenD_571_i3 (4, 3) envelope_571_i3
    pivot_mem_571_i3 child_envelope_sub_571_i3 envelope_origin_571_i3
def checked_571_i3 : CheckedCard where
  required := required_571_i3
  envelope := envelope_571_i3
  height := height_571_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_571_i3
def height_571_i2 : ℕ := 9
def childrenH_571_i2 : Fin 2 → ℕ := ![height_0, height_571_i3]
theorem height_exact_571_i2 : height_571_i2 = 1 + Finset.univ.sup childrenH_571_i2 := by decide +kernel
theorem required_origin_571_i2 : ∀ x ∈ required_571_i2,
    (∃ j, x ∈ childrenC_571_i2 j) ∨ ∀ j, x ∈ childrenD_571_i2 j := by decide +kernel
theorem required_exact_571_i2 : required_571_i2 =
    ((Finset.univ.biUnion childrenC_571_i2) ∪ commonEnvelope childrenD_571_i2).erase (4, 5) := by
  exact required_eq_combination childrenC_571_i2 childrenD_571_i2 (4, 5) required_571_i2
    (by decide +kernel) child_required_sub_571_i2 common_sub_571_i2 required_origin_571_i2
theorem envelope_origin_571_i2 : ∀ x ∈ envelope_571_i2,
    x = (4, 5) ∨ ∃ j, x ∈ childrenD_571_i2 j := by decide +kernel
theorem envelope_exact_571_i2 : envelope_571_i2 =
    insert (4, 5) (Finset.univ.biUnion childrenD_571_i2) := by
  exact envelope_eq_combination childrenD_571_i2 (4, 5) envelope_571_i2
    pivot_mem_571_i2 child_envelope_sub_571_i2 envelope_origin_571_i2
def checked_571_i2 : CheckedCard where
  required := required_571_i2
  envelope := envelope_571_i2
  height := height_571_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_571_i2
def height_571_i5 : ℕ := 7
def childrenH_571_i5 : Fin 2 → ℕ := ![height_5, height_283]
theorem height_exact_571_i5 : height_571_i5 = 1 + Finset.univ.sup childrenH_571_i5 := by decide +kernel
theorem required_origin_571_i5 : ∀ x ∈ required_571_i5,
    (∃ j, x ∈ childrenC_571_i5 j) ∨ ∀ j, x ∈ childrenD_571_i5 j := by decide +kernel
theorem required_exact_571_i5 : required_571_i5 =
    ((Finset.univ.biUnion childrenC_571_i5) ∪ commonEnvelope childrenD_571_i5).erase (4, 3) := by
  exact required_eq_combination childrenC_571_i5 childrenD_571_i5 (4, 3) required_571_i5
    (by decide +kernel) child_required_sub_571_i5 common_sub_571_i5 required_origin_571_i5
theorem envelope_origin_571_i5 : ∀ x ∈ envelope_571_i5,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_571_i5 j := by decide +kernel
theorem envelope_exact_571_i5 : envelope_571_i5 =
    insert (4, 3) (Finset.univ.biUnion childrenD_571_i5) := by
  exact envelope_eq_combination childrenD_571_i5 (4, 3) envelope_571_i5
    pivot_mem_571_i5 child_envelope_sub_571_i5 envelope_origin_571_i5
def checked_571_i5 : CheckedCard where
  required := required_571_i5
  envelope := envelope_571_i5
  height := height_571_i5
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_571_i5
def height_571_i4 : ℕ := 8
def childrenH_571_i4 : Fin 2 → ℕ := ![height_0, height_571_i5]
theorem height_exact_571_i4 : height_571_i4 = 1 + Finset.univ.sup childrenH_571_i4 := by decide +kernel
theorem required_origin_571_i4 : ∀ x ∈ required_571_i4,
    (∃ j, x ∈ childrenC_571_i4 j) ∨ ∀ j, x ∈ childrenD_571_i4 j := by decide +kernel
theorem required_exact_571_i4 : required_571_i4 =
    ((Finset.univ.biUnion childrenC_571_i4) ∪ commonEnvelope childrenD_571_i4).erase (4, 5) := by
  exact required_eq_combination childrenC_571_i4 childrenD_571_i4 (4, 5) required_571_i4
    (by decide +kernel) child_required_sub_571_i4 common_sub_571_i4 required_origin_571_i4
theorem envelope_origin_571_i4 : ∀ x ∈ envelope_571_i4,
    x = (4, 5) ∨ ∃ j, x ∈ childrenD_571_i4 j := by decide +kernel
theorem envelope_exact_571_i4 : envelope_571_i4 =
    insert (4, 5) (Finset.univ.biUnion childrenD_571_i4) := by
  exact envelope_eq_combination childrenD_571_i4 (4, 5) envelope_571_i4
    pivot_mem_571_i4 child_envelope_sub_571_i4 envelope_origin_571_i4
def checked_571_i4 : CheckedCard where
  required := required_571_i4
  envelope := envelope_571_i4
  height := height_571_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_571_i4
def height_571_i9 : ℕ := 4
def childrenH_571_i9 : Fin 2 → ℕ := ![height_5, height_29]
theorem height_exact_571_i9 : height_571_i9 = 1 + Finset.univ.sup childrenH_571_i9 := by decide +kernel
theorem required_origin_571_i9 : ∀ x ∈ required_571_i9,
    (∃ j, x ∈ childrenC_571_i9 j) ∨ ∀ j, x ∈ childrenD_571_i9 j := by decide +kernel
theorem required_exact_571_i9 : required_571_i9 =
    ((Finset.univ.biUnion childrenC_571_i9) ∪ commonEnvelope childrenD_571_i9).erase (5, 3) := by
  exact required_eq_combination childrenC_571_i9 childrenD_571_i9 (5, 3) required_571_i9
    (by decide +kernel) child_required_sub_571_i9 common_sub_571_i9 required_origin_571_i9
theorem envelope_origin_571_i9 : ∀ x ∈ envelope_571_i9,
    x = (5, 3) ∨ ∃ j, x ∈ childrenD_571_i9 j := by decide +kernel
theorem envelope_exact_571_i9 : envelope_571_i9 =
    insert (5, 3) (Finset.univ.biUnion childrenD_571_i9) := by
  exact envelope_eq_combination childrenD_571_i9 (5, 3) envelope_571_i9
    pivot_mem_571_i9 child_envelope_sub_571_i9 envelope_origin_571_i9
def checked_571_i9 : CheckedCard where
  required := required_571_i9
  envelope := envelope_571_i9
  height := height_571_i9
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_571_i9
def height_571_i8 : ℕ := 8
def childrenH_571_i8 : Fin 3 → ℕ := ![height_7, height_571_i9, height_446]
theorem height_exact_571_i8 : height_571_i8 = 1 + Finset.univ.sup childrenH_571_i8 := by decide +kernel
theorem required_origin_571_i8 : ∀ x ∈ required_571_i8,
    (∃ j, x ∈ childrenC_571_i8 j) ∨ ∀ j, x ∈ childrenD_571_i8 j := by decide +kernel
theorem required_exact_571_i8 : required_571_i8 =
    ((Finset.univ.biUnion childrenC_571_i8) ∪ commonEnvelope childrenD_571_i8).erase (4, 3) := by
  exact required_eq_combination childrenC_571_i8 childrenD_571_i8 (4, 3) required_571_i8
    (by decide +kernel) child_required_sub_571_i8 common_sub_571_i8 required_origin_571_i8
theorem envelope_origin_571_i8 : ∀ x ∈ envelope_571_i8,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_571_i8 j := by decide +kernel
theorem envelope_exact_571_i8 : envelope_571_i8 =
    insert (4, 3) (Finset.univ.biUnion childrenD_571_i8) := by
  exact envelope_eq_combination childrenD_571_i8 (4, 3) envelope_571_i8
    pivot_mem_571_i8 child_envelope_sub_571_i8 envelope_origin_571_i8
def checked_571_i8 : CheckedCard where
  required := required_571_i8
  envelope := envelope_571_i8
  height := height_571_i8
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_571_i8
def height_571_i7 : ℕ := 9
def childrenH_571_i7 : Fin 2 → ℕ := ![height_0, height_571_i8]
theorem height_exact_571_i7 : height_571_i7 = 1 + Finset.univ.sup childrenH_571_i7 := by decide +kernel
theorem required_origin_571_i7 : ∀ x ∈ required_571_i7,
    (∃ j, x ∈ childrenC_571_i7 j) ∨ ∀ j, x ∈ childrenD_571_i7 j := by decide +kernel
theorem required_exact_571_i7 : required_571_i7 =
    ((Finset.univ.biUnion childrenC_571_i7) ∪ commonEnvelope childrenD_571_i7).erase (4, 5) := by
  exact required_eq_combination childrenC_571_i7 childrenD_571_i7 (4, 5) required_571_i7
    (by decide +kernel) child_required_sub_571_i7 common_sub_571_i7 required_origin_571_i7
theorem envelope_origin_571_i7 : ∀ x ∈ envelope_571_i7,
    x = (4, 5) ∨ ∃ j, x ∈ childrenD_571_i7 j := by decide +kernel
theorem envelope_exact_571_i7 : envelope_571_i7 =
    insert (4, 5) (Finset.univ.biUnion childrenD_571_i7) := by
  exact envelope_eq_combination childrenD_571_i7 (4, 5) envelope_571_i7
    pivot_mem_571_i7 child_envelope_sub_571_i7 envelope_origin_571_i7
def checked_571_i7 : CheckedCard where
  required := required_571_i7
  envelope := envelope_571_i7
  height := height_571_i7
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_571_i7
def height_571_i6 : ℕ := 10
def childrenH_571_i6 : Fin 2 → ℕ := ![height_1, height_571_i7]
theorem height_exact_571_i6 : height_571_i6 = 1 + Finset.univ.sup childrenH_571_i6 := by decide +kernel
theorem required_origin_571_i6 : ∀ x ∈ required_571_i6,
    (∃ j, x ∈ childrenC_571_i6 j) ∨ ∀ j, x ∈ childrenD_571_i6 j := by decide +kernel
theorem required_exact_571_i6 : required_571_i6 =
    ((Finset.univ.biUnion childrenC_571_i6) ∪ commonEnvelope childrenD_571_i6).erase (2, 3) := by
  exact required_eq_combination childrenC_571_i6 childrenD_571_i6 (2, 3) required_571_i6
    (by decide +kernel) child_required_sub_571_i6 common_sub_571_i6 required_origin_571_i6
theorem envelope_origin_571_i6 : ∀ x ∈ envelope_571_i6,
    x = (2, 3) ∨ ∃ j, x ∈ childrenD_571_i6 j := by decide +kernel
theorem envelope_exact_571_i6 : envelope_571_i6 =
    insert (2, 3) (Finset.univ.biUnion childrenD_571_i6) := by
  exact envelope_eq_combination childrenD_571_i6 (2, 3) envelope_571_i6
    pivot_mem_571_i6 child_envelope_sub_571_i6 envelope_origin_571_i6
def checked_571_i6 : CheckedCard where
  required := required_571_i6
  envelope := envelope_571_i6
  height := height_571_i6
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_571_i6
def height_571 : ℕ := 12
def childrenH_571 : Fin 7 → ℕ := ![height_250, height_569, height_571_i0, height_571_i2, height_571_i4, height_570, height_571_i6]
theorem height_exact_571 : height_571 = 1 + Finset.univ.sup childrenH_571 := by decide +kernel
theorem required_origin_571 : ∀ x ∈ required_571,
    (∃ j, x ∈ childrenC_571 j) ∨ ∀ j, x ∈ childrenD_571 j := by decide +kernel
theorem required_exact_571 : required_571 =
    ((Finset.univ.biUnion childrenC_571) ∪ commonEnvelope childrenD_571).erase (4, 4) := by
  exact required_eq_combination childrenC_571 childrenD_571 (4, 4) required_571
    (by decide +kernel) child_required_sub_571 common_sub_571 required_origin_571
theorem envelope_origin_571 : ∀ x ∈ envelope_571,
    x = (4, 4) ∨ ∃ j, x ∈ childrenD_571 j := by decide +kernel
theorem envelope_exact_571 : envelope_571 =
    insert (4, 4) (Finset.univ.biUnion childrenD_571) := by
  exact envelope_eq_combination childrenD_571 (4, 4) envelope_571
    pivot_mem_571 child_envelope_sub_571 envelope_origin_571
def checked_571 : CheckedCard where
  required := required_571
  envelope := envelope_571
  height := height_571
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_571
def height_587 : ℕ := 12
def childrenH_587 : Fin 6 → ℕ := ![height_12, height_12, height_12, height_12, height_586, height_586]
theorem height_exact_587 : height_587 = 1 + Finset.univ.sup childrenH_587 := by decide +kernel
theorem required_origin_587 : ∀ x ∈ required_587,
    (∃ j, x ∈ childrenC_587 j) ∨ ∀ j, x ∈ childrenD_587 j := by decide +kernel
theorem required_exact_587 : required_587 =
    ((Finset.univ.biUnion childrenC_587) ∪ commonEnvelope childrenD_587).erase (2, 5) := by
  exact required_eq_combination childrenC_587 childrenD_587 (2, 5) required_587
    (by decide +kernel) child_required_sub_587 common_sub_587 required_origin_587
theorem envelope_origin_587 : ∀ x ∈ envelope_587,
    x = (2, 5) ∨ ∃ j, x ∈ childrenD_587 j := by decide +kernel
theorem envelope_exact_587 : envelope_587 =
    insert (2, 5) (Finset.univ.biUnion childrenD_587) := by
  exact envelope_eq_combination childrenD_587 (2, 5) envelope_587
    pivot_mem_587 child_envelope_sub_587 envelope_origin_587
def checked_587 : CheckedCard where
  required := required_587
  envelope := envelope_587
  height := height_587
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_587
def height_588 : ℕ := 12
def childrenH_588 : Fin 4 → ℕ := ![height_42, height_289, height_291, height_586]
theorem height_exact_588 : height_588 = 1 + Finset.univ.sup childrenH_588 := by decide +kernel
theorem required_origin_588 : ∀ x ∈ required_588,
    (∃ j, x ∈ childrenC_588 j) ∨ ∀ j, x ∈ childrenD_588 j := by decide +kernel
theorem required_exact_588 : required_588 =
    ((Finset.univ.biUnion childrenC_588) ∪ commonEnvelope childrenD_588).erase (4, 3) := by
  exact required_eq_combination childrenC_588 childrenD_588 (4, 3) required_588
    (by decide +kernel) child_required_sub_588 common_sub_588 required_origin_588
theorem envelope_origin_588 : ∀ x ∈ envelope_588,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_588 j := by decide +kernel
theorem envelope_exact_588 : envelope_588 =
    insert (4, 3) (Finset.univ.biUnion childrenD_588) := by
  exact envelope_eq_combination childrenD_588 (4, 3) envelope_588
    pivot_mem_588 child_envelope_sub_588 envelope_origin_588
def checked_588 : CheckedCard where
  required := required_588
  envelope := envelope_588
  height := height_588
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_588
end SnakyPrototype.Certificate21

end OAI
