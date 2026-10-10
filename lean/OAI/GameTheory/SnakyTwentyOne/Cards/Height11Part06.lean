import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part07
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part08
import OAI.GameTheory.SnakyTwentyOne.Cards.Height10Part01
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_689_i0 : Finset Cell := ⟨(([(2, 4), (3, 4), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_689_i0 : Finset Cell := ⟨(([(0, 5), (0, 7), (0, 8), (0, 9), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 4), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, 1), (5, 2), (5, 3), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (6, 5), (6, 6), (6, 7), (7, 5), (7, 6), (7, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_689_i0 : Fin 6 → Finset Cell := ![(placed21 2 (5, 2) required_67), (placed21 6 (5, 8) required_175), (placed21 1 (1, 3) required_228), (placed21 5 (5, 3) required_373), (placed21 5 (7, 3) required_435), (placed21 1 (0, 4) required_688)]
def childrenD_689_i0 : Fin 6 → Finset Cell := ![(placed21 2 (5, 2) envelope_67), (placed21 6 (5, 8) envelope_175), (placed21 1 (1, 3) envelope_228), (placed21 5 (5, 3) envelope_373), (placed21 5 (7, 3) envelope_435), (placed21 1 (0, 4) envelope_688)]
theorem common_sub_689_i0 : commonEnvelope childrenD_689_i0 ⊆ insert (4, 6) required_689_i0 := by decide +kernel
theorem child_required_sub_689_i0 : ∀ j, childrenC_689_i0 j ⊆ insert (4, 6) required_689_i0 := by decide +kernel
theorem child_envelope_sub_689_i0 : ∀ j, childrenD_689_i0 j ⊆ envelope_689_i0 := by decide +kernel
theorem pivot_mem_689_i0 : (4, 6) ∈ envelope_689_i0 := by decide +kernel
theorem children_work_689_i0 : ∀ j, Template HasSnaky 9 (childrenC_689_i0 j) (childrenD_689_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_67 2 (5, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_175 6 (5, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_228 1 (1, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_373 5 (5, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_435 5 (7, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_688 1 (0, 4)).mono (by decide +kernel)
theorem row_works_689_i0 : Template HasSnaky 10 required_689_i0 envelope_689_i0 := by
  refine compose HasSnaky 9 childrenC_689_i0 childrenD_689_i0 children_work_689_i0 (4, 6)
    required_689_i0 envelope_689_i0 pivot_mem_689_i0 child_required_sub_689_i0 child_envelope_sub_689_i0 ?_
  intro b hb
  exact common_sub_689_i0 (mem_commonEnvelope childrenD_689_i0 b hb)
def required_689 : Finset Cell := ⟨(([(2, 4), (3, 4), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_689 : Finset Cell := ⟨(([(0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 0), (3, 1), (3, 2), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, 0), (5, 1), (5, 2), (5, 3), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (6, 5), (6, 6), (6, 7), (7, 5), (7, 6), (7, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_689 : Fin 4 → Finset Cell := ![(placed21 1 (1, 4) required_44), (placed21 2 (5, 0) required_324), (placed21 0 (0, 1) required_686), required_689_i0]
def childrenD_689 : Fin 4 → Finset Cell := ![(placed21 1 (1, 4) envelope_44), (placed21 2 (5, 0) envelope_324), (placed21 0 (0, 1) envelope_686), envelope_689_i0]
theorem common_sub_689 : commonEnvelope childrenD_689 ⊆ insert (4, 5) required_689 := by decide +kernel
theorem child_required_sub_689 : ∀ j, childrenC_689 j ⊆ insert (4, 5) required_689 := by decide +kernel
theorem child_envelope_sub_689 : ∀ j, childrenD_689 j ⊆ envelope_689 := by decide +kernel
theorem pivot_mem_689 : (4, 5) ∈ envelope_689 := by decide +kernel
theorem children_work_689 : ∀ j, Template HasSnaky 10 (childrenC_689 j) (childrenD_689 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_44 1 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_324 2 (5, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_686 0 (0, 1)).mono (by decide +kernel)
  · exact row_works_689_i0.mono (by decide +kernel)
theorem row_works_689 : Template HasSnaky 11 required_689 envelope_689 := by
  refine compose HasSnaky 10 childrenC_689 childrenD_689 children_work_689 (4, 5)
    required_689 envelope_689 pivot_mem_689 child_required_sub_689 child_envelope_sub_689 ?_
  intro b hb
  exact common_sub_689 (mem_commonEnvelope childrenD_689 b hb)
def required_700_i0 : Finset Cell := ⟨(([(1, 3), (1, 4), (1, 5), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_700_i0 : Finset Cell := ⟨(([(0, 4), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 5), (2, 6), (2, 7), (2, 8), (3, 5), (4, 4), (4, 5), (4, 6), (5, 4), (5, 5), (5, 6), (6, 4), (6, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_700_i0 : Fin 2 → Finset Cell := ![(placed21 1 (0, 4) required_39), (placed21 0 (1, 2) required_52)]
def childrenD_700_i0 : Fin 2 → Finset Cell := ![(placed21 1 (0, 4) envelope_39), (placed21 0 (1, 2) envelope_52)]
theorem common_sub_700_i0 : commonEnvelope childrenD_700_i0 ⊆ insert (2, 5) required_700_i0 := by decide +kernel
theorem child_required_sub_700_i0 : ∀ j, childrenC_700_i0 j ⊆ insert (2, 5) required_700_i0 := by decide +kernel
theorem child_envelope_sub_700_i0 : ∀ j, childrenD_700_i0 j ⊆ envelope_700_i0 := by decide +kernel
theorem pivot_mem_700_i0 : (2, 5) ∈ envelope_700_i0 := by decide +kernel
theorem children_work_700_i0 : ∀ j, Template HasSnaky 4 (childrenC_700_i0 j) (childrenD_700_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_39 1 (0, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_52 0 (1, 2)).mono (by decide +kernel)
theorem row_works_700_i0 : Template HasSnaky 5 required_700_i0 envelope_700_i0 := by
  refine compose HasSnaky 4 childrenC_700_i0 childrenD_700_i0 children_work_700_i0 (2, 5)
    required_700_i0 envelope_700_i0 pivot_mem_700_i0 child_required_sub_700_i0 child_envelope_sub_700_i0 ?_
  intro b hb
  exact common_sub_700_i0 (mem_commonEnvelope childrenD_700_i0 b hb)
def required_700_i3 : Finset Cell := ⟨(([(1, 4), (1, 5), (2, 5), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_700_i3 : Finset Cell := ⟨(([(0, 4), (1, 4), (1, 5), (2, 5), (2, 6), (3, 5), (3, 6), (4, 5), (4, 6), (5, 4), (5, 5), (5, 6), (6, 4), (6, 5), (6, 6), (7, 4), (7, 5), (7, 6), (8, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_700_i3 : Fin 2 → Finset Cell := ![(placed21 6 (4, 5) required_5), (placed21 4 (1, 6) required_197)]
def childrenD_700_i3 : Fin 2 → Finset Cell := ![(placed21 6 (4, 5) envelope_5), (placed21 4 (1, 6) envelope_197)]
theorem common_sub_700_i3 : commonEnvelope childrenD_700_i3 ⊆ insert (3, 5) required_700_i3 := by decide +kernel
theorem child_required_sub_700_i3 : ∀ j, childrenC_700_i3 j ⊆ insert (3, 5) required_700_i3 := by decide +kernel
theorem child_envelope_sub_700_i3 : ∀ j, childrenD_700_i3 j ⊆ envelope_700_i3 := by decide +kernel
theorem pivot_mem_700_i3 : (3, 5) ∈ envelope_700_i3 := by decide +kernel
theorem children_work_700_i3 : ∀ j, Template HasSnaky 5 (childrenC_700_i3 j) (childrenD_700_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 6 (4, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_197 4 (1, 6)).mono (by decide +kernel)
theorem row_works_700_i3 : Template HasSnaky 6 required_700_i3 envelope_700_i3 := by
  refine compose HasSnaky 5 childrenC_700_i3 childrenD_700_i3 children_work_700_i3 (3, 5)
    required_700_i3 envelope_700_i3 pivot_mem_700_i3 child_required_sub_700_i3 child_envelope_sub_700_i3 ?_
  intro b hb
  exact common_sub_700_i3 (mem_commonEnvelope childrenD_700_i3 b hb)
def required_700_i2 : Finset Cell := ⟨(([(1, 3), (1, 4), (1, 5), (2, 6), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_700_i2 : Finset Cell := ⟨(([(0, 4), (1, 2), (1, 3), (1, 4), (1, 5), (2, 5), (2, 6), (3, 5), (3, 6), (4, 5), (4, 6), (5, 4), (5, 5), (5, 6), (6, 4), (6, 5), (6, 6), (7, 4), (7, 5), (7, 6), (8, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_700_i2 : Fin 2 → Finset Cell := ![(placed21 1 (1, 2) required_0), required_700_i3]
def childrenD_700_i2 : Fin 2 → Finset Cell := ![(placed21 1 (1, 2) envelope_0), envelope_700_i3]
theorem common_sub_700_i2 : commonEnvelope childrenD_700_i2 ⊆ insert (2, 5) required_700_i2 := by decide +kernel
theorem child_required_sub_700_i2 : ∀ j, childrenC_700_i2 j ⊆ insert (2, 5) required_700_i2 := by decide +kernel
theorem child_envelope_sub_700_i2 : ∀ j, childrenD_700_i2 j ⊆ envelope_700_i2 := by decide +kernel
theorem pivot_mem_700_i2 : (2, 5) ∈ envelope_700_i2 := by decide +kernel
theorem children_work_700_i2 : ∀ j, Template HasSnaky 6 (childrenC_700_i2 j) (childrenD_700_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 1 (1, 2)).mono (by decide +kernel)
  · exact row_works_700_i3.mono (by decide +kernel)
theorem row_works_700_i2 : Template HasSnaky 7 required_700_i2 envelope_700_i2 := by
  refine compose HasSnaky 6 childrenC_700_i2 childrenD_700_i2 children_work_700_i2 (2, 5)
    required_700_i2 envelope_700_i2 pivot_mem_700_i2 child_required_sub_700_i2 child_envelope_sub_700_i2 ?_
  intro b hb
  exact common_sub_700_i2 (mem_commonEnvelope childrenD_700_i2 b hb)
def required_700_i1 : Finset Cell := ⟨(([(1, 3), (1, 4), (1, 5), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_700_i1 : Finset Cell := ⟨(([(0, 4), (0, 6), (0, 7), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 5), (2, 6), (2, 7), (2, 8), (3, 5), (3, 6), (3, 7), (4, 5), (4, 6), (4, 7), (5, 4), (5, 5), (5, 6), (5, 7), (6, 4), (6, 5), (6, 6), (7, 4), (7, 5), (7, 6), (8, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_700_i1 : Fin 3 → Finset Cell := ![(placed21 0 (1, 2) required_61), (placed21 1 (0, 3) required_348), required_700_i2]
def childrenD_700_i1 : Fin 3 → Finset Cell := ![(placed21 0 (1, 2) envelope_61), (placed21 1 (0, 3) envelope_348), envelope_700_i2]
theorem common_sub_700_i1 : commonEnvelope childrenD_700_i1 ⊆ insert (2, 6) required_700_i1 := by decide +kernel
theorem child_required_sub_700_i1 : ∀ j, childrenC_700_i1 j ⊆ insert (2, 6) required_700_i1 := by decide +kernel
theorem child_envelope_sub_700_i1 : ∀ j, childrenD_700_i1 j ⊆ envelope_700_i1 := by decide +kernel
theorem pivot_mem_700_i1 : (2, 6) ∈ envelope_700_i1 := by decide +kernel
theorem children_work_700_i1 : ∀ j, Template HasSnaky 7 (childrenC_700_i1 j) (childrenD_700_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_61 0 (1, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_348 1 (0, 3)).mono (by decide +kernel)
  · exact row_works_700_i2.mono (by decide +kernel)
theorem row_works_700_i1 : Template HasSnaky 8 required_700_i1 envelope_700_i1 := by
  refine compose HasSnaky 7 childrenC_700_i1 childrenD_700_i1 children_work_700_i1 (2, 6)
    required_700_i1 envelope_700_i1 pivot_mem_700_i1 child_required_sub_700_i1 child_envelope_sub_700_i1 ?_
  intro b hb
  exact common_sub_700_i1 (mem_commonEnvelope childrenD_700_i1 b hb)
def required_700_i5 : Finset Cell := ⟨(([(4, 3), (4, 5), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_700_i5 : Finset Cell := ⟨(([(3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 1), (5, 2), (5, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_700_i5 : Fin 3 → Finset Cell := ![(placed21 2 (4, 2) required_7), (placed21 3 (3, 6) required_8), (placed21 4 (3, 7) required_9)]
def childrenD_700_i5 : Fin 3 → Finset Cell := ![(placed21 2 (4, 2) envelope_7), (placed21 3 (3, 6) envelope_8), (placed21 4 (3, 7) envelope_9)]
theorem common_sub_700_i5 : commonEnvelope childrenD_700_i5 ⊆ insert (4, 4) required_700_i5 := by decide +kernel
theorem child_required_sub_700_i5 : ∀ j, childrenC_700_i5 j ⊆ insert (4, 4) required_700_i5 := by decide +kernel
theorem child_envelope_sub_700_i5 : ∀ j, childrenD_700_i5 j ⊆ envelope_700_i5 := by decide +kernel
theorem pivot_mem_700_i5 : (4, 4) ∈ envelope_700_i5 := by decide +kernel
theorem children_work_700_i5 : ∀ j, Template HasSnaky 3 (childrenC_700_i5 j) (childrenD_700_i5 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 2 (4, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_8 3 (3, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_9 4 (3, 7)).mono (by decide +kernel)
theorem row_works_700_i5 : Template HasSnaky 4 required_700_i5 envelope_700_i5 := by
  refine compose HasSnaky 3 childrenC_700_i5 childrenD_700_i5 children_work_700_i5 (4, 4)
    required_700_i5 envelope_700_i5 pivot_mem_700_i5 child_required_sub_700_i5 child_envelope_sub_700_i5 ?_
  intro b hb
  exact common_sub_700_i5 (mem_commonEnvelope childrenD_700_i5 b hb)
def required_700_i6 : Finset Cell := ⟨(([(1, 3), (1, 4), (1, 5), (4, 5), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_700_i6 : Finset Cell := ⟨(([(0, 4), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 5), (2, 6), (2, 7), (2, 8), (3, 5), (4, 5), (4, 6), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_700_i6 : Fin 2 → Finset Cell := ![(placed21 1 (0, 4) required_40), (placed21 0 (1, 2) required_52)]
def childrenD_700_i6 : Fin 2 → Finset Cell := ![(placed21 1 (0, 4) envelope_40), (placed21 0 (1, 2) envelope_52)]
theorem common_sub_700_i6 : commonEnvelope childrenD_700_i6 ⊆ insert (2, 5) required_700_i6 := by decide +kernel
theorem child_required_sub_700_i6 : ∀ j, childrenC_700_i6 j ⊆ insert (2, 5) required_700_i6 := by decide +kernel
theorem child_envelope_sub_700_i6 : ∀ j, childrenD_700_i6 j ⊆ envelope_700_i6 := by decide +kernel
theorem pivot_mem_700_i6 : (2, 5) ∈ envelope_700_i6 := by decide +kernel
theorem children_work_700_i6 : ∀ j, Template HasSnaky 3 (childrenC_700_i6 j) (childrenD_700_i6 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_40 1 (0, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_52 0 (1, 2)).mono (by decide +kernel)
theorem row_works_700_i6 : Template HasSnaky 4 required_700_i6 envelope_700_i6 := by
  refine compose HasSnaky 3 childrenC_700_i6 childrenD_700_i6 children_work_700_i6 (2, 5)
    required_700_i6 envelope_700_i6 pivot_mem_700_i6 child_required_sub_700_i6 child_envelope_sub_700_i6 ?_
  intro b hb
  exact common_sub_700_i6 (mem_commonEnvelope childrenD_700_i6 b hb)
def required_700_i4 : Finset Cell := ⟨(([(1, 3), (1, 4), (1, 5), (4, 3), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_700_i4 : Finset Cell := ⟨(([(0, 4), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 5), (2, 6), (2, 7), (2, 8), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 1), (5, 2), (5, 3), (5, 5), (5, 6), (5, 7), (5, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_700_i4 : Fin 3 → Finset Cell := ![(placed21 6 (5, 8) required_304), required_700_i5, required_700_i6]
def childrenD_700_i4 : Fin 3 → Finset Cell := ![(placed21 6 (5, 8) envelope_304), envelope_700_i5, envelope_700_i6]
theorem common_sub_700_i4 : commonEnvelope childrenD_700_i4 ⊆ insert (4, 6) required_700_i4 := by decide +kernel
theorem child_required_sub_700_i4 : ∀ j, childrenC_700_i4 j ⊆ insert (4, 6) required_700_i4 := by decide +kernel
theorem child_envelope_sub_700_i4 : ∀ j, childrenD_700_i4 j ⊆ envelope_700_i4 := by decide +kernel
theorem pivot_mem_700_i4 : (4, 6) ∈ envelope_700_i4 := by decide +kernel
theorem children_work_700_i4 : ∀ j, Template HasSnaky 4 (childrenC_700_i4 j) (childrenD_700_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_304 6 (5, 8)).mono (by decide +kernel)
  · exact row_works_700_i5.mono (by decide +kernel)
  · exact row_works_700_i6.mono (by decide +kernel)
theorem row_works_700_i4 : Template HasSnaky 5 required_700_i4 envelope_700_i4 := by
  refine compose HasSnaky 4 childrenC_700_i4 childrenD_700_i4 children_work_700_i4 (4, 6)
    required_700_i4 envelope_700_i4 pivot_mem_700_i4 child_required_sub_700_i4 child_envelope_sub_700_i4 ?_
  intro b hb
  exact common_sub_700_i4 (mem_commonEnvelope childrenD_700_i4 b hb)
def required_700 : Finset Cell := ⟨(([(1, 3), (1, 4), (1, 5), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_700 : Finset Cell := ⟨(([(0, 4), (0, 6), (0, 7), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 5), (2, 6), (2, 7), (2, 8), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (8, 1), (8, 2), (8, 3), (8, 4), (8, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_700 : Fin 5 → Finset Cell := ![(placed21 4 (0, 8) required_204), required_700_i0, (placed21 0 (3, 0) required_460), required_700_i1, required_700_i4]
def childrenD_700 : Fin 5 → Finset Cell := ![(placed21 4 (0, 8) envelope_204), envelope_700_i0, (placed21 0 (3, 0) envelope_460), envelope_700_i1, envelope_700_i4]
theorem common_sub_700 : commonEnvelope childrenD_700 ⊆ insert (4, 5) required_700 := by decide +kernel
theorem child_required_sub_700 : ∀ j, childrenC_700 j ⊆ insert (4, 5) required_700 := by decide +kernel
theorem child_envelope_sub_700 : ∀ j, childrenD_700 j ⊆ envelope_700 := by decide +kernel
theorem pivot_mem_700 : (4, 5) ∈ envelope_700 := by decide +kernel
theorem children_work_700 : ∀ j, Template HasSnaky 10 (childrenC_700 j) (childrenD_700 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_204 4 (0, 8)).mono (by decide +kernel)
  · exact row_works_700_i0.mono (by decide +kernel)
  · exact (placed21_template row_works_460 0 (3, 0)).mono (by decide +kernel)
  · exact row_works_700_i1.mono (by decide +kernel)
  · exact row_works_700_i4.mono (by decide +kernel)
theorem row_works_700 : Template HasSnaky 11 required_700 envelope_700 := by
  refine compose HasSnaky 10 childrenC_700 childrenD_700 children_work_700 (4, 5)
    required_700 envelope_700 pivot_mem_700 child_required_sub_700 child_envelope_sub_700 ?_
  intro b hb
  exact common_sub_700 (mem_commonEnvelope childrenD_700 b hb)
def required_710_i1 : Finset Cell := ⟨(([(3, 3), (3, 4), (3, 5), (3, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_710_i1 : Finset Cell := ⟨(([(2, 2), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 0), (4, 1), (4, 2), (4, 5), (4, 6), (4, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_710_i1 : Fin 2 → Finset Cell := ![(placed21 0 (3, 2) required_6), (placed21 3 (2, 6) required_196)]
def childrenD_710_i1 : Fin 2 → Finset Cell := ![(placed21 0 (3, 2) envelope_6), (placed21 3 (2, 6) envelope_196)]
theorem common_sub_710_i1 : commonEnvelope childrenD_710_i1 ⊆ insert (3, 2) required_710_i1 := by decide +kernel
theorem child_required_sub_710_i1 : ∀ j, childrenC_710_i1 j ⊆ insert (3, 2) required_710_i1 := by decide +kernel
theorem child_envelope_sub_710_i1 : ∀ j, childrenD_710_i1 j ⊆ envelope_710_i1 := by decide +kernel
theorem pivot_mem_710_i1 : (3, 2) ∈ envelope_710_i1 := by decide +kernel
theorem children_work_710_i1 : ∀ j, Template HasSnaky 4 (childrenC_710_i1 j) (childrenD_710_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_6 0 (3, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_196 3 (2, 6)).mono (by decide +kernel)
theorem row_works_710_i1 : Template HasSnaky 5 required_710_i1 envelope_710_i1 := by
  refine compose HasSnaky 4 childrenC_710_i1 childrenD_710_i1 children_work_710_i1 (3, 2)
    required_710_i1 envelope_710_i1 pivot_mem_710_i1 child_required_sub_710_i1 child_envelope_sub_710_i1 ?_
  intro b hb
  exact common_sub_710_i1 (mem_commonEnvelope childrenD_710_i1 b hb)
def required_710_i0 : Finset Cell := ⟨(([(3, 4), (3, 5), (3, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_710_i0 : Finset Cell := ⟨(([(0, 4), (1, 3), (1, 4), (1, 5), (2, 2), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (7, 2), (7, 4), (7, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_710_i0 : Fin 4 → Finset Cell := ![(placed21 4 (3, 7) required_7), (placed21 3 (0, 6) required_115), required_710_i1, (placed21 1 (1, 2) required_577)]
def childrenD_710_i0 : Fin 4 → Finset Cell := ![(placed21 4 (3, 7) envelope_7), (placed21 3 (0, 6) envelope_115), envelope_710_i1, (placed21 1 (1, 2) envelope_577)]
theorem common_sub_710_i0 : commonEnvelope childrenD_710_i0 ⊆ insert (3, 3) required_710_i0 := by decide +kernel
theorem child_required_sub_710_i0 : ∀ j, childrenC_710_i0 j ⊆ insert (3, 3) required_710_i0 := by decide +kernel
theorem child_envelope_sub_710_i0 : ∀ j, childrenD_710_i0 j ⊆ envelope_710_i0 := by decide +kernel
theorem pivot_mem_710_i0 : (3, 3) ∈ envelope_710_i0 := by decide +kernel
theorem children_work_710_i0 : ∀ j, Template HasSnaky 9 (childrenC_710_i0 j) (childrenD_710_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 4 (3, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_115 3 (0, 6)).mono (by decide +kernel)
  · exact row_works_710_i1.mono (by decide +kernel)
  · exact (placed21_template row_works_577 1 (1, 2)).mono (by decide +kernel)
theorem row_works_710_i0 : Template HasSnaky 10 required_710_i0 envelope_710_i0 := by
  refine compose HasSnaky 9 childrenC_710_i0 childrenD_710_i0 children_work_710_i0 (3, 3)
    required_710_i0 envelope_710_i0 pivot_mem_710_i0 child_required_sub_710_i0 child_envelope_sub_710_i0 ?_
  intro b hb
  exact common_sub_710_i0 (mem_commonEnvelope childrenD_710_i0 b hb)
def required_710 : Finset Cell := ⟨(([(3, 4), (3, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_710 : Finset Cell := ⟨(([(0, 4), (0, 5), (1, 3), (1, 4), (1, 5), (2, 2), (2, 3), (2, 4), (2, 5), (2, 7), (2, 8), (2, 9), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (7, 2), (7, 3), (7, 4), (7, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_710 : Fin 4 → Finset Cell := ![(placed21 0 (2, 2) required_13), (placed21 2 (4, 2) required_14), (placed21 1 (0, 3) required_117), required_710_i0]
def childrenD_710 : Fin 4 → Finset Cell := ![(placed21 0 (2, 2) envelope_13), (placed21 2 (4, 2) envelope_14), (placed21 1 (0, 3) envelope_117), envelope_710_i0]
theorem common_sub_710 : commonEnvelope childrenD_710 ⊆ insert (3, 6) required_710 := by decide +kernel
theorem child_required_sub_710 : ∀ j, childrenC_710 j ⊆ insert (3, 6) required_710 := by decide +kernel
theorem child_envelope_sub_710 : ∀ j, childrenD_710 j ⊆ envelope_710 := by decide +kernel
theorem pivot_mem_710 : (3, 6) ∈ envelope_710 := by decide +kernel
theorem children_work_710 : ∀ j, Template HasSnaky 10 (childrenC_710 j) (childrenD_710 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_13 0 (2, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_14 2 (4, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_117 1 (0, 3)).mono (by decide +kernel)
  · exact row_works_710_i0.mono (by decide +kernel)
theorem row_works_710 : Template HasSnaky 11 required_710 envelope_710 := by
  refine compose HasSnaky 10 childrenC_710 childrenD_710 children_work_710 (3, 6)
    required_710 envelope_710 pivot_mem_710 child_required_sub_710 child_envelope_sub_710 ?_
  intro b hb
  exact common_sub_710 (mem_commonEnvelope childrenD_710 b hb)
def required_716_i0 : Finset Cell := ⟨(([(4, 5), (5, 5), (6, 5), (7, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_716_i0 : Finset Cell := ⟨(([(0, 2), (0, 4), (1, 2), (1, 3), (1, 4), (2, 2), (2, 3), (2, 4), (3, 1), (3, 2), (3, 3), (3, 4), (3, 7), (3, 8), (3, 9), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (7, 5), (7, 6), (7, 7), (7, 8), (8, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_716_i0 : Fin 2 → Finset Cell := ![(placed21 0 (4, 2) required_55), (placed21 2 (7, 0) required_659)]
def childrenD_716_i0 : Fin 2 → Finset Cell := ![(placed21 0 (4, 2) envelope_55), (placed21 2 (7, 0) envelope_659)]
theorem common_sub_716_i0 : commonEnvelope childrenD_716_i0 ⊆ insert (6, 4) required_716_i0 := by decide +kernel
theorem child_required_sub_716_i0 : ∀ j, childrenC_716_i0 j ⊆ insert (6, 4) required_716_i0 := by decide +kernel
theorem child_envelope_sub_716_i0 : ∀ j, childrenD_716_i0 j ⊆ envelope_716_i0 := by decide +kernel
theorem pivot_mem_716_i0 : (6, 4) ∈ envelope_716_i0 := by decide +kernel
theorem children_work_716_i0 : ∀ j, Template HasSnaky 9 (childrenC_716_i0 j) (childrenD_716_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_55 0 (4, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_659 2 (7, 0)).mono (by decide +kernel)
theorem row_works_716_i0 : Template HasSnaky 10 required_716_i0 envelope_716_i0 := by
  refine compose HasSnaky 9 childrenC_716_i0 childrenD_716_i0 children_work_716_i0 (6, 4)
    required_716_i0 envelope_716_i0 pivot_mem_716_i0 child_required_sub_716_i0 child_envelope_sub_716_i0 ?_
  intro b hb
  exact common_sub_716_i0 (mem_commonEnvelope childrenD_716_i0 b hb)
def required_716 : Finset Cell := ⟨(([(4, 5), (5, 5), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_716 : Finset Cell := ⟨(([(0, 2), (0, 4), (1, 2), (1, 3), (1, 4), (2, 2), (2, 3), (2, 4), (3, 1), (3, 2), (3, 3), (3, 4), (3, 7), (3, 8), (3, 9), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (7, 5), (7, 6), (7, 7), (7, 8), (8, 4), (8, 5), (8, 6), (9, 4), (9, 5), (9, 6), (10, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_716 : Fin 4 → Finset Cell := ![(placed21 1 (3, 4) required_9), (placed21 4 (4, 6) required_49), (placed21 0 (3, 2) required_142), required_716_i0]
def childrenD_716 : Fin 4 → Finset Cell := ![(placed21 1 (3, 4) envelope_9), (placed21 4 (4, 6) envelope_49), (placed21 0 (3, 2) envelope_142), envelope_716_i0]
theorem common_sub_716 : commonEnvelope childrenD_716 ⊆ insert (7, 5) required_716 := by decide +kernel
theorem child_required_sub_716 : ∀ j, childrenC_716 j ⊆ insert (7, 5) required_716 := by decide +kernel
theorem child_envelope_sub_716 : ∀ j, childrenD_716 j ⊆ envelope_716 := by decide +kernel
theorem pivot_mem_716 : (7, 5) ∈ envelope_716 := by decide +kernel
theorem children_work_716 : ∀ j, Template HasSnaky 10 (childrenC_716 j) (childrenD_716 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_9 1 (3, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_49 4 (4, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_142 0 (3, 2)).mono (by decide +kernel)
  · exact row_works_716_i0.mono (by decide +kernel)
theorem row_works_716 : Template HasSnaky 11 required_716 envelope_716 := by
  refine compose HasSnaky 10 childrenC_716 childrenD_716 children_work_716 (7, 5)
    required_716 envelope_716 pivot_mem_716 child_required_sub_716 child_envelope_sub_716 ?_
  intro b hb
  exact common_sub_716 (mem_commonEnvelope childrenD_716 b hb)
def height_689_i0 : ℕ := 10
def childrenH_689_i0 : Fin 6 → ℕ := ![height_67, height_175, height_228, height_373, height_435, height_688]
theorem height_exact_689_i0 : height_689_i0 = 1 + Finset.univ.sup childrenH_689_i0 := by decide +kernel
theorem required_origin_689_i0 : ∀ x ∈ required_689_i0,
    (∃ j, x ∈ childrenC_689_i0 j) ∨ ∀ j, x ∈ childrenD_689_i0 j := by decide +kernel
theorem required_exact_689_i0 : required_689_i0 =
    ((Finset.univ.biUnion childrenC_689_i0) ∪ commonEnvelope childrenD_689_i0).erase (4, 6) := by
  exact required_eq_combination childrenC_689_i0 childrenD_689_i0 (4, 6) required_689_i0
    (by decide +kernel) child_required_sub_689_i0 common_sub_689_i0 required_origin_689_i0
theorem envelope_origin_689_i0 : ∀ x ∈ envelope_689_i0,
    x = (4, 6) ∨ ∃ j, x ∈ childrenD_689_i0 j := by decide +kernel
theorem envelope_exact_689_i0 : envelope_689_i0 =
    insert (4, 6) (Finset.univ.biUnion childrenD_689_i0) := by
  exact envelope_eq_combination childrenD_689_i0 (4, 6) envelope_689_i0
    pivot_mem_689_i0 child_envelope_sub_689_i0 envelope_origin_689_i0
def checked_689_i0 : CheckedCard where
  required := required_689_i0
  envelope := envelope_689_i0
  height := height_689_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_689_i0
def height_689 : ℕ := 11
def childrenH_689 : Fin 4 → ℕ := ![height_44, height_324, height_686, height_689_i0]
theorem height_exact_689 : height_689 = 1 + Finset.univ.sup childrenH_689 := by decide +kernel
theorem required_origin_689 : ∀ x ∈ required_689,
    (∃ j, x ∈ childrenC_689 j) ∨ ∀ j, x ∈ childrenD_689 j := by decide +kernel
theorem required_exact_689 : required_689 =
    ((Finset.univ.biUnion childrenC_689) ∪ commonEnvelope childrenD_689).erase (4, 5) := by
  exact required_eq_combination childrenC_689 childrenD_689 (4, 5) required_689
    (by decide +kernel) child_required_sub_689 common_sub_689 required_origin_689
theorem envelope_origin_689 : ∀ x ∈ envelope_689,
    x = (4, 5) ∨ ∃ j, x ∈ childrenD_689 j := by decide +kernel
theorem envelope_exact_689 : envelope_689 =
    insert (4, 5) (Finset.univ.biUnion childrenD_689) := by
  exact envelope_eq_combination childrenD_689 (4, 5) envelope_689
    pivot_mem_689 child_envelope_sub_689 envelope_origin_689
def checked_689 : CheckedCard where
  required := required_689
  envelope := envelope_689
  height := height_689
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_689
def height_700_i0 : ℕ := 5
def childrenH_700_i0 : Fin 2 → ℕ := ![height_39, height_52]
theorem height_exact_700_i0 : height_700_i0 = 1 + Finset.univ.sup childrenH_700_i0 := by decide +kernel
theorem required_origin_700_i0 : ∀ x ∈ required_700_i0,
    (∃ j, x ∈ childrenC_700_i0 j) ∨ ∀ j, x ∈ childrenD_700_i0 j := by decide +kernel
theorem required_exact_700_i0 : required_700_i0 =
    ((Finset.univ.biUnion childrenC_700_i0) ∪ commonEnvelope childrenD_700_i0).erase (2, 5) := by
  exact required_eq_combination childrenC_700_i0 childrenD_700_i0 (2, 5) required_700_i0
    (by decide +kernel) child_required_sub_700_i0 common_sub_700_i0 required_origin_700_i0
theorem envelope_origin_700_i0 : ∀ x ∈ envelope_700_i0,
    x = (2, 5) ∨ ∃ j, x ∈ childrenD_700_i0 j := by decide +kernel
theorem envelope_exact_700_i0 : envelope_700_i0 =
    insert (2, 5) (Finset.univ.biUnion childrenD_700_i0) := by
  exact envelope_eq_combination childrenD_700_i0 (2, 5) envelope_700_i0
    pivot_mem_700_i0 child_envelope_sub_700_i0 envelope_origin_700_i0
def checked_700_i0 : CheckedCard where
  required := required_700_i0
  envelope := envelope_700_i0
  height := height_700_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_700_i0
def height_700_i3 : ℕ := 6
def childrenH_700_i3 : Fin 2 → ℕ := ![height_5, height_197]
theorem height_exact_700_i3 : height_700_i3 = 1 + Finset.univ.sup childrenH_700_i3 := by decide +kernel
theorem required_origin_700_i3 : ∀ x ∈ required_700_i3,
    (∃ j, x ∈ childrenC_700_i3 j) ∨ ∀ j, x ∈ childrenD_700_i3 j := by decide +kernel
theorem required_exact_700_i3 : required_700_i3 =
    ((Finset.univ.biUnion childrenC_700_i3) ∪ commonEnvelope childrenD_700_i3).erase (3, 5) := by
  exact required_eq_combination childrenC_700_i3 childrenD_700_i3 (3, 5) required_700_i3
    (by decide +kernel) child_required_sub_700_i3 common_sub_700_i3 required_origin_700_i3
theorem envelope_origin_700_i3 : ∀ x ∈ envelope_700_i3,
    x = (3, 5) ∨ ∃ j, x ∈ childrenD_700_i3 j := by decide +kernel
theorem envelope_exact_700_i3 : envelope_700_i3 =
    insert (3, 5) (Finset.univ.biUnion childrenD_700_i3) := by
  exact envelope_eq_combination childrenD_700_i3 (3, 5) envelope_700_i3
    pivot_mem_700_i3 child_envelope_sub_700_i3 envelope_origin_700_i3
def checked_700_i3 : CheckedCard where
  required := required_700_i3
  envelope := envelope_700_i3
  height := height_700_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_700_i3
def height_700_i2 : ℕ := 7
def childrenH_700_i2 : Fin 2 → ℕ := ![height_0, height_700_i3]
theorem height_exact_700_i2 : height_700_i2 = 1 + Finset.univ.sup childrenH_700_i2 := by decide +kernel
theorem required_origin_700_i2 : ∀ x ∈ required_700_i2,
    (∃ j, x ∈ childrenC_700_i2 j) ∨ ∀ j, x ∈ childrenD_700_i2 j := by decide +kernel
theorem required_exact_700_i2 : required_700_i2 =
    ((Finset.univ.biUnion childrenC_700_i2) ∪ commonEnvelope childrenD_700_i2).erase (2, 5) := by
  exact required_eq_combination childrenC_700_i2 childrenD_700_i2 (2, 5) required_700_i2
    (by decide +kernel) child_required_sub_700_i2 common_sub_700_i2 required_origin_700_i2
theorem envelope_origin_700_i2 : ∀ x ∈ envelope_700_i2,
    x = (2, 5) ∨ ∃ j, x ∈ childrenD_700_i2 j := by decide +kernel
theorem envelope_exact_700_i2 : envelope_700_i2 =
    insert (2, 5) (Finset.univ.biUnion childrenD_700_i2) := by
  exact envelope_eq_combination childrenD_700_i2 (2, 5) envelope_700_i2
    pivot_mem_700_i2 child_envelope_sub_700_i2 envelope_origin_700_i2
def checked_700_i2 : CheckedCard where
  required := required_700_i2
  envelope := envelope_700_i2
  height := height_700_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_700_i2
def height_700_i1 : ℕ := 8
def childrenH_700_i1 : Fin 3 → ℕ := ![height_61, height_348, height_700_i2]
theorem height_exact_700_i1 : height_700_i1 = 1 + Finset.univ.sup childrenH_700_i1 := by decide +kernel
theorem required_origin_700_i1 : ∀ x ∈ required_700_i1,
    (∃ j, x ∈ childrenC_700_i1 j) ∨ ∀ j, x ∈ childrenD_700_i1 j := by decide +kernel
theorem required_exact_700_i1 : required_700_i1 =
    ((Finset.univ.biUnion childrenC_700_i1) ∪ commonEnvelope childrenD_700_i1).erase (2, 6) := by
  exact required_eq_combination childrenC_700_i1 childrenD_700_i1 (2, 6) required_700_i1
    (by decide +kernel) child_required_sub_700_i1 common_sub_700_i1 required_origin_700_i1
theorem envelope_origin_700_i1 : ∀ x ∈ envelope_700_i1,
    x = (2, 6) ∨ ∃ j, x ∈ childrenD_700_i1 j := by decide +kernel
theorem envelope_exact_700_i1 : envelope_700_i1 =
    insert (2, 6) (Finset.univ.biUnion childrenD_700_i1) := by
  exact envelope_eq_combination childrenD_700_i1 (2, 6) envelope_700_i1
    pivot_mem_700_i1 child_envelope_sub_700_i1 envelope_origin_700_i1
def checked_700_i1 : CheckedCard where
  required := required_700_i1
  envelope := envelope_700_i1
  height := height_700_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_700_i1
def height_700_i5 : ℕ := 4
def childrenH_700_i5 : Fin 3 → ℕ := ![height_7, height_8, height_9]
theorem height_exact_700_i5 : height_700_i5 = 1 + Finset.univ.sup childrenH_700_i5 := by decide +kernel
theorem required_origin_700_i5 : ∀ x ∈ required_700_i5,
    (∃ j, x ∈ childrenC_700_i5 j) ∨ ∀ j, x ∈ childrenD_700_i5 j := by decide +kernel
theorem required_exact_700_i5 : required_700_i5 =
    ((Finset.univ.biUnion childrenC_700_i5) ∪ commonEnvelope childrenD_700_i5).erase (4, 4) := by
  exact required_eq_combination childrenC_700_i5 childrenD_700_i5 (4, 4) required_700_i5
    (by decide +kernel) child_required_sub_700_i5 common_sub_700_i5 required_origin_700_i5
theorem envelope_origin_700_i5 : ∀ x ∈ envelope_700_i5,
    x = (4, 4) ∨ ∃ j, x ∈ childrenD_700_i5 j := by decide +kernel
theorem envelope_exact_700_i5 : envelope_700_i5 =
    insert (4, 4) (Finset.univ.biUnion childrenD_700_i5) := by
  exact envelope_eq_combination childrenD_700_i5 (4, 4) envelope_700_i5
    pivot_mem_700_i5 child_envelope_sub_700_i5 envelope_origin_700_i5
def checked_700_i5 : CheckedCard where
  required := required_700_i5
  envelope := envelope_700_i5
  height := height_700_i5
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_700_i5
def height_700_i6 : ℕ := 4
def childrenH_700_i6 : Fin 2 → ℕ := ![height_40, height_52]
theorem height_exact_700_i6 : height_700_i6 = 1 + Finset.univ.sup childrenH_700_i6 := by decide +kernel
theorem required_origin_700_i6 : ∀ x ∈ required_700_i6,
    (∃ j, x ∈ childrenC_700_i6 j) ∨ ∀ j, x ∈ childrenD_700_i6 j := by decide +kernel
theorem required_exact_700_i6 : required_700_i6 =
    ((Finset.univ.biUnion childrenC_700_i6) ∪ commonEnvelope childrenD_700_i6).erase (2, 5) := by
  exact required_eq_combination childrenC_700_i6 childrenD_700_i6 (2, 5) required_700_i6
    (by decide +kernel) child_required_sub_700_i6 common_sub_700_i6 required_origin_700_i6
theorem envelope_origin_700_i6 : ∀ x ∈ envelope_700_i6,
    x = (2, 5) ∨ ∃ j, x ∈ childrenD_700_i6 j := by decide +kernel
theorem envelope_exact_700_i6 : envelope_700_i6 =
    insert (2, 5) (Finset.univ.biUnion childrenD_700_i6) := by
  exact envelope_eq_combination childrenD_700_i6 (2, 5) envelope_700_i6
    pivot_mem_700_i6 child_envelope_sub_700_i6 envelope_origin_700_i6
def checked_700_i6 : CheckedCard where
  required := required_700_i6
  envelope := envelope_700_i6
  height := height_700_i6
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_700_i6
def height_700_i4 : ℕ := 5
def childrenH_700_i4 : Fin 3 → ℕ := ![height_304, height_700_i5, height_700_i6]
theorem height_exact_700_i4 : height_700_i4 = 1 + Finset.univ.sup childrenH_700_i4 := by decide +kernel
theorem required_origin_700_i4 : ∀ x ∈ required_700_i4,
    (∃ j, x ∈ childrenC_700_i4 j) ∨ ∀ j, x ∈ childrenD_700_i4 j := by decide +kernel
theorem required_exact_700_i4 : required_700_i4 =
    ((Finset.univ.biUnion childrenC_700_i4) ∪ commonEnvelope childrenD_700_i4).erase (4, 6) := by
  exact required_eq_combination childrenC_700_i4 childrenD_700_i4 (4, 6) required_700_i4
    (by decide +kernel) child_required_sub_700_i4 common_sub_700_i4 required_origin_700_i4
theorem envelope_origin_700_i4 : ∀ x ∈ envelope_700_i4,
    x = (4, 6) ∨ ∃ j, x ∈ childrenD_700_i4 j := by decide +kernel
theorem envelope_exact_700_i4 : envelope_700_i4 =
    insert (4, 6) (Finset.univ.biUnion childrenD_700_i4) := by
  exact envelope_eq_combination childrenD_700_i4 (4, 6) envelope_700_i4
    pivot_mem_700_i4 child_envelope_sub_700_i4 envelope_origin_700_i4
def checked_700_i4 : CheckedCard where
  required := required_700_i4
  envelope := envelope_700_i4
  height := height_700_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_700_i4
def height_700 : ℕ := 11
def childrenH_700 : Fin 5 → ℕ := ![height_204, height_700_i0, height_460, height_700_i1, height_700_i4]
theorem height_exact_700 : height_700 = 1 + Finset.univ.sup childrenH_700 := by decide +kernel
theorem required_origin_700 : ∀ x ∈ required_700,
    (∃ j, x ∈ childrenC_700 j) ∨ ∀ j, x ∈ childrenD_700 j := by decide +kernel
theorem required_exact_700 : required_700 =
    ((Finset.univ.biUnion childrenC_700) ∪ commonEnvelope childrenD_700).erase (4, 5) := by
  exact required_eq_combination childrenC_700 childrenD_700 (4, 5) required_700
    (by decide +kernel) child_required_sub_700 common_sub_700 required_origin_700
theorem envelope_origin_700 : ∀ x ∈ envelope_700,
    x = (4, 5) ∨ ∃ j, x ∈ childrenD_700 j := by decide +kernel
theorem envelope_exact_700 : envelope_700 =
    insert (4, 5) (Finset.univ.biUnion childrenD_700) := by
  exact envelope_eq_combination childrenD_700 (4, 5) envelope_700
    pivot_mem_700 child_envelope_sub_700 envelope_origin_700
def checked_700 : CheckedCard where
  required := required_700
  envelope := envelope_700
  height := height_700
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_700
def height_710_i1 : ℕ := 5
def childrenH_710_i1 : Fin 2 → ℕ := ![height_6, height_196]
theorem height_exact_710_i1 : height_710_i1 = 1 + Finset.univ.sup childrenH_710_i1 := by decide +kernel
theorem required_origin_710_i1 : ∀ x ∈ required_710_i1,
    (∃ j, x ∈ childrenC_710_i1 j) ∨ ∀ j, x ∈ childrenD_710_i1 j := by decide +kernel
theorem required_exact_710_i1 : required_710_i1 =
    ((Finset.univ.biUnion childrenC_710_i1) ∪ commonEnvelope childrenD_710_i1).erase (3, 2) := by
  exact required_eq_combination childrenC_710_i1 childrenD_710_i1 (3, 2) required_710_i1
    (by decide +kernel) child_required_sub_710_i1 common_sub_710_i1 required_origin_710_i1
theorem envelope_origin_710_i1 : ∀ x ∈ envelope_710_i1,
    x = (3, 2) ∨ ∃ j, x ∈ childrenD_710_i1 j := by decide +kernel
theorem envelope_exact_710_i1 : envelope_710_i1 =
    insert (3, 2) (Finset.univ.biUnion childrenD_710_i1) := by
  exact envelope_eq_combination childrenD_710_i1 (3, 2) envelope_710_i1
    pivot_mem_710_i1 child_envelope_sub_710_i1 envelope_origin_710_i1
def checked_710_i1 : CheckedCard where
  required := required_710_i1
  envelope := envelope_710_i1
  height := height_710_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_710_i1
def height_710_i0 : ℕ := 10
def childrenH_710_i0 : Fin 4 → ℕ := ![height_7, height_115, height_710_i1, height_577]
theorem height_exact_710_i0 : height_710_i0 = 1 + Finset.univ.sup childrenH_710_i0 := by decide +kernel
theorem required_origin_710_i0 : ∀ x ∈ required_710_i0,
    (∃ j, x ∈ childrenC_710_i0 j) ∨ ∀ j, x ∈ childrenD_710_i0 j := by decide +kernel
theorem required_exact_710_i0 : required_710_i0 =
    ((Finset.univ.biUnion childrenC_710_i0) ∪ commonEnvelope childrenD_710_i0).erase (3, 3) := by
  exact required_eq_combination childrenC_710_i0 childrenD_710_i0 (3, 3) required_710_i0
    (by decide +kernel) child_required_sub_710_i0 common_sub_710_i0 required_origin_710_i0
theorem envelope_origin_710_i0 : ∀ x ∈ envelope_710_i0,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_710_i0 j := by decide +kernel
theorem envelope_exact_710_i0 : envelope_710_i0 =
    insert (3, 3) (Finset.univ.biUnion childrenD_710_i0) := by
  exact envelope_eq_combination childrenD_710_i0 (3, 3) envelope_710_i0
    pivot_mem_710_i0 child_envelope_sub_710_i0 envelope_origin_710_i0
def checked_710_i0 : CheckedCard where
  required := required_710_i0
  envelope := envelope_710_i0
  height := height_710_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_710_i0
def height_710 : ℕ := 11
def childrenH_710 : Fin 4 → ℕ := ![height_13, height_14, height_117, height_710_i0]
theorem height_exact_710 : height_710 = 1 + Finset.univ.sup childrenH_710 := by decide +kernel
theorem required_origin_710 : ∀ x ∈ required_710,
    (∃ j, x ∈ childrenC_710 j) ∨ ∀ j, x ∈ childrenD_710 j := by decide +kernel
theorem required_exact_710 : required_710 =
    ((Finset.univ.biUnion childrenC_710) ∪ commonEnvelope childrenD_710).erase (3, 6) := by
  exact required_eq_combination childrenC_710 childrenD_710 (3, 6) required_710
    (by decide +kernel) child_required_sub_710 common_sub_710 required_origin_710
theorem envelope_origin_710 : ∀ x ∈ envelope_710,
    x = (3, 6) ∨ ∃ j, x ∈ childrenD_710 j := by decide +kernel
theorem envelope_exact_710 : envelope_710 =
    insert (3, 6) (Finset.univ.biUnion childrenD_710) := by
  exact envelope_eq_combination childrenD_710 (3, 6) envelope_710
    pivot_mem_710 child_envelope_sub_710 envelope_origin_710
def checked_710 : CheckedCard where
  required := required_710
  envelope := envelope_710
  height := height_710
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_710
def height_716_i0 : ℕ := 10
def childrenH_716_i0 : Fin 2 → ℕ := ![height_55, height_659]
theorem height_exact_716_i0 : height_716_i0 = 1 + Finset.univ.sup childrenH_716_i0 := by decide +kernel
theorem required_origin_716_i0 : ∀ x ∈ required_716_i0,
    (∃ j, x ∈ childrenC_716_i0 j) ∨ ∀ j, x ∈ childrenD_716_i0 j := by decide +kernel
theorem required_exact_716_i0 : required_716_i0 =
    ((Finset.univ.biUnion childrenC_716_i0) ∪ commonEnvelope childrenD_716_i0).erase (6, 4) := by
  exact required_eq_combination childrenC_716_i0 childrenD_716_i0 (6, 4) required_716_i0
    (by decide +kernel) child_required_sub_716_i0 common_sub_716_i0 required_origin_716_i0
theorem envelope_origin_716_i0 : ∀ x ∈ envelope_716_i0,
    x = (6, 4) ∨ ∃ j, x ∈ childrenD_716_i0 j := by decide +kernel
theorem envelope_exact_716_i0 : envelope_716_i0 =
    insert (6, 4) (Finset.univ.biUnion childrenD_716_i0) := by
  exact envelope_eq_combination childrenD_716_i0 (6, 4) envelope_716_i0
    pivot_mem_716_i0 child_envelope_sub_716_i0 envelope_origin_716_i0
def checked_716_i0 : CheckedCard where
  required := required_716_i0
  envelope := envelope_716_i0
  height := height_716_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_716_i0
def height_716 : ℕ := 11
def childrenH_716 : Fin 4 → ℕ := ![height_9, height_49, height_142, height_716_i0]
theorem height_exact_716 : height_716 = 1 + Finset.univ.sup childrenH_716 := by decide +kernel
theorem required_origin_716 : ∀ x ∈ required_716,
    (∃ j, x ∈ childrenC_716 j) ∨ ∀ j, x ∈ childrenD_716 j := by decide +kernel
theorem required_exact_716 : required_716 =
    ((Finset.univ.biUnion childrenC_716) ∪ commonEnvelope childrenD_716).erase (7, 5) := by
  exact required_eq_combination childrenC_716 childrenD_716 (7, 5) required_716
    (by decide +kernel) child_required_sub_716 common_sub_716 required_origin_716
theorem envelope_origin_716 : ∀ x ∈ envelope_716,
    x = (7, 5) ∨ ∃ j, x ∈ childrenD_716 j := by decide +kernel
theorem envelope_exact_716 : envelope_716 =
    insert (7, 5) (Finset.univ.biUnion childrenD_716) := by
  exact envelope_eq_combination childrenD_716 (7, 5) envelope_716
    pivot_mem_716 child_envelope_sub_716 envelope_origin_716
def checked_716 : CheckedCard where
  required := required_716
  envelope := envelope_716
  height := height_716
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_716
end SnakyPrototype.Certificate21

end OAI
