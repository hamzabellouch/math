import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part04
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_546_i4 : Finset Cell := ⟨(([(0, 6), (1, 5), (1, 6), (2, 3), (2, 4), (2, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_546_i4 : Finset Cell := ⟨(([(0, 5), (0, 6), (1, 5), (1, 6), (2, 3), (2, 4), (2, 5), (2, 6), (3, 6), (3, 7), (4, 5), (4, 6), (4, 7), (5, 5), (5, 6), (5, 7), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_546_i4 : Fin 3 → Finset Cell := ![(placed21 4 (0, 7) required_25), (placed21 3 (0, 6) required_27), (placed21 1 (0, 5) required_37)]
def childrenD_546_i4 : Fin 3 → Finset Cell := ![(placed21 4 (0, 7) envelope_25), (placed21 3 (0, 6) envelope_27), (placed21 1 (0, 5) envelope_37)]
theorem common_sub_546_i4 : commonEnvelope childrenD_546_i4 ⊆ insert (3, 6) required_546_i4 := by decide +kernel
theorem child_required_sub_546_i4 : ∀ j, childrenC_546_i4 j ⊆ insert (3, 6) required_546_i4 := by decide +kernel
theorem child_envelope_sub_546_i4 : ∀ j, childrenD_546_i4 j ⊆ envelope_546_i4 := by decide +kernel
theorem pivot_mem_546_i4 : (3, 6) ∈ envelope_546_i4 := by decide +kernel
theorem children_work_546_i4 : ∀ j, Template HasSnaky 4 (childrenC_546_i4 j) (childrenD_546_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_25 4 (0, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_27 3 (0, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_37 1 (0, 5)).mono (by decide +kernel)
theorem row_works_546_i4 : Template HasSnaky 5 required_546_i4 envelope_546_i4 := by
  refine compose HasSnaky 4 childrenC_546_i4 childrenD_546_i4 children_work_546_i4 (3, 6)
    required_546_i4 envelope_546_i4 pivot_mem_546_i4 child_required_sub_546_i4 child_envelope_sub_546_i4 ?_
  intro b hb
  exact common_sub_546_i4 (mem_commonEnvelope childrenD_546_i4 b hb)
def required_546_i3 : Finset Cell := ⟨(([(1, 3), (1, 4), (1, 5), (1, 6), (2, 3), (2, 4), (2, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_546_i3 : Finset Cell := ⟨(([(0, 5), (0, 6), (0, 7), (1, 3), (1, 4), (1, 5), (1, 6), (2, 3), (2, 4), (2, 5), (2, 6), (3, 6), (3, 7), (4, 5), (4, 6), (4, 7), (5, 5), (5, 6), (5, 7), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_546_i3 : Fin 2 → Finset Cell := ![(placed21 5 (1, 3) required_5), required_546_i4]
def childrenD_546_i3 : Fin 2 → Finset Cell := ![(placed21 5 (1, 3) envelope_5), envelope_546_i4]
theorem common_sub_546_i3 : commonEnvelope childrenD_546_i3 ⊆ insert (0, 6) required_546_i3 := by decide +kernel
theorem child_required_sub_546_i3 : ∀ j, childrenC_546_i3 j ⊆ insert (0, 6) required_546_i3 := by decide +kernel
theorem child_envelope_sub_546_i3 : ∀ j, childrenD_546_i3 j ⊆ envelope_546_i3 := by decide +kernel
theorem pivot_mem_546_i3 : (0, 6) ∈ envelope_546_i3 := by decide +kernel
theorem children_work_546_i3 : ∀ j, Template HasSnaky 5 (childrenC_546_i3 j) (childrenD_546_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 5 (1, 3)).mono (by decide +kernel)
  · exact row_works_546_i4.mono (by decide +kernel)
theorem row_works_546_i3 : Template HasSnaky 6 required_546_i3 envelope_546_i3 := by
  refine compose HasSnaky 5 childrenC_546_i3 childrenD_546_i3 children_work_546_i3 (0, 6)
    required_546_i3 envelope_546_i3 pivot_mem_546_i3 child_required_sub_546_i3 child_envelope_sub_546_i3 ?_
  intro b hb
  exact common_sub_546_i3 (mem_commonEnvelope childrenD_546_i3 b hb)
def required_546_i2 : Finset Cell := ⟨(([(1, 3), (1, 4), (1, 5), (1, 6), (2, 3), (2, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_546_i2 : Finset Cell := ⟨(([(0, 5), (0, 6), (0, 7), (1, 3), (1, 4), (1, 5), (1, 6), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 6), (3, 7), (4, 5), (4, 6), (4, 7), (5, 5), (5, 6), (5, 7), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_546_i2 : Fin 2 → Finset Cell := ![(placed21 1 (1, 3) required_5), required_546_i3]
def childrenD_546_i2 : Fin 2 → Finset Cell := ![(placed21 1 (1, 3) envelope_5), envelope_546_i3]
theorem common_sub_546_i2 : commonEnvelope childrenD_546_i2 ⊆ insert (2, 6) required_546_i2 := by decide +kernel
theorem child_required_sub_546_i2 : ∀ j, childrenC_546_i2 j ⊆ insert (2, 6) required_546_i2 := by decide +kernel
theorem child_envelope_sub_546_i2 : ∀ j, childrenD_546_i2 j ⊆ envelope_546_i2 := by decide +kernel
theorem pivot_mem_546_i2 : (2, 6) ∈ envelope_546_i2 := by decide +kernel
theorem children_work_546_i2 : ∀ j, Template HasSnaky 6 (childrenC_546_i2 j) (childrenD_546_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 1 (1, 3)).mono (by decide +kernel)
  · exact row_works_546_i3.mono (by decide +kernel)
theorem row_works_546_i2 : Template HasSnaky 7 required_546_i2 envelope_546_i2 := by
  refine compose HasSnaky 6 childrenC_546_i2 childrenD_546_i2 children_work_546_i2 (2, 6)
    required_546_i2 envelope_546_i2 pivot_mem_546_i2 child_required_sub_546_i2 child_envelope_sub_546_i2 ?_
  intro b hb
  exact common_sub_546_i2 (mem_commonEnvelope childrenD_546_i2 b hb)
def required_546_i1 : Finset Cell := ⟨(([(1, 3), (1, 4), (1, 5), (1, 6), (2, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_546_i1 : Finset Cell := ⟨(([(0, 5), (0, 6), (0, 7), (1, 3), (1, 4), (1, 5), (1, 6), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 6), (3, 7), (4, 5), (4, 6), (4, 7), (5, 5), (5, 6), (5, 7), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_546_i1 : Fin 2 → Finset Cell := ![(placed21 3 (1, 6) required_5), required_546_i2]
def childrenD_546_i1 : Fin 2 → Finset Cell := ![(placed21 3 (1, 6) envelope_5), envelope_546_i2]
theorem common_sub_546_i1 : commonEnvelope childrenD_546_i1 ⊆ insert (2, 3) required_546_i1 := by decide +kernel
theorem child_required_sub_546_i1 : ∀ j, childrenC_546_i1 j ⊆ insert (2, 3) required_546_i1 := by decide +kernel
theorem child_envelope_sub_546_i1 : ∀ j, childrenD_546_i1 j ⊆ envelope_546_i1 := by decide +kernel
theorem pivot_mem_546_i1 : (2, 3) ∈ envelope_546_i1 := by decide +kernel
theorem children_work_546_i1 : ∀ j, Template HasSnaky 7 (childrenC_546_i1 j) (childrenD_546_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 3 (1, 6)).mono (by decide +kernel)
  · exact row_works_546_i2.mono (by decide +kernel)
theorem row_works_546_i1 : Template HasSnaky 8 required_546_i1 envelope_546_i1 := by
  refine compose HasSnaky 7 childrenC_546_i1 childrenD_546_i1 children_work_546_i1 (2, 3)
    required_546_i1 envelope_546_i1 pivot_mem_546_i1 child_required_sub_546_i1 child_envelope_sub_546_i1 ?_
  intro b hb
  exact common_sub_546_i1 (mem_commonEnvelope childrenD_546_i1 b hb)
def required_546_i0 : Finset Cell := ⟨(([(1, 4), (1, 5), (1, 6), (2, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_546_i0 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 5), (0, 6), (0, 7), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 6), (3, 7), (4, 5), (4, 6), (4, 7), (5, 5), (5, 6), (5, 7), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_546_i0 : Fin 4 → Finset Cell := ![(placed21 4 (0, 7) required_19), (placed21 6 (2, 7) required_19), (placed21 4 (0, 7) required_62), required_546_i1]
def childrenD_546_i0 : Fin 4 → Finset Cell := ![(placed21 4 (0, 7) envelope_19), (placed21 6 (2, 7) envelope_19), (placed21 4 (0, 7) envelope_62), envelope_546_i1]
theorem common_sub_546_i0 : commonEnvelope childrenD_546_i0 ⊆ insert (1, 3) required_546_i0 := by decide +kernel
theorem child_required_sub_546_i0 : ∀ j, childrenC_546_i0 j ⊆ insert (1, 3) required_546_i0 := by decide +kernel
theorem child_envelope_sub_546_i0 : ∀ j, childrenD_546_i0 j ⊆ envelope_546_i0 := by decide +kernel
theorem pivot_mem_546_i0 : (1, 3) ∈ envelope_546_i0 := by decide +kernel
theorem children_work_546_i0 : ∀ j, Template HasSnaky 8 (childrenC_546_i0 j) (childrenD_546_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_19 4 (0, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_19 6 (2, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_62 4 (0, 7)).mono (by decide +kernel)
  · exact row_works_546_i1.mono (by decide +kernel)
theorem row_works_546_i0 : Template HasSnaky 9 required_546_i0 envelope_546_i0 := by
  refine compose HasSnaky 8 childrenC_546_i0 childrenD_546_i0 children_work_546_i0 (1, 3)
    required_546_i0 envelope_546_i0 pivot_mem_546_i0 child_required_sub_546_i0 child_envelope_sub_546_i0 ?_
  intro b hb
  exact common_sub_546_i0 (mem_commonEnvelope childrenD_546_i0 b hb)
def required_546 : Finset Cell := ⟨(([(1, 4), (1, 5), (2, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_546 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, 6), (3, 7), (4, 5), (4, 6), (4, 7), (5, 5), (5, 6), (5, 7), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_546 : Fin 4 → Finset Cell := ![(placed21 2 (2, 3) required_10), (placed21 4 (1, 7) required_44), (placed21 2 (2, 3) required_63), required_546_i0]
def childrenD_546 : Fin 4 → Finset Cell := ![(placed21 2 (2, 3) envelope_10), (placed21 4 (1, 7) envelope_44), (placed21 2 (2, 3) envelope_63), envelope_546_i0]
theorem common_sub_546 : commonEnvelope childrenD_546 ⊆ insert (1, 6) required_546 := by decide +kernel
theorem child_required_sub_546 : ∀ j, childrenC_546 j ⊆ insert (1, 6) required_546 := by decide +kernel
theorem child_envelope_sub_546 : ∀ j, childrenD_546 j ⊆ envelope_546 := by decide +kernel
theorem pivot_mem_546 : (1, 6) ∈ envelope_546 := by decide +kernel
theorem children_work_546 : ∀ j, Template HasSnaky 9 (childrenC_546 j) (childrenD_546 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_10 2 (2, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_44 4 (1, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_63 2 (2, 3)).mono (by decide +kernel)
  · exact row_works_546_i0.mono (by decide +kernel)
theorem row_works_546 : Template HasSnaky 10 required_546 envelope_546 := by
  refine compose HasSnaky 9 childrenC_546 childrenD_546 children_work_546 (1, 6)
    required_546 envelope_546 pivot_mem_546 child_required_sub_546 child_envelope_sub_546 ?_
  intro b hb
  exact common_sub_546 (mem_commonEnvelope childrenD_546 b hb)
def required_556_i0 : Finset Cell := ⟨(([(2, 4), (3, 4), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_556_i0 : Finset Cell := ⟨(([(2, 4), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (7, 3), (7, 4), (7, 5), (8, 3), (8, 4), (8, 5), (9, 3), (9, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_556_i0 : Fin 5 → Finset Cell := ![(placed21 4 (2, 7) required_115), (placed21 4 (2, 7) required_171), (placed21 4 (2, 5) required_197), (placed21 0 (2, 3) required_197), (placed21 4 (2, 7) required_285)]
def childrenD_556_i0 : Fin 5 → Finset Cell := ![(placed21 4 (2, 7) envelope_115), (placed21 4 (2, 7) envelope_171), (placed21 4 (2, 5) envelope_197), (placed21 0 (2, 3) envelope_197), (placed21 4 (2, 7) envelope_285)]
theorem common_sub_556_i0 : commonEnvelope childrenD_556_i0 ⊆ insert (5, 4) required_556_i0 := by decide +kernel
theorem child_required_sub_556_i0 : ∀ j, childrenC_556_i0 j ⊆ insert (5, 4) required_556_i0 := by decide +kernel
theorem child_envelope_sub_556_i0 : ∀ j, childrenD_556_i0 j ⊆ envelope_556_i0 := by decide +kernel
theorem pivot_mem_556_i0 : (5, 4) ∈ envelope_556_i0 := by decide +kernel
theorem children_work_556_i0 : ∀ j, Template HasSnaky 8 (childrenC_556_i0 j) (childrenD_556_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_115 4 (2, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_171 4 (2, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_197 4 (2, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_197 0 (2, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_285 4 (2, 7)).mono (by decide +kernel)
theorem row_works_556_i0 : Template HasSnaky 9 required_556_i0 envelope_556_i0 := by
  refine compose HasSnaky 8 childrenC_556_i0 childrenD_556_i0 children_work_556_i0 (5, 4)
    required_556_i0 envelope_556_i0 pivot_mem_556_i0 child_required_sub_556_i0 child_envelope_sub_556_i0 ?_
  intro b hb
  exact common_sub_556_i0 (mem_commonEnvelope childrenD_556_i0 b hb)
def required_556 : Finset Cell := ⟨(([(0, 3), (1, 3), (3, 4), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_556 : Finset Cell := ⟨(([(0, 3), (1, 3), (1, 4), (2, 4), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (7, 3), (7, 4), (7, 5), (8, 3), (8, 4), (8, 5), (9, 3), (9, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_556 : Fin 2 → Finset Cell := ![(placed21 6 (4, 4) required_3), required_556_i0]
def childrenD_556 : Fin 2 → Finset Cell := ![(placed21 6 (4, 4) envelope_3), envelope_556_i0]
theorem common_sub_556 : commonEnvelope childrenD_556 ⊆ insert (2, 4) required_556 := by decide +kernel
theorem child_required_sub_556 : ∀ j, childrenC_556 j ⊆ insert (2, 4) required_556 := by decide +kernel
theorem child_envelope_sub_556 : ∀ j, childrenD_556 j ⊆ envelope_556 := by decide +kernel
theorem pivot_mem_556 : (2, 4) ∈ envelope_556 := by decide +kernel
theorem children_work_556 : ∀ j, Template HasSnaky 9 (childrenC_556 j) (childrenD_556 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_3 6 (4, 4)).mono (by decide +kernel)
  · exact row_works_556_i0.mono (by decide +kernel)
theorem row_works_556 : Template HasSnaky 10 required_556 envelope_556 := by
  refine compose HasSnaky 9 childrenC_556 childrenD_556 children_work_556 (2, 4)
    required_556 envelope_556 pivot_mem_556 child_required_sub_556 child_envelope_sub_556 ?_
  intro b hb
  exact common_sub_556 (mem_commonEnvelope childrenD_556 b hb)
def required_560_i4 : Finset Cell := ⟨(([(3, 1), (3, 4), (4, 1), (4, 4), (5, 1), (5, 4), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_560_i4 : Finset Cell := ⟨(([(2, 1), (3, 1), (3, 4), (4, 1), (4, 2), (4, 4), (5, 1), (5, 2), (5, 3), (5, 4), (6, 2), (6, 4), (6, 5), (7, 2), (7, 5), (8, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_560_i4 : Fin 2 → Finset Cell := ![(placed21 1 (2, 1) required_44), (placed21 4 (3, 5) required_156)]
def childrenD_560_i4 : Fin 2 → Finset Cell := ![(placed21 1 (2, 1) envelope_44), (placed21 4 (3, 5) envelope_156)]
theorem common_sub_560_i4 : commonEnvelope childrenD_560_i4 ⊆ insert (5, 2) required_560_i4 := by decide +kernel
theorem child_required_sub_560_i4 : ∀ j, childrenC_560_i4 j ⊆ insert (5, 2) required_560_i4 := by decide +kernel
theorem child_envelope_sub_560_i4 : ∀ j, childrenD_560_i4 j ⊆ envelope_560_i4 := by decide +kernel
theorem pivot_mem_560_i4 : (5, 2) ∈ envelope_560_i4 := by decide +kernel
theorem children_work_560_i4 : ∀ j, Template HasSnaky 3 (childrenC_560_i4 j) (childrenD_560_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_44 1 (2, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_156 4 (3, 5)).mono (by decide +kernel)
theorem row_works_560_i4 : Template HasSnaky 4 required_560_i4 envelope_560_i4 := by
  refine compose HasSnaky 3 childrenC_560_i4 childrenD_560_i4 children_work_560_i4 (5, 2)
    required_560_i4 envelope_560_i4 pivot_mem_560_i4 child_required_sub_560_i4 child_envelope_sub_560_i4 ?_
  intro b hb
  exact common_sub_560_i4 (mem_commonEnvelope childrenD_560_i4 b hb)
def required_560_i3 : Finset Cell := ⟨(([(3, 1), (3, 2), (3, 4), (4, 1), (4, 4), (5, 4), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_560_i3 : Finset Cell := ⟨(([(0, 2), (1, 2), (2, 1), (2, 2), (3, 1), (3, 2), (3, 4), (4, 1), (4, 2), (4, 4), (5, 1), (5, 2), (5, 3), (5, 4), (6, 1), (6, 2), (6, 4), (6, 5), (7, 2), (7, 5), (8, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_560_i3 : Fin 3 → Finset Cell := ![(placed21 5 (6, 1) required_44), (placed21 5 (6, 1) required_52), required_560_i4]
def childrenD_560_i3 : Fin 3 → Finset Cell := ![(placed21 5 (6, 1) envelope_44), (placed21 5 (6, 1) envelope_52), envelope_560_i4]
theorem common_sub_560_i3 : commonEnvelope childrenD_560_i3 ⊆ insert (5, 1) required_560_i3 := by decide +kernel
theorem child_required_sub_560_i3 : ∀ j, childrenC_560_i3 j ⊆ insert (5, 1) required_560_i3 := by decide +kernel
theorem child_envelope_sub_560_i3 : ∀ j, childrenD_560_i3 j ⊆ envelope_560_i3 := by decide +kernel
theorem pivot_mem_560_i3 : (5, 1) ∈ envelope_560_i3 := by decide +kernel
theorem children_work_560_i3 : ∀ j, Template HasSnaky 4 (childrenC_560_i3 j) (childrenD_560_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_44 5 (6, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_52 5 (6, 1)).mono (by decide +kernel)
  · exact row_works_560_i4.mono (by decide +kernel)
theorem row_works_560_i3 : Template HasSnaky 5 required_560_i3 envelope_560_i3 := by
  refine compose HasSnaky 4 childrenC_560_i3 childrenD_560_i3 children_work_560_i3 (5, 1)
    required_560_i3 envelope_560_i3 pivot_mem_560_i3 child_required_sub_560_i3 child_envelope_sub_560_i3 ?_
  intro b hb
  exact common_sub_560_i3 (mem_commonEnvelope childrenD_560_i3 b hb)
def required_560_i2 : Finset Cell := ⟨(([(3, 1), (3, 2), (3, 3), (3, 4), (4, 4), (5, 4), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_560_i2 : Finset Cell := ⟨(([(0, 2), (1, 2), (2, 1), (2, 2), (3, 1), (3, 2), (3, 3), (3, 4), (4, 0), (4, 1), (4, 2), (4, 4), (5, 1), (5, 2), (5, 3), (5, 4), (6, 1), (6, 2), (6, 4), (6, 5), (7, 2), (7, 5), (8, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_560_i2 : Fin 2 → Finset Cell := ![(placed21 3 (3, 4) required_5), required_560_i3]
def childrenD_560_i2 : Fin 2 → Finset Cell := ![(placed21 3 (3, 4) envelope_5), envelope_560_i3]
theorem common_sub_560_i2 : commonEnvelope childrenD_560_i2 ⊆ insert (4, 1) required_560_i2 := by decide +kernel
theorem child_required_sub_560_i2 : ∀ j, childrenC_560_i2 j ⊆ insert (4, 1) required_560_i2 := by decide +kernel
theorem child_envelope_sub_560_i2 : ∀ j, childrenD_560_i2 j ⊆ envelope_560_i2 := by decide +kernel
theorem pivot_mem_560_i2 : (4, 1) ∈ envelope_560_i2 := by decide +kernel
theorem children_work_560_i2 : ∀ j, Template HasSnaky 5 (childrenC_560_i2 j) (childrenD_560_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 3 (3, 4)).mono (by decide +kernel)
  · exact row_works_560_i3.mono (by decide +kernel)
theorem row_works_560_i2 : Template HasSnaky 6 required_560_i2 envelope_560_i2 := by
  refine compose HasSnaky 5 childrenC_560_i2 childrenD_560_i2 children_work_560_i2 (4, 1)
    required_560_i2 envelope_560_i2 pivot_mem_560_i2 child_required_sub_560_i2 child_envelope_sub_560_i2 ?_
  intro b hb
  exact common_sub_560_i2 (mem_commonEnvelope childrenD_560_i2 b hb)
def required_560_i1 : Finset Cell := ⟨(([(3, 1), (3, 2), (3, 3), (3, 4), (4, 4), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_560_i1 : Finset Cell := ⟨(([(0, 2), (1, 2), (2, 1), (2, 2), (2, 4), (2, 5), (3, 1), (3, 2), (3, 3), (3, 4), (4, 0), (4, 1), (4, 2), (4, 4), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (6, 1), (6, 2), (6, 4), (6, 5), (7, 2), (7, 5), (8, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_560_i1 : Fin 2 → Finset Cell := ![(placed21 7 (6, 5) required_153), required_560_i2]
def childrenD_560_i1 : Fin 2 → Finset Cell := ![(placed21 7 (6, 5) envelope_153), envelope_560_i2]
theorem common_sub_560_i1 : commonEnvelope childrenD_560_i1 ⊆ insert (6, 5) required_560_i1 := by decide +kernel
theorem child_required_sub_560_i1 : ∀ j, childrenC_560_i1 j ⊆ insert (6, 5) required_560_i1 := by decide +kernel
theorem child_envelope_sub_560_i1 : ∀ j, childrenD_560_i1 j ⊆ envelope_560_i1 := by decide +kernel
theorem pivot_mem_560_i1 : (6, 5) ∈ envelope_560_i1 := by decide +kernel
theorem children_work_560_i1 : ∀ j, Template HasSnaky 6 (childrenC_560_i1 j) (childrenD_560_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_153 7 (6, 5)).mono (by decide +kernel)
  · exact row_works_560_i2.mono (by decide +kernel)
theorem row_works_560_i1 : Template HasSnaky 7 required_560_i1 envelope_560_i1 := by
  refine compose HasSnaky 6 childrenC_560_i1 childrenD_560_i1 children_work_560_i1 (6, 5)
    required_560_i1 envelope_560_i1 pivot_mem_560_i1 child_required_sub_560_i1 child_envelope_sub_560_i1 ?_
  intro b hb
  exact common_sub_560_i1 (mem_commonEnvelope childrenD_560_i1 b hb)
def required_560_i0 : Finset Cell := ⟨(([(3, 2), (3, 3), (3, 4), (4, 4), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_560_i0 : Finset Cell := ⟨(([(0, 2), (1, 2), (2, 1), (2, 2), (2, 4), (2, 5), (3, 1), (3, 2), (3, 3), (3, 4), (4, 0), (4, 1), (4, 2), (4, 4), (4, 5), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (6, 1), (6, 2), (6, 4), (6, 5), (7, 2), (7, 5), (8, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_560_i0 : Fin 2 → Finset Cell := ![(placed21 1 (3, 1) required_5), required_560_i1]
def childrenD_560_i0 : Fin 2 → Finset Cell := ![(placed21 1 (3, 1) envelope_5), envelope_560_i1]
theorem common_sub_560_i0 : commonEnvelope childrenD_560_i0 ⊆ insert (3, 1) required_560_i0 := by decide +kernel
theorem child_required_sub_560_i0 : ∀ j, childrenC_560_i0 j ⊆ insert (3, 1) required_560_i0 := by decide +kernel
theorem child_envelope_sub_560_i0 : ∀ j, childrenD_560_i0 j ⊆ envelope_560_i0 := by decide +kernel
theorem pivot_mem_560_i0 : (3, 1) ∈ envelope_560_i0 := by decide +kernel
theorem children_work_560_i0 : ∀ j, Template HasSnaky 7 (childrenC_560_i0 j) (childrenD_560_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 1 (3, 1)).mono (by decide +kernel)
  · exact row_works_560_i1.mono (by decide +kernel)
theorem row_works_560_i0 : Template HasSnaky 8 required_560_i0 envelope_560_i0 := by
  refine compose HasSnaky 7 childrenC_560_i0 childrenD_560_i0 children_work_560_i0 (3, 1)
    required_560_i0 envelope_560_i0 pivot_mem_560_i0 child_required_sub_560_i0 child_envelope_sub_560_i0 ?_
  intro b hb
  exact common_sub_560_i0 (mem_commonEnvelope childrenD_560_i0 b hb)
def required_560_i5 : Finset Cell := ⟨(([(3, 2), (3, 3), (3, 4), (4, 4), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_560_i5 : Finset Cell := ⟨(([(1, 5), (2, 4), (2, 5), (3, 1), (3, 2), (3, 3), (3, 4), (4, 0), (4, 1), (4, 2), (4, 4), (4, 5), (4, 6), (4, 7), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (6, 0), (6, 1), (6, 2), (6, 3), (6, 5), (7, 5), (8, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_560_i5 : Fin 3 → Finset Cell := ![(placed21 0 (3, 1) required_227), (placed21 7 (6, 5) required_245), (placed21 4 (2, 7) required_274)]
def childrenD_560_i5 : Fin 3 → Finset Cell := ![(placed21 0 (3, 1) envelope_227), (placed21 7 (6, 5) envelope_245), (placed21 4 (2, 7) envelope_274)]
theorem common_sub_560_i5 : commonEnvelope childrenD_560_i5 ⊆ insert (5, 3) required_560_i5 := by decide +kernel
theorem child_required_sub_560_i5 : ∀ j, childrenC_560_i5 j ⊆ insert (5, 3) required_560_i5 := by decide +kernel
theorem child_envelope_sub_560_i5 : ∀ j, childrenD_560_i5 j ⊆ envelope_560_i5 := by decide +kernel
theorem pivot_mem_560_i5 : (5, 3) ∈ envelope_560_i5 := by decide +kernel
theorem children_work_560_i5 : ∀ j, Template HasSnaky 5 (childrenC_560_i5 j) (childrenD_560_i5 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_227 0 (3, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_245 7 (6, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_274 4 (2, 7)).mono (by decide +kernel)
theorem row_works_560_i5 : Template HasSnaky 6 required_560_i5 envelope_560_i5 := by
  refine compose HasSnaky 5 childrenC_560_i5 childrenD_560_i5 children_work_560_i5 (5, 3)
    required_560_i5 envelope_560_i5 pivot_mem_560_i5 child_required_sub_560_i5 child_envelope_sub_560_i5 ?_
  intro b hb
  exact common_sub_560_i5 (mem_commonEnvelope childrenD_560_i5 b hb)
def required_560 : Finset Cell := ⟨(([(0, 3), (1, 3), (3, 2), (3, 3), (3, 4), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_560 : Finset Cell := ⟨(([(0, 2), (0, 3), (1, 2), (1, 3), (1, 5), (2, 1), (2, 2), (2, 4), (2, 5), (3, 1), (3, 2), (3, 3), (3, 4), (4, 0), (4, 1), (4, 2), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (8, 0), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (9, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_560 : Fin 8 → Finset Cell := ![(placed21 3 (1, 5) required_67), (placed21 0 (2, 1) required_228), (placed21 4 (2, 5) required_373), (placed21 4 (2, 7) required_435), (placed21 0 (3, 1) required_531), required_560_i0, required_560_i5, (placed21 4 (0, 5) required_559)]
def childrenD_560 : Fin 8 → Finset Cell := ![(placed21 3 (1, 5) envelope_67), (placed21 0 (2, 1) envelope_228), (placed21 4 (2, 5) envelope_373), (placed21 4 (2, 7) envelope_435), (placed21 0 (3, 1) envelope_531), envelope_560_i0, envelope_560_i5, (placed21 4 (0, 5) envelope_559)]
theorem common_sub_560 : commonEnvelope childrenD_560 ⊆ insert (5, 4) required_560 := by decide +kernel
theorem child_required_sub_560 : ∀ j, childrenC_560 j ⊆ insert (5, 4) required_560 := by decide +kernel
theorem child_envelope_sub_560 : ∀ j, childrenD_560 j ⊆ envelope_560 := by decide +kernel
theorem pivot_mem_560 : (5, 4) ∈ envelope_560 := by decide +kernel
theorem children_work_560 : ∀ j, Template HasSnaky 9 (childrenC_560 j) (childrenD_560 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_67 3 (1, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_228 0 (2, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_373 4 (2, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_435 4 (2, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_531 0 (3, 1)).mono (by decide +kernel)
  · exact row_works_560_i0.mono (by decide +kernel)
  · exact row_works_560_i5.mono (by decide +kernel)
  · exact (placed21_template row_works_559 4 (0, 5)).mono (by decide +kernel)
theorem row_works_560 : Template HasSnaky 10 required_560 envelope_560 := by
  refine compose HasSnaky 9 childrenC_560 childrenD_560 children_work_560 (5, 4)
    required_560 envelope_560 pivot_mem_560 child_required_sub_560 child_envelope_sub_560 ?_
  intro b hb
  exact common_sub_560 (mem_commonEnvelope childrenD_560 b hb)
def required_563_i2 : Finset Cell := ⟨(([(1, 3), (1, 4), (1, 5), (2, 4), (2, 5), (3, 5), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_563_i2 : Finset Cell := ⟨(([(1, 3), (1, 4), (1, 5), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 2), (4, 3), (4, 4), (4, 5), (5, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_563_i2 : Fin 2 → Finset Cell := ![(placed21 7 (2, 7) required_0), (placed21 4 (1, 7) required_393)]
def childrenD_563_i2 : Fin 2 → Finset Cell := ![(placed21 7 (2, 7) envelope_0), (placed21 4 (1, 7) envelope_393)]
theorem common_sub_563_i2 : commonEnvelope childrenD_563_i2 ⊆ insert (2, 6) required_563_i2 := by decide +kernel
theorem child_required_sub_563_i2 : ∀ j, childrenC_563_i2 j ⊆ insert (2, 6) required_563_i2 := by decide +kernel
theorem child_envelope_sub_563_i2 : ∀ j, childrenD_563_i2 j ⊆ envelope_563_i2 := by decide +kernel
theorem pivot_mem_563_i2 : (2, 6) ∈ envelope_563_i2 := by decide +kernel
theorem children_work_563_i2 : ∀ j, Template HasSnaky 6 (childrenC_563_i2 j) (childrenD_563_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 7 (2, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_393 4 (1, 7)).mono (by decide +kernel)
theorem row_works_563_i2 : Template HasSnaky 7 required_563_i2 envelope_563_i2 := by
  refine compose HasSnaky 6 childrenC_563_i2 childrenD_563_i2 children_work_563_i2 (2, 6)
    required_563_i2 envelope_563_i2 pivot_mem_563_i2 child_required_sub_563_i2 child_envelope_sub_563_i2 ?_
  intro b hb
  exact common_sub_563_i2 (mem_commonEnvelope childrenD_563_i2 b hb)
def required_563_i1 : Finset Cell := ⟨(([(1, 3), (1, 4), (1, 5), (2, 5), (3, 5), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_563_i1 : Finset Cell := ⟨(([(1, 3), (1, 4), (1, 5), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 2), (4, 3), (4, 4), (4, 5), (5, 3), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_563_i1 : Fin 2 → Finset Cell := ![(placed21 6 (5, 5) required_0), required_563_i2]
def childrenD_563_i1 : Fin 2 → Finset Cell := ![(placed21 6 (5, 5) envelope_0), envelope_563_i2]
theorem common_sub_563_i1 : commonEnvelope childrenD_563_i1 ⊆ insert (2, 4) required_563_i1 := by decide +kernel
theorem child_required_sub_563_i1 : ∀ j, childrenC_563_i1 j ⊆ insert (2, 4) required_563_i1 := by decide +kernel
theorem child_envelope_sub_563_i1 : ∀ j, childrenD_563_i1 j ⊆ envelope_563_i1 := by decide +kernel
theorem pivot_mem_563_i1 : (2, 4) ∈ envelope_563_i1 := by decide +kernel
theorem children_work_563_i1 : ∀ j, Template HasSnaky 7 (childrenC_563_i1 j) (childrenD_563_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 6 (5, 5)).mono (by decide +kernel)
  · exact row_works_563_i2.mono (by decide +kernel)
theorem row_works_563_i1 : Template HasSnaky 8 required_563_i1 envelope_563_i1 := by
  refine compose HasSnaky 7 childrenC_563_i1 childrenD_563_i1 children_work_563_i1 (2, 4)
    required_563_i1 envelope_563_i1 pivot_mem_563_i1 child_required_sub_563_i1 child_envelope_sub_563_i1 ?_
  intro b hb
  exact common_sub_563_i1 (mem_commonEnvelope childrenD_563_i1 b hb)
def required_563_i6 : Finset Cell := ⟨(([(1, 3), (2, 5), (3, 4), (3, 5), (3, 6), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_563_i6 : Finset Cell := ⟨(([(0, 3), (1, 3), (2, 2), (2, 3), (2, 5), (2, 6), (2, 7), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_563_i6 : Fin 2 → Finset Cell := ![(placed21 6 (3, 7) required_11), (placed21 7 (4, 6) required_38)]
def childrenD_563_i6 : Fin 2 → Finset Cell := ![(placed21 6 (3, 7) envelope_11), (placed21 7 (4, 6) envelope_38)]
theorem common_sub_563_i6 : commonEnvelope childrenD_563_i6 ⊆ insert (3, 3) required_563_i6 := by decide +kernel
theorem child_required_sub_563_i6 : ∀ j, childrenC_563_i6 j ⊆ insert (3, 3) required_563_i6 := by decide +kernel
theorem child_envelope_sub_563_i6 : ∀ j, childrenD_563_i6 j ⊆ envelope_563_i6 := by decide +kernel
theorem pivot_mem_563_i6 : (3, 3) ∈ envelope_563_i6 := by decide +kernel
theorem children_work_563_i6 : ∀ j, Template HasSnaky 2 (childrenC_563_i6 j) (childrenD_563_i6 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_11 6 (3, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_38 7 (4, 6)).mono (by decide +kernel)
theorem row_works_563_i6 : Template HasSnaky 3 required_563_i6 envelope_563_i6 := by
  refine compose HasSnaky 2 childrenC_563_i6 childrenD_563_i6 children_work_563_i6 (3, 3)
    required_563_i6 envelope_563_i6 pivot_mem_563_i6 child_required_sub_563_i6 child_envelope_sub_563_i6 ?_
  intro b hb
  exact common_sub_563_i6 (mem_commonEnvelope childrenD_563_i6 b hb)
def required_563_i5 : Finset Cell := ⟨(([(1, 3), (2, 5), (3, 4), (3, 5), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_563_i5 : Finset Cell := ⟨(([(0, 3), (1, 3), (2, 2), (2, 3), (2, 5), (2, 6), (2, 7), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 2), (4, 3), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_563_i5 : Fin 2 → Finset Cell := ![(placed21 4 (3, 7) required_15), required_563_i6]
def childrenD_563_i5 : Fin 2 → Finset Cell := ![(placed21 4 (3, 7) envelope_15), envelope_563_i6]
theorem common_sub_563_i5 : commonEnvelope childrenD_563_i5 ⊆ insert (3, 6) required_563_i5 := by decide +kernel
theorem child_required_sub_563_i5 : ∀ j, childrenC_563_i5 j ⊆ insert (3, 6) required_563_i5 := by decide +kernel
theorem child_envelope_sub_563_i5 : ∀ j, childrenD_563_i5 j ⊆ envelope_563_i5 := by decide +kernel
theorem pivot_mem_563_i5 : (3, 6) ∈ envelope_563_i5 := by decide +kernel
theorem children_work_563_i5 : ∀ j, Template HasSnaky 3 (childrenC_563_i5 j) (childrenD_563_i5 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_15 4 (3, 7)).mono (by decide +kernel)
  · exact row_works_563_i6.mono (by decide +kernel)
theorem row_works_563_i5 : Template HasSnaky 4 required_563_i5 envelope_563_i5 := by
  refine compose HasSnaky 3 childrenC_563_i5 childrenD_563_i5 children_work_563_i5 (3, 6)
    required_563_i5 envelope_563_i5 pivot_mem_563_i5 child_required_sub_563_i5 child_envelope_sub_563_i5 ?_
  intro b hb
  exact common_sub_563_i5 (mem_commonEnvelope childrenD_563_i5 b hb)
def required_563_i4 : Finset Cell := ⟨(([(1, 3), (1, 5), (2, 5), (3, 5), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_563_i4 : Finset Cell := ⟨(([(0, 3), (0, 5), (1, 3), (1, 5), (2, 2), (2, 3), (2, 5), (2, 6), (2, 7), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 2), (4, 3), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_563_i4 : Fin 2 → Finset Cell := ![(placed21 4 (0, 5) required_0), required_563_i5]
def childrenD_563_i4 : Fin 2 → Finset Cell := ![(placed21 4 (0, 5) envelope_0), envelope_563_i5]
theorem common_sub_563_i4 : commonEnvelope childrenD_563_i4 ⊆ insert (3, 4) required_563_i4 := by decide +kernel
theorem child_required_sub_563_i4 : ∀ j, childrenC_563_i4 j ⊆ insert (3, 4) required_563_i4 := by decide +kernel
theorem child_envelope_sub_563_i4 : ∀ j, childrenD_563_i4 j ⊆ envelope_563_i4 := by decide +kernel
theorem pivot_mem_563_i4 : (3, 4) ∈ envelope_563_i4 := by decide +kernel
theorem children_work_563_i4 : ∀ j, Template HasSnaky 4 (childrenC_563_i4 j) (childrenD_563_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 4 (0, 5)).mono (by decide +kernel)
  · exact row_works_563_i5.mono (by decide +kernel)
theorem row_works_563_i4 : Template HasSnaky 5 required_563_i4 envelope_563_i4 := by
  refine compose HasSnaky 4 childrenC_563_i4 childrenD_563_i4 children_work_563_i4 (3, 4)
    required_563_i4 envelope_563_i4 pivot_mem_563_i4 child_required_sub_563_i4 child_envelope_sub_563_i4 ?_
  intro b hb
  exact common_sub_563_i4 (mem_commonEnvelope childrenD_563_i4 b hb)
def required_563_i3 : Finset Cell := ⟨(([(1, 3), (1, 5), (2, 5), (3, 5), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_563_i3 : Finset Cell := ⟨(([(0, 3), (0, 5), (1, 3), (1, 5), (2, 2), (2, 3), (2, 5), (2, 6), (2, 7), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 2), (4, 3), (4, 4), (4, 5), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_563_i3 : Fin 2 → Finset Cell := ![(placed21 4 (1, 5) required_5), required_563_i4]
def childrenD_563_i3 : Fin 2 → Finset Cell := ![(placed21 4 (1, 5) envelope_5), envelope_563_i4]
theorem common_sub_563_i3 : commonEnvelope childrenD_563_i3 ⊆ insert (4, 4) required_563_i3 := by decide +kernel
theorem child_required_sub_563_i3 : ∀ j, childrenC_563_i3 j ⊆ insert (4, 4) required_563_i3 := by decide +kernel
theorem child_envelope_sub_563_i3 : ∀ j, childrenD_563_i3 j ⊆ envelope_563_i3 := by decide +kernel
theorem pivot_mem_563_i3 : (4, 4) ∈ envelope_563_i3 := by decide +kernel
theorem children_work_563_i3 : ∀ j, Template HasSnaky 5 (childrenC_563_i3 j) (childrenD_563_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 4 (1, 5)).mono (by decide +kernel)
  · exact row_works_563_i4.mono (by decide +kernel)
theorem row_works_563_i3 : Template HasSnaky 6 required_563_i3 envelope_563_i3 := by
  refine compose HasSnaky 5 childrenC_563_i3 childrenD_563_i3 children_work_563_i3 (4, 4)
    required_563_i3 envelope_563_i3 pivot_mem_563_i3 child_required_sub_563_i3 child_envelope_sub_563_i3 ?_
  intro b hb
  exact common_sub_563_i3 (mem_commonEnvelope childrenD_563_i3 b hb)
def required_563_i0 : Finset Cell := ⟨(([(1, 3), (1, 4), (1, 5), (2, 5), (3, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_563_i0 : Finset Cell := ⟨(([(0, 3), (0, 5), (1, 3), (1, 4), (1, 5), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 2), (4, 3), (4, 4), (4, 5), (5, 3), (5, 4), (5, 5), (5, 6), (6, 4), (6, 5), (6, 6), (7, 4), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_563_i0 : Fin 3 → Finset Cell := ![(placed21 1 (1, 4) required_18), required_563_i1, required_563_i3]
def childrenD_563_i0 : Fin 3 → Finset Cell := ![(placed21 1 (1, 4) envelope_18), envelope_563_i1, envelope_563_i3]
theorem common_sub_563_i0 : commonEnvelope childrenD_563_i0 ⊆ insert (4, 5) required_563_i0 := by decide +kernel
theorem child_required_sub_563_i0 : ∀ j, childrenC_563_i0 j ⊆ insert (4, 5) required_563_i0 := by decide +kernel
theorem child_envelope_sub_563_i0 : ∀ j, childrenD_563_i0 j ⊆ envelope_563_i0 := by decide +kernel
theorem pivot_mem_563_i0 : (4, 5) ∈ envelope_563_i0 := by decide +kernel
theorem children_work_563_i0 : ∀ j, Template HasSnaky 8 (childrenC_563_i0 j) (childrenD_563_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_18 1 (1, 4)).mono (by decide +kernel)
  · exact row_works_563_i1.mono (by decide +kernel)
  · exact row_works_563_i3.mono (by decide +kernel)
theorem row_works_563_i0 : Template HasSnaky 9 required_563_i0 envelope_563_i0 := by
  refine compose HasSnaky 8 childrenC_563_i0 childrenD_563_i0 children_work_563_i0 (4, 5)
    required_563_i0 envelope_563_i0 pivot_mem_563_i0 child_required_sub_563_i0 child_envelope_sub_563_i0 ?_
  intro b hb
  exact common_sub_563_i0 (mem_commonEnvelope childrenD_563_i0 b hb)
def required_563 : Finset Cell := ⟨(([(1, 3), (1, 4), (1, 5), (2, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_563 : Finset Cell := ⟨(([(0, 3), (0, 5), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (6, 3), (6, 4), (6, 5), (6, 6), (7, 4), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_563 : Fin 8 → Finset Cell := ![(placed21 4 (0, 7) required_134), (placed21 4 (0, 7) required_180), (placed21 4 (1, 8) required_258), (placed21 4 (0, 8) required_435), (placed21 0 (0, 2) required_507), required_563_i0, required_561, (placed21 0 (0, 1) required_562)]
def childrenD_563 : Fin 8 → Finset Cell := ![(placed21 4 (0, 7) envelope_134), (placed21 4 (0, 7) envelope_180), (placed21 4 (1, 8) envelope_258), (placed21 4 (0, 8) envelope_435), (placed21 0 (0, 2) envelope_507), envelope_563_i0, envelope_561, (placed21 0 (0, 1) envelope_562)]
theorem common_sub_563 : commonEnvelope childrenD_563 ⊆ insert (3, 5) required_563 := by decide +kernel
theorem child_required_sub_563 : ∀ j, childrenC_563 j ⊆ insert (3, 5) required_563 := by decide +kernel
theorem child_envelope_sub_563 : ∀ j, childrenD_563 j ⊆ envelope_563 := by decide +kernel
theorem pivot_mem_563 : (3, 5) ∈ envelope_563 := by decide +kernel
theorem children_work_563 : ∀ j, Template HasSnaky 9 (childrenC_563 j) (childrenD_563 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_134 4 (0, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_180 4 (0, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_258 4 (1, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_435 4 (0, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_507 0 (0, 2)).mono (by decide +kernel)
  · exact row_works_563_i0.mono (by decide +kernel)
  · exact row_works_561.mono (by decide +kernel)
  · exact (placed21_template row_works_562 0 (0, 1)).mono (by decide +kernel)
theorem row_works_563 : Template HasSnaky 10 required_563 envelope_563 := by
  refine compose HasSnaky 9 childrenC_563 childrenD_563 children_work_563 (3, 5)
    required_563 envelope_563 pivot_mem_563 child_required_sub_563 child_envelope_sub_563 ?_
  intro b hb
  exact common_sub_563 (mem_commonEnvelope childrenD_563 b hb)
def height_546_i4 : ℕ := 5
def childrenH_546_i4 : Fin 3 → ℕ := ![height_25, height_27, height_37]
theorem height_exact_546_i4 : height_546_i4 = 1 + Finset.univ.sup childrenH_546_i4 := by decide +kernel
theorem required_origin_546_i4 : ∀ x ∈ required_546_i4,
    (∃ j, x ∈ childrenC_546_i4 j) ∨ ∀ j, x ∈ childrenD_546_i4 j := by decide +kernel
theorem required_exact_546_i4 : required_546_i4 =
    ((Finset.univ.biUnion childrenC_546_i4) ∪ commonEnvelope childrenD_546_i4).erase (3, 6) := by
  exact required_eq_combination childrenC_546_i4 childrenD_546_i4 (3, 6) required_546_i4
    (by decide +kernel) child_required_sub_546_i4 common_sub_546_i4 required_origin_546_i4
theorem envelope_origin_546_i4 : ∀ x ∈ envelope_546_i4,
    x = (3, 6) ∨ ∃ j, x ∈ childrenD_546_i4 j := by decide +kernel
theorem envelope_exact_546_i4 : envelope_546_i4 =
    insert (3, 6) (Finset.univ.biUnion childrenD_546_i4) := by
  exact envelope_eq_combination childrenD_546_i4 (3, 6) envelope_546_i4
    pivot_mem_546_i4 child_envelope_sub_546_i4 envelope_origin_546_i4
def checked_546_i4 : CheckedCard where
  required := required_546_i4
  envelope := envelope_546_i4
  height := height_546_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_546_i4
def height_546_i3 : ℕ := 6
def childrenH_546_i3 : Fin 2 → ℕ := ![height_5, height_546_i4]
theorem height_exact_546_i3 : height_546_i3 = 1 + Finset.univ.sup childrenH_546_i3 := by decide +kernel
theorem required_origin_546_i3 : ∀ x ∈ required_546_i3,
    (∃ j, x ∈ childrenC_546_i3 j) ∨ ∀ j, x ∈ childrenD_546_i3 j := by decide +kernel
theorem required_exact_546_i3 : required_546_i3 =
    ((Finset.univ.biUnion childrenC_546_i3) ∪ commonEnvelope childrenD_546_i3).erase (0, 6) := by
  exact required_eq_combination childrenC_546_i3 childrenD_546_i3 (0, 6) required_546_i3
    (by decide +kernel) child_required_sub_546_i3 common_sub_546_i3 required_origin_546_i3
theorem envelope_origin_546_i3 : ∀ x ∈ envelope_546_i3,
    x = (0, 6) ∨ ∃ j, x ∈ childrenD_546_i3 j := by decide +kernel
theorem envelope_exact_546_i3 : envelope_546_i3 =
    insert (0, 6) (Finset.univ.biUnion childrenD_546_i3) := by
  exact envelope_eq_combination childrenD_546_i3 (0, 6) envelope_546_i3
    pivot_mem_546_i3 child_envelope_sub_546_i3 envelope_origin_546_i3
def checked_546_i3 : CheckedCard where
  required := required_546_i3
  envelope := envelope_546_i3
  height := height_546_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_546_i3
def height_546_i2 : ℕ := 7
def childrenH_546_i2 : Fin 2 → ℕ := ![height_5, height_546_i3]
theorem height_exact_546_i2 : height_546_i2 = 1 + Finset.univ.sup childrenH_546_i2 := by decide +kernel
theorem required_origin_546_i2 : ∀ x ∈ required_546_i2,
    (∃ j, x ∈ childrenC_546_i2 j) ∨ ∀ j, x ∈ childrenD_546_i2 j := by decide +kernel
theorem required_exact_546_i2 : required_546_i2 =
    ((Finset.univ.biUnion childrenC_546_i2) ∪ commonEnvelope childrenD_546_i2).erase (2, 6) := by
  exact required_eq_combination childrenC_546_i2 childrenD_546_i2 (2, 6) required_546_i2
    (by decide +kernel) child_required_sub_546_i2 common_sub_546_i2 required_origin_546_i2
theorem envelope_origin_546_i2 : ∀ x ∈ envelope_546_i2,
    x = (2, 6) ∨ ∃ j, x ∈ childrenD_546_i2 j := by decide +kernel
theorem envelope_exact_546_i2 : envelope_546_i2 =
    insert (2, 6) (Finset.univ.biUnion childrenD_546_i2) := by
  exact envelope_eq_combination childrenD_546_i2 (2, 6) envelope_546_i2
    pivot_mem_546_i2 child_envelope_sub_546_i2 envelope_origin_546_i2
def checked_546_i2 : CheckedCard where
  required := required_546_i2
  envelope := envelope_546_i2
  height := height_546_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_546_i2
def height_546_i1 : ℕ := 8
def childrenH_546_i1 : Fin 2 → ℕ := ![height_5, height_546_i2]
theorem height_exact_546_i1 : height_546_i1 = 1 + Finset.univ.sup childrenH_546_i1 := by decide +kernel
theorem required_origin_546_i1 : ∀ x ∈ required_546_i1,
    (∃ j, x ∈ childrenC_546_i1 j) ∨ ∀ j, x ∈ childrenD_546_i1 j := by decide +kernel
theorem required_exact_546_i1 : required_546_i1 =
    ((Finset.univ.biUnion childrenC_546_i1) ∪ commonEnvelope childrenD_546_i1).erase (2, 3) := by
  exact required_eq_combination childrenC_546_i1 childrenD_546_i1 (2, 3) required_546_i1
    (by decide +kernel) child_required_sub_546_i1 common_sub_546_i1 required_origin_546_i1
theorem envelope_origin_546_i1 : ∀ x ∈ envelope_546_i1,
    x = (2, 3) ∨ ∃ j, x ∈ childrenD_546_i1 j := by decide +kernel
theorem envelope_exact_546_i1 : envelope_546_i1 =
    insert (2, 3) (Finset.univ.biUnion childrenD_546_i1) := by
  exact envelope_eq_combination childrenD_546_i1 (2, 3) envelope_546_i1
    pivot_mem_546_i1 child_envelope_sub_546_i1 envelope_origin_546_i1
def checked_546_i1 : CheckedCard where
  required := required_546_i1
  envelope := envelope_546_i1
  height := height_546_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_546_i1
def height_546_i0 : ℕ := 9
def childrenH_546_i0 : Fin 4 → ℕ := ![height_19, height_19, height_62, height_546_i1]
theorem height_exact_546_i0 : height_546_i0 = 1 + Finset.univ.sup childrenH_546_i0 := by decide +kernel
theorem required_origin_546_i0 : ∀ x ∈ required_546_i0,
    (∃ j, x ∈ childrenC_546_i0 j) ∨ ∀ j, x ∈ childrenD_546_i0 j := by decide +kernel
theorem required_exact_546_i0 : required_546_i0 =
    ((Finset.univ.biUnion childrenC_546_i0) ∪ commonEnvelope childrenD_546_i0).erase (1, 3) := by
  exact required_eq_combination childrenC_546_i0 childrenD_546_i0 (1, 3) required_546_i0
    (by decide +kernel) child_required_sub_546_i0 common_sub_546_i0 required_origin_546_i0
theorem envelope_origin_546_i0 : ∀ x ∈ envelope_546_i0,
    x = (1, 3) ∨ ∃ j, x ∈ childrenD_546_i0 j := by decide +kernel
theorem envelope_exact_546_i0 : envelope_546_i0 =
    insert (1, 3) (Finset.univ.biUnion childrenD_546_i0) := by
  exact envelope_eq_combination childrenD_546_i0 (1, 3) envelope_546_i0
    pivot_mem_546_i0 child_envelope_sub_546_i0 envelope_origin_546_i0
def checked_546_i0 : CheckedCard where
  required := required_546_i0
  envelope := envelope_546_i0
  height := height_546_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_546_i0
def height_546 : ℕ := 10
def childrenH_546 : Fin 4 → ℕ := ![height_10, height_44, height_63, height_546_i0]
theorem height_exact_546 : height_546 = 1 + Finset.univ.sup childrenH_546 := by decide +kernel
theorem required_origin_546 : ∀ x ∈ required_546,
    (∃ j, x ∈ childrenC_546 j) ∨ ∀ j, x ∈ childrenD_546 j := by decide +kernel
theorem required_exact_546 : required_546 =
    ((Finset.univ.biUnion childrenC_546) ∪ commonEnvelope childrenD_546).erase (1, 6) := by
  exact required_eq_combination childrenC_546 childrenD_546 (1, 6) required_546
    (by decide +kernel) child_required_sub_546 common_sub_546 required_origin_546
theorem envelope_origin_546 : ∀ x ∈ envelope_546,
    x = (1, 6) ∨ ∃ j, x ∈ childrenD_546 j := by decide +kernel
theorem envelope_exact_546 : envelope_546 =
    insert (1, 6) (Finset.univ.biUnion childrenD_546) := by
  exact envelope_eq_combination childrenD_546 (1, 6) envelope_546
    pivot_mem_546 child_envelope_sub_546 envelope_origin_546
def checked_546 : CheckedCard where
  required := required_546
  envelope := envelope_546
  height := height_546
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_546
def height_556_i0 : ℕ := 9
def childrenH_556_i0 : Fin 5 → ℕ := ![height_115, height_171, height_197, height_197, height_285]
theorem height_exact_556_i0 : height_556_i0 = 1 + Finset.univ.sup childrenH_556_i0 := by decide +kernel
theorem required_origin_556_i0 : ∀ x ∈ required_556_i0,
    (∃ j, x ∈ childrenC_556_i0 j) ∨ ∀ j, x ∈ childrenD_556_i0 j := by decide +kernel
theorem required_exact_556_i0 : required_556_i0 =
    ((Finset.univ.biUnion childrenC_556_i0) ∪ commonEnvelope childrenD_556_i0).erase (5, 4) := by
  exact required_eq_combination childrenC_556_i0 childrenD_556_i0 (5, 4) required_556_i0
    (by decide +kernel) child_required_sub_556_i0 common_sub_556_i0 required_origin_556_i0
theorem envelope_origin_556_i0 : ∀ x ∈ envelope_556_i0,
    x = (5, 4) ∨ ∃ j, x ∈ childrenD_556_i0 j := by decide +kernel
theorem envelope_exact_556_i0 : envelope_556_i0 =
    insert (5, 4) (Finset.univ.biUnion childrenD_556_i0) := by
  exact envelope_eq_combination childrenD_556_i0 (5, 4) envelope_556_i0
    pivot_mem_556_i0 child_envelope_sub_556_i0 envelope_origin_556_i0
def checked_556_i0 : CheckedCard where
  required := required_556_i0
  envelope := envelope_556_i0
  height := height_556_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_556_i0
def height_556 : ℕ := 10
def childrenH_556 : Fin 2 → ℕ := ![height_3, height_556_i0]
theorem height_exact_556 : height_556 = 1 + Finset.univ.sup childrenH_556 := by decide +kernel
theorem required_origin_556 : ∀ x ∈ required_556,
    (∃ j, x ∈ childrenC_556 j) ∨ ∀ j, x ∈ childrenD_556 j := by decide +kernel
theorem required_exact_556 : required_556 =
    ((Finset.univ.biUnion childrenC_556) ∪ commonEnvelope childrenD_556).erase (2, 4) := by
  exact required_eq_combination childrenC_556 childrenD_556 (2, 4) required_556
    (by decide +kernel) child_required_sub_556 common_sub_556 required_origin_556
theorem envelope_origin_556 : ∀ x ∈ envelope_556,
    x = (2, 4) ∨ ∃ j, x ∈ childrenD_556 j := by decide +kernel
theorem envelope_exact_556 : envelope_556 =
    insert (2, 4) (Finset.univ.biUnion childrenD_556) := by
  exact envelope_eq_combination childrenD_556 (2, 4) envelope_556
    pivot_mem_556 child_envelope_sub_556 envelope_origin_556
def checked_556 : CheckedCard where
  required := required_556
  envelope := envelope_556
  height := height_556
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_556
def height_560_i4 : ℕ := 4
def childrenH_560_i4 : Fin 2 → ℕ := ![height_44, height_156]
theorem height_exact_560_i4 : height_560_i4 = 1 + Finset.univ.sup childrenH_560_i4 := by decide +kernel
theorem required_origin_560_i4 : ∀ x ∈ required_560_i4,
    (∃ j, x ∈ childrenC_560_i4 j) ∨ ∀ j, x ∈ childrenD_560_i4 j := by decide +kernel
theorem required_exact_560_i4 : required_560_i4 =
    ((Finset.univ.biUnion childrenC_560_i4) ∪ commonEnvelope childrenD_560_i4).erase (5, 2) := by
  exact required_eq_combination childrenC_560_i4 childrenD_560_i4 (5, 2) required_560_i4
    (by decide +kernel) child_required_sub_560_i4 common_sub_560_i4 required_origin_560_i4
theorem envelope_origin_560_i4 : ∀ x ∈ envelope_560_i4,
    x = (5, 2) ∨ ∃ j, x ∈ childrenD_560_i4 j := by decide +kernel
theorem envelope_exact_560_i4 : envelope_560_i4 =
    insert (5, 2) (Finset.univ.biUnion childrenD_560_i4) := by
  exact envelope_eq_combination childrenD_560_i4 (5, 2) envelope_560_i4
    pivot_mem_560_i4 child_envelope_sub_560_i4 envelope_origin_560_i4
def checked_560_i4 : CheckedCard where
  required := required_560_i4
  envelope := envelope_560_i4
  height := height_560_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_560_i4
def height_560_i3 : ℕ := 5
def childrenH_560_i3 : Fin 3 → ℕ := ![height_44, height_52, height_560_i4]
theorem height_exact_560_i3 : height_560_i3 = 1 + Finset.univ.sup childrenH_560_i3 := by decide +kernel
theorem required_origin_560_i3 : ∀ x ∈ required_560_i3,
    (∃ j, x ∈ childrenC_560_i3 j) ∨ ∀ j, x ∈ childrenD_560_i3 j := by decide +kernel
theorem required_exact_560_i3 : required_560_i3 =
    ((Finset.univ.biUnion childrenC_560_i3) ∪ commonEnvelope childrenD_560_i3).erase (5, 1) := by
  exact required_eq_combination childrenC_560_i3 childrenD_560_i3 (5, 1) required_560_i3
    (by decide +kernel) child_required_sub_560_i3 common_sub_560_i3 required_origin_560_i3
theorem envelope_origin_560_i3 : ∀ x ∈ envelope_560_i3,
    x = (5, 1) ∨ ∃ j, x ∈ childrenD_560_i3 j := by decide +kernel
theorem envelope_exact_560_i3 : envelope_560_i3 =
    insert (5, 1) (Finset.univ.biUnion childrenD_560_i3) := by
  exact envelope_eq_combination childrenD_560_i3 (5, 1) envelope_560_i3
    pivot_mem_560_i3 child_envelope_sub_560_i3 envelope_origin_560_i3
def checked_560_i3 : CheckedCard where
  required := required_560_i3
  envelope := envelope_560_i3
  height := height_560_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_560_i3
def height_560_i2 : ℕ := 6
def childrenH_560_i2 : Fin 2 → ℕ := ![height_5, height_560_i3]
theorem height_exact_560_i2 : height_560_i2 = 1 + Finset.univ.sup childrenH_560_i2 := by decide +kernel
theorem required_origin_560_i2 : ∀ x ∈ required_560_i2,
    (∃ j, x ∈ childrenC_560_i2 j) ∨ ∀ j, x ∈ childrenD_560_i2 j := by decide +kernel
theorem required_exact_560_i2 : required_560_i2 =
    ((Finset.univ.biUnion childrenC_560_i2) ∪ commonEnvelope childrenD_560_i2).erase (4, 1) := by
  exact required_eq_combination childrenC_560_i2 childrenD_560_i2 (4, 1) required_560_i2
    (by decide +kernel) child_required_sub_560_i2 common_sub_560_i2 required_origin_560_i2
theorem envelope_origin_560_i2 : ∀ x ∈ envelope_560_i2,
    x = (4, 1) ∨ ∃ j, x ∈ childrenD_560_i2 j := by decide +kernel
theorem envelope_exact_560_i2 : envelope_560_i2 =
    insert (4, 1) (Finset.univ.biUnion childrenD_560_i2) := by
  exact envelope_eq_combination childrenD_560_i2 (4, 1) envelope_560_i2
    pivot_mem_560_i2 child_envelope_sub_560_i2 envelope_origin_560_i2
def checked_560_i2 : CheckedCard where
  required := required_560_i2
  envelope := envelope_560_i2
  height := height_560_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_560_i2
def height_560_i1 : ℕ := 7
def childrenH_560_i1 : Fin 2 → ℕ := ![height_153, height_560_i2]
theorem height_exact_560_i1 : height_560_i1 = 1 + Finset.univ.sup childrenH_560_i1 := by decide +kernel
theorem required_origin_560_i1 : ∀ x ∈ required_560_i1,
    (∃ j, x ∈ childrenC_560_i1 j) ∨ ∀ j, x ∈ childrenD_560_i1 j := by decide +kernel
theorem required_exact_560_i1 : required_560_i1 =
    ((Finset.univ.biUnion childrenC_560_i1) ∪ commonEnvelope childrenD_560_i1).erase (6, 5) := by
  exact required_eq_combination childrenC_560_i1 childrenD_560_i1 (6, 5) required_560_i1
    (by decide +kernel) child_required_sub_560_i1 common_sub_560_i1 required_origin_560_i1
theorem envelope_origin_560_i1 : ∀ x ∈ envelope_560_i1,
    x = (6, 5) ∨ ∃ j, x ∈ childrenD_560_i1 j := by decide +kernel
theorem envelope_exact_560_i1 : envelope_560_i1 =
    insert (6, 5) (Finset.univ.biUnion childrenD_560_i1) := by
  exact envelope_eq_combination childrenD_560_i1 (6, 5) envelope_560_i1
    pivot_mem_560_i1 child_envelope_sub_560_i1 envelope_origin_560_i1
def checked_560_i1 : CheckedCard where
  required := required_560_i1
  envelope := envelope_560_i1
  height := height_560_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_560_i1
def height_560_i0 : ℕ := 8
def childrenH_560_i0 : Fin 2 → ℕ := ![height_5, height_560_i1]
theorem height_exact_560_i0 : height_560_i0 = 1 + Finset.univ.sup childrenH_560_i0 := by decide +kernel
theorem required_origin_560_i0 : ∀ x ∈ required_560_i0,
    (∃ j, x ∈ childrenC_560_i0 j) ∨ ∀ j, x ∈ childrenD_560_i0 j := by decide +kernel
theorem required_exact_560_i0 : required_560_i0 =
    ((Finset.univ.biUnion childrenC_560_i0) ∪ commonEnvelope childrenD_560_i0).erase (3, 1) := by
  exact required_eq_combination childrenC_560_i0 childrenD_560_i0 (3, 1) required_560_i0
    (by decide +kernel) child_required_sub_560_i0 common_sub_560_i0 required_origin_560_i0
theorem envelope_origin_560_i0 : ∀ x ∈ envelope_560_i0,
    x = (3, 1) ∨ ∃ j, x ∈ childrenD_560_i0 j := by decide +kernel
theorem envelope_exact_560_i0 : envelope_560_i0 =
    insert (3, 1) (Finset.univ.biUnion childrenD_560_i0) := by
  exact envelope_eq_combination childrenD_560_i0 (3, 1) envelope_560_i0
    pivot_mem_560_i0 child_envelope_sub_560_i0 envelope_origin_560_i0
def checked_560_i0 : CheckedCard where
  required := required_560_i0
  envelope := envelope_560_i0
  height := height_560_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_560_i0
def height_560_i5 : ℕ := 6
def childrenH_560_i5 : Fin 3 → ℕ := ![height_227, height_245, height_274]
theorem height_exact_560_i5 : height_560_i5 = 1 + Finset.univ.sup childrenH_560_i5 := by decide +kernel
theorem required_origin_560_i5 : ∀ x ∈ required_560_i5,
    (∃ j, x ∈ childrenC_560_i5 j) ∨ ∀ j, x ∈ childrenD_560_i5 j := by decide +kernel
theorem required_exact_560_i5 : required_560_i5 =
    ((Finset.univ.biUnion childrenC_560_i5) ∪ commonEnvelope childrenD_560_i5).erase (5, 3) := by
  exact required_eq_combination childrenC_560_i5 childrenD_560_i5 (5, 3) required_560_i5
    (by decide +kernel) child_required_sub_560_i5 common_sub_560_i5 required_origin_560_i5
theorem envelope_origin_560_i5 : ∀ x ∈ envelope_560_i5,
    x = (5, 3) ∨ ∃ j, x ∈ childrenD_560_i5 j := by decide +kernel
theorem envelope_exact_560_i5 : envelope_560_i5 =
    insert (5, 3) (Finset.univ.biUnion childrenD_560_i5) := by
  exact envelope_eq_combination childrenD_560_i5 (5, 3) envelope_560_i5
    pivot_mem_560_i5 child_envelope_sub_560_i5 envelope_origin_560_i5
def checked_560_i5 : CheckedCard where
  required := required_560_i5
  envelope := envelope_560_i5
  height := height_560_i5
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_560_i5
def height_560 : ℕ := 10
def childrenH_560 : Fin 8 → ℕ := ![height_67, height_228, height_373, height_435, height_531, height_560_i0, height_560_i5, height_559]
theorem height_exact_560 : height_560 = 1 + Finset.univ.sup childrenH_560 := by decide +kernel
theorem required_origin_560 : ∀ x ∈ required_560,
    (∃ j, x ∈ childrenC_560 j) ∨ ∀ j, x ∈ childrenD_560 j := by decide +kernel
theorem required_exact_560 : required_560 =
    ((Finset.univ.biUnion childrenC_560) ∪ commonEnvelope childrenD_560).erase (5, 4) := by
  exact required_eq_combination childrenC_560 childrenD_560 (5, 4) required_560
    (by decide +kernel) child_required_sub_560 common_sub_560 required_origin_560
theorem envelope_origin_560 : ∀ x ∈ envelope_560,
    x = (5, 4) ∨ ∃ j, x ∈ childrenD_560 j := by decide +kernel
theorem envelope_exact_560 : envelope_560 =
    insert (5, 4) (Finset.univ.biUnion childrenD_560) := by
  exact envelope_eq_combination childrenD_560 (5, 4) envelope_560
    pivot_mem_560 child_envelope_sub_560 envelope_origin_560
def checked_560 : CheckedCard where
  required := required_560
  envelope := envelope_560
  height := height_560
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_560
def height_563_i2 : ℕ := 7
def childrenH_563_i2 : Fin 2 → ℕ := ![height_0, height_393]
theorem height_exact_563_i2 : height_563_i2 = 1 + Finset.univ.sup childrenH_563_i2 := by decide +kernel
theorem required_origin_563_i2 : ∀ x ∈ required_563_i2,
    (∃ j, x ∈ childrenC_563_i2 j) ∨ ∀ j, x ∈ childrenD_563_i2 j := by decide +kernel
theorem required_exact_563_i2 : required_563_i2 =
    ((Finset.univ.biUnion childrenC_563_i2) ∪ commonEnvelope childrenD_563_i2).erase (2, 6) := by
  exact required_eq_combination childrenC_563_i2 childrenD_563_i2 (2, 6) required_563_i2
    (by decide +kernel) child_required_sub_563_i2 common_sub_563_i2 required_origin_563_i2
theorem envelope_origin_563_i2 : ∀ x ∈ envelope_563_i2,
    x = (2, 6) ∨ ∃ j, x ∈ childrenD_563_i2 j := by decide +kernel
theorem envelope_exact_563_i2 : envelope_563_i2 =
    insert (2, 6) (Finset.univ.biUnion childrenD_563_i2) := by
  exact envelope_eq_combination childrenD_563_i2 (2, 6) envelope_563_i2
    pivot_mem_563_i2 child_envelope_sub_563_i2 envelope_origin_563_i2
def checked_563_i2 : CheckedCard where
  required := required_563_i2
  envelope := envelope_563_i2
  height := height_563_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_563_i2
def height_563_i1 : ℕ := 8
def childrenH_563_i1 : Fin 2 → ℕ := ![height_0, height_563_i2]
theorem height_exact_563_i1 : height_563_i1 = 1 + Finset.univ.sup childrenH_563_i1 := by decide +kernel
theorem required_origin_563_i1 : ∀ x ∈ required_563_i1,
    (∃ j, x ∈ childrenC_563_i1 j) ∨ ∀ j, x ∈ childrenD_563_i1 j := by decide +kernel
theorem required_exact_563_i1 : required_563_i1 =
    ((Finset.univ.biUnion childrenC_563_i1) ∪ commonEnvelope childrenD_563_i1).erase (2, 4) := by
  exact required_eq_combination childrenC_563_i1 childrenD_563_i1 (2, 4) required_563_i1
    (by decide +kernel) child_required_sub_563_i1 common_sub_563_i1 required_origin_563_i1
theorem envelope_origin_563_i1 : ∀ x ∈ envelope_563_i1,
    x = (2, 4) ∨ ∃ j, x ∈ childrenD_563_i1 j := by decide +kernel
theorem envelope_exact_563_i1 : envelope_563_i1 =
    insert (2, 4) (Finset.univ.biUnion childrenD_563_i1) := by
  exact envelope_eq_combination childrenD_563_i1 (2, 4) envelope_563_i1
    pivot_mem_563_i1 child_envelope_sub_563_i1 envelope_origin_563_i1
def checked_563_i1 : CheckedCard where
  required := required_563_i1
  envelope := envelope_563_i1
  height := height_563_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_563_i1
def height_563_i6 : ℕ := 3
def childrenH_563_i6 : Fin 2 → ℕ := ![height_11, height_38]
theorem height_exact_563_i6 : height_563_i6 = 1 + Finset.univ.sup childrenH_563_i6 := by decide +kernel
theorem required_origin_563_i6 : ∀ x ∈ required_563_i6,
    (∃ j, x ∈ childrenC_563_i6 j) ∨ ∀ j, x ∈ childrenD_563_i6 j := by decide +kernel
theorem required_exact_563_i6 : required_563_i6 =
    ((Finset.univ.biUnion childrenC_563_i6) ∪ commonEnvelope childrenD_563_i6).erase (3, 3) := by
  exact required_eq_combination childrenC_563_i6 childrenD_563_i6 (3, 3) required_563_i6
    (by decide +kernel) child_required_sub_563_i6 common_sub_563_i6 required_origin_563_i6
theorem envelope_origin_563_i6 : ∀ x ∈ envelope_563_i6,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_563_i6 j := by decide +kernel
theorem envelope_exact_563_i6 : envelope_563_i6 =
    insert (3, 3) (Finset.univ.biUnion childrenD_563_i6) := by
  exact envelope_eq_combination childrenD_563_i6 (3, 3) envelope_563_i6
    pivot_mem_563_i6 child_envelope_sub_563_i6 envelope_origin_563_i6
def checked_563_i6 : CheckedCard where
  required := required_563_i6
  envelope := envelope_563_i6
  height := height_563_i6
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_563_i6
def height_563_i5 : ℕ := 4
def childrenH_563_i5 : Fin 2 → ℕ := ![height_15, height_563_i6]
theorem height_exact_563_i5 : height_563_i5 = 1 + Finset.univ.sup childrenH_563_i5 := by decide +kernel
theorem required_origin_563_i5 : ∀ x ∈ required_563_i5,
    (∃ j, x ∈ childrenC_563_i5 j) ∨ ∀ j, x ∈ childrenD_563_i5 j := by decide +kernel
theorem required_exact_563_i5 : required_563_i5 =
    ((Finset.univ.biUnion childrenC_563_i5) ∪ commonEnvelope childrenD_563_i5).erase (3, 6) := by
  exact required_eq_combination childrenC_563_i5 childrenD_563_i5 (3, 6) required_563_i5
    (by decide +kernel) child_required_sub_563_i5 common_sub_563_i5 required_origin_563_i5
theorem envelope_origin_563_i5 : ∀ x ∈ envelope_563_i5,
    x = (3, 6) ∨ ∃ j, x ∈ childrenD_563_i5 j := by decide +kernel
theorem envelope_exact_563_i5 : envelope_563_i5 =
    insert (3, 6) (Finset.univ.biUnion childrenD_563_i5) := by
  exact envelope_eq_combination childrenD_563_i5 (3, 6) envelope_563_i5
    pivot_mem_563_i5 child_envelope_sub_563_i5 envelope_origin_563_i5
def checked_563_i5 : CheckedCard where
  required := required_563_i5
  envelope := envelope_563_i5
  height := height_563_i5
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_563_i5
def height_563_i4 : ℕ := 5
def childrenH_563_i4 : Fin 2 → ℕ := ![height_0, height_563_i5]
theorem height_exact_563_i4 : height_563_i4 = 1 + Finset.univ.sup childrenH_563_i4 := by decide +kernel
theorem required_origin_563_i4 : ∀ x ∈ required_563_i4,
    (∃ j, x ∈ childrenC_563_i4 j) ∨ ∀ j, x ∈ childrenD_563_i4 j := by decide +kernel
theorem required_exact_563_i4 : required_563_i4 =
    ((Finset.univ.biUnion childrenC_563_i4) ∪ commonEnvelope childrenD_563_i4).erase (3, 4) := by
  exact required_eq_combination childrenC_563_i4 childrenD_563_i4 (3, 4) required_563_i4
    (by decide +kernel) child_required_sub_563_i4 common_sub_563_i4 required_origin_563_i4
theorem envelope_origin_563_i4 : ∀ x ∈ envelope_563_i4,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_563_i4 j := by decide +kernel
theorem envelope_exact_563_i4 : envelope_563_i4 =
    insert (3, 4) (Finset.univ.biUnion childrenD_563_i4) := by
  exact envelope_eq_combination childrenD_563_i4 (3, 4) envelope_563_i4
    pivot_mem_563_i4 child_envelope_sub_563_i4 envelope_origin_563_i4
def checked_563_i4 : CheckedCard where
  required := required_563_i4
  envelope := envelope_563_i4
  height := height_563_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_563_i4
def height_563_i3 : ℕ := 6
def childrenH_563_i3 : Fin 2 → ℕ := ![height_5, height_563_i4]
theorem height_exact_563_i3 : height_563_i3 = 1 + Finset.univ.sup childrenH_563_i3 := by decide +kernel
theorem required_origin_563_i3 : ∀ x ∈ required_563_i3,
    (∃ j, x ∈ childrenC_563_i3 j) ∨ ∀ j, x ∈ childrenD_563_i3 j := by decide +kernel
theorem required_exact_563_i3 : required_563_i3 =
    ((Finset.univ.biUnion childrenC_563_i3) ∪ commonEnvelope childrenD_563_i3).erase (4, 4) := by
  exact required_eq_combination childrenC_563_i3 childrenD_563_i3 (4, 4) required_563_i3
    (by decide +kernel) child_required_sub_563_i3 common_sub_563_i3 required_origin_563_i3
theorem envelope_origin_563_i3 : ∀ x ∈ envelope_563_i3,
    x = (4, 4) ∨ ∃ j, x ∈ childrenD_563_i3 j := by decide +kernel
theorem envelope_exact_563_i3 : envelope_563_i3 =
    insert (4, 4) (Finset.univ.biUnion childrenD_563_i3) := by
  exact envelope_eq_combination childrenD_563_i3 (4, 4) envelope_563_i3
    pivot_mem_563_i3 child_envelope_sub_563_i3 envelope_origin_563_i3
def checked_563_i3 : CheckedCard where
  required := required_563_i3
  envelope := envelope_563_i3
  height := height_563_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_563_i3
def height_563_i0 : ℕ := 9
def childrenH_563_i0 : Fin 3 → ℕ := ![height_18, height_563_i1, height_563_i3]
theorem height_exact_563_i0 : height_563_i0 = 1 + Finset.univ.sup childrenH_563_i0 := by decide +kernel
theorem required_origin_563_i0 : ∀ x ∈ required_563_i0,
    (∃ j, x ∈ childrenC_563_i0 j) ∨ ∀ j, x ∈ childrenD_563_i0 j := by decide +kernel
theorem required_exact_563_i0 : required_563_i0 =
    ((Finset.univ.biUnion childrenC_563_i0) ∪ commonEnvelope childrenD_563_i0).erase (4, 5) := by
  exact required_eq_combination childrenC_563_i0 childrenD_563_i0 (4, 5) required_563_i0
    (by decide +kernel) child_required_sub_563_i0 common_sub_563_i0 required_origin_563_i0
theorem envelope_origin_563_i0 : ∀ x ∈ envelope_563_i0,
    x = (4, 5) ∨ ∃ j, x ∈ childrenD_563_i0 j := by decide +kernel
theorem envelope_exact_563_i0 : envelope_563_i0 =
    insert (4, 5) (Finset.univ.biUnion childrenD_563_i0) := by
  exact envelope_eq_combination childrenD_563_i0 (4, 5) envelope_563_i0
    pivot_mem_563_i0 child_envelope_sub_563_i0 envelope_origin_563_i0
def checked_563_i0 : CheckedCard where
  required := required_563_i0
  envelope := envelope_563_i0
  height := height_563_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_563_i0
def height_563 : ℕ := 10
def childrenH_563 : Fin 8 → ℕ := ![height_134, height_180, height_258, height_435, height_507, height_563_i0, height_561, height_562]
theorem height_exact_563 : height_563 = 1 + Finset.univ.sup childrenH_563 := by decide +kernel
theorem required_origin_563 : ∀ x ∈ required_563,
    (∃ j, x ∈ childrenC_563 j) ∨ ∀ j, x ∈ childrenD_563 j := by decide +kernel
theorem required_exact_563 : required_563 =
    ((Finset.univ.biUnion childrenC_563) ∪ commonEnvelope childrenD_563).erase (3, 5) := by
  exact required_eq_combination childrenC_563 childrenD_563 (3, 5) required_563
    (by decide +kernel) child_required_sub_563 common_sub_563 required_origin_563
theorem envelope_origin_563 : ∀ x ∈ envelope_563,
    x = (3, 5) ∨ ∃ j, x ∈ childrenD_563 j := by decide +kernel
theorem envelope_exact_563 : envelope_563 =
    insert (3, 5) (Finset.univ.biUnion childrenD_563) := by
  exact envelope_eq_combination childrenD_563 (3, 5) envelope_563
    pivot_mem_563 child_envelope_sub_563 envelope_origin_563
def checked_563 : CheckedCard where
  required := required_563
  envelope := envelope_563
  height := height_563
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_563
end SnakyPrototype.Certificate21

end OAI
