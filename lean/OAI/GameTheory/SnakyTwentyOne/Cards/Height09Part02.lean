import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part02
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_443_i6 : Finset Cell := ⟨(([(1, 4), (2, 4), (3, 3), (4, 0), (4, 1), (4, 2), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_443_i6 : Finset Cell := ⟨(([(1, 4), (2, 3), (2, 4), (3, 3), (4, 0), (4, 1), (4, 2), (4, 3), (5, 3), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_443_i6 : Fin 2 → Finset Cell := ![(placed21 2 (5, 3) required_3), (placed21 1 (4, 0) required_5)]
def childrenD_443_i6 : Fin 2 → Finset Cell := ![(placed21 2 (5, 3) envelope_3), (placed21 1 (4, 0) envelope_5)]
theorem common_sub_443_i6 : commonEnvelope childrenD_443_i6 ⊆ insert (5, 3) required_443_i6 := by decide +kernel
theorem child_required_sub_443_i6 : ∀ j, childrenC_443_i6 j ⊆ insert (5, 3) required_443_i6 := by decide +kernel
theorem child_envelope_sub_443_i6 : ∀ j, childrenD_443_i6 j ⊆ envelope_443_i6 := by decide +kernel
theorem pivot_mem_443_i6 : (5, 3) ∈ envelope_443_i6 := by decide +kernel
theorem children_work_443_i6 : ∀ j, Template HasSnaky 1 (childrenC_443_i6 j) (childrenD_443_i6 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_3 2 (5, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_5 1 (4, 0)).mono (by decide +kernel)
theorem row_works_443_i6 : Template HasSnaky 2 required_443_i6 envelope_443_i6 := by
  refine compose HasSnaky 1 childrenC_443_i6 childrenD_443_i6 children_work_443_i6 (5, 3)
    required_443_i6 envelope_443_i6 pivot_mem_443_i6 child_required_sub_443_i6 child_envelope_sub_443_i6 ?_
  intro b hb
  exact common_sub_443_i6 (mem_commonEnvelope childrenD_443_i6 b hb)
def required_443_i5 : Finset Cell := ⟨(([(1, 4), (2, 4), (4, 0), (4, 1), (4, 2), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_443_i5 : Finset Cell := ⟨(([(1, 4), (2, 3), (2, 4), (3, 3), (3, 4), (4, 0), (4, 1), (4, 2), (4, 3), (5, 3), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_443_i5 : Fin 2 → Finset Cell := ![(placed21 5 (4, 0) required_5), required_443_i6]
def childrenD_443_i5 : Fin 2 → Finset Cell := ![(placed21 5 (4, 0) envelope_5), envelope_443_i6]
theorem common_sub_443_i5 : commonEnvelope childrenD_443_i5 ⊆ insert (3, 3) required_443_i5 := by decide +kernel
theorem child_required_sub_443_i5 : ∀ j, childrenC_443_i5 j ⊆ insert (3, 3) required_443_i5 := by decide +kernel
theorem child_envelope_sub_443_i5 : ∀ j, childrenD_443_i5 j ⊆ envelope_443_i5 := by decide +kernel
theorem pivot_mem_443_i5 : (3, 3) ∈ envelope_443_i5 := by decide +kernel
theorem children_work_443_i5 : ∀ j, Template HasSnaky 2 (childrenC_443_i5 j) (childrenD_443_i5 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 5 (4, 0)).mono (by decide +kernel)
  · exact row_works_443_i6.mono (by decide +kernel)
theorem row_works_443_i5 : Template HasSnaky 3 required_443_i5 envelope_443_i5 := by
  refine compose HasSnaky 2 childrenC_443_i5 childrenD_443_i5 children_work_443_i5 (3, 3)
    required_443_i5 envelope_443_i5 pivot_mem_443_i5 child_required_sub_443_i5 child_envelope_sub_443_i5 ?_
  intro b hb
  exact common_sub_443_i5 (mem_commonEnvelope childrenD_443_i5 b hb)
def required_443_i4 : Finset Cell := ⟨(([(1, 1), (1, 4), (2, 1), (2, 4), (3, 1), (4, 0), (4, 2), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_443_i4 : Finset Cell := ⟨(([(1, 1), (1, 4), (2, 1), (2, 3), (2, 4), (3, 1), (3, 3), (3, 4), (4, 0), (4, 1), (4, 2), (4, 3), (5, 0), (5, 3), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_443_i4 : Fin 2 → Finset Cell := ![(placed21 4 (1, 1) required_5), required_443_i5]
def childrenD_443_i4 : Fin 2 → Finset Cell := ![(placed21 4 (1, 1) envelope_5), envelope_443_i5]
theorem common_sub_443_i4 : commonEnvelope childrenD_443_i4 ⊆ insert (4, 1) required_443_i4 := by decide +kernel
theorem child_required_sub_443_i4 : ∀ j, childrenC_443_i4 j ⊆ insert (4, 1) required_443_i4 := by decide +kernel
theorem child_envelope_sub_443_i4 : ∀ j, childrenD_443_i4 j ⊆ envelope_443_i4 := by decide +kernel
theorem pivot_mem_443_i4 : (4, 1) ∈ envelope_443_i4 := by decide +kernel
theorem children_work_443_i4 : ∀ j, Template HasSnaky 3 (childrenC_443_i4 j) (childrenD_443_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 4 (1, 1)).mono (by decide +kernel)
  · exact row_works_443_i5.mono (by decide +kernel)
theorem row_works_443_i4 : Template HasSnaky 4 required_443_i4 envelope_443_i4 := by
  refine compose HasSnaky 3 childrenC_443_i4 childrenD_443_i4 children_work_443_i4 (4, 1)
    required_443_i4 envelope_443_i4 pivot_mem_443_i4 child_required_sub_443_i4 child_envelope_sub_443_i4 ?_
  intro b hb
  exact common_sub_443_i4 (mem_commonEnvelope childrenD_443_i4 b hb)
def required_443_i3 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 3), (1, 4), (2, 1), (3, 1), (4, 0), (4, 2), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_443_i3 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 3), (1, 4), (2, 1), (2, 3), (2, 4), (2, 5), (3, 1), (3, 3), (3, 4), (4, 0), (4, 1), (4, 2), (4, 3), (5, 0), (5, 3), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_443_i3 : Fin 2 → Finset Cell := ![(placed21 1 (1, 1) required_5), required_443_i4]
def childrenD_443_i3 : Fin 2 → Finset Cell := ![(placed21 1 (1, 1) envelope_5), envelope_443_i4]
theorem common_sub_443_i3 : commonEnvelope childrenD_443_i3 ⊆ insert (2, 4) required_443_i3 := by decide +kernel
theorem child_required_sub_443_i3 : ∀ j, childrenC_443_i3 j ⊆ insert (2, 4) required_443_i3 := by decide +kernel
theorem child_envelope_sub_443_i3 : ∀ j, childrenD_443_i3 j ⊆ envelope_443_i3 := by decide +kernel
theorem pivot_mem_443_i3 : (2, 4) ∈ envelope_443_i3 := by decide +kernel
theorem children_work_443_i3 : ∀ j, Template HasSnaky 4 (childrenC_443_i3 j) (childrenD_443_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 1 (1, 1)).mono (by decide +kernel)
  · exact row_works_443_i4.mono (by decide +kernel)
theorem row_works_443_i3 : Template HasSnaky 5 required_443_i3 envelope_443_i3 := by
  refine compose HasSnaky 4 childrenC_443_i3 childrenD_443_i3 children_work_443_i3 (2, 4)
    required_443_i3 envelope_443_i3 pivot_mem_443_i3 child_required_sub_443_i3 child_envelope_sub_443_i3 ?_
  intro b hb
  exact common_sub_443_i3 (mem_commonEnvelope childrenD_443_i3 b hb)
def required_443_i2 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 2), (1, 3), (1, 4), (2, 1), (3, 1), (4, 2), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_443_i2 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 2), (1, 3), (1, 4), (2, 1), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 3), (3, 4), (4, 0), (4, 1), (4, 2), (4, 3), (5, 0), (5, 3), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_443_i2 : Fin 2 → Finset Cell := ![(placed21 4 (0, 1) required_4), required_443_i3]
def childrenD_443_i2 : Fin 2 → Finset Cell := ![(placed21 4 (0, 1) envelope_4), envelope_443_i3]
theorem common_sub_443_i2 : commonEnvelope childrenD_443_i2 ⊆ insert (4, 0) required_443_i2 := by decide +kernel
theorem child_required_sub_443_i2 : ∀ j, childrenC_443_i2 j ⊆ insert (4, 0) required_443_i2 := by decide +kernel
theorem child_envelope_sub_443_i2 : ∀ j, childrenD_443_i2 j ⊆ envelope_443_i2 := by decide +kernel
theorem pivot_mem_443_i2 : (4, 0) ∈ envelope_443_i2 := by decide +kernel
theorem children_work_443_i2 : ∀ j, Template HasSnaky 5 (childrenC_443_i2 j) (childrenD_443_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_4 4 (0, 1)).mono (by decide +kernel)
  · exact row_works_443_i3.mono (by decide +kernel)
theorem row_works_443_i2 : Template HasSnaky 6 required_443_i2 envelope_443_i2 := by
  refine compose HasSnaky 5 childrenC_443_i2 childrenD_443_i2 children_work_443_i2 (4, 0)
    required_443_i2 envelope_443_i2 pivot_mem_443_i2 child_required_sub_443_i2 child_envelope_sub_443_i2 ?_
  intro b hb
  exact common_sub_443_i2 (mem_commonEnvelope childrenD_443_i2 b hb)
def required_443_i1 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 2), (1, 3), (1, 4), (2, 1), (4, 2), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_443_i1 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 2), (1, 3), (1, 4), (2, 1), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 0), (4, 1), (4, 2), (4, 3), (5, 0), (5, 3), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_443_i1 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) required_4), required_443_i2]
def childrenD_443_i1 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) envelope_4), envelope_443_i2]
theorem common_sub_443_i1 : commonEnvelope childrenD_443_i1 ⊆ insert (3, 1) required_443_i1 := by decide +kernel
theorem child_required_sub_443_i1 : ∀ j, childrenC_443_i1 j ⊆ insert (3, 1) required_443_i1 := by decide +kernel
theorem child_envelope_sub_443_i1 : ∀ j, childrenD_443_i1 j ⊆ envelope_443_i1 := by decide +kernel
theorem pivot_mem_443_i1 : (3, 1) ∈ envelope_443_i1 := by decide +kernel
theorem children_work_443_i1 : ∀ j, Template HasSnaky 6 (childrenC_443_i1 j) (childrenD_443_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_4 0 (0, 1)).mono (by decide +kernel)
  · exact row_works_443_i2.mono (by decide +kernel)
theorem row_works_443_i1 : Template HasSnaky 7 required_443_i1 envelope_443_i1 := by
  refine compose HasSnaky 6 childrenC_443_i1 childrenD_443_i1 children_work_443_i1 (3, 1)
    required_443_i1 envelope_443_i1 pivot_mem_443_i1 child_required_sub_443_i1 child_envelope_sub_443_i1 ?_
  intro b hb
  exact common_sub_443_i1 (mem_commonEnvelope childrenD_443_i1 b hb)
def required_443_i0 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 3), (1, 4), (2, 1), (4, 2), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_443_i0 : Finset Cell := ⟨(([(0, 0), (0, 1), (1, 1), (1, 2), (1, 3), (1, 4), (2, 1), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 0), (4, 1), (4, 2), (4, 3), (5, 0), (5, 3), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_443_i0 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) required_5), required_443_i1]
def childrenD_443_i0 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) envelope_5), envelope_443_i1]
theorem common_sub_443_i0 : commonEnvelope childrenD_443_i0 ⊆ insert (0, 1) required_443_i0 := by decide +kernel
theorem child_required_sub_443_i0 : ∀ j, childrenC_443_i0 j ⊆ insert (0, 1) required_443_i0 := by decide +kernel
theorem child_envelope_sub_443_i0 : ∀ j, childrenD_443_i0 j ⊆ envelope_443_i0 := by decide +kernel
theorem pivot_mem_443_i0 : (0, 1) ∈ envelope_443_i0 := by decide +kernel
theorem children_work_443_i0 : ∀ j, Template HasSnaky 7 (childrenC_443_i0 j) (childrenD_443_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 7 (1, 4)).mono (by decide +kernel)
  · exact row_works_443_i1.mono (by decide +kernel)
theorem row_works_443_i0 : Template HasSnaky 8 required_443_i0 envelope_443_i0 := by
  refine compose HasSnaky 7 childrenC_443_i0 childrenD_443_i0 children_work_443_i0 (0, 1)
    required_443_i0 envelope_443_i0 pivot_mem_443_i0 child_required_sub_443_i0 child_envelope_sub_443_i0 ?_
  intro b hb
  exact common_sub_443_i0 (mem_commonEnvelope childrenD_443_i0 b hb)
def required_443 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 3), (1, 4), (4, 2), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_443 : Finset Cell := ⟨(([(0, 0), (0, 1), (1, 1), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 0), (4, 1), (4, 2), (4, 3), (5, 0), (5, 3), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_443 : Fin 2 → Finset Cell := ![(placed21 3 (1, 4) required_5), required_443_i0]
def childrenD_443 : Fin 2 → Finset Cell := ![(placed21 3 (1, 4) envelope_5), envelope_443_i0]
theorem common_sub_443 : commonEnvelope childrenD_443 ⊆ insert (2, 1) required_443 := by decide +kernel
theorem child_required_sub_443 : ∀ j, childrenC_443 j ⊆ insert (2, 1) required_443 := by decide +kernel
theorem child_envelope_sub_443 : ∀ j, childrenD_443 j ⊆ envelope_443 := by decide +kernel
theorem pivot_mem_443 : (2, 1) ∈ envelope_443 := by decide +kernel
theorem children_work_443 : ∀ j, Template HasSnaky 8 (childrenC_443 j) (childrenD_443 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 3 (1, 4)).mono (by decide +kernel)
  · exact row_works_443_i0.mono (by decide +kernel)
theorem row_works_443 : Template HasSnaky 9 required_443 envelope_443 := by
  refine compose HasSnaky 8 childrenC_443 childrenD_443 children_work_443 (2, 1)
    required_443 envelope_443 pivot_mem_443 child_required_sub_443 child_envelope_sub_443 ?_
  intro b hb
  exact common_sub_443 (mem_commonEnvelope childrenD_443 b hb)
def required_449 : Finset Cell := ⟨(([(2, 3), (2, 4), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_449 : Finset Cell := ⟨(([(0, 2), (0, 3), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (2, 5), (2, 6), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 2), (6, 3), (6, 4), (6, 5), (7, 2), (7, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_449 : Fin 5 → Finset Cell := ![(placed21 3 (1, 4) required_10), (placed21 1 (1, 3) required_27), (placed21 3 (1, 4) required_48), (placed21 3 (1, 4) required_63), required_448]
def childrenD_449 : Fin 5 → Finset Cell := ![(placed21 3 (1, 4) envelope_10), (placed21 1 (1, 3) envelope_27), (placed21 3 (1, 4) envelope_48), (placed21 3 (1, 4) envelope_63), envelope_448]
theorem common_sub_449 : commonEnvelope childrenD_449 ⊆ insert (4, 3) required_449 := by decide +kernel
theorem child_required_sub_449 : ∀ j, childrenC_449 j ⊆ insert (4, 3) required_449 := by decide +kernel
theorem child_envelope_sub_449 : ∀ j, childrenD_449 j ⊆ envelope_449 := by decide +kernel
theorem pivot_mem_449 : (4, 3) ∈ envelope_449 := by decide +kernel
theorem children_work_449 : ∀ j, Template HasSnaky 8 (childrenC_449 j) (childrenD_449 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_10 3 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_27 1 (1, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_48 3 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_63 3 (1, 4)).mono (by decide +kernel)
  · exact row_works_448.mono (by decide +kernel)
theorem row_works_449 : Template HasSnaky 9 required_449 envelope_449 := by
  refine compose HasSnaky 8 childrenC_449 childrenD_449 children_work_449 (4, 3)
    required_449 envelope_449 pivot_mem_449 child_required_sub_449 child_envelope_sub_449 ?_
  intro b hb
  exact common_sub_449 (mem_commonEnvelope childrenD_449 b hb)
def required_450 : Finset Cell := ⟨(([(1, 3), (2, 3), (2, 4), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_450 : Finset Cell := ⟨(([(0, 4), (0, 5), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 1), (2, 2), (2, 3), (2, 4), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (6, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_450 : Fin 2 → Finset Cell := ![(placed21 6 (5, 4) required_0), (placed21 4 (0, 7) required_448)]
def childrenD_450 : Fin 2 → Finset Cell := ![(placed21 6 (5, 4) envelope_0), (placed21 4 (0, 7) envelope_448)]
theorem common_sub_450 : commonEnvelope childrenD_450 ⊆ insert (3, 4) required_450 := by decide +kernel
theorem child_required_sub_450 : ∀ j, childrenC_450 j ⊆ insert (3, 4) required_450 := by decide +kernel
theorem child_envelope_sub_450 : ∀ j, childrenD_450 j ⊆ envelope_450 := by decide +kernel
theorem pivot_mem_450 : (3, 4) ∈ envelope_450 := by decide +kernel
theorem children_work_450 : ∀ j, Template HasSnaky 8 (childrenC_450 j) (childrenD_450 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 6 (5, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_448 4 (0, 7)).mono (by decide +kernel)
theorem row_works_450 : Template HasSnaky 9 required_450 envelope_450 := by
  refine compose HasSnaky 8 childrenC_450 childrenD_450 children_work_450 (3, 4)
    required_450 envelope_450 pivot_mem_450 child_required_sub_450 child_envelope_sub_450 ?_
  intro b hb
  exact common_sub_450 (mem_commonEnvelope childrenD_450 b hb)
def required_457 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_457 : Finset Cell := ⟨(([(0, 3), (0, 4), (0, 5), (0, 6), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 2), (3, 3), (3, 4), (3, 5), (4, 3), (4, 4), (4, 5), (5, 3), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_457 : Fin 4 → Finset Cell := ![(placed21 0 (1, 0) required_7), (placed21 1 (0, 1) required_8), (placed21 2 (2, 0) required_9), (placed21 4 (0, 5) required_456)]
def childrenD_457 : Fin 4 → Finset Cell := ![(placed21 0 (1, 0) envelope_7), (placed21 1 (0, 1) envelope_8), (placed21 2 (2, 0) envelope_9), (placed21 4 (0, 5) envelope_456)]
theorem common_sub_457 : commonEnvelope childrenD_457 ⊆ insert (1, 4) required_457 := by decide +kernel
theorem child_required_sub_457 : ∀ j, childrenC_457 j ⊆ insert (1, 4) required_457 := by decide +kernel
theorem child_envelope_sub_457 : ∀ j, childrenD_457 j ⊆ envelope_457 := by decide +kernel
theorem pivot_mem_457 : (1, 4) ∈ envelope_457 := by decide +kernel
theorem children_work_457 : ∀ j, Template HasSnaky 8 (childrenC_457 j) (childrenD_457 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 0 (1, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_8 1 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_9 2 (2, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_456 4 (0, 5)).mono (by decide +kernel)
theorem row_works_457 : Template HasSnaky 9 required_457 envelope_457 := by
  refine compose HasSnaky 8 childrenC_457 childrenD_457 children_work_457 (1, 4)
    required_457 envelope_457 pivot_mem_457 child_required_sub_457 child_envelope_sub_457 ?_
  intro b hb
  exact common_sub_457 (mem_commonEnvelope childrenD_457 b hb)
def required_458 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_458 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 0), (3, 1), (3, 2), (3, 3), (4, 0), (4, 1), (4, 2), (5, 0), (5, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_458 : Fin 4 → Finset Cell := ![(placed21 0 (1, 0) required_7), required_9, required_62, required_456]
def childrenD_458 : Fin 4 → Finset Cell := ![(placed21 0 (1, 0) envelope_7), envelope_9, envelope_62, envelope_456]
theorem common_sub_458 : commonEnvelope childrenD_458 ⊆ insert (1, 4) required_458 := by decide +kernel
theorem child_required_sub_458 : ∀ j, childrenC_458 j ⊆ insert (1, 4) required_458 := by decide +kernel
theorem child_envelope_sub_458 : ∀ j, childrenD_458 j ⊆ envelope_458 := by decide +kernel
theorem pivot_mem_458 : (1, 4) ∈ envelope_458 := by decide +kernel
theorem children_work_458 : ∀ j, Template HasSnaky 8 (childrenC_458 j) (childrenD_458 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 0 (1, 0)).mono (by decide +kernel)
  · exact row_works_9.mono (by decide +kernel)
  · exact row_works_62.mono (by decide +kernel)
  · exact row_works_456.mono (by decide +kernel)
theorem row_works_458 : Template HasSnaky 9 required_458 envelope_458 := by
  refine compose HasSnaky 8 childrenC_458 childrenD_458 children_work_458 (1, 4)
    required_458 envelope_458 pivot_mem_458 child_required_sub_458 child_envelope_sub_458 ?_
  intro b hb
  exact common_sub_458 (mem_commonEnvelope childrenD_458 b hb)
def required_470_i0 : Finset Cell := ⟨(([(1, 5), (2, 2), (2, 5), (3, 3), (3, 5), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_470_i0 : Finset Cell := ⟨(([(0, 4), (0, 6), (1, 3), (1, 4), (1, 5), (1, 6), (2, 0), (2, 1), (2, 2), (2, 3), (2, 5), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_470_i0 : Fin 2 → Finset Cell := ![(placed21 6 (3, 6) required_54), (placed21 6 (4, 6) required_78)]
def childrenD_470_i0 : Fin 2 → Finset Cell := ![(placed21 6 (3, 6) envelope_54), (placed21 6 (4, 6) envelope_78)]
theorem common_sub_470_i0 : commonEnvelope childrenD_470_i0 ⊆ insert (2, 3) required_470_i0 := by decide +kernel
theorem child_required_sub_470_i0 : ∀ j, childrenC_470_i0 j ⊆ insert (2, 3) required_470_i0 := by decide +kernel
theorem child_envelope_sub_470_i0 : ∀ j, childrenD_470_i0 j ⊆ envelope_470_i0 := by decide +kernel
theorem pivot_mem_470_i0 : (2, 3) ∈ envelope_470_i0 := by decide +kernel
theorem children_work_470_i0 : ∀ j, Template HasSnaky 3 (childrenC_470_i0 j) (childrenD_470_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_54 6 (3, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_78 6 (4, 6)).mono (by decide +kernel)
theorem row_works_470_i0 : Template HasSnaky 4 required_470_i0 envelope_470_i0 := by
  refine compose HasSnaky 3 childrenC_470_i0 childrenD_470_i0 children_work_470_i0 (2, 3)
    required_470_i0 envelope_470_i0 pivot_mem_470_i0 child_required_sub_470_i0 child_envelope_sub_470_i0 ?_
  intro b hb
  exact common_sub_470_i0 (mem_commonEnvelope childrenD_470_i0 b hb)
def required_470_i2 : Finset Cell := ⟨(([(1, 5), (2, 2), (2, 5), (3, 3), (3, 5), (3, 6), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_470_i2 : Finset Cell := ⟨(([(0, 4), (0, 6), (1, 3), (1, 4), (1, 5), (1, 6), (2, 2), (2, 3), (2, 5), (3, 3), (3, 4), (3, 5), (3, 6), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_470_i2 : Fin 2 → Finset Cell := ![(placed21 7 (3, 6) required_2), (placed21 6 (4, 6) required_78)]
def childrenD_470_i2 : Fin 2 → Finset Cell := ![(placed21 7 (3, 6) envelope_2), (placed21 6 (4, 6) envelope_78)]
theorem common_sub_470_i2 : commonEnvelope childrenD_470_i2 ⊆ insert (2, 3) required_470_i2 := by decide +kernel
theorem child_required_sub_470_i2 : ∀ j, childrenC_470_i2 j ⊆ insert (2, 3) required_470_i2 := by decide +kernel
theorem child_envelope_sub_470_i2 : ∀ j, childrenD_470_i2 j ⊆ envelope_470_i2 := by decide +kernel
theorem pivot_mem_470_i2 : (2, 3) ∈ envelope_470_i2 := by decide +kernel
theorem children_work_470_i2 : ∀ j, Template HasSnaky 3 (childrenC_470_i2 j) (childrenD_470_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_2 7 (3, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_78 6 (4, 6)).mono (by decide +kernel)
theorem row_works_470_i2 : Template HasSnaky 4 required_470_i2 envelope_470_i2 := by
  refine compose HasSnaky 3 childrenC_470_i2 childrenD_470_i2 children_work_470_i2 (2, 3)
    required_470_i2 envelope_470_i2 pivot_mem_470_i2 child_required_sub_470_i2 child_envelope_sub_470_i2 ?_
  intro b hb
  exact common_sub_470_i2 (mem_commonEnvelope childrenD_470_i2 b hb)
def required_470_i1 : Finset Cell := ⟨(([(1, 5), (2, 2), (2, 5), (3, 3), (3, 5), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_470_i1 : Finset Cell := ⟨(([(0, 4), (0, 6), (1, 3), (1, 4), (1, 5), (1, 6), (2, 2), (2, 3), (2, 5), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_470_i1 : Fin 2 → Finset Cell := ![(placed21 4 (1, 8) required_56), required_470_i2]
def childrenD_470_i1 : Fin 2 → Finset Cell := ![(placed21 4 (1, 8) envelope_56), envelope_470_i2]
theorem common_sub_470_i1 : commonEnvelope childrenD_470_i1 ⊆ insert (3, 6) required_470_i1 := by decide +kernel
theorem child_required_sub_470_i1 : ∀ j, childrenC_470_i1 j ⊆ insert (3, 6) required_470_i1 := by decide +kernel
theorem child_envelope_sub_470_i1 : ∀ j, childrenD_470_i1 j ⊆ envelope_470_i1 := by decide +kernel
theorem pivot_mem_470_i1 : (3, 6) ∈ envelope_470_i1 := by decide +kernel
theorem children_work_470_i1 : ∀ j, Template HasSnaky 4 (childrenC_470_i1 j) (childrenD_470_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_56 4 (1, 8)).mono (by decide +kernel)
  · exact row_works_470_i2.mono (by decide +kernel)
theorem row_works_470_i1 : Template HasSnaky 5 required_470_i1 envelope_470_i1 := by
  refine compose HasSnaky 4 childrenC_470_i1 childrenD_470_i1 children_work_470_i1 (3, 6)
    required_470_i1 envelope_470_i1 pivot_mem_470_i1 child_required_sub_470_i1 child_envelope_sub_470_i1 ?_
  intro b hb
  exact common_sub_470_i1 (mem_commonEnvelope childrenD_470_i1 b hb)
def required_470 : Finset Cell := ⟨(([(1, 5), (2, 2), (2, 5), (3, 5), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_470 : Finset Cell := ⟨(([(0, 4), (0, 6), (1, 3), (1, 4), (1, 5), (1, 6), (2, 0), (2, 1), (2, 2), (2, 3), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 0), (5, 1), (5, 2), (5, 4), (5, 5), (5, 7), (5, 8), (5, 9), (6, 4), (7, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_470 : Fin 4 → Finset Cell := ![(placed21 0 (1, 0) required_319), (placed21 4 (1, 7) required_335), required_470_i0, required_470_i1]
def childrenD_470 : Fin 4 → Finset Cell := ![(placed21 0 (1, 0) envelope_319), (placed21 4 (1, 7) envelope_335), envelope_470_i0, envelope_470_i1]
theorem common_sub_470 : commonEnvelope childrenD_470 ⊆ insert (3, 3) required_470 := by decide +kernel
theorem child_required_sub_470 : ∀ j, childrenC_470 j ⊆ insert (3, 3) required_470 := by decide +kernel
theorem child_envelope_sub_470 : ∀ j, childrenD_470 j ⊆ envelope_470 := by decide +kernel
theorem pivot_mem_470 : (3, 3) ∈ envelope_470 := by decide +kernel
theorem children_work_470 : ∀ j, Template HasSnaky 8 (childrenC_470 j) (childrenD_470 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_319 0 (1, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_335 4 (1, 7)).mono (by decide +kernel)
  · exact row_works_470_i0.mono (by decide +kernel)
  · exact row_works_470_i1.mono (by decide +kernel)
theorem row_works_470 : Template HasSnaky 9 required_470 envelope_470 := by
  refine compose HasSnaky 8 childrenC_470 childrenD_470 children_work_470 (3, 3)
    required_470 envelope_470 pivot_mem_470 child_required_sub_470 child_envelope_sub_470 ?_
  intro b hb
  exact common_sub_470 (mem_commonEnvelope childrenD_470 b hb)
def required_474 : Finset Cell := ⟨(([(1, 2), (2, 2), (3, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_474 : Finset Cell := ⟨(([(0, 3), (1, 2), (1, 3), (2, 2), (2, 3), (2, 4), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (6, 1), (6, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_474 : Fin 4 → Finset Cell := ![(placed21 1 (0, 2) required_7), (placed21 0 (1, 1) required_8), (placed21 3 (0, 3) required_9), (placed21 2 (5, 0) required_473)]
def childrenD_474 : Fin 4 → Finset Cell := ![(placed21 1 (0, 2) envelope_7), (placed21 0 (1, 1) envelope_8), (placed21 3 (0, 3) envelope_9), (placed21 2 (5, 0) envelope_473)]
theorem common_sub_474 : commonEnvelope childrenD_474 ⊆ insert (4, 2) required_474 := by decide +kernel
theorem child_required_sub_474 : ∀ j, childrenC_474 j ⊆ insert (4, 2) required_474 := by decide +kernel
theorem child_envelope_sub_474 : ∀ j, childrenD_474 j ⊆ envelope_474 := by decide +kernel
theorem pivot_mem_474 : (4, 2) ∈ envelope_474 := by decide +kernel
theorem children_work_474 : ∀ j, Template HasSnaky 8 (childrenC_474 j) (childrenD_474 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 1 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_8 0 (1, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_9 3 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_473 2 (5, 0)).mono (by decide +kernel)
theorem row_works_474 : Template HasSnaky 9 required_474 envelope_474 := by
  refine compose HasSnaky 8 childrenC_474 childrenD_474 children_work_474 (4, 2)
    required_474 envelope_474 pivot_mem_474 child_required_sub_474 child_envelope_sub_474 ?_
  intro b hb
  exact common_sub_474 (mem_commonEnvelope childrenD_474 b hb)
def required_477 : Finset Cell := ⟨(([(1, 2), (2, 2), (3, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_477 : Finset Cell := ⟨(([(0, 1), (0, 3), (0, 4), (0, 5), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 2), (3, 3), (3, 4), (4, 2), (4, 3), (5, 2), (5, 3), (6, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_477 : Fin 4 → Finset Cell := ![(placed21 1 (0, 2) required_7), (placed21 1 (0, 1) required_9), (placed21 1 (0, 1) required_62), required_473]
def childrenD_477 : Fin 4 → Finset Cell := ![(placed21 1 (0, 2) envelope_7), (placed21 1 (0, 1) envelope_9), (placed21 1 (0, 1) envelope_62), envelope_473]
theorem common_sub_477 : commonEnvelope childrenD_477 ⊆ insert (4, 2) required_477 := by decide +kernel
theorem child_required_sub_477 : ∀ j, childrenC_477 j ⊆ insert (4, 2) required_477 := by decide +kernel
theorem child_envelope_sub_477 : ∀ j, childrenD_477 j ⊆ envelope_477 := by decide +kernel
theorem pivot_mem_477 : (4, 2) ∈ envelope_477 := by decide +kernel
theorem children_work_477 : ∀ j, Template HasSnaky 8 (childrenC_477 j) (childrenD_477 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 1 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_9 1 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_62 1 (0, 1)).mono (by decide +kernel)
  · exact row_works_473.mono (by decide +kernel)
theorem row_works_477 : Template HasSnaky 9 required_477 envelope_477 := by
  refine compose HasSnaky 8 childrenC_477 childrenD_477 children_work_477 (4, 2)
    required_477 envelope_477 pivot_mem_477 child_required_sub_477 child_envelope_sub_477 ?_
  intro b hb
  exact common_sub_477 (mem_commonEnvelope childrenD_477 b hb)
def height_443_i6 : ℕ := 2
def childrenH_443_i6 : Fin 2 → ℕ := ![height_3, height_5]
theorem height_exact_443_i6 : height_443_i6 = 1 + Finset.univ.sup childrenH_443_i6 := by decide +kernel
theorem required_origin_443_i6 : ∀ x ∈ required_443_i6,
    (∃ j, x ∈ childrenC_443_i6 j) ∨ ∀ j, x ∈ childrenD_443_i6 j := by decide +kernel
theorem required_exact_443_i6 : required_443_i6 =
    ((Finset.univ.biUnion childrenC_443_i6) ∪ commonEnvelope childrenD_443_i6).erase (5, 3) := by
  exact required_eq_combination childrenC_443_i6 childrenD_443_i6 (5, 3) required_443_i6
    (by decide +kernel) child_required_sub_443_i6 common_sub_443_i6 required_origin_443_i6
theorem envelope_origin_443_i6 : ∀ x ∈ envelope_443_i6,
    x = (5, 3) ∨ ∃ j, x ∈ childrenD_443_i6 j := by decide +kernel
theorem envelope_exact_443_i6 : envelope_443_i6 =
    insert (5, 3) (Finset.univ.biUnion childrenD_443_i6) := by
  exact envelope_eq_combination childrenD_443_i6 (5, 3) envelope_443_i6
    pivot_mem_443_i6 child_envelope_sub_443_i6 envelope_origin_443_i6
def checked_443_i6 : CheckedCard where
  required := required_443_i6
  envelope := envelope_443_i6
  height := height_443_i6
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_443_i6
def height_443_i5 : ℕ := 3
def childrenH_443_i5 : Fin 2 → ℕ := ![height_5, height_443_i6]
theorem height_exact_443_i5 : height_443_i5 = 1 + Finset.univ.sup childrenH_443_i5 := by decide +kernel
theorem required_origin_443_i5 : ∀ x ∈ required_443_i5,
    (∃ j, x ∈ childrenC_443_i5 j) ∨ ∀ j, x ∈ childrenD_443_i5 j := by decide +kernel
theorem required_exact_443_i5 : required_443_i5 =
    ((Finset.univ.biUnion childrenC_443_i5) ∪ commonEnvelope childrenD_443_i5).erase (3, 3) := by
  exact required_eq_combination childrenC_443_i5 childrenD_443_i5 (3, 3) required_443_i5
    (by decide +kernel) child_required_sub_443_i5 common_sub_443_i5 required_origin_443_i5
theorem envelope_origin_443_i5 : ∀ x ∈ envelope_443_i5,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_443_i5 j := by decide +kernel
theorem envelope_exact_443_i5 : envelope_443_i5 =
    insert (3, 3) (Finset.univ.biUnion childrenD_443_i5) := by
  exact envelope_eq_combination childrenD_443_i5 (3, 3) envelope_443_i5
    pivot_mem_443_i5 child_envelope_sub_443_i5 envelope_origin_443_i5
def checked_443_i5 : CheckedCard where
  required := required_443_i5
  envelope := envelope_443_i5
  height := height_443_i5
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_443_i5
def height_443_i4 : ℕ := 4
def childrenH_443_i4 : Fin 2 → ℕ := ![height_5, height_443_i5]
theorem height_exact_443_i4 : height_443_i4 = 1 + Finset.univ.sup childrenH_443_i4 := by decide +kernel
theorem required_origin_443_i4 : ∀ x ∈ required_443_i4,
    (∃ j, x ∈ childrenC_443_i4 j) ∨ ∀ j, x ∈ childrenD_443_i4 j := by decide +kernel
theorem required_exact_443_i4 : required_443_i4 =
    ((Finset.univ.biUnion childrenC_443_i4) ∪ commonEnvelope childrenD_443_i4).erase (4, 1) := by
  exact required_eq_combination childrenC_443_i4 childrenD_443_i4 (4, 1) required_443_i4
    (by decide +kernel) child_required_sub_443_i4 common_sub_443_i4 required_origin_443_i4
theorem envelope_origin_443_i4 : ∀ x ∈ envelope_443_i4,
    x = (4, 1) ∨ ∃ j, x ∈ childrenD_443_i4 j := by decide +kernel
theorem envelope_exact_443_i4 : envelope_443_i4 =
    insert (4, 1) (Finset.univ.biUnion childrenD_443_i4) := by
  exact envelope_eq_combination childrenD_443_i4 (4, 1) envelope_443_i4
    pivot_mem_443_i4 child_envelope_sub_443_i4 envelope_origin_443_i4
def checked_443_i4 : CheckedCard where
  required := required_443_i4
  envelope := envelope_443_i4
  height := height_443_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_443_i4
def height_443_i3 : ℕ := 5
def childrenH_443_i3 : Fin 2 → ℕ := ![height_5, height_443_i4]
theorem height_exact_443_i3 : height_443_i3 = 1 + Finset.univ.sup childrenH_443_i3 := by decide +kernel
theorem required_origin_443_i3 : ∀ x ∈ required_443_i3,
    (∃ j, x ∈ childrenC_443_i3 j) ∨ ∀ j, x ∈ childrenD_443_i3 j := by decide +kernel
theorem required_exact_443_i3 : required_443_i3 =
    ((Finset.univ.biUnion childrenC_443_i3) ∪ commonEnvelope childrenD_443_i3).erase (2, 4) := by
  exact required_eq_combination childrenC_443_i3 childrenD_443_i3 (2, 4) required_443_i3
    (by decide +kernel) child_required_sub_443_i3 common_sub_443_i3 required_origin_443_i3
theorem envelope_origin_443_i3 : ∀ x ∈ envelope_443_i3,
    x = (2, 4) ∨ ∃ j, x ∈ childrenD_443_i3 j := by decide +kernel
theorem envelope_exact_443_i3 : envelope_443_i3 =
    insert (2, 4) (Finset.univ.biUnion childrenD_443_i3) := by
  exact envelope_eq_combination childrenD_443_i3 (2, 4) envelope_443_i3
    pivot_mem_443_i3 child_envelope_sub_443_i3 envelope_origin_443_i3
def checked_443_i3 : CheckedCard where
  required := required_443_i3
  envelope := envelope_443_i3
  height := height_443_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_443_i3
def height_443_i2 : ℕ := 6
def childrenH_443_i2 : Fin 2 → ℕ := ![height_4, height_443_i3]
theorem height_exact_443_i2 : height_443_i2 = 1 + Finset.univ.sup childrenH_443_i2 := by decide +kernel
theorem required_origin_443_i2 : ∀ x ∈ required_443_i2,
    (∃ j, x ∈ childrenC_443_i2 j) ∨ ∀ j, x ∈ childrenD_443_i2 j := by decide +kernel
theorem required_exact_443_i2 : required_443_i2 =
    ((Finset.univ.biUnion childrenC_443_i2) ∪ commonEnvelope childrenD_443_i2).erase (4, 0) := by
  exact required_eq_combination childrenC_443_i2 childrenD_443_i2 (4, 0) required_443_i2
    (by decide +kernel) child_required_sub_443_i2 common_sub_443_i2 required_origin_443_i2
theorem envelope_origin_443_i2 : ∀ x ∈ envelope_443_i2,
    x = (4, 0) ∨ ∃ j, x ∈ childrenD_443_i2 j := by decide +kernel
theorem envelope_exact_443_i2 : envelope_443_i2 =
    insert (4, 0) (Finset.univ.biUnion childrenD_443_i2) := by
  exact envelope_eq_combination childrenD_443_i2 (4, 0) envelope_443_i2
    pivot_mem_443_i2 child_envelope_sub_443_i2 envelope_origin_443_i2
def checked_443_i2 : CheckedCard where
  required := required_443_i2
  envelope := envelope_443_i2
  height := height_443_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_443_i2
def height_443_i1 : ℕ := 7
def childrenH_443_i1 : Fin 2 → ℕ := ![height_4, height_443_i2]
theorem height_exact_443_i1 : height_443_i1 = 1 + Finset.univ.sup childrenH_443_i1 := by decide +kernel
theorem required_origin_443_i1 : ∀ x ∈ required_443_i1,
    (∃ j, x ∈ childrenC_443_i1 j) ∨ ∀ j, x ∈ childrenD_443_i1 j := by decide +kernel
theorem required_exact_443_i1 : required_443_i1 =
    ((Finset.univ.biUnion childrenC_443_i1) ∪ commonEnvelope childrenD_443_i1).erase (3, 1) := by
  exact required_eq_combination childrenC_443_i1 childrenD_443_i1 (3, 1) required_443_i1
    (by decide +kernel) child_required_sub_443_i1 common_sub_443_i1 required_origin_443_i1
theorem envelope_origin_443_i1 : ∀ x ∈ envelope_443_i1,
    x = (3, 1) ∨ ∃ j, x ∈ childrenD_443_i1 j := by decide +kernel
theorem envelope_exact_443_i1 : envelope_443_i1 =
    insert (3, 1) (Finset.univ.biUnion childrenD_443_i1) := by
  exact envelope_eq_combination childrenD_443_i1 (3, 1) envelope_443_i1
    pivot_mem_443_i1 child_envelope_sub_443_i1 envelope_origin_443_i1
def checked_443_i1 : CheckedCard where
  required := required_443_i1
  envelope := envelope_443_i1
  height := height_443_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_443_i1
def height_443_i0 : ℕ := 8
def childrenH_443_i0 : Fin 2 → ℕ := ![height_5, height_443_i1]
theorem height_exact_443_i0 : height_443_i0 = 1 + Finset.univ.sup childrenH_443_i0 := by decide +kernel
theorem required_origin_443_i0 : ∀ x ∈ required_443_i0,
    (∃ j, x ∈ childrenC_443_i0 j) ∨ ∀ j, x ∈ childrenD_443_i0 j := by decide +kernel
theorem required_exact_443_i0 : required_443_i0 =
    ((Finset.univ.biUnion childrenC_443_i0) ∪ commonEnvelope childrenD_443_i0).erase (0, 1) := by
  exact required_eq_combination childrenC_443_i0 childrenD_443_i0 (0, 1) required_443_i0
    (by decide +kernel) child_required_sub_443_i0 common_sub_443_i0 required_origin_443_i0
theorem envelope_origin_443_i0 : ∀ x ∈ envelope_443_i0,
    x = (0, 1) ∨ ∃ j, x ∈ childrenD_443_i0 j := by decide +kernel
theorem envelope_exact_443_i0 : envelope_443_i0 =
    insert (0, 1) (Finset.univ.biUnion childrenD_443_i0) := by
  exact envelope_eq_combination childrenD_443_i0 (0, 1) envelope_443_i0
    pivot_mem_443_i0 child_envelope_sub_443_i0 envelope_origin_443_i0
def checked_443_i0 : CheckedCard where
  required := required_443_i0
  envelope := envelope_443_i0
  height := height_443_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_443_i0
def height_443 : ℕ := 9
def childrenH_443 : Fin 2 → ℕ := ![height_5, height_443_i0]
theorem height_exact_443 : height_443 = 1 + Finset.univ.sup childrenH_443 := by decide +kernel
theorem required_origin_443 : ∀ x ∈ required_443,
    (∃ j, x ∈ childrenC_443 j) ∨ ∀ j, x ∈ childrenD_443 j := by decide +kernel
theorem required_exact_443 : required_443 =
    ((Finset.univ.biUnion childrenC_443) ∪ commonEnvelope childrenD_443).erase (2, 1) := by
  exact required_eq_combination childrenC_443 childrenD_443 (2, 1) required_443
    (by decide +kernel) child_required_sub_443 common_sub_443 required_origin_443
theorem envelope_origin_443 : ∀ x ∈ envelope_443,
    x = (2, 1) ∨ ∃ j, x ∈ childrenD_443 j := by decide +kernel
theorem envelope_exact_443 : envelope_443 =
    insert (2, 1) (Finset.univ.biUnion childrenD_443) := by
  exact envelope_eq_combination childrenD_443 (2, 1) envelope_443
    pivot_mem_443 child_envelope_sub_443 envelope_origin_443
def checked_443 : CheckedCard where
  required := required_443
  envelope := envelope_443
  height := height_443
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_443
def height_449 : ℕ := 9
def childrenH_449 : Fin 5 → ℕ := ![height_10, height_27, height_48, height_63, height_448]
theorem height_exact_449 : height_449 = 1 + Finset.univ.sup childrenH_449 := by decide +kernel
theorem required_origin_449 : ∀ x ∈ required_449,
    (∃ j, x ∈ childrenC_449 j) ∨ ∀ j, x ∈ childrenD_449 j := by decide +kernel
theorem required_exact_449 : required_449 =
    ((Finset.univ.biUnion childrenC_449) ∪ commonEnvelope childrenD_449).erase (4, 3) := by
  exact required_eq_combination childrenC_449 childrenD_449 (4, 3) required_449
    (by decide +kernel) child_required_sub_449 common_sub_449 required_origin_449
theorem envelope_origin_449 : ∀ x ∈ envelope_449,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_449 j := by decide +kernel
theorem envelope_exact_449 : envelope_449 =
    insert (4, 3) (Finset.univ.biUnion childrenD_449) := by
  exact envelope_eq_combination childrenD_449 (4, 3) envelope_449
    pivot_mem_449 child_envelope_sub_449 envelope_origin_449
def checked_449 : CheckedCard where
  required := required_449
  envelope := envelope_449
  height := height_449
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_449
def height_450 : ℕ := 9
def childrenH_450 : Fin 2 → ℕ := ![height_0, height_448]
theorem height_exact_450 : height_450 = 1 + Finset.univ.sup childrenH_450 := by decide +kernel
theorem required_origin_450 : ∀ x ∈ required_450,
    (∃ j, x ∈ childrenC_450 j) ∨ ∀ j, x ∈ childrenD_450 j := by decide +kernel
theorem required_exact_450 : required_450 =
    ((Finset.univ.biUnion childrenC_450) ∪ commonEnvelope childrenD_450).erase (3, 4) := by
  exact required_eq_combination childrenC_450 childrenD_450 (3, 4) required_450
    (by decide +kernel) child_required_sub_450 common_sub_450 required_origin_450
theorem envelope_origin_450 : ∀ x ∈ envelope_450,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_450 j := by decide +kernel
theorem envelope_exact_450 : envelope_450 =
    insert (3, 4) (Finset.univ.biUnion childrenD_450) := by
  exact envelope_eq_combination childrenD_450 (3, 4) envelope_450
    pivot_mem_450 child_envelope_sub_450 envelope_origin_450
def checked_450 : CheckedCard where
  required := required_450
  envelope := envelope_450
  height := height_450
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_450
def height_457 : ℕ := 9
def childrenH_457 : Fin 4 → ℕ := ![height_7, height_8, height_9, height_456]
theorem height_exact_457 : height_457 = 1 + Finset.univ.sup childrenH_457 := by decide +kernel
theorem required_origin_457 : ∀ x ∈ required_457,
    (∃ j, x ∈ childrenC_457 j) ∨ ∀ j, x ∈ childrenD_457 j := by decide +kernel
theorem required_exact_457 : required_457 =
    ((Finset.univ.biUnion childrenC_457) ∪ commonEnvelope childrenD_457).erase (1, 4) := by
  exact required_eq_combination childrenC_457 childrenD_457 (1, 4) required_457
    (by decide +kernel) child_required_sub_457 common_sub_457 required_origin_457
theorem envelope_origin_457 : ∀ x ∈ envelope_457,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_457 j := by decide +kernel
theorem envelope_exact_457 : envelope_457 =
    insert (1, 4) (Finset.univ.biUnion childrenD_457) := by
  exact envelope_eq_combination childrenD_457 (1, 4) envelope_457
    pivot_mem_457 child_envelope_sub_457 envelope_origin_457
def checked_457 : CheckedCard where
  required := required_457
  envelope := envelope_457
  height := height_457
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_457
def height_458 : ℕ := 9
def childrenH_458 : Fin 4 → ℕ := ![height_7, height_9, height_62, height_456]
theorem height_exact_458 : height_458 = 1 + Finset.univ.sup childrenH_458 := by decide +kernel
theorem required_origin_458 : ∀ x ∈ required_458,
    (∃ j, x ∈ childrenC_458 j) ∨ ∀ j, x ∈ childrenD_458 j := by decide +kernel
theorem required_exact_458 : required_458 =
    ((Finset.univ.biUnion childrenC_458) ∪ commonEnvelope childrenD_458).erase (1, 4) := by
  exact required_eq_combination childrenC_458 childrenD_458 (1, 4) required_458
    (by decide +kernel) child_required_sub_458 common_sub_458 required_origin_458
theorem envelope_origin_458 : ∀ x ∈ envelope_458,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_458 j := by decide +kernel
theorem envelope_exact_458 : envelope_458 =
    insert (1, 4) (Finset.univ.biUnion childrenD_458) := by
  exact envelope_eq_combination childrenD_458 (1, 4) envelope_458
    pivot_mem_458 child_envelope_sub_458 envelope_origin_458
def checked_458 : CheckedCard where
  required := required_458
  envelope := envelope_458
  height := height_458
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_458
def height_470_i0 : ℕ := 4
def childrenH_470_i0 : Fin 2 → ℕ := ![height_54, height_78]
theorem height_exact_470_i0 : height_470_i0 = 1 + Finset.univ.sup childrenH_470_i0 := by decide +kernel
theorem required_origin_470_i0 : ∀ x ∈ required_470_i0,
    (∃ j, x ∈ childrenC_470_i0 j) ∨ ∀ j, x ∈ childrenD_470_i0 j := by decide +kernel
theorem required_exact_470_i0 : required_470_i0 =
    ((Finset.univ.biUnion childrenC_470_i0) ∪ commonEnvelope childrenD_470_i0).erase (2, 3) := by
  exact required_eq_combination childrenC_470_i0 childrenD_470_i0 (2, 3) required_470_i0
    (by decide +kernel) child_required_sub_470_i0 common_sub_470_i0 required_origin_470_i0
theorem envelope_origin_470_i0 : ∀ x ∈ envelope_470_i0,
    x = (2, 3) ∨ ∃ j, x ∈ childrenD_470_i0 j := by decide +kernel
theorem envelope_exact_470_i0 : envelope_470_i0 =
    insert (2, 3) (Finset.univ.biUnion childrenD_470_i0) := by
  exact envelope_eq_combination childrenD_470_i0 (2, 3) envelope_470_i0
    pivot_mem_470_i0 child_envelope_sub_470_i0 envelope_origin_470_i0
def checked_470_i0 : CheckedCard where
  required := required_470_i0
  envelope := envelope_470_i0
  height := height_470_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_470_i0
def height_470_i2 : ℕ := 4
def childrenH_470_i2 : Fin 2 → ℕ := ![height_2, height_78]
theorem height_exact_470_i2 : height_470_i2 = 1 + Finset.univ.sup childrenH_470_i2 := by decide +kernel
theorem required_origin_470_i2 : ∀ x ∈ required_470_i2,
    (∃ j, x ∈ childrenC_470_i2 j) ∨ ∀ j, x ∈ childrenD_470_i2 j := by decide +kernel
theorem required_exact_470_i2 : required_470_i2 =
    ((Finset.univ.biUnion childrenC_470_i2) ∪ commonEnvelope childrenD_470_i2).erase (2, 3) := by
  exact required_eq_combination childrenC_470_i2 childrenD_470_i2 (2, 3) required_470_i2
    (by decide +kernel) child_required_sub_470_i2 common_sub_470_i2 required_origin_470_i2
theorem envelope_origin_470_i2 : ∀ x ∈ envelope_470_i2,
    x = (2, 3) ∨ ∃ j, x ∈ childrenD_470_i2 j := by decide +kernel
theorem envelope_exact_470_i2 : envelope_470_i2 =
    insert (2, 3) (Finset.univ.biUnion childrenD_470_i2) := by
  exact envelope_eq_combination childrenD_470_i2 (2, 3) envelope_470_i2
    pivot_mem_470_i2 child_envelope_sub_470_i2 envelope_origin_470_i2
def checked_470_i2 : CheckedCard where
  required := required_470_i2
  envelope := envelope_470_i2
  height := height_470_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_470_i2
def height_470_i1 : ℕ := 5
def childrenH_470_i1 : Fin 2 → ℕ := ![height_56, height_470_i2]
theorem height_exact_470_i1 : height_470_i1 = 1 + Finset.univ.sup childrenH_470_i1 := by decide +kernel
theorem required_origin_470_i1 : ∀ x ∈ required_470_i1,
    (∃ j, x ∈ childrenC_470_i1 j) ∨ ∀ j, x ∈ childrenD_470_i1 j := by decide +kernel
theorem required_exact_470_i1 : required_470_i1 =
    ((Finset.univ.biUnion childrenC_470_i1) ∪ commonEnvelope childrenD_470_i1).erase (3, 6) := by
  exact required_eq_combination childrenC_470_i1 childrenD_470_i1 (3, 6) required_470_i1
    (by decide +kernel) child_required_sub_470_i1 common_sub_470_i1 required_origin_470_i1
theorem envelope_origin_470_i1 : ∀ x ∈ envelope_470_i1,
    x = (3, 6) ∨ ∃ j, x ∈ childrenD_470_i1 j := by decide +kernel
theorem envelope_exact_470_i1 : envelope_470_i1 =
    insert (3, 6) (Finset.univ.biUnion childrenD_470_i1) := by
  exact envelope_eq_combination childrenD_470_i1 (3, 6) envelope_470_i1
    pivot_mem_470_i1 child_envelope_sub_470_i1 envelope_origin_470_i1
def checked_470_i1 : CheckedCard where
  required := required_470_i1
  envelope := envelope_470_i1
  height := height_470_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_470_i1
def height_470 : ℕ := 9
def childrenH_470 : Fin 4 → ℕ := ![height_319, height_335, height_470_i0, height_470_i1]
theorem height_exact_470 : height_470 = 1 + Finset.univ.sup childrenH_470 := by decide +kernel
theorem required_origin_470 : ∀ x ∈ required_470,
    (∃ j, x ∈ childrenC_470 j) ∨ ∀ j, x ∈ childrenD_470 j := by decide +kernel
theorem required_exact_470 : required_470 =
    ((Finset.univ.biUnion childrenC_470) ∪ commonEnvelope childrenD_470).erase (3, 3) := by
  exact required_eq_combination childrenC_470 childrenD_470 (3, 3) required_470
    (by decide +kernel) child_required_sub_470 common_sub_470 required_origin_470
theorem envelope_origin_470 : ∀ x ∈ envelope_470,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_470 j := by decide +kernel
theorem envelope_exact_470 : envelope_470 =
    insert (3, 3) (Finset.univ.biUnion childrenD_470) := by
  exact envelope_eq_combination childrenD_470 (3, 3) envelope_470
    pivot_mem_470 child_envelope_sub_470 envelope_origin_470
def checked_470 : CheckedCard where
  required := required_470
  envelope := envelope_470
  height := height_470
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_470
def height_474 : ℕ := 9
def childrenH_474 : Fin 4 → ℕ := ![height_7, height_8, height_9, height_473]
theorem height_exact_474 : height_474 = 1 + Finset.univ.sup childrenH_474 := by decide +kernel
theorem required_origin_474 : ∀ x ∈ required_474,
    (∃ j, x ∈ childrenC_474 j) ∨ ∀ j, x ∈ childrenD_474 j := by decide +kernel
theorem required_exact_474 : required_474 =
    ((Finset.univ.biUnion childrenC_474) ∪ commonEnvelope childrenD_474).erase (4, 2) := by
  exact required_eq_combination childrenC_474 childrenD_474 (4, 2) required_474
    (by decide +kernel) child_required_sub_474 common_sub_474 required_origin_474
theorem envelope_origin_474 : ∀ x ∈ envelope_474,
    x = (4, 2) ∨ ∃ j, x ∈ childrenD_474 j := by decide +kernel
theorem envelope_exact_474 : envelope_474 =
    insert (4, 2) (Finset.univ.biUnion childrenD_474) := by
  exact envelope_eq_combination childrenD_474 (4, 2) envelope_474
    pivot_mem_474 child_envelope_sub_474 envelope_origin_474
def checked_474 : CheckedCard where
  required := required_474
  envelope := envelope_474
  height := height_474
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_474
def height_477 : ℕ := 9
def childrenH_477 : Fin 4 → ℕ := ![height_7, height_9, height_62, height_473]
theorem height_exact_477 : height_477 = 1 + Finset.univ.sup childrenH_477 := by decide +kernel
theorem required_origin_477 : ∀ x ∈ required_477,
    (∃ j, x ∈ childrenC_477 j) ∨ ∀ j, x ∈ childrenD_477 j := by decide +kernel
theorem required_exact_477 : required_477 =
    ((Finset.univ.biUnion childrenC_477) ∪ commonEnvelope childrenD_477).erase (4, 2) := by
  exact required_eq_combination childrenC_477 childrenD_477 (4, 2) required_477
    (by decide +kernel) child_required_sub_477 common_sub_477 required_origin_477
theorem envelope_origin_477 : ∀ x ∈ envelope_477,
    x = (4, 2) ∨ ∃ j, x ∈ childrenD_477 j := by decide +kernel
theorem envelope_exact_477 : envelope_477 =
    insert (4, 2) (Finset.univ.biUnion childrenD_477) := by
  exact envelope_eq_combination childrenD_477 (4, 2) envelope_477
    pivot_mem_477 child_envelope_sub_477 envelope_origin_477
def checked_477 : CheckedCard where
  required := required_477
  envelope := envelope_477
  height := height_477
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_477
end SnakyPrototype.Certificate21

end OAI
