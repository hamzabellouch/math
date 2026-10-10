import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part06
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part06
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part03
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_595_i6 : Finset Cell := ⟨(([(1, 1), (2, 1), (3, 1), (5, 0), (5, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_595_i6 : Finset Cell := ⟨(([(1, 1), (2, 1), (3, 1), (4, 0), (4, 1), (5, 0), (5, 1), (6, 0)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_595_i6 : Fin 2 → Finset Cell := ![(placed21 4 (1, 1) required_4), (placed21 4 (2, 1) required_5)]
def childrenD_595_i6 : Fin 2 → Finset Cell := ![(placed21 4 (1, 1) envelope_4), (placed21 4 (2, 1) envelope_5)]
theorem common_sub_595_i6 : commonEnvelope childrenD_595_i6 ⊆ insert (4, 1) required_595_i6 := by decide +kernel
theorem child_required_sub_595_i6 : ∀ j, childrenC_595_i6 j ⊆ insert (4, 1) required_595_i6 := by decide +kernel
theorem child_envelope_sub_595_i6 : ∀ j, childrenD_595_i6 j ⊆ envelope_595_i6 := by decide +kernel
theorem pivot_mem_595_i6 : (4, 1) ∈ envelope_595_i6 := by decide +kernel
theorem children_work_595_i6 : ∀ j, Template HasSnaky 1 (childrenC_595_i6 j) (childrenD_595_i6 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_4 4 (1, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_5 4 (2, 1)).mono (by decide +kernel)
theorem row_works_595_i6 : Template HasSnaky 2 required_595_i6 envelope_595_i6 := by
  refine compose HasSnaky 1 childrenC_595_i6 childrenD_595_i6 children_work_595_i6 (4, 1)
    required_595_i6 envelope_595_i6 pivot_mem_595_i6 child_required_sub_595_i6 child_envelope_sub_595_i6 ?_
  intro b hb
  exact common_sub_595_i6 (mem_commonEnvelope childrenD_595_i6 b hb)
def required_595_i5 : Finset Cell := ⟨(([(1, 1), (2, 1), (3, 1), (5, 1), (6, 2), (6, 3), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_595_i5 : Finset Cell := ⟨(([(1, 1), (2, 1), (3, 1), (4, 0), (4, 1), (5, 0), (5, 1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_595_i5 : Fin 2 → Finset Cell := ![(placed21 7 (6, 4) required_3), required_595_i6]
def childrenD_595_i5 : Fin 2 → Finset Cell := ![(placed21 7 (6, 4) envelope_3), envelope_595_i6]
theorem common_sub_595_i5 : commonEnvelope childrenD_595_i5 ⊆ insert (5, 0) required_595_i5 := by decide +kernel
theorem child_required_sub_595_i5 : ∀ j, childrenC_595_i5 j ⊆ insert (5, 0) required_595_i5 := by decide +kernel
theorem child_envelope_sub_595_i5 : ∀ j, childrenD_595_i5 j ⊆ envelope_595_i5 := by decide +kernel
theorem pivot_mem_595_i5 : (5, 0) ∈ envelope_595_i5 := by decide +kernel
theorem children_work_595_i5 : ∀ j, Template HasSnaky 2 (childrenC_595_i5 j) (childrenD_595_i5 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_3 7 (6, 4)).mono (by decide +kernel)
  · exact row_works_595_i6.mono (by decide +kernel)
theorem row_works_595_i5 : Template HasSnaky 3 required_595_i5 envelope_595_i5 := by
  refine compose HasSnaky 2 childrenC_595_i5 childrenD_595_i5 children_work_595_i5 (5, 0)
    required_595_i5 envelope_595_i5 pivot_mem_595_i5 child_required_sub_595_i5 child_envelope_sub_595_i5 ?_
  intro b hb
  exact common_sub_595_i5 (mem_commonEnvelope childrenD_595_i5 b hb)
def required_595_i4 : Finset Cell := ⟨(([(1, 1), (2, 1), (3, 1), (6, 2), (6, 3), (6, 4), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_595_i4 : Finset Cell := ⟨(([(1, 1), (2, 1), (3, 1), (4, 0), (4, 1), (5, 0), (5, 1), (5, 2), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_595_i4 : Fin 2 → Finset Cell := ![(placed21 7 (6, 5) required_4), required_595_i5]
def childrenD_595_i4 : Fin 2 → Finset Cell := ![(placed21 7 (6, 5) envelope_4), envelope_595_i5]
theorem common_sub_595_i4 : commonEnvelope childrenD_595_i4 ⊆ insert (5, 1) required_595_i4 := by decide +kernel
theorem child_required_sub_595_i4 : ∀ j, childrenC_595_i4 j ⊆ insert (5, 1) required_595_i4 := by decide +kernel
theorem child_envelope_sub_595_i4 : ∀ j, childrenD_595_i4 j ⊆ envelope_595_i4 := by decide +kernel
theorem pivot_mem_595_i4 : (5, 1) ∈ envelope_595_i4 := by decide +kernel
theorem children_work_595_i4 : ∀ j, Template HasSnaky 3 (childrenC_595_i4 j) (childrenD_595_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_4 7 (6, 5)).mono (by decide +kernel)
  · exact row_works_595_i5.mono (by decide +kernel)
theorem row_works_595_i4 : Template HasSnaky 4 required_595_i4 envelope_595_i4 := by
  refine compose HasSnaky 3 childrenC_595_i4 childrenD_595_i4 children_work_595_i4 (5, 1)
    required_595_i4 envelope_595_i4 pivot_mem_595_i4 child_required_sub_595_i4 child_envelope_sub_595_i4 ?_
  intro b hb
  exact common_sub_595_i4 (mem_commonEnvelope childrenD_595_i4 b hb)
def required_595_i3 : Finset Cell := ⟨(([(0, 1), (1, 1), (3, 1), (3, 2), (6, 2), (6, 3), (6, 4), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_595_i3 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2), (5, 0), (5, 1), (5, 2), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_595_i3 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) required_5), required_595_i4]
def childrenD_595_i3 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) envelope_5), envelope_595_i4]
theorem common_sub_595_i3 : commonEnvelope childrenD_595_i3 ⊆ insert (2, 1) required_595_i3 := by decide +kernel
theorem child_required_sub_595_i3 : ∀ j, childrenC_595_i3 j ⊆ insert (2, 1) required_595_i3 := by decide +kernel
theorem child_envelope_sub_595_i3 : ∀ j, childrenD_595_i3 j ⊆ envelope_595_i3 := by decide +kernel
theorem pivot_mem_595_i3 : (2, 1) ∈ envelope_595_i3 := by decide +kernel
theorem children_work_595_i3 : ∀ j, Template HasSnaky 4 (childrenC_595_i3 j) (childrenD_595_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 0 (0, 1)).mono (by decide +kernel)
  · exact row_works_595_i4.mono (by decide +kernel)
theorem row_works_595_i3 : Template HasSnaky 5 required_595_i3 envelope_595_i3 := by
  refine compose HasSnaky 4 childrenC_595_i3 childrenD_595_i3 children_work_595_i3 (2, 1)
    required_595_i3 envelope_595_i3 pivot_mem_595_i3 child_required_sub_595_i3 child_envelope_sub_595_i3 ?_
  intro b hb
  exact common_sub_595_i3 (mem_commonEnvelope childrenD_595_i3 b hb)
def required_595_i7 : Finset Cell := ⟨(([(0, 1), (1, 1), (3, 1), (3, 2), (6, 2), (6, 3), (6, 4), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_595_i7 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (3, 1), (3, 2), (4, 1), (4, 2), (5, 0), (5, 1), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (7, 0), (7, 1), (7, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_595_i7 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) required_2), (placed21 7 (7, 5) required_208)]
def childrenD_595_i7 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) envelope_2), (placed21 7 (7, 5) envelope_208)]
theorem common_sub_595_i7 : commonEnvelope childrenD_595_i7 ⊆ insert (4, 2) required_595_i7 := by decide +kernel
theorem child_required_sub_595_i7 : ∀ j, childrenC_595_i7 j ⊆ insert (4, 2) required_595_i7 := by decide +kernel
theorem child_envelope_sub_595_i7 : ∀ j, childrenD_595_i7 j ⊆ envelope_595_i7 := by decide +kernel
theorem pivot_mem_595_i7 : (4, 2) ∈ envelope_595_i7 := by decide +kernel
theorem children_work_595_i7 : ∀ j, Template HasSnaky 4 (childrenC_595_i7 j) (childrenD_595_i7 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_2 0 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_208 7 (7, 5)).mono (by decide +kernel)
theorem row_works_595_i7 : Template HasSnaky 5 required_595_i7 envelope_595_i7 := by
  refine compose HasSnaky 4 childrenC_595_i7 childrenD_595_i7 children_work_595_i7 (4, 2)
    required_595_i7 envelope_595_i7 pivot_mem_595_i7 child_required_sub_595_i7 child_envelope_sub_595_i7 ?_
  intro b hb
  exact common_sub_595_i7 (mem_commonEnvelope childrenD_595_i7 b hb)
def required_595_i9 : Finset Cell := ⟨(([(3, 1), (3, 2), (5, 2), (6, 2), (6, 3), (6, 4), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_595_i9 : Finset Cell := ⟨(([(2, 1), (3, 1), (3, 2), (4, 1), (4, 2), (5, 2), (6, 2), (6, 3), (6, 4), (6, 5), (7, 1), (7, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_595_i9 : Fin 2 → Finset Cell := ![(placed21 6 (6, 2) required_5), (placed21 1 (3, 1) required_153)]
def childrenD_595_i9 : Fin 2 → Finset Cell := ![(placed21 6 (6, 2) envelope_5), (placed21 1 (3, 1) envelope_153)]
theorem common_sub_595_i9 : commonEnvelope childrenD_595_i9 ⊆ insert (4, 2) required_595_i9 := by decide +kernel
theorem child_required_sub_595_i9 : ∀ j, childrenC_595_i9 j ⊆ insert (4, 2) required_595_i9 := by decide +kernel
theorem child_envelope_sub_595_i9 : ∀ j, childrenD_595_i9 j ⊆ envelope_595_i9 := by decide +kernel
theorem pivot_mem_595_i9 : (4, 2) ∈ envelope_595_i9 := by decide +kernel
theorem children_work_595_i9 : ∀ j, Template HasSnaky 2 (childrenC_595_i9 j) (childrenD_595_i9 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 6 (6, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_153 1 (3, 1)).mono (by decide +kernel)
theorem row_works_595_i9 : Template HasSnaky 3 required_595_i9 envelope_595_i9 := by
  refine compose HasSnaky 2 childrenC_595_i9 childrenD_595_i9 children_work_595_i9 (4, 2)
    required_595_i9 envelope_595_i9 pivot_mem_595_i9 child_required_sub_595_i9 child_envelope_sub_595_i9 ?_
  intro b hb
  exact common_sub_595_i9 (mem_commonEnvelope childrenD_595_i9 b hb)
def required_595_i8 : Finset Cell := ⟨(([(3, 1), (3, 2), (6, 2), (6, 3), (6, 4), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_595_i8 : Finset Cell := ⟨(([(2, 1), (3, 1), (3, 2), (4, 1), (4, 2), (5, 1), (5, 2), (6, 2), (6, 3), (6, 4), (6, 5), (7, 1), (7, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_595_i8 : Fin 2 → Finset Cell := ![(placed21 7 (6, 5) required_5), required_595_i9]
def childrenD_595_i8 : Fin 2 → Finset Cell := ![(placed21 7 (6, 5) envelope_5), envelope_595_i9]
theorem common_sub_595_i8 : commonEnvelope childrenD_595_i8 ⊆ insert (5, 2) required_595_i8 := by decide +kernel
theorem child_required_sub_595_i8 : ∀ j, childrenC_595_i8 j ⊆ insert (5, 2) required_595_i8 := by decide +kernel
theorem child_envelope_sub_595_i8 : ∀ j, childrenD_595_i8 j ⊆ envelope_595_i8 := by decide +kernel
theorem pivot_mem_595_i8 : (5, 2) ∈ envelope_595_i8 := by decide +kernel
theorem children_work_595_i8 : ∀ j, Template HasSnaky 3 (childrenC_595_i8 j) (childrenD_595_i8 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 7 (6, 5)).mono (by decide +kernel)
  · exact row_works_595_i9.mono (by decide +kernel)
theorem row_works_595_i8 : Template HasSnaky 4 required_595_i8 envelope_595_i8 := by
  refine compose HasSnaky 3 childrenC_595_i8 childrenD_595_i8 children_work_595_i8 (5, 2)
    required_595_i8 envelope_595_i8 pivot_mem_595_i8 child_required_sub_595_i8 child_envelope_sub_595_i8 ?_
  intro b hb
  exact common_sub_595_i8 (mem_commonEnvelope childrenD_595_i8 b hb)
def required_595_i10 : Finset Cell := ⟨(([(0, 1), (1, 1), (3, 1), (3, 2), (6, 2), (6, 3), (6, 4), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_595_i10 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (3, 1), (3, 2), (4, 2), (5, 2), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (7, 0), (7, 1), (7, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_595_i10 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) required_2), (placed21 7 (7, 5) required_157)]
def childrenD_595_i10 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) envelope_2), (placed21 7 (7, 5) envelope_157)]
theorem common_sub_595_i10 : commonEnvelope childrenD_595_i10 ⊆ insert (4, 2) required_595_i10 := by decide +kernel
theorem child_required_sub_595_i10 : ∀ j, childrenC_595_i10 j ⊆ insert (4, 2) required_595_i10 := by decide +kernel
theorem child_envelope_sub_595_i10 : ∀ j, childrenD_595_i10 j ⊆ envelope_595_i10 := by decide +kernel
theorem pivot_mem_595_i10 : (4, 2) ∈ envelope_595_i10 := by decide +kernel
theorem children_work_595_i10 : ∀ j, Template HasSnaky 3 (childrenC_595_i10 j) (childrenD_595_i10 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_2 0 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_157 7 (7, 5)).mono (by decide +kernel)
theorem row_works_595_i10 : Template HasSnaky 4 required_595_i10 envelope_595_i10 := by
  refine compose HasSnaky 3 childrenC_595_i10 childrenD_595_i10 children_work_595_i10 (4, 2)
    required_595_i10 envelope_595_i10 pivot_mem_595_i10 child_required_sub_595_i10 child_envelope_sub_595_i10 ?_
  intro b hb
  exact common_sub_595_i10 (mem_commonEnvelope childrenD_595_i10 b hb)
def required_595_i2 : Finset Cell := ⟨(([(0, 1), (1, 1), (3, 1), (3, 2), (6, 3), (6, 4), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_595_i2 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2), (5, 0), (5, 1), (5, 2), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (7, 0), (7, 1), (7, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_595_i2 : Fin 5 → Finset Cell := ![(placed21 7 (7, 5) required_8), required_595_i3, required_595_i7, required_595_i8, required_595_i10]
def childrenD_595_i2 : Fin 5 → Finset Cell := ![(placed21 7 (7, 5) envelope_8), envelope_595_i3, envelope_595_i7, envelope_595_i8, envelope_595_i10]
theorem common_sub_595_i2 : commonEnvelope childrenD_595_i2 ⊆ insert (6, 2) required_595_i2 := by decide +kernel
theorem child_required_sub_595_i2 : ∀ j, childrenC_595_i2 j ⊆ insert (6, 2) required_595_i2 := by decide +kernel
theorem child_envelope_sub_595_i2 : ∀ j, childrenD_595_i2 j ⊆ envelope_595_i2 := by decide +kernel
theorem pivot_mem_595_i2 : (6, 2) ∈ envelope_595_i2 := by decide +kernel
theorem children_work_595_i2 : ∀ j, Template HasSnaky 5 (childrenC_595_i2 j) (childrenD_595_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_8 7 (7, 5)).mono (by decide +kernel)
  · exact row_works_595_i3.mono (by decide +kernel)
  · exact row_works_595_i7.mono (by decide +kernel)
  · exact row_works_595_i8.mono (by decide +kernel)
  · exact row_works_595_i10.mono (by decide +kernel)
theorem row_works_595_i2 : Template HasSnaky 6 required_595_i2 envelope_595_i2 := by
  refine compose HasSnaky 5 childrenC_595_i2 childrenD_595_i2 children_work_595_i2 (6, 2)
    required_595_i2 envelope_595_i2 pivot_mem_595_i2 child_required_sub_595_i2 child_envelope_sub_595_i2 ?_
  intro b hb
  exact common_sub_595_i2 (mem_commonEnvelope childrenD_595_i2 b hb)
def required_595_i1 : Finset Cell := ⟨(([(0, 1), (1, 1), (3, 1), (3, 2), (3, 4), (4, 4), (5, 4), (6, 4), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_595_i1 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (3, 1), (3, 2), (3, 4), (4, 0), (4, 1), (4, 2), (4, 4), (5, 0), (5, 1), (5, 2), (5, 4), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (7, 0), (7, 1), (7, 2), (7, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_595_i1 : Fin 2 → Finset Cell := ![(placed21 4 (3, 4) required_5), required_595_i2]
def childrenD_595_i1 : Fin 2 → Finset Cell := ![(placed21 4 (3, 4) envelope_5), envelope_595_i2]
theorem common_sub_595_i1 : commonEnvelope childrenD_595_i1 ⊆ insert (6, 3) required_595_i1 := by decide +kernel
theorem child_required_sub_595_i1 : ∀ j, childrenC_595_i1 j ⊆ insert (6, 3) required_595_i1 := by decide +kernel
theorem child_envelope_sub_595_i1 : ∀ j, childrenD_595_i1 j ⊆ envelope_595_i1 := by decide +kernel
theorem pivot_mem_595_i1 : (6, 3) ∈ envelope_595_i1 := by decide +kernel
theorem children_work_595_i1 : ∀ j, Template HasSnaky 6 (childrenC_595_i1 j) (childrenD_595_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 4 (3, 4)).mono (by decide +kernel)
  · exact row_works_595_i2.mono (by decide +kernel)
theorem row_works_595_i1 : Template HasSnaky 7 required_595_i1 envelope_595_i1 := by
  refine compose HasSnaky 6 childrenC_595_i1 childrenD_595_i1 children_work_595_i1 (6, 3)
    required_595_i1 envelope_595_i1 pivot_mem_595_i1 child_required_sub_595_i1 child_envelope_sub_595_i1 ?_
  intro b hb
  exact common_sub_595_i1 (mem_commonEnvelope childrenD_595_i1 b hb)
def required_595_i0 : Finset Cell := ⟨(([(0, 1), (1, 1), (3, 1), (3, 2), (3, 4), (4, 4), (5, 4), (6, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_595_i0 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (3, 1), (3, 2), (3, 4), (4, 0), (4, 1), (4, 2), (4, 4), (5, 0), (5, 1), (5, 2), (5, 4), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (7, 0), (7, 1), (7, 2), (7, 3), (7, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_595_i0 : Fin 2 → Finset Cell := ![(placed21 0 (3, 4) required_5), required_595_i1]
def childrenD_595_i0 : Fin 2 → Finset Cell := ![(placed21 0 (3, 4) envelope_5), envelope_595_i1]
theorem common_sub_595_i0 : commonEnvelope childrenD_595_i0 ⊆ insert (6, 4) required_595_i0 := by decide +kernel
theorem child_required_sub_595_i0 : ∀ j, childrenC_595_i0 j ⊆ insert (6, 4) required_595_i0 := by decide +kernel
theorem child_envelope_sub_595_i0 : ∀ j, childrenD_595_i0 j ⊆ envelope_595_i0 := by decide +kernel
theorem pivot_mem_595_i0 : (6, 4) ∈ envelope_595_i0 := by decide +kernel
theorem children_work_595_i0 : ∀ j, Template HasSnaky 7 (childrenC_595_i0 j) (childrenD_595_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 0 (3, 4)).mono (by decide +kernel)
  · exact row_works_595_i1.mono (by decide +kernel)
theorem row_works_595_i0 : Template HasSnaky 8 required_595_i0 envelope_595_i0 := by
  refine compose HasSnaky 7 childrenC_595_i0 childrenD_595_i0 children_work_595_i0 (6, 4)
    required_595_i0 envelope_595_i0 pivot_mem_595_i0 child_required_sub_595_i0 child_envelope_sub_595_i0 ?_
  intro b hb
  exact common_sub_595_i0 (mem_commonEnvelope childrenD_595_i0 b hb)
def required_595 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 4), (3, 1), (3, 2), (3, 4), (4, 4), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_595 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (2, 4), (3, 1), (3, 2), (3, 4), (4, 0), (4, 1), (4, 2), (4, 4), (5, 0), (5, 1), (5, 2), (5, 4), (5, 5), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (7, 0), (7, 1), (7, 2), (7, 3), (7, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_595 : Fin 2 → Finset Cell := ![(placed21 0 (2, 4) required_4), required_595_i0]
def childrenD_595 : Fin 2 → Finset Cell := ![(placed21 0 (2, 4) envelope_4), envelope_595_i0]
theorem common_sub_595 : commonEnvelope childrenD_595 ⊆ insert (6, 5) required_595 := by decide +kernel
theorem child_required_sub_595 : ∀ j, childrenC_595 j ⊆ insert (6, 5) required_595 := by decide +kernel
theorem child_envelope_sub_595 : ∀ j, childrenD_595 j ⊆ envelope_595 := by decide +kernel
theorem pivot_mem_595 : (6, 5) ∈ envelope_595 := by decide +kernel
theorem children_work_595 : ∀ j, Template HasSnaky 8 (childrenC_595 j) (childrenD_595 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_4 0 (2, 4)).mono (by decide +kernel)
  · exact row_works_595_i0.mono (by decide +kernel)
theorem row_works_595 : Template HasSnaky 9 required_595 envelope_595 := by
  refine compose HasSnaky 8 childrenC_595 childrenD_595 children_work_595 (6, 5)
    required_595 envelope_595 pivot_mem_595 child_required_sub_595 child_envelope_sub_595 ?_
  intro b hb
  exact common_sub_595 (mem_commonEnvelope childrenD_595 b hb)
def required_614_i1 : Finset Cell := ⟨(([(0, 4), (3, 3), (3, 4), (3, 5), (4, 5), (5, 3), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_614_i1 : Finset Cell := ⟨(([(0, 4), (1, 4), (2, 4), (3, 3), (3, 4), (3, 5), (4, 3), (4, 4), (4, 5), (5, 3), (5, 4), (5, 5), (5, 6), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_614_i1 : Fin 2 → Finset Cell := ![(placed21 0 (0, 4) required_1), (placed21 4 (2, 6) required_425)]
def childrenD_614_i1 : Fin 2 → Finset Cell := ![(placed21 0 (0, 4) envelope_1), (placed21 4 (2, 6) envelope_425)]
theorem common_sub_614_i1 : commonEnvelope childrenD_614_i1 ⊆ insert (2, 4) required_614_i1 := by decide +kernel
theorem child_required_sub_614_i1 : ∀ j, childrenC_614_i1 j ⊆ insert (2, 4) required_614_i1 := by decide +kernel
theorem child_envelope_sub_614_i1 : ∀ j, childrenD_614_i1 j ⊆ envelope_614_i1 := by decide +kernel
theorem pivot_mem_614_i1 : (2, 4) ∈ envelope_614_i1 := by decide +kernel
theorem children_work_614_i1 : ∀ j, Template HasSnaky 5 (childrenC_614_i1 j) (childrenD_614_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_1 0 (0, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_425 4 (2, 6)).mono (by decide +kernel)
theorem row_works_614_i1 : Template HasSnaky 6 required_614_i1 envelope_614_i1 := by
  refine compose HasSnaky 5 childrenC_614_i1 childrenD_614_i1 children_work_614_i1 (2, 4)
    required_614_i1 envelope_614_i1 pivot_mem_614_i1 child_required_sub_614_i1 child_envelope_sub_614_i1 ?_
  intro b hb
  exact common_sub_614_i1 (mem_commonEnvelope childrenD_614_i1 b hb)
def required_614_i2 : Finset Cell := ⟨(([(0, 4), (3, 3), (3, 4), (3, 5), (4, 5), (5, 3), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_614_i2 : Finset Cell := ⟨(([(0, 4), (1, 4), (2, 4), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 2), (4, 3), (4, 5), (4, 6), (4, 7), (4, 8), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (6, 0), (6, 1), (6, 2), (6, 3), (6, 6), (6, 7), (7, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_614_i2 : Fin 2 → Finset Cell := ![(placed21 3 (0, 4) required_68), (placed21 4 (3, 8) required_495)]
def childrenD_614_i2 : Fin 2 → Finset Cell := ![(placed21 3 (0, 4) envelope_68), (placed21 4 (3, 8) envelope_495)]
theorem common_sub_614_i2 : commonEnvelope childrenD_614_i2 ⊆ insert (4, 3) required_614_i2 := by decide +kernel
theorem child_required_sub_614_i2 : ∀ j, childrenC_614_i2 j ⊆ insert (4, 3) required_614_i2 := by decide +kernel
theorem child_envelope_sub_614_i2 : ∀ j, childrenD_614_i2 j ⊆ envelope_614_i2 := by decide +kernel
theorem pivot_mem_614_i2 : (4, 3) ∈ envelope_614_i2 := by decide +kernel
theorem children_work_614_i2 : ∀ j, Template HasSnaky 5 (childrenC_614_i2 j) (childrenD_614_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_68 3 (0, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_495 4 (3, 8)).mono (by decide +kernel)
theorem row_works_614_i2 : Template HasSnaky 6 required_614_i2 envelope_614_i2 := by
  refine compose HasSnaky 5 childrenC_614_i2 childrenD_614_i2 children_work_614_i2 (4, 3)
    required_614_i2 envelope_614_i2 pivot_mem_614_i2 child_required_sub_614_i2 child_envelope_sub_614_i2 ?_
  intro b hb
  exact common_sub_614_i2 (mem_commonEnvelope childrenD_614_i2 b hb)
def required_614_i4 : Finset Cell := ⟨(([(3, 3), (3, 4), (3, 5), (4, 3), (4, 5), (5, 3), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_614_i4 : Finset Cell := ⟨(([(3, 3), (3, 4), (3, 5), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 2), (5, 3), (5, 5), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_614_i4 : Fin 2 → Finset Cell := ![(placed21 4 (3, 6) required_66), (placed21 0 (3, 2) required_66)]
def childrenD_614_i4 : Fin 2 → Finset Cell := ![(placed21 4 (3, 6) envelope_66), (placed21 0 (3, 2) envelope_66)]
theorem common_sub_614_i4 : commonEnvelope childrenD_614_i4 ⊆ insert (4, 4) required_614_i4 := by decide +kernel
theorem child_required_sub_614_i4 : ∀ j, childrenC_614_i4 j ⊆ insert (4, 4) required_614_i4 := by decide +kernel
theorem child_envelope_sub_614_i4 : ∀ j, childrenD_614_i4 j ⊆ envelope_614_i4 := by decide +kernel
theorem pivot_mem_614_i4 : (4, 4) ∈ envelope_614_i4 := by decide +kernel
theorem children_work_614_i4 : ∀ j, Template HasSnaky 2 (childrenC_614_i4 j) (childrenD_614_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_66 4 (3, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_66 0 (3, 2)).mono (by decide +kernel)
theorem row_works_614_i4 : Template HasSnaky 3 required_614_i4 envelope_614_i4 := by
  refine compose HasSnaky 2 childrenC_614_i4 childrenD_614_i4 children_work_614_i4 (4, 4)
    required_614_i4 envelope_614_i4 pivot_mem_614_i4 child_required_sub_614_i4 child_envelope_sub_614_i4 ?_
  intro b hb
  exact common_sub_614_i4 (mem_commonEnvelope childrenD_614_i4 b hb)
def required_614_i3 : Finset Cell := ⟨(([(0, 4), (3, 3), (3, 4), (3, 5), (4, 5), (5, 3), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_614_i3 : Finset Cell := ⟨(([(0, 4), (1, 4), (2, 4), (3, 3), (3, 4), (3, 5), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 2), (5, 3), (5, 5), (5, 6), (6, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_614_i3 : Fin 2 → Finset Cell := ![(placed21 3 (0, 4) required_68), required_614_i4]
def childrenD_614_i3 : Fin 2 → Finset Cell := ![(placed21 3 (0, 4) envelope_68), envelope_614_i4]
theorem common_sub_614_i3 : commonEnvelope childrenD_614_i3 ⊆ insert (4, 3) required_614_i3 := by decide +kernel
theorem child_required_sub_614_i3 : ∀ j, childrenC_614_i3 j ⊆ insert (4, 3) required_614_i3 := by decide +kernel
theorem child_envelope_sub_614_i3 : ∀ j, childrenD_614_i3 j ⊆ envelope_614_i3 := by decide +kernel
theorem pivot_mem_614_i3 : (4, 3) ∈ envelope_614_i3 := by decide +kernel
theorem children_work_614_i3 : ∀ j, Template HasSnaky 3 (childrenC_614_i3 j) (childrenD_614_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_68 3 (0, 4)).mono (by decide +kernel)
  · exact row_works_614_i4.mono (by decide +kernel)
theorem row_works_614_i3 : Template HasSnaky 4 required_614_i3 envelope_614_i3 := by
  refine compose HasSnaky 3 childrenC_614_i3 childrenD_614_i3 children_work_614_i3 (4, 3)
    required_614_i3 envelope_614_i3 pivot_mem_614_i3 child_required_sub_614_i3 child_envelope_sub_614_i3 ?_
  intro b hb
  exact common_sub_614_i3 (mem_commonEnvelope childrenD_614_i3 b hb)
def required_614_i5 : Finset Cell := ⟨(([(0, 4), (3, 3), (3, 4), (4, 5), (5, 3), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_614_i5 : Finset Cell := ⟨(([(0, 4), (1, 4), (2, 4), (3, 3), (3, 4), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (6, 0), (6, 1), (6, 2), (6, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_614_i5 : Fin 2 → Finset Cell := ![(placed21 3 (0, 4) required_68), (placed21 4 (4, 6) required_612)]
def childrenD_614_i5 : Fin 2 → Finset Cell := ![(placed21 3 (0, 4) envelope_68), (placed21 4 (4, 6) envelope_612)]
theorem common_sub_614_i5 : commonEnvelope childrenD_614_i5 ⊆ insert (4, 3) required_614_i5 := by decide +kernel
theorem child_required_sub_614_i5 : ∀ j, childrenC_614_i5 j ⊆ insert (4, 3) required_614_i5 := by decide +kernel
theorem child_envelope_sub_614_i5 : ∀ j, childrenD_614_i5 j ⊆ envelope_614_i5 := by decide +kernel
theorem pivot_mem_614_i5 : (4, 3) ∈ envelope_614_i5 := by decide +kernel
theorem children_work_614_i5 : ∀ j, Template HasSnaky 5 (childrenC_614_i5 j) (childrenD_614_i5 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_68 3 (0, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_612 4 (4, 6)).mono (by decide +kernel)
theorem row_works_614_i5 : Template HasSnaky 6 required_614_i5 envelope_614_i5 := by
  refine compose HasSnaky 5 childrenC_614_i5 childrenD_614_i5 children_work_614_i5 (4, 3)
    required_614_i5 envelope_614_i5 pivot_mem_614_i5 child_required_sub_614_i5 child_envelope_sub_614_i5 ?_
  intro b hb
  exact common_sub_614_i5 (mem_commonEnvelope childrenD_614_i5 b hb)
def required_614_i0 : Finset Cell := ⟨(([(0, 4), (3, 3), (3, 4), (3, 5), (4, 5), (5, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_614_i0 : Finset Cell := ⟨(([(0, 4), (1, 4), (2, 4), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 6), (6, 7), (6, 8), (7, 2), (7, 6), (8, 2), (8, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_614_i0 : Fin 6 → Finset Cell := ![(placed21 4 (3, 8) required_276), required_614_i1, (placed21 4 (3, 9) required_611), required_614_i2, required_614_i3, required_614_i5]
def childrenD_614_i0 : Fin 6 → Finset Cell := ![(placed21 4 (3, 8) envelope_276), envelope_614_i1, (placed21 4 (3, 9) envelope_611), envelope_614_i2, envelope_614_i3, envelope_614_i5]
theorem common_sub_614_i0 : commonEnvelope childrenD_614_i0 ⊆ insert (5, 3) required_614_i0 := by decide +kernel
theorem child_required_sub_614_i0 : ∀ j, childrenC_614_i0 j ⊆ insert (5, 3) required_614_i0 := by decide +kernel
theorem child_envelope_sub_614_i0 : ∀ j, childrenD_614_i0 j ⊆ envelope_614_i0 := by decide +kernel
theorem pivot_mem_614_i0 : (5, 3) ∈ envelope_614_i0 := by decide +kernel
theorem children_work_614_i0 : ∀ j, Template HasSnaky 7 (childrenC_614_i0 j) (childrenD_614_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_276 4 (3, 8)).mono (by decide +kernel)
  · exact row_works_614_i1.mono (by decide +kernel)
  · exact (placed21_template row_works_611 4 (3, 9)).mono (by decide +kernel)
  · exact row_works_614_i2.mono (by decide +kernel)
  · exact row_works_614_i3.mono (by decide +kernel)
  · exact row_works_614_i5.mono (by decide +kernel)
theorem row_works_614_i0 : Template HasSnaky 8 required_614_i0 envelope_614_i0 := by
  refine compose HasSnaky 7 childrenC_614_i0 childrenD_614_i0 children_work_614_i0 (5, 3)
    required_614_i0 envelope_614_i0 pivot_mem_614_i0 child_required_sub_614_i0 child_envelope_sub_614_i0 ?_
  intro b hb
  exact common_sub_614_i0 (mem_commonEnvelope childrenD_614_i0 b hb)
def required_614 : Finset Cell := ⟨(([(0, 4), (3, 3), (3, 4), (3, 5), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_614 : Finset Cell := ⟨(([(0, 4), (1, 4), (2, 4), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (8, 2), (8, 4), (8, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_614 : Fin 3 → Finset Cell := ![(placed21 1 (0, 4) required_68), (placed21 4 (3, 7) required_558), required_614_i0]
def childrenD_614 : Fin 3 → Finset Cell := ![(placed21 1 (0, 4) envelope_68), (placed21 4 (3, 7) envelope_558), envelope_614_i0]
theorem common_sub_614 : commonEnvelope childrenD_614 ⊆ insert (5, 5) required_614 := by decide +kernel
theorem child_required_sub_614 : ∀ j, childrenC_614 j ⊆ insert (5, 5) required_614 := by decide +kernel
theorem child_envelope_sub_614 : ∀ j, childrenD_614 j ⊆ envelope_614 := by decide +kernel
theorem pivot_mem_614 : (5, 5) ∈ envelope_614 := by decide +kernel
theorem children_work_614 : ∀ j, Template HasSnaky 8 (childrenC_614 j) (childrenD_614 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_68 1 (0, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_558 4 (3, 7)).mono (by decide +kernel)
  · exact row_works_614_i0.mono (by decide +kernel)
theorem row_works_614 : Template HasSnaky 9 required_614 envelope_614 := by
  refine compose HasSnaky 8 childrenC_614 childrenD_614 children_work_614 (5, 5)
    required_614 envelope_614 pivot_mem_614 child_required_sub_614 child_envelope_sub_614 ?_
  intro b hb
  exact common_sub_614 (mem_commonEnvelope childrenD_614 b hb)
def height_595_i6 : ℕ := 2
def childrenH_595_i6 : Fin 2 → ℕ := ![height_4, height_5]
theorem height_exact_595_i6 : height_595_i6 = 1 + Finset.univ.sup childrenH_595_i6 := by decide +kernel
theorem required_origin_595_i6 : ∀ x ∈ required_595_i6,
    (∃ j, x ∈ childrenC_595_i6 j) ∨ ∀ j, x ∈ childrenD_595_i6 j := by decide +kernel
theorem required_exact_595_i6 : required_595_i6 =
    ((Finset.univ.biUnion childrenC_595_i6) ∪ commonEnvelope childrenD_595_i6).erase (4, 1) := by
  exact required_eq_combination childrenC_595_i6 childrenD_595_i6 (4, 1) required_595_i6
    (by decide +kernel) child_required_sub_595_i6 common_sub_595_i6 required_origin_595_i6
theorem envelope_origin_595_i6 : ∀ x ∈ envelope_595_i6,
    x = (4, 1) ∨ ∃ j, x ∈ childrenD_595_i6 j := by decide +kernel
theorem envelope_exact_595_i6 : envelope_595_i6 =
    insert (4, 1) (Finset.univ.biUnion childrenD_595_i6) := by
  exact envelope_eq_combination childrenD_595_i6 (4, 1) envelope_595_i6
    pivot_mem_595_i6 child_envelope_sub_595_i6 envelope_origin_595_i6
def checked_595_i6 : CheckedCard where
  required := required_595_i6
  envelope := envelope_595_i6
  height := height_595_i6
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_595_i6
def height_595_i5 : ℕ := 3
def childrenH_595_i5 : Fin 2 → ℕ := ![height_3, height_595_i6]
theorem height_exact_595_i5 : height_595_i5 = 1 + Finset.univ.sup childrenH_595_i5 := by decide +kernel
theorem required_origin_595_i5 : ∀ x ∈ required_595_i5,
    (∃ j, x ∈ childrenC_595_i5 j) ∨ ∀ j, x ∈ childrenD_595_i5 j := by decide +kernel
theorem required_exact_595_i5 : required_595_i5 =
    ((Finset.univ.biUnion childrenC_595_i5) ∪ commonEnvelope childrenD_595_i5).erase (5, 0) := by
  exact required_eq_combination childrenC_595_i5 childrenD_595_i5 (5, 0) required_595_i5
    (by decide +kernel) child_required_sub_595_i5 common_sub_595_i5 required_origin_595_i5
theorem envelope_origin_595_i5 : ∀ x ∈ envelope_595_i5,
    x = (5, 0) ∨ ∃ j, x ∈ childrenD_595_i5 j := by decide +kernel
theorem envelope_exact_595_i5 : envelope_595_i5 =
    insert (5, 0) (Finset.univ.biUnion childrenD_595_i5) := by
  exact envelope_eq_combination childrenD_595_i5 (5, 0) envelope_595_i5
    pivot_mem_595_i5 child_envelope_sub_595_i5 envelope_origin_595_i5
def checked_595_i5 : CheckedCard where
  required := required_595_i5
  envelope := envelope_595_i5
  height := height_595_i5
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_595_i5
def height_595_i4 : ℕ := 4
def childrenH_595_i4 : Fin 2 → ℕ := ![height_4, height_595_i5]
theorem height_exact_595_i4 : height_595_i4 = 1 + Finset.univ.sup childrenH_595_i4 := by decide +kernel
theorem required_origin_595_i4 : ∀ x ∈ required_595_i4,
    (∃ j, x ∈ childrenC_595_i4 j) ∨ ∀ j, x ∈ childrenD_595_i4 j := by decide +kernel
theorem required_exact_595_i4 : required_595_i4 =
    ((Finset.univ.biUnion childrenC_595_i4) ∪ commonEnvelope childrenD_595_i4).erase (5, 1) := by
  exact required_eq_combination childrenC_595_i4 childrenD_595_i4 (5, 1) required_595_i4
    (by decide +kernel) child_required_sub_595_i4 common_sub_595_i4 required_origin_595_i4
theorem envelope_origin_595_i4 : ∀ x ∈ envelope_595_i4,
    x = (5, 1) ∨ ∃ j, x ∈ childrenD_595_i4 j := by decide +kernel
theorem envelope_exact_595_i4 : envelope_595_i4 =
    insert (5, 1) (Finset.univ.biUnion childrenD_595_i4) := by
  exact envelope_eq_combination childrenD_595_i4 (5, 1) envelope_595_i4
    pivot_mem_595_i4 child_envelope_sub_595_i4 envelope_origin_595_i4
def checked_595_i4 : CheckedCard where
  required := required_595_i4
  envelope := envelope_595_i4
  height := height_595_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_595_i4
def height_595_i3 : ℕ := 5
def childrenH_595_i3 : Fin 2 → ℕ := ![height_5, height_595_i4]
theorem height_exact_595_i3 : height_595_i3 = 1 + Finset.univ.sup childrenH_595_i3 := by decide +kernel
theorem required_origin_595_i3 : ∀ x ∈ required_595_i3,
    (∃ j, x ∈ childrenC_595_i3 j) ∨ ∀ j, x ∈ childrenD_595_i3 j := by decide +kernel
theorem required_exact_595_i3 : required_595_i3 =
    ((Finset.univ.biUnion childrenC_595_i3) ∪ commonEnvelope childrenD_595_i3).erase (2, 1) := by
  exact required_eq_combination childrenC_595_i3 childrenD_595_i3 (2, 1) required_595_i3
    (by decide +kernel) child_required_sub_595_i3 common_sub_595_i3 required_origin_595_i3
theorem envelope_origin_595_i3 : ∀ x ∈ envelope_595_i3,
    x = (2, 1) ∨ ∃ j, x ∈ childrenD_595_i3 j := by decide +kernel
theorem envelope_exact_595_i3 : envelope_595_i3 =
    insert (2, 1) (Finset.univ.biUnion childrenD_595_i3) := by
  exact envelope_eq_combination childrenD_595_i3 (2, 1) envelope_595_i3
    pivot_mem_595_i3 child_envelope_sub_595_i3 envelope_origin_595_i3
def checked_595_i3 : CheckedCard where
  required := required_595_i3
  envelope := envelope_595_i3
  height := height_595_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_595_i3
def height_595_i7 : ℕ := 5
def childrenH_595_i7 : Fin 2 → ℕ := ![height_2, height_208]
theorem height_exact_595_i7 : height_595_i7 = 1 + Finset.univ.sup childrenH_595_i7 := by decide +kernel
theorem required_origin_595_i7 : ∀ x ∈ required_595_i7,
    (∃ j, x ∈ childrenC_595_i7 j) ∨ ∀ j, x ∈ childrenD_595_i7 j := by decide +kernel
theorem required_exact_595_i7 : required_595_i7 =
    ((Finset.univ.biUnion childrenC_595_i7) ∪ commonEnvelope childrenD_595_i7).erase (4, 2) := by
  exact required_eq_combination childrenC_595_i7 childrenD_595_i7 (4, 2) required_595_i7
    (by decide +kernel) child_required_sub_595_i7 common_sub_595_i7 required_origin_595_i7
theorem envelope_origin_595_i7 : ∀ x ∈ envelope_595_i7,
    x = (4, 2) ∨ ∃ j, x ∈ childrenD_595_i7 j := by decide +kernel
theorem envelope_exact_595_i7 : envelope_595_i7 =
    insert (4, 2) (Finset.univ.biUnion childrenD_595_i7) := by
  exact envelope_eq_combination childrenD_595_i7 (4, 2) envelope_595_i7
    pivot_mem_595_i7 child_envelope_sub_595_i7 envelope_origin_595_i7
def checked_595_i7 : CheckedCard where
  required := required_595_i7
  envelope := envelope_595_i7
  height := height_595_i7
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_595_i7
def height_595_i9 : ℕ := 3
def childrenH_595_i9 : Fin 2 → ℕ := ![height_5, height_153]
theorem height_exact_595_i9 : height_595_i9 = 1 + Finset.univ.sup childrenH_595_i9 := by decide +kernel
theorem required_origin_595_i9 : ∀ x ∈ required_595_i9,
    (∃ j, x ∈ childrenC_595_i9 j) ∨ ∀ j, x ∈ childrenD_595_i9 j := by decide +kernel
theorem required_exact_595_i9 : required_595_i9 =
    ((Finset.univ.biUnion childrenC_595_i9) ∪ commonEnvelope childrenD_595_i9).erase (4, 2) := by
  exact required_eq_combination childrenC_595_i9 childrenD_595_i9 (4, 2) required_595_i9
    (by decide +kernel) child_required_sub_595_i9 common_sub_595_i9 required_origin_595_i9
theorem envelope_origin_595_i9 : ∀ x ∈ envelope_595_i9,
    x = (4, 2) ∨ ∃ j, x ∈ childrenD_595_i9 j := by decide +kernel
theorem envelope_exact_595_i9 : envelope_595_i9 =
    insert (4, 2) (Finset.univ.biUnion childrenD_595_i9) := by
  exact envelope_eq_combination childrenD_595_i9 (4, 2) envelope_595_i9
    pivot_mem_595_i9 child_envelope_sub_595_i9 envelope_origin_595_i9
def checked_595_i9 : CheckedCard where
  required := required_595_i9
  envelope := envelope_595_i9
  height := height_595_i9
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_595_i9
def height_595_i8 : ℕ := 4
def childrenH_595_i8 : Fin 2 → ℕ := ![height_5, height_595_i9]
theorem height_exact_595_i8 : height_595_i8 = 1 + Finset.univ.sup childrenH_595_i8 := by decide +kernel
theorem required_origin_595_i8 : ∀ x ∈ required_595_i8,
    (∃ j, x ∈ childrenC_595_i8 j) ∨ ∀ j, x ∈ childrenD_595_i8 j := by decide +kernel
theorem required_exact_595_i8 : required_595_i8 =
    ((Finset.univ.biUnion childrenC_595_i8) ∪ commonEnvelope childrenD_595_i8).erase (5, 2) := by
  exact required_eq_combination childrenC_595_i8 childrenD_595_i8 (5, 2) required_595_i8
    (by decide +kernel) child_required_sub_595_i8 common_sub_595_i8 required_origin_595_i8
theorem envelope_origin_595_i8 : ∀ x ∈ envelope_595_i8,
    x = (5, 2) ∨ ∃ j, x ∈ childrenD_595_i8 j := by decide +kernel
theorem envelope_exact_595_i8 : envelope_595_i8 =
    insert (5, 2) (Finset.univ.biUnion childrenD_595_i8) := by
  exact envelope_eq_combination childrenD_595_i8 (5, 2) envelope_595_i8
    pivot_mem_595_i8 child_envelope_sub_595_i8 envelope_origin_595_i8
def checked_595_i8 : CheckedCard where
  required := required_595_i8
  envelope := envelope_595_i8
  height := height_595_i8
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_595_i8
def height_595_i10 : ℕ := 4
def childrenH_595_i10 : Fin 2 → ℕ := ![height_2, height_157]
theorem height_exact_595_i10 : height_595_i10 = 1 + Finset.univ.sup childrenH_595_i10 := by decide +kernel
theorem required_origin_595_i10 : ∀ x ∈ required_595_i10,
    (∃ j, x ∈ childrenC_595_i10 j) ∨ ∀ j, x ∈ childrenD_595_i10 j := by decide +kernel
theorem required_exact_595_i10 : required_595_i10 =
    ((Finset.univ.biUnion childrenC_595_i10) ∪ commonEnvelope childrenD_595_i10).erase (4, 2) := by
  exact required_eq_combination childrenC_595_i10 childrenD_595_i10 (4, 2) required_595_i10
    (by decide +kernel) child_required_sub_595_i10 common_sub_595_i10 required_origin_595_i10
theorem envelope_origin_595_i10 : ∀ x ∈ envelope_595_i10,
    x = (4, 2) ∨ ∃ j, x ∈ childrenD_595_i10 j := by decide +kernel
theorem envelope_exact_595_i10 : envelope_595_i10 =
    insert (4, 2) (Finset.univ.biUnion childrenD_595_i10) := by
  exact envelope_eq_combination childrenD_595_i10 (4, 2) envelope_595_i10
    pivot_mem_595_i10 child_envelope_sub_595_i10 envelope_origin_595_i10
def checked_595_i10 : CheckedCard where
  required := required_595_i10
  envelope := envelope_595_i10
  height := height_595_i10
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_595_i10
def height_595_i2 : ℕ := 6
def childrenH_595_i2 : Fin 5 → ℕ := ![height_8, height_595_i3, height_595_i7, height_595_i8, height_595_i10]
theorem height_exact_595_i2 : height_595_i2 = 1 + Finset.univ.sup childrenH_595_i2 := by decide +kernel
theorem required_origin_595_i2 : ∀ x ∈ required_595_i2,
    (∃ j, x ∈ childrenC_595_i2 j) ∨ ∀ j, x ∈ childrenD_595_i2 j := by decide +kernel
theorem required_exact_595_i2 : required_595_i2 =
    ((Finset.univ.biUnion childrenC_595_i2) ∪ commonEnvelope childrenD_595_i2).erase (6, 2) := by
  exact required_eq_combination childrenC_595_i2 childrenD_595_i2 (6, 2) required_595_i2
    (by decide +kernel) child_required_sub_595_i2 common_sub_595_i2 required_origin_595_i2
theorem envelope_origin_595_i2 : ∀ x ∈ envelope_595_i2,
    x = (6, 2) ∨ ∃ j, x ∈ childrenD_595_i2 j := by decide +kernel
theorem envelope_exact_595_i2 : envelope_595_i2 =
    insert (6, 2) (Finset.univ.biUnion childrenD_595_i2) := by
  exact envelope_eq_combination childrenD_595_i2 (6, 2) envelope_595_i2
    pivot_mem_595_i2 child_envelope_sub_595_i2 envelope_origin_595_i2
def checked_595_i2 : CheckedCard where
  required := required_595_i2
  envelope := envelope_595_i2
  height := height_595_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_595_i2
def height_595_i1 : ℕ := 7
def childrenH_595_i1 : Fin 2 → ℕ := ![height_5, height_595_i2]
theorem height_exact_595_i1 : height_595_i1 = 1 + Finset.univ.sup childrenH_595_i1 := by decide +kernel
theorem required_origin_595_i1 : ∀ x ∈ required_595_i1,
    (∃ j, x ∈ childrenC_595_i1 j) ∨ ∀ j, x ∈ childrenD_595_i1 j := by decide +kernel
theorem required_exact_595_i1 : required_595_i1 =
    ((Finset.univ.biUnion childrenC_595_i1) ∪ commonEnvelope childrenD_595_i1).erase (6, 3) := by
  exact required_eq_combination childrenC_595_i1 childrenD_595_i1 (6, 3) required_595_i1
    (by decide +kernel) child_required_sub_595_i1 common_sub_595_i1 required_origin_595_i1
theorem envelope_origin_595_i1 : ∀ x ∈ envelope_595_i1,
    x = (6, 3) ∨ ∃ j, x ∈ childrenD_595_i1 j := by decide +kernel
theorem envelope_exact_595_i1 : envelope_595_i1 =
    insert (6, 3) (Finset.univ.biUnion childrenD_595_i1) := by
  exact envelope_eq_combination childrenD_595_i1 (6, 3) envelope_595_i1
    pivot_mem_595_i1 child_envelope_sub_595_i1 envelope_origin_595_i1
def checked_595_i1 : CheckedCard where
  required := required_595_i1
  envelope := envelope_595_i1
  height := height_595_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_595_i1
def height_595_i0 : ℕ := 8
def childrenH_595_i0 : Fin 2 → ℕ := ![height_5, height_595_i1]
theorem height_exact_595_i0 : height_595_i0 = 1 + Finset.univ.sup childrenH_595_i0 := by decide +kernel
theorem required_origin_595_i0 : ∀ x ∈ required_595_i0,
    (∃ j, x ∈ childrenC_595_i0 j) ∨ ∀ j, x ∈ childrenD_595_i0 j := by decide +kernel
theorem required_exact_595_i0 : required_595_i0 =
    ((Finset.univ.biUnion childrenC_595_i0) ∪ commonEnvelope childrenD_595_i0).erase (6, 4) := by
  exact required_eq_combination childrenC_595_i0 childrenD_595_i0 (6, 4) required_595_i0
    (by decide +kernel) child_required_sub_595_i0 common_sub_595_i0 required_origin_595_i0
theorem envelope_origin_595_i0 : ∀ x ∈ envelope_595_i0,
    x = (6, 4) ∨ ∃ j, x ∈ childrenD_595_i0 j := by decide +kernel
theorem envelope_exact_595_i0 : envelope_595_i0 =
    insert (6, 4) (Finset.univ.biUnion childrenD_595_i0) := by
  exact envelope_eq_combination childrenD_595_i0 (6, 4) envelope_595_i0
    pivot_mem_595_i0 child_envelope_sub_595_i0 envelope_origin_595_i0
def checked_595_i0 : CheckedCard where
  required := required_595_i0
  envelope := envelope_595_i0
  height := height_595_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_595_i0
def height_595 : ℕ := 9
def childrenH_595 : Fin 2 → ℕ := ![height_4, height_595_i0]
theorem height_exact_595 : height_595 = 1 + Finset.univ.sup childrenH_595 := by decide +kernel
theorem required_origin_595 : ∀ x ∈ required_595,
    (∃ j, x ∈ childrenC_595 j) ∨ ∀ j, x ∈ childrenD_595 j := by decide +kernel
theorem required_exact_595 : required_595 =
    ((Finset.univ.biUnion childrenC_595) ∪ commonEnvelope childrenD_595).erase (6, 5) := by
  exact required_eq_combination childrenC_595 childrenD_595 (6, 5) required_595
    (by decide +kernel) child_required_sub_595 common_sub_595 required_origin_595
theorem envelope_origin_595 : ∀ x ∈ envelope_595,
    x = (6, 5) ∨ ∃ j, x ∈ childrenD_595 j := by decide +kernel
theorem envelope_exact_595 : envelope_595 =
    insert (6, 5) (Finset.univ.biUnion childrenD_595) := by
  exact envelope_eq_combination childrenD_595 (6, 5) envelope_595
    pivot_mem_595 child_envelope_sub_595 envelope_origin_595
def checked_595 : CheckedCard where
  required := required_595
  envelope := envelope_595
  height := height_595
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_595
def height_614_i1 : ℕ := 6
def childrenH_614_i1 : Fin 2 → ℕ := ![height_1, height_425]
theorem height_exact_614_i1 : height_614_i1 = 1 + Finset.univ.sup childrenH_614_i1 := by decide +kernel
theorem required_origin_614_i1 : ∀ x ∈ required_614_i1,
    (∃ j, x ∈ childrenC_614_i1 j) ∨ ∀ j, x ∈ childrenD_614_i1 j := by decide +kernel
theorem required_exact_614_i1 : required_614_i1 =
    ((Finset.univ.biUnion childrenC_614_i1) ∪ commonEnvelope childrenD_614_i1).erase (2, 4) := by
  exact required_eq_combination childrenC_614_i1 childrenD_614_i1 (2, 4) required_614_i1
    (by decide +kernel) child_required_sub_614_i1 common_sub_614_i1 required_origin_614_i1
theorem envelope_origin_614_i1 : ∀ x ∈ envelope_614_i1,
    x = (2, 4) ∨ ∃ j, x ∈ childrenD_614_i1 j := by decide +kernel
theorem envelope_exact_614_i1 : envelope_614_i1 =
    insert (2, 4) (Finset.univ.biUnion childrenD_614_i1) := by
  exact envelope_eq_combination childrenD_614_i1 (2, 4) envelope_614_i1
    pivot_mem_614_i1 child_envelope_sub_614_i1 envelope_origin_614_i1
def checked_614_i1 : CheckedCard where
  required := required_614_i1
  envelope := envelope_614_i1
  height := height_614_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_614_i1
def height_614_i2 : ℕ := 6
def childrenH_614_i2 : Fin 2 → ℕ := ![height_68, height_495]
theorem height_exact_614_i2 : height_614_i2 = 1 + Finset.univ.sup childrenH_614_i2 := by decide +kernel
theorem required_origin_614_i2 : ∀ x ∈ required_614_i2,
    (∃ j, x ∈ childrenC_614_i2 j) ∨ ∀ j, x ∈ childrenD_614_i2 j := by decide +kernel
theorem required_exact_614_i2 : required_614_i2 =
    ((Finset.univ.biUnion childrenC_614_i2) ∪ commonEnvelope childrenD_614_i2).erase (4, 3) := by
  exact required_eq_combination childrenC_614_i2 childrenD_614_i2 (4, 3) required_614_i2
    (by decide +kernel) child_required_sub_614_i2 common_sub_614_i2 required_origin_614_i2
theorem envelope_origin_614_i2 : ∀ x ∈ envelope_614_i2,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_614_i2 j := by decide +kernel
theorem envelope_exact_614_i2 : envelope_614_i2 =
    insert (4, 3) (Finset.univ.biUnion childrenD_614_i2) := by
  exact envelope_eq_combination childrenD_614_i2 (4, 3) envelope_614_i2
    pivot_mem_614_i2 child_envelope_sub_614_i2 envelope_origin_614_i2
def checked_614_i2 : CheckedCard where
  required := required_614_i2
  envelope := envelope_614_i2
  height := height_614_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_614_i2
def height_614_i4 : ℕ := 3
def childrenH_614_i4 : Fin 2 → ℕ := ![height_66, height_66]
theorem height_exact_614_i4 : height_614_i4 = 1 + Finset.univ.sup childrenH_614_i4 := by decide +kernel
theorem required_origin_614_i4 : ∀ x ∈ required_614_i4,
    (∃ j, x ∈ childrenC_614_i4 j) ∨ ∀ j, x ∈ childrenD_614_i4 j := by decide +kernel
theorem required_exact_614_i4 : required_614_i4 =
    ((Finset.univ.biUnion childrenC_614_i4) ∪ commonEnvelope childrenD_614_i4).erase (4, 4) := by
  exact required_eq_combination childrenC_614_i4 childrenD_614_i4 (4, 4) required_614_i4
    (by decide +kernel) child_required_sub_614_i4 common_sub_614_i4 required_origin_614_i4
theorem envelope_origin_614_i4 : ∀ x ∈ envelope_614_i4,
    x = (4, 4) ∨ ∃ j, x ∈ childrenD_614_i4 j := by decide +kernel
theorem envelope_exact_614_i4 : envelope_614_i4 =
    insert (4, 4) (Finset.univ.biUnion childrenD_614_i4) := by
  exact envelope_eq_combination childrenD_614_i4 (4, 4) envelope_614_i4
    pivot_mem_614_i4 child_envelope_sub_614_i4 envelope_origin_614_i4
def checked_614_i4 : CheckedCard where
  required := required_614_i4
  envelope := envelope_614_i4
  height := height_614_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_614_i4
def height_614_i3 : ℕ := 4
def childrenH_614_i3 : Fin 2 → ℕ := ![height_68, height_614_i4]
theorem height_exact_614_i3 : height_614_i3 = 1 + Finset.univ.sup childrenH_614_i3 := by decide +kernel
theorem required_origin_614_i3 : ∀ x ∈ required_614_i3,
    (∃ j, x ∈ childrenC_614_i3 j) ∨ ∀ j, x ∈ childrenD_614_i3 j := by decide +kernel
theorem required_exact_614_i3 : required_614_i3 =
    ((Finset.univ.biUnion childrenC_614_i3) ∪ commonEnvelope childrenD_614_i3).erase (4, 3) := by
  exact required_eq_combination childrenC_614_i3 childrenD_614_i3 (4, 3) required_614_i3
    (by decide +kernel) child_required_sub_614_i3 common_sub_614_i3 required_origin_614_i3
theorem envelope_origin_614_i3 : ∀ x ∈ envelope_614_i3,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_614_i3 j := by decide +kernel
theorem envelope_exact_614_i3 : envelope_614_i3 =
    insert (4, 3) (Finset.univ.biUnion childrenD_614_i3) := by
  exact envelope_eq_combination childrenD_614_i3 (4, 3) envelope_614_i3
    pivot_mem_614_i3 child_envelope_sub_614_i3 envelope_origin_614_i3
def checked_614_i3 : CheckedCard where
  required := required_614_i3
  envelope := envelope_614_i3
  height := height_614_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_614_i3
def height_614_i5 : ℕ := 6
def childrenH_614_i5 : Fin 2 → ℕ := ![height_68, height_612]
theorem height_exact_614_i5 : height_614_i5 = 1 + Finset.univ.sup childrenH_614_i5 := by decide +kernel
theorem required_origin_614_i5 : ∀ x ∈ required_614_i5,
    (∃ j, x ∈ childrenC_614_i5 j) ∨ ∀ j, x ∈ childrenD_614_i5 j := by decide +kernel
theorem required_exact_614_i5 : required_614_i5 =
    ((Finset.univ.biUnion childrenC_614_i5) ∪ commonEnvelope childrenD_614_i5).erase (4, 3) := by
  exact required_eq_combination childrenC_614_i5 childrenD_614_i5 (4, 3) required_614_i5
    (by decide +kernel) child_required_sub_614_i5 common_sub_614_i5 required_origin_614_i5
theorem envelope_origin_614_i5 : ∀ x ∈ envelope_614_i5,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_614_i5 j := by decide +kernel
theorem envelope_exact_614_i5 : envelope_614_i5 =
    insert (4, 3) (Finset.univ.biUnion childrenD_614_i5) := by
  exact envelope_eq_combination childrenD_614_i5 (4, 3) envelope_614_i5
    pivot_mem_614_i5 child_envelope_sub_614_i5 envelope_origin_614_i5
def checked_614_i5 : CheckedCard where
  required := required_614_i5
  envelope := envelope_614_i5
  height := height_614_i5
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_614_i5
def height_614_i0 : ℕ := 8
def childrenH_614_i0 : Fin 6 → ℕ := ![height_276, height_614_i1, height_611, height_614_i2, height_614_i3, height_614_i5]
theorem height_exact_614_i0 : height_614_i0 = 1 + Finset.univ.sup childrenH_614_i0 := by decide +kernel
theorem required_origin_614_i0 : ∀ x ∈ required_614_i0,
    (∃ j, x ∈ childrenC_614_i0 j) ∨ ∀ j, x ∈ childrenD_614_i0 j := by decide +kernel
theorem required_exact_614_i0 : required_614_i0 =
    ((Finset.univ.biUnion childrenC_614_i0) ∪ commonEnvelope childrenD_614_i0).erase (5, 3) := by
  exact required_eq_combination childrenC_614_i0 childrenD_614_i0 (5, 3) required_614_i0
    (by decide +kernel) child_required_sub_614_i0 common_sub_614_i0 required_origin_614_i0
theorem envelope_origin_614_i0 : ∀ x ∈ envelope_614_i0,
    x = (5, 3) ∨ ∃ j, x ∈ childrenD_614_i0 j := by decide +kernel
theorem envelope_exact_614_i0 : envelope_614_i0 =
    insert (5, 3) (Finset.univ.biUnion childrenD_614_i0) := by
  exact envelope_eq_combination childrenD_614_i0 (5, 3) envelope_614_i0
    pivot_mem_614_i0 child_envelope_sub_614_i0 envelope_origin_614_i0
def checked_614_i0 : CheckedCard where
  required := required_614_i0
  envelope := envelope_614_i0
  height := height_614_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_614_i0
def height_614 : ℕ := 9
def childrenH_614 : Fin 3 → ℕ := ![height_68, height_558, height_614_i0]
theorem height_exact_614 : height_614 = 1 + Finset.univ.sup childrenH_614 := by decide +kernel
theorem required_origin_614 : ∀ x ∈ required_614,
    (∃ j, x ∈ childrenC_614 j) ∨ ∀ j, x ∈ childrenD_614 j := by decide +kernel
theorem required_exact_614 : required_614 =
    ((Finset.univ.biUnion childrenC_614) ∪ commonEnvelope childrenD_614).erase (5, 5) := by
  exact required_eq_combination childrenC_614 childrenD_614 (5, 5) required_614
    (by decide +kernel) child_required_sub_614 common_sub_614 required_origin_614
theorem envelope_origin_614 : ∀ x ∈ envelope_614,
    x = (5, 5) ∨ ∃ j, x ∈ childrenD_614 j := by decide +kernel
theorem envelope_exact_614 : envelope_614 =
    insert (5, 5) (Finset.univ.biUnion childrenD_614) := by
  exact envelope_eq_combination childrenD_614 (5, 5) envelope_614
    pivot_mem_614 child_envelope_sub_614 envelope_origin_614
def checked_614 : CheckedCard where
  required := required_614
  envelope := envelope_614
  height := height_614
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_614
end SnakyPrototype.Certificate21

end OAI
