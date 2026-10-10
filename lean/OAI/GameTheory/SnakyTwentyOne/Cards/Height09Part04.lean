import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part06
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part03
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_539_i4 : Finset Cell := ⟨(([(0, 5), (1, 5), (2, 5), (3, 1), (3, 2), (3, 3), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_539_i4 : Finset Cell := ⟨(([(0, 5), (1, 5), (2, 5), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 2), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_539_i4 : Fin 2 → Finset Cell := ![(placed21 4 (0, 5) required_5), (placed21 4 (3, 5) required_6)]
def childrenD_539_i4 : Fin 2 → Finset Cell := ![(placed21 4 (0, 5) envelope_5), (placed21 4 (3, 5) envelope_6)]
theorem common_sub_539_i4 : commonEnvelope childrenD_539_i4 ⊆ insert (3, 5) required_539_i4 := by decide +kernel
theorem child_required_sub_539_i4 : ∀ j, childrenC_539_i4 j ⊆ insert (3, 5) required_539_i4 := by decide +kernel
theorem child_envelope_sub_539_i4 : ∀ j, childrenD_539_i4 j ⊆ envelope_539_i4 := by decide +kernel
theorem pivot_mem_539_i4 : (3, 5) ∈ envelope_539_i4 := by decide +kernel
theorem children_work_539_i4 : ∀ j, Template HasSnaky 2 (childrenC_539_i4 j) (childrenD_539_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 4 (0, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_6 4 (3, 5)).mono (by decide +kernel)
theorem row_works_539_i4 : Template HasSnaky 3 required_539_i4 envelope_539_i4 := by
  refine compose HasSnaky 2 childrenC_539_i4 childrenD_539_i4 children_work_539_i4 (3, 5)
    required_539_i4 envelope_539_i4 pivot_mem_539_i4 child_required_sub_539_i4 child_envelope_sub_539_i4 ?_
  intro b hb
  exact common_sub_539_i4 (mem_commonEnvelope childrenD_539_i4 b hb)
def required_539_i3 : Finset Cell := ⟨(([(0, 5), (1, 5), (2, 1), (2, 5), (3, 1), (3, 2), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_539_i3 : Finset Cell := ⟨(([(0, 5), (1, 5), (2, 0), (2, 1), (2, 5), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 2), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_539_i3 : Fin 2 → Finset Cell := ![(placed21 7 (3, 4) required_5), required_539_i4]
def childrenD_539_i3 : Fin 2 → Finset Cell := ![(placed21 7 (3, 4) envelope_5), envelope_539_i4]
theorem common_sub_539_i3 : commonEnvelope childrenD_539_i3 ⊆ insert (3, 4) required_539_i3 := by decide +kernel
theorem child_required_sub_539_i3 : ∀ j, childrenC_539_i3 j ⊆ insert (3, 4) required_539_i3 := by decide +kernel
theorem child_envelope_sub_539_i3 : ∀ j, childrenD_539_i3 j ⊆ envelope_539_i3 := by decide +kernel
theorem pivot_mem_539_i3 : (3, 4) ∈ envelope_539_i3 := by decide +kernel
theorem children_work_539_i3 : ∀ j, Template HasSnaky 3 (childrenC_539_i3 j) (childrenD_539_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 7 (3, 4)).mono (by decide +kernel)
  · exact row_works_539_i4.mono (by decide +kernel)
theorem row_works_539_i3 : Template HasSnaky 4 required_539_i3 envelope_539_i3 := by
  refine compose HasSnaky 3 childrenC_539_i3 childrenD_539_i3 children_work_539_i3 (3, 4)
    required_539_i3 envelope_539_i3 pivot_mem_539_i3 child_required_sub_539_i3 child_envelope_sub_539_i3 ?_
  intro b hb
  exact common_sub_539_i3 (mem_commonEnvelope childrenD_539_i3 b hb)
def required_539_i7 : Finset Cell := ⟨(([(0, 1), (0, 5), (1, 5), (2, 1), (2, 5), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_539_i7 : Finset Cell := ⟨(([(0, 1), (0, 5), (1, 1), (1, 5), (2, 1), (2, 5), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 2), (4, 3), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_539_i7 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) required_1), (placed21 2 (4, 2) required_153)]
def childrenD_539_i7 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) envelope_1), (placed21 2 (4, 2) envelope_153)]
theorem common_sub_539_i7 : commonEnvelope childrenD_539_i7 ⊆ insert (4, 2) required_539_i7 := by decide +kernel
theorem child_required_sub_539_i7 : ∀ j, childrenC_539_i7 j ⊆ insert (4, 2) required_539_i7 := by decide +kernel
theorem child_envelope_sub_539_i7 : ∀ j, childrenD_539_i7 j ⊆ envelope_539_i7 := by decide +kernel
theorem pivot_mem_539_i7 : (4, 2) ∈ envelope_539_i7 := by decide +kernel
theorem children_work_539_i7 : ∀ j, Template HasSnaky 2 (childrenC_539_i7 j) (childrenD_539_i7 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_1 0 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_153 2 (4, 2)).mono (by decide +kernel)
theorem row_works_539_i7 : Template HasSnaky 3 required_539_i7 envelope_539_i7 := by
  refine compose HasSnaky 2 childrenC_539_i7 childrenD_539_i7 children_work_539_i7 (4, 2)
    required_539_i7 envelope_539_i7 pivot_mem_539_i7 child_required_sub_539_i7 child_envelope_sub_539_i7 ?_
  intro b hb
  exact common_sub_539_i7 (mem_commonEnvelope childrenD_539_i7 b hb)
def required_539_i6 : Finset Cell := ⟨(([(0, 1), (0, 5), (1, 5), (2, 1), (2, 5), (3, 1), (3, 2), (3, 3), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_539_i6 : Finset Cell := ⟨(([(0, 1), (0, 5), (1, 1), (1, 5), (2, 1), (2, 5), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 2), (4, 3), (4, 4), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_539_i6 : Fin 2 → Finset Cell := ![(placed21 4 (0, 5) required_5), required_539_i7]
def childrenD_539_i6 : Fin 2 → Finset Cell := ![(placed21 4 (0, 5) envelope_5), envelope_539_i7]
theorem common_sub_539_i6 : commonEnvelope childrenD_539_i6 ⊆ insert (3, 5) required_539_i6 := by decide +kernel
theorem child_required_sub_539_i6 : ∀ j, childrenC_539_i6 j ⊆ insert (3, 5) required_539_i6 := by decide +kernel
theorem child_envelope_sub_539_i6 : ∀ j, childrenD_539_i6 j ⊆ envelope_539_i6 := by decide +kernel
theorem pivot_mem_539_i6 : (3, 5) ∈ envelope_539_i6 := by decide +kernel
theorem children_work_539_i6 : ∀ j, Template HasSnaky 3 (childrenC_539_i6 j) (childrenD_539_i6 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 4 (0, 5)).mono (by decide +kernel)
  · exact row_works_539_i7.mono (by decide +kernel)
theorem row_works_539_i6 : Template HasSnaky 4 required_539_i6 envelope_539_i6 := by
  refine compose HasSnaky 3 childrenC_539_i6 childrenD_539_i6 children_work_539_i6 (3, 5)
    required_539_i6 envelope_539_i6 pivot_mem_539_i6 child_required_sub_539_i6 child_envelope_sub_539_i6 ?_
  intro b hb
  exact common_sub_539_i6 (mem_commonEnvelope childrenD_539_i6 b hb)
def required_539_i5 : Finset Cell := ⟨(([(0, 1), (0, 5), (1, 5), (2, 1), (2, 5), (3, 1), (3, 2), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_539_i5 : Finset Cell := ⟨(([(0, 1), (0, 5), (1, 1), (1, 5), (2, 0), (2, 1), (2, 5), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 2), (4, 3), (4, 4), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_539_i5 : Fin 2 → Finset Cell := ![(placed21 7 (3, 4) required_5), required_539_i6]
def childrenD_539_i5 : Fin 2 → Finset Cell := ![(placed21 7 (3, 4) envelope_5), envelope_539_i6]
theorem common_sub_539_i5 : commonEnvelope childrenD_539_i5 ⊆ insert (3, 4) required_539_i5 := by decide +kernel
theorem child_required_sub_539_i5 : ∀ j, childrenC_539_i5 j ⊆ insert (3, 4) required_539_i5 := by decide +kernel
theorem child_envelope_sub_539_i5 : ∀ j, childrenD_539_i5 j ⊆ envelope_539_i5 := by decide +kernel
theorem pivot_mem_539_i5 : (3, 4) ∈ envelope_539_i5 := by decide +kernel
theorem children_work_539_i5 : ∀ j, Template HasSnaky 4 (childrenC_539_i5 j) (childrenD_539_i5 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 7 (3, 4)).mono (by decide +kernel)
  · exact row_works_539_i6.mono (by decide +kernel)
theorem row_works_539_i5 : Template HasSnaky 5 required_539_i5 envelope_539_i5 := by
  refine compose HasSnaky 4 childrenC_539_i5 childrenD_539_i5 children_work_539_i5 (3, 4)
    required_539_i5 envelope_539_i5 pivot_mem_539_i5 child_required_sub_539_i5 child_envelope_sub_539_i5 ?_
  intro b hb
  exact common_sub_539_i5 (mem_commonEnvelope childrenD_539_i5 b hb)
def required_539_i9 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 1), (1, 4), (1, 5), (2, 1), (3, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_539_i9 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 1), (3, 1), (4, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_539_i9 : Fin 2 → Finset Cell := ![(placed21 2 (4, 1) required_0), (placed21 7 (1, 5) required_2)]
def childrenD_539_i9 : Fin 2 → Finset Cell := ![(placed21 2 (4, 1) envelope_0), (placed21 7 (1, 5) envelope_2)]
theorem common_sub_539_i9 : commonEnvelope childrenD_539_i9 ⊆ insert (1, 2) required_539_i9 := by decide +kernel
theorem child_required_sub_539_i9 : ∀ j, childrenC_539_i9 j ⊆ insert (1, 2) required_539_i9 := by decide +kernel
theorem child_envelope_sub_539_i9 : ∀ j, childrenD_539_i9 j ⊆ envelope_539_i9 := by decide +kernel
theorem pivot_mem_539_i9 : (1, 2) ∈ envelope_539_i9 := by decide +kernel
theorem children_work_539_i9 : ∀ j, Template HasSnaky 1 (childrenC_539_i9 j) (childrenD_539_i9 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 2 (4, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_2 7 (1, 5)).mono (by decide +kernel)
theorem row_works_539_i9 : Template HasSnaky 2 required_539_i9 envelope_539_i9 := by
  refine compose HasSnaky 1 childrenC_539_i9 childrenD_539_i9 children_work_539_i9 (1, 2)
    required_539_i9 envelope_539_i9 pivot_mem_539_i9 child_required_sub_539_i9 child_envelope_sub_539_i9 ?_
  intro b hb
  exact common_sub_539_i9 (mem_commonEnvelope childrenD_539_i9 b hb)
def required_539_i8 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 4), (1, 5), (2, 1), (3, 1), (3, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_539_i8 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 1), (3, 1), (3, 2), (4, 1), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_539_i8 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) required_5), required_539_i9]
def childrenD_539_i8 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) envelope_5), envelope_539_i9]
theorem common_sub_539_i8 : commonEnvelope childrenD_539_i8 ⊆ insert (1, 1) required_539_i8 := by decide +kernel
theorem child_required_sub_539_i8 : ∀ j, childrenC_539_i8 j ⊆ insert (1, 1) required_539_i8 := by decide +kernel
theorem child_envelope_sub_539_i8 : ∀ j, childrenD_539_i8 j ⊆ envelope_539_i8 := by decide +kernel
theorem pivot_mem_539_i8 : (1, 1) ∈ envelope_539_i8 := by decide +kernel
theorem children_work_539_i8 : ∀ j, Template HasSnaky 2 (childrenC_539_i8 j) (childrenD_539_i8 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 0 (0, 1)).mono (by decide +kernel)
  · exact row_works_539_i9.mono (by decide +kernel)
theorem row_works_539_i8 : Template HasSnaky 3 required_539_i8 envelope_539_i8 := by
  refine compose HasSnaky 2 childrenC_539_i8 childrenD_539_i8 children_work_539_i8 (1, 1)
    required_539_i8 envelope_539_i8 pivot_mem_539_i8 child_required_sub_539_i8 child_envelope_sub_539_i8 ?_
  intro b hb
  exact common_sub_539_i8 (mem_commonEnvelope childrenD_539_i8 b hb)
def required_539_i10 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 4), (1, 5), (2, 1), (3, 1), (3, 2), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_539_i10 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (3, 1), (3, 2), (3, 3), (3, 4), (4, 0), (4, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_539_i10 : Fin 2 → Finset Cell := ![(placed21 0 (2, 0) required_83), (placed21 5 (4, 1) required_281)]
def childrenD_539_i10 : Fin 2 → Finset Cell := ![(placed21 0 (2, 0) envelope_83), (placed21 5 (4, 1) envelope_281)]
theorem common_sub_539_i10 : commonEnvelope childrenD_539_i10 ⊆ insert (4, 1) required_539_i10 := by decide +kernel
theorem child_required_sub_539_i10 : ∀ j, childrenC_539_i10 j ⊆ insert (4, 1) required_539_i10 := by decide +kernel
theorem child_envelope_sub_539_i10 : ∀ j, childrenD_539_i10 j ⊆ envelope_539_i10 := by decide +kernel
theorem pivot_mem_539_i10 : (4, 1) ∈ envelope_539_i10 := by decide +kernel
theorem children_work_539_i10 : ∀ j, Template HasSnaky 2 (childrenC_539_i10 j) (childrenD_539_i10 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_83 0 (2, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_281 5 (4, 1)).mono (by decide +kernel)
theorem row_works_539_i10 : Template HasSnaky 3 required_539_i10 envelope_539_i10 := by
  refine compose HasSnaky 2 childrenC_539_i10 childrenD_539_i10 children_work_539_i10 (4, 1)
    required_539_i10 envelope_539_i10 pivot_mem_539_i10 child_required_sub_539_i10 child_envelope_sub_539_i10 ?_
  intro b hb
  exact common_sub_539_i10 (mem_commonEnvelope childrenD_539_i10 b hb)
def required_539_i2 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 5), (1, 4), (1, 5), (2, 5), (3, 1), (3, 2), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_539_i2 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 5), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 5), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_539_i2 : Fin 4 → Finset Cell := ![required_539_i3, required_539_i5, required_539_i8, required_539_i10]
def childrenD_539_i2 : Fin 4 → Finset Cell := ![envelope_539_i3, envelope_539_i5, envelope_539_i8, envelope_539_i10]
theorem common_sub_539_i2 : commonEnvelope childrenD_539_i2 ⊆ insert (2, 1) required_539_i2 := by decide +kernel
theorem child_required_sub_539_i2 : ∀ j, childrenC_539_i2 j ⊆ insert (2, 1) required_539_i2 := by decide +kernel
theorem child_envelope_sub_539_i2 : ∀ j, childrenD_539_i2 j ⊆ envelope_539_i2 := by decide +kernel
theorem pivot_mem_539_i2 : (2, 1) ∈ envelope_539_i2 := by decide +kernel
theorem children_work_539_i2 : ∀ j, Template HasSnaky 5 (childrenC_539_i2 j) (childrenD_539_i2 j) := by
  intro j
  fin_cases j
  · exact row_works_539_i3.mono (by decide +kernel)
  · exact row_works_539_i5.mono (by decide +kernel)
  · exact row_works_539_i8.mono (by decide +kernel)
  · exact row_works_539_i10.mono (by decide +kernel)
theorem row_works_539_i2 : Template HasSnaky 6 required_539_i2 envelope_539_i2 := by
  refine compose HasSnaky 5 childrenC_539_i2 childrenD_539_i2 children_work_539_i2 (2, 1)
    required_539_i2 envelope_539_i2 pivot_mem_539_i2 child_required_sub_539_i2 child_envelope_sub_539_i2 ?_
  intro b hb
  exact common_sub_539_i2 (mem_commonEnvelope childrenD_539_i2 b hb)
def required_539_i1 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 5), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (3, 1), (3, 2), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_539_i1 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 5), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, 0), (2, 1), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_539_i1 : Fin 2 → Finset Cell := ![(placed21 3 (1, 9) required_4), required_539_i2]
def childrenD_539_i1 : Fin 2 → Finset Cell := ![(placed21 3 (1, 9) envelope_4), envelope_539_i2]
theorem common_sub_539_i1 : commonEnvelope childrenD_539_i1 ⊆ insert (2, 5) required_539_i1 := by decide +kernel
theorem child_required_sub_539_i1 : ∀ j, childrenC_539_i1 j ⊆ insert (2, 5) required_539_i1 := by decide +kernel
theorem child_envelope_sub_539_i1 : ∀ j, childrenD_539_i1 j ⊆ envelope_539_i1 := by decide +kernel
theorem pivot_mem_539_i1 : (2, 5) ∈ envelope_539_i1 := by decide +kernel
theorem children_work_539_i1 : ∀ j, Template HasSnaky 6 (childrenC_539_i1 j) (childrenD_539_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_4 3 (1, 9)).mono (by decide +kernel)
  · exact row_works_539_i2.mono (by decide +kernel)
theorem row_works_539_i1 : Template HasSnaky 7 required_539_i1 envelope_539_i1 := by
  refine compose HasSnaky 6 childrenC_539_i1 childrenD_539_i1 children_work_539_i1 (2, 5)
    required_539_i1 envelope_539_i1 pivot_mem_539_i1 child_required_sub_539_i1 child_envelope_sub_539_i1 ?_
  intro b hb
  exact common_sub_539_i1 (mem_commonEnvelope childrenD_539_i1 b hb)
def required_539_i0 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (3, 1), (3, 2), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_539_i0 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 4), (0, 5), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, 0), (2, 1), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_539_i0 : Fin 2 → Finset Cell := ![(placed21 7 (1, 8) required_5), required_539_i1]
def childrenD_539_i0 : Fin 2 → Finset Cell := ![(placed21 7 (1, 8) envelope_5), envelope_539_i1]
theorem common_sub_539_i0 : commonEnvelope childrenD_539_i0 ⊆ insert (0, 5) required_539_i0 := by decide +kernel
theorem child_required_sub_539_i0 : ∀ j, childrenC_539_i0 j ⊆ insert (0, 5) required_539_i0 := by decide +kernel
theorem child_envelope_sub_539_i0 : ∀ j, childrenD_539_i0 j ⊆ envelope_539_i0 := by decide +kernel
theorem pivot_mem_539_i0 : (0, 5) ∈ envelope_539_i0 := by decide +kernel
theorem children_work_539_i0 : ∀ j, Template HasSnaky 7 (childrenC_539_i0 j) (childrenD_539_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 7 (1, 8)).mono (by decide +kernel)
  · exact row_works_539_i1.mono (by decide +kernel)
theorem row_works_539_i0 : Template HasSnaky 8 required_539_i0 envelope_539_i0 := by
  refine compose HasSnaky 7 childrenC_539_i0 childrenD_539_i0 children_work_539_i0 (0, 5)
    required_539_i0 envelope_539_i0 pivot_mem_539_i0 child_required_sub_539_i0 child_envelope_sub_539_i0 ?_
  intro b hb
  exact common_sub_539_i0 (mem_commonEnvelope childrenD_539_i0 b hb)
def required_539 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (3, 1), (3, 2), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_539 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 4), (0, 5), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, 0), (2, 1), (2, 5), (2, 6), (2, 8), (2, 9), (2, 10), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_539 : Fin 2 → Finset Cell := ![(placed21 0 (1, 5) required_6), required_539_i0]
def childrenD_539 : Fin 2 → Finset Cell := ![(placed21 0 (1, 5) envelope_6), envelope_539_i0]
theorem common_sub_539 : commonEnvelope childrenD_539 ⊆ insert (1, 9) required_539 := by decide +kernel
theorem child_required_sub_539 : ∀ j, childrenC_539 j ⊆ insert (1, 9) required_539 := by decide +kernel
theorem child_envelope_sub_539 : ∀ j, childrenD_539 j ⊆ envelope_539 := by decide +kernel
theorem pivot_mem_539 : (1, 9) ∈ envelope_539 := by decide +kernel
theorem children_work_539 : ∀ j, Template HasSnaky 8 (childrenC_539 j) (childrenD_539 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_6 0 (1, 5)).mono (by decide +kernel)
  · exact row_works_539_i0.mono (by decide +kernel)
theorem row_works_539 : Template HasSnaky 9 required_539 envelope_539 := by
  refine compose HasSnaky 8 childrenC_539 childrenD_539 children_work_539 (1, 9)
    required_539 envelope_539 pivot_mem_539 child_required_sub_539 child_envelope_sub_539 ?_
  intro b hb
  exact common_sub_539 (mem_commonEnvelope childrenD_539 b hb)
def required_548 : Finset Cell := ⟨(([(1, 5), (1, 6), (2, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_548 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 3), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 7), (2, 8), (2, 9), (2, 10), (3, 5), (3, 6), (3, 7), (3, 8), (4, 6), (4, 7), (4, 8), (5, 6), (5, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_548 : Fin 4 → Finset Cell := ![(placed21 2 (2, 4) required_10), (placed21 4 (1, 8) required_52), (placed21 0 (0, 3) required_189), (placed21 4 (0, 8) required_547)]
def childrenD_548 : Fin 4 → Finset Cell := ![(placed21 2 (2, 4) envelope_10), (placed21 4 (1, 8) envelope_52), (placed21 0 (0, 3) envelope_189), (placed21 4 (0, 8) envelope_547)]
theorem common_sub_548 : commonEnvelope childrenD_548 ⊆ insert (1, 7) required_548 := by decide +kernel
theorem child_required_sub_548 : ∀ j, childrenC_548 j ⊆ insert (1, 7) required_548 := by decide +kernel
theorem child_envelope_sub_548 : ∀ j, childrenD_548 j ⊆ envelope_548 := by decide +kernel
theorem pivot_mem_548 : (1, 7) ∈ envelope_548 := by decide +kernel
theorem children_work_548 : ∀ j, Template HasSnaky 8 (childrenC_548 j) (childrenD_548 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_10 2 (2, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_52 4 (1, 8)).mono (by decide +kernel)
  · exact (placed21_template row_works_189 0 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_547 4 (0, 8)).mono (by decide +kernel)
theorem row_works_548 : Template HasSnaky 9 required_548 envelope_548 := by
  refine compose HasSnaky 8 childrenC_548 childrenD_548 children_work_548 (1, 7)
    required_548 envelope_548 pivot_mem_548 child_required_sub_548 child_envelope_sub_548 ?_
  intro b hb
  exact common_sub_548 (mem_commonEnvelope childrenD_548 b hb)
def required_549 : Finset Cell := ⟨(([(0, 5), (1, 4), (1, 5), (2, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_549 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 7), (0, 8), (0, 9), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, 0), (2, 1), (2, 2), (2, 3), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (3, 2), (3, 3), (3, 4), (3, 5), (4, 2), (4, 3), (4, 4), (5, 2), (5, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_549 : Fin 4 → Finset Cell := ![(placed21 6 (2, 6) required_10), (placed21 0 (1, 2) required_52), (placed21 4 (0, 6) required_63), (placed21 0 (0, 2) required_547)]
def childrenD_549 : Fin 4 → Finset Cell := ![(placed21 6 (2, 6) envelope_10), (placed21 0 (1, 2) envelope_52), (placed21 4 (0, 6) envelope_63), (placed21 0 (0, 2) envelope_547)]
theorem common_sub_549 : commonEnvelope childrenD_549 ⊆ insert (1, 3) required_549 := by decide +kernel
theorem child_required_sub_549 : ∀ j, childrenC_549 j ⊆ insert (1, 3) required_549 := by decide +kernel
theorem child_envelope_sub_549 : ∀ j, childrenD_549 j ⊆ envelope_549 := by decide +kernel
theorem pivot_mem_549 : (1, 3) ∈ envelope_549 := by decide +kernel
theorem children_work_549 : ∀ j, Template HasSnaky 8 (childrenC_549 j) (childrenD_549 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_10 6 (2, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_52 0 (1, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_63 4 (0, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_547 0 (0, 2)).mono (by decide +kernel)
theorem row_works_549 : Template HasSnaky 9 required_549 envelope_549 := by
  refine compose HasSnaky 8 childrenC_549 childrenD_549 children_work_549 (1, 3)
    required_549 envelope_549 pivot_mem_549 child_required_sub_549 child_envelope_sub_549 ?_
  intro b hb
  exact common_sub_549 (mem_commonEnvelope childrenD_549 b hb)
def required_561_i0 : Finset Cell := ⟨(([(1, 3), (1, 4), (1, 5), (2, 5), (2, 7), (3, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_561_i0 : Finset Cell := ⟨(([(0, 5), (1, 3), (1, 4), (1, 5), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 5), (4, 6), (5, 6), (6, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_561_i0 : Fin 2 → Finset Cell := ![(placed21 7 (2, 7) required_1), (placed21 0 (0, 2) required_57)]
def childrenD_561_i0 : Fin 2 → Finset Cell := ![(placed21 7 (2, 7) envelope_1), (placed21 0 (0, 2) envelope_57)]
theorem common_sub_561_i0 : commonEnvelope childrenD_561_i0 ⊆ insert (2, 4) required_561_i0 := by decide +kernel
theorem child_required_sub_561_i0 : ∀ j, childrenC_561_i0 j ⊆ insert (2, 4) required_561_i0 := by decide +kernel
theorem child_envelope_sub_561_i0 : ∀ j, childrenD_561_i0 j ⊆ envelope_561_i0 := by decide +kernel
theorem pivot_mem_561_i0 : (2, 4) ∈ envelope_561_i0 := by decide +kernel
theorem children_work_561_i0 : ∀ j, Template HasSnaky 4 (childrenC_561_i0 j) (childrenD_561_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_1 7 (2, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_57 0 (0, 2)).mono (by decide +kernel)
theorem row_works_561_i0 : Template HasSnaky 5 required_561_i0 envelope_561_i0 := by
  refine compose HasSnaky 4 childrenC_561_i0 childrenD_561_i0 children_work_561_i0 (2, 4)
    required_561_i0 envelope_561_i0 pivot_mem_561_i0 child_required_sub_561_i0 child_envelope_sub_561_i0 ?_
  intro b hb
  exact common_sub_561_i0 (mem_commonEnvelope childrenD_561_i0 b hb)
def required_561 : Finset Cell := ⟨(([(1, 3), (1, 4), (1, 5), (2, 5), (3, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_561 : Finset Cell := ⟨(([(0, 5), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 1), (4, 2), (4, 3), (4, 5), (4, 6), (4, 8), (4, 9), (4, 10), (5, 6), (6, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_561 : Fin 4 → Finset Cell := ![(placed21 0 (1, 3) required_154), (placed21 4 (0, 10) required_319), (placed21 0 (0, 3) required_335), required_561_i0]
def childrenD_561 : Fin 4 → Finset Cell := ![(placed21 0 (1, 3) envelope_154), (placed21 4 (0, 10) envelope_319), (placed21 0 (0, 3) envelope_335), envelope_561_i0]
theorem common_sub_561 : commonEnvelope childrenD_561 ⊆ insert (2, 7) required_561 := by decide +kernel
theorem child_required_sub_561 : ∀ j, childrenC_561 j ⊆ insert (2, 7) required_561 := by decide +kernel
theorem child_envelope_sub_561 : ∀ j, childrenD_561 j ⊆ envelope_561 := by decide +kernel
theorem pivot_mem_561 : (2, 7) ∈ envelope_561 := by decide +kernel
theorem children_work_561 : ∀ j, Template HasSnaky 8 (childrenC_561 j) (childrenD_561 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_154 0 (1, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_319 4 (0, 10)).mono (by decide +kernel)
  · exact (placed21_template row_works_335 0 (0, 3)).mono (by decide +kernel)
  · exact row_works_561_i0.mono (by decide +kernel)
theorem row_works_561 : Template HasSnaky 9 required_561 envelope_561 := by
  refine compose HasSnaky 8 childrenC_561 childrenD_561 children_work_561 (2, 7)
    required_561 envelope_561 pivot_mem_561 child_required_sub_561 child_envelope_sub_561 ?_
  intro b hb
  exact common_sub_561 (mem_commonEnvelope childrenD_561 b hb)
def required_562_i0 : Finset Cell := ⟨(([(1, 4), (2, 4), (3, 3), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_562_i0 : Finset Cell := ⟨(([(1, 3), (1, 4), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 1), (4, 2), (4, 3), (4, 4), (4, 6), (4, 7), (4, 8), (5, 2), (5, 3), (6, 2), (6, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_562_i0 : Fin 5 → Finset Cell := ![(placed21 2 (4, 1) required_13), (placed21 0 (2, 1) required_14), (placed21 2 (4, 1) required_33), (placed21 0 (1, 2) required_122), (placed21 4 (1, 6) required_388)]
def childrenD_562_i0 : Fin 5 → Finset Cell := ![(placed21 2 (4, 1) envelope_13), (placed21 0 (2, 1) envelope_14), (placed21 2 (4, 1) envelope_33), (placed21 0 (1, 2) envelope_122), (placed21 4 (1, 6) envelope_388)]
theorem common_sub_562_i0 : commonEnvelope childrenD_562_i0 ⊆ insert (3, 5) required_562_i0 := by decide +kernel
theorem child_required_sub_562_i0 : ∀ j, childrenC_562_i0 j ⊆ insert (3, 5) required_562_i0 := by decide +kernel
theorem child_envelope_sub_562_i0 : ∀ j, childrenD_562_i0 j ⊆ envelope_562_i0 := by decide +kernel
theorem pivot_mem_562_i0 : (3, 5) ∈ envelope_562_i0 := by decide +kernel
theorem children_work_562_i0 : ∀ j, Template HasSnaky 7 (childrenC_562_i0 j) (childrenD_562_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_13 2 (4, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_14 0 (2, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_33 2 (4, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_122 0 (1, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_388 4 (1, 6)).mono (by decide +kernel)
theorem row_works_562_i0 : Template HasSnaky 8 required_562_i0 envelope_562_i0 := by
  refine compose HasSnaky 7 childrenC_562_i0 childrenD_562_i0 children_work_562_i0 (3, 5)
    required_562_i0 envelope_562_i0 pivot_mem_562_i0 child_required_sub_562_i0 child_envelope_sub_562_i0 ?_
  intro b hb
  exact common_sub_562_i0 (mem_commonEnvelope childrenD_562_i0 b hb)
def required_562 : Finset Cell := ⟨(([(1, 4), (2, 4), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_562 : Finset Cell := ⟨(([(0, 4), (1, 3), (1, 4), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 2), (5, 3), (6, 2), (6, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_562 : Fin 3 → Finset Cell := ![(placed21 3 (0, 4) required_52), (placed21 6 (4, 7) required_506), required_562_i0]
def childrenD_562 : Fin 3 → Finset Cell := ![(placed21 3 (0, 4) envelope_52), (placed21 6 (4, 7) envelope_506), envelope_562_i0]
theorem common_sub_562 : commonEnvelope childrenD_562 ⊆ insert (3, 3) required_562 := by decide +kernel
theorem child_required_sub_562 : ∀ j, childrenC_562 j ⊆ insert (3, 3) required_562 := by decide +kernel
theorem child_envelope_sub_562 : ∀ j, childrenD_562 j ⊆ envelope_562 := by decide +kernel
theorem pivot_mem_562 : (3, 3) ∈ envelope_562 := by decide +kernel
theorem children_work_562 : ∀ j, Template HasSnaky 8 (childrenC_562 j) (childrenD_562 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_52 3 (0, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_506 6 (4, 7)).mono (by decide +kernel)
  · exact row_works_562_i0.mono (by decide +kernel)
theorem row_works_562 : Template HasSnaky 9 required_562 envelope_562 := by
  refine compose HasSnaky 8 childrenC_562 childrenD_562 children_work_562 (3, 3)
    required_562 envelope_562 pivot_mem_562 child_required_sub_562 child_envelope_sub_562 ?_
  intro b hb
  exact common_sub_562 (mem_commonEnvelope childrenD_562 b hb)
def required_570_i0 : Finset Cell := ⟨(([(3, 6), (4, 3), (4, 4), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_570_i0 : Finset Cell := ⟨(([(3, 6), (3, 7), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 4), (5, 5), (5, 6), (5, 7), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (7, 5), (7, 6), (7, 7), (8, 5), (8, 6), (8, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_570_i0 : Fin 2 → Finset Cell := ![(placed21 5 (4, 3) required_5), (placed21 4 (3, 9) required_446)]
def childrenD_570_i0 : Fin 2 → Finset Cell := ![(placed21 5 (4, 3) envelope_5), (placed21 4 (3, 9) envelope_446)]
theorem common_sub_570_i0 : commonEnvelope childrenD_570_i0 ⊆ insert (4, 5) required_570_i0 := by decide +kernel
theorem child_required_sub_570_i0 : ∀ j, childrenC_570_i0 j ⊆ insert (4, 5) required_570_i0 := by decide +kernel
theorem child_envelope_sub_570_i0 : ∀ j, childrenD_570_i0 j ⊆ envelope_570_i0 := by decide +kernel
theorem pivot_mem_570_i0 : (4, 5) ∈ envelope_570_i0 := by decide +kernel
theorem children_work_570_i0 : ∀ j, Template HasSnaky 7 (childrenC_570_i0 j) (childrenD_570_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 5 (4, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_446 4 (3, 9)).mono (by decide +kernel)
theorem row_works_570_i0 : Template HasSnaky 8 required_570_i0 envelope_570_i0 := by
  refine compose HasSnaky 7 childrenC_570_i0 childrenD_570_i0 children_work_570_i0 (4, 5)
    required_570_i0 envelope_570_i0 pivot_mem_570_i0 child_required_sub_570_i0 child_envelope_sub_570_i0 ?_
  intro b hb
  exact common_sub_570_i0 (mem_commonEnvelope childrenD_570_i0 b hb)
def required_570_i2 : Finset Cell := ⟨(([(2, 3), (3, 3), (3, 4), (4, 3), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_570_i2 : Finset Cell := ⟨(([(2, 3), (3, 3), (3, 4), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, 2), (7, 3), (7, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_570_i2 : Fin 3 → Finset Cell := ![(placed21 3 (2, 4) required_20), (placed21 1 (2, 3) required_29), (placed21 0 (2, 0) required_331)]
def childrenD_570_i2 : Fin 3 → Finset Cell := ![(placed21 3 (2, 4) envelope_20), (placed21 1 (2, 3) envelope_29), (placed21 0 (2, 0) envelope_331)]
theorem common_sub_570_i2 : commonEnvelope childrenD_570_i2 ⊆ insert (5, 3) required_570_i2 := by decide +kernel
theorem child_required_sub_570_i2 : ∀ j, childrenC_570_i2 j ⊆ insert (5, 3) required_570_i2 := by decide +kernel
theorem child_envelope_sub_570_i2 : ∀ j, childrenD_570_i2 j ⊆ envelope_570_i2 := by decide +kernel
theorem pivot_mem_570_i2 : (5, 3) ∈ envelope_570_i2 := by decide +kernel
theorem children_work_570_i2 : ∀ j, Template HasSnaky 6 (childrenC_570_i2 j) (childrenD_570_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_20 3 (2, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_29 1 (2, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_331 0 (2, 0)).mono (by decide +kernel)
theorem row_works_570_i2 : Template HasSnaky 7 required_570_i2 envelope_570_i2 := by
  refine compose HasSnaky 6 childrenC_570_i2 childrenD_570_i2 children_work_570_i2 (5, 3)
    required_570_i2 envelope_570_i2 pivot_mem_570_i2 child_required_sub_570_i2 child_envelope_sub_570_i2 ?_
  intro b hb
  exact common_sub_570_i2 (mem_commonEnvelope childrenD_570_i2 b hb)
def required_570_i1 : Finset Cell := ⟨(([(0, 3), (3, 3), (3, 4), (4, 3), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_570_i1 : Finset Cell := ⟨(([(0, 3), (1, 3), (2, 3), (3, 3), (3, 4), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, 2), (7, 3), (7, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_570_i1 : Fin 2 → Finset Cell := ![(placed21 0 (0, 3) required_1), required_570_i2]
def childrenD_570_i1 : Fin 2 → Finset Cell := ![(placed21 0 (0, 3) envelope_1), envelope_570_i2]
theorem common_sub_570_i1 : commonEnvelope childrenD_570_i1 ⊆ insert (2, 3) required_570_i1 := by decide +kernel
theorem child_required_sub_570_i1 : ∀ j, childrenC_570_i1 j ⊆ insert (2, 3) required_570_i1 := by decide +kernel
theorem child_envelope_sub_570_i1 : ∀ j, childrenD_570_i1 j ⊆ envelope_570_i1 := by decide +kernel
theorem pivot_mem_570_i1 : (2, 3) ∈ envelope_570_i1 := by decide +kernel
theorem children_work_570_i1 : ∀ j, Template HasSnaky 7 (childrenC_570_i1 j) (childrenD_570_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_1 0 (0, 3)).mono (by decide +kernel)
  · exact row_works_570_i2.mono (by decide +kernel)
theorem row_works_570_i1 : Template HasSnaky 8 required_570_i1 envelope_570_i1 := by
  refine compose HasSnaky 7 childrenC_570_i1 childrenD_570_i1 children_work_570_i1 (2, 3)
    required_570_i1 envelope_570_i1 pivot_mem_570_i1 child_required_sub_570_i1 child_envelope_sub_570_i1 ?_
  intro b hb
  exact common_sub_570_i1 (mem_commonEnvelope childrenD_570_i1 b hb)
def required_570 : Finset Cell := ⟨(([(0, 3), (3, 3), (3, 4), (3, 6), (4, 4), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_570 : Finset Cell := ⟨(([(0, 3), (1, 3), (2, 3), (3, 3), (3, 4), (3, 6), (3, 7), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (8, 5), (8, 6), (8, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_570 : Fin 4 → Finset Cell := ![(placed21 4 (3, 7) required_150), (placed21 0 (0, 1) required_283), required_570_i0, required_570_i1]
def childrenD_570 : Fin 4 → Finset Cell := ![(placed21 4 (3, 7) envelope_150), (placed21 0 (0, 1) envelope_283), envelope_570_i0, envelope_570_i1]
theorem common_sub_570 : commonEnvelope childrenD_570 ⊆ insert (4, 3) required_570 := by decide +kernel
theorem child_required_sub_570 : ∀ j, childrenC_570 j ⊆ insert (4, 3) required_570 := by decide +kernel
theorem child_envelope_sub_570 : ∀ j, childrenD_570 j ⊆ envelope_570 := by decide +kernel
theorem pivot_mem_570 : (4, 3) ∈ envelope_570 := by decide +kernel
theorem children_work_570 : ∀ j, Template HasSnaky 8 (childrenC_570 j) (childrenD_570 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_150 4 (3, 7)).mono (by decide +kernel)
  · exact (placed21_template row_works_283 0 (0, 1)).mono (by decide +kernel)
  · exact row_works_570_i0.mono (by decide +kernel)
  · exact row_works_570_i1.mono (by decide +kernel)
theorem row_works_570 : Template HasSnaky 9 required_570 envelope_570 := by
  refine compose HasSnaky 8 childrenC_570 childrenD_570 children_work_570 (4, 3)
    required_570 envelope_570 pivot_mem_570 child_required_sub_570 child_envelope_sub_570 ?_
  intro b hb
  exact common_sub_570 (mem_commonEnvelope childrenD_570 b hb)
def height_539_i4 : ℕ := 3
def childrenH_539_i4 : Fin 2 → ℕ := ![height_5, height_6]
theorem height_exact_539_i4 : height_539_i4 = 1 + Finset.univ.sup childrenH_539_i4 := by decide +kernel
theorem required_origin_539_i4 : ∀ x ∈ required_539_i4,
    (∃ j, x ∈ childrenC_539_i4 j) ∨ ∀ j, x ∈ childrenD_539_i4 j := by decide +kernel
theorem required_exact_539_i4 : required_539_i4 =
    ((Finset.univ.biUnion childrenC_539_i4) ∪ commonEnvelope childrenD_539_i4).erase (3, 5) := by
  exact required_eq_combination childrenC_539_i4 childrenD_539_i4 (3, 5) required_539_i4
    (by decide +kernel) child_required_sub_539_i4 common_sub_539_i4 required_origin_539_i4
theorem envelope_origin_539_i4 : ∀ x ∈ envelope_539_i4,
    x = (3, 5) ∨ ∃ j, x ∈ childrenD_539_i4 j := by decide +kernel
theorem envelope_exact_539_i4 : envelope_539_i4 =
    insert (3, 5) (Finset.univ.biUnion childrenD_539_i4) := by
  exact envelope_eq_combination childrenD_539_i4 (3, 5) envelope_539_i4
    pivot_mem_539_i4 child_envelope_sub_539_i4 envelope_origin_539_i4
def checked_539_i4 : CheckedCard where
  required := required_539_i4
  envelope := envelope_539_i4
  height := height_539_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_539_i4
def height_539_i3 : ℕ := 4
def childrenH_539_i3 : Fin 2 → ℕ := ![height_5, height_539_i4]
theorem height_exact_539_i3 : height_539_i3 = 1 + Finset.univ.sup childrenH_539_i3 := by decide +kernel
theorem required_origin_539_i3 : ∀ x ∈ required_539_i3,
    (∃ j, x ∈ childrenC_539_i3 j) ∨ ∀ j, x ∈ childrenD_539_i3 j := by decide +kernel
theorem required_exact_539_i3 : required_539_i3 =
    ((Finset.univ.biUnion childrenC_539_i3) ∪ commonEnvelope childrenD_539_i3).erase (3, 4) := by
  exact required_eq_combination childrenC_539_i3 childrenD_539_i3 (3, 4) required_539_i3
    (by decide +kernel) child_required_sub_539_i3 common_sub_539_i3 required_origin_539_i3
theorem envelope_origin_539_i3 : ∀ x ∈ envelope_539_i3,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_539_i3 j := by decide +kernel
theorem envelope_exact_539_i3 : envelope_539_i3 =
    insert (3, 4) (Finset.univ.biUnion childrenD_539_i3) := by
  exact envelope_eq_combination childrenD_539_i3 (3, 4) envelope_539_i3
    pivot_mem_539_i3 child_envelope_sub_539_i3 envelope_origin_539_i3
def checked_539_i3 : CheckedCard where
  required := required_539_i3
  envelope := envelope_539_i3
  height := height_539_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_539_i3
def height_539_i7 : ℕ := 3
def childrenH_539_i7 : Fin 2 → ℕ := ![height_1, height_153]
theorem height_exact_539_i7 : height_539_i7 = 1 + Finset.univ.sup childrenH_539_i7 := by decide +kernel
theorem required_origin_539_i7 : ∀ x ∈ required_539_i7,
    (∃ j, x ∈ childrenC_539_i7 j) ∨ ∀ j, x ∈ childrenD_539_i7 j := by decide +kernel
theorem required_exact_539_i7 : required_539_i7 =
    ((Finset.univ.biUnion childrenC_539_i7) ∪ commonEnvelope childrenD_539_i7).erase (4, 2) := by
  exact required_eq_combination childrenC_539_i7 childrenD_539_i7 (4, 2) required_539_i7
    (by decide +kernel) child_required_sub_539_i7 common_sub_539_i7 required_origin_539_i7
theorem envelope_origin_539_i7 : ∀ x ∈ envelope_539_i7,
    x = (4, 2) ∨ ∃ j, x ∈ childrenD_539_i7 j := by decide +kernel
theorem envelope_exact_539_i7 : envelope_539_i7 =
    insert (4, 2) (Finset.univ.biUnion childrenD_539_i7) := by
  exact envelope_eq_combination childrenD_539_i7 (4, 2) envelope_539_i7
    pivot_mem_539_i7 child_envelope_sub_539_i7 envelope_origin_539_i7
def checked_539_i7 : CheckedCard where
  required := required_539_i7
  envelope := envelope_539_i7
  height := height_539_i7
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_539_i7
def height_539_i6 : ℕ := 4
def childrenH_539_i6 : Fin 2 → ℕ := ![height_5, height_539_i7]
theorem height_exact_539_i6 : height_539_i6 = 1 + Finset.univ.sup childrenH_539_i6 := by decide +kernel
theorem required_origin_539_i6 : ∀ x ∈ required_539_i6,
    (∃ j, x ∈ childrenC_539_i6 j) ∨ ∀ j, x ∈ childrenD_539_i6 j := by decide +kernel
theorem required_exact_539_i6 : required_539_i6 =
    ((Finset.univ.biUnion childrenC_539_i6) ∪ commonEnvelope childrenD_539_i6).erase (3, 5) := by
  exact required_eq_combination childrenC_539_i6 childrenD_539_i6 (3, 5) required_539_i6
    (by decide +kernel) child_required_sub_539_i6 common_sub_539_i6 required_origin_539_i6
theorem envelope_origin_539_i6 : ∀ x ∈ envelope_539_i6,
    x = (3, 5) ∨ ∃ j, x ∈ childrenD_539_i6 j := by decide +kernel
theorem envelope_exact_539_i6 : envelope_539_i6 =
    insert (3, 5) (Finset.univ.biUnion childrenD_539_i6) := by
  exact envelope_eq_combination childrenD_539_i6 (3, 5) envelope_539_i6
    pivot_mem_539_i6 child_envelope_sub_539_i6 envelope_origin_539_i6
def checked_539_i6 : CheckedCard where
  required := required_539_i6
  envelope := envelope_539_i6
  height := height_539_i6
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_539_i6
def height_539_i5 : ℕ := 5
def childrenH_539_i5 : Fin 2 → ℕ := ![height_5, height_539_i6]
theorem height_exact_539_i5 : height_539_i5 = 1 + Finset.univ.sup childrenH_539_i5 := by decide +kernel
theorem required_origin_539_i5 : ∀ x ∈ required_539_i5,
    (∃ j, x ∈ childrenC_539_i5 j) ∨ ∀ j, x ∈ childrenD_539_i5 j := by decide +kernel
theorem required_exact_539_i5 : required_539_i5 =
    ((Finset.univ.biUnion childrenC_539_i5) ∪ commonEnvelope childrenD_539_i5).erase (3, 4) := by
  exact required_eq_combination childrenC_539_i5 childrenD_539_i5 (3, 4) required_539_i5
    (by decide +kernel) child_required_sub_539_i5 common_sub_539_i5 required_origin_539_i5
theorem envelope_origin_539_i5 : ∀ x ∈ envelope_539_i5,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_539_i5 j := by decide +kernel
theorem envelope_exact_539_i5 : envelope_539_i5 =
    insert (3, 4) (Finset.univ.biUnion childrenD_539_i5) := by
  exact envelope_eq_combination childrenD_539_i5 (3, 4) envelope_539_i5
    pivot_mem_539_i5 child_envelope_sub_539_i5 envelope_origin_539_i5
def checked_539_i5 : CheckedCard where
  required := required_539_i5
  envelope := envelope_539_i5
  height := height_539_i5
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_539_i5
def height_539_i9 : ℕ := 2
def childrenH_539_i9 : Fin 2 → ℕ := ![height_0, height_2]
theorem height_exact_539_i9 : height_539_i9 = 1 + Finset.univ.sup childrenH_539_i9 := by decide +kernel
theorem required_origin_539_i9 : ∀ x ∈ required_539_i9,
    (∃ j, x ∈ childrenC_539_i9 j) ∨ ∀ j, x ∈ childrenD_539_i9 j := by decide +kernel
theorem required_exact_539_i9 : required_539_i9 =
    ((Finset.univ.biUnion childrenC_539_i9) ∪ commonEnvelope childrenD_539_i9).erase (1, 2) := by
  exact required_eq_combination childrenC_539_i9 childrenD_539_i9 (1, 2) required_539_i9
    (by decide +kernel) child_required_sub_539_i9 common_sub_539_i9 required_origin_539_i9
theorem envelope_origin_539_i9 : ∀ x ∈ envelope_539_i9,
    x = (1, 2) ∨ ∃ j, x ∈ childrenD_539_i9 j := by decide +kernel
theorem envelope_exact_539_i9 : envelope_539_i9 =
    insert (1, 2) (Finset.univ.biUnion childrenD_539_i9) := by
  exact envelope_eq_combination childrenD_539_i9 (1, 2) envelope_539_i9
    pivot_mem_539_i9 child_envelope_sub_539_i9 envelope_origin_539_i9
def checked_539_i9 : CheckedCard where
  required := required_539_i9
  envelope := envelope_539_i9
  height := height_539_i9
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_539_i9
def height_539_i8 : ℕ := 3
def childrenH_539_i8 : Fin 2 → ℕ := ![height_5, height_539_i9]
theorem height_exact_539_i8 : height_539_i8 = 1 + Finset.univ.sup childrenH_539_i8 := by decide +kernel
theorem required_origin_539_i8 : ∀ x ∈ required_539_i8,
    (∃ j, x ∈ childrenC_539_i8 j) ∨ ∀ j, x ∈ childrenD_539_i8 j := by decide +kernel
theorem required_exact_539_i8 : required_539_i8 =
    ((Finset.univ.biUnion childrenC_539_i8) ∪ commonEnvelope childrenD_539_i8).erase (1, 1) := by
  exact required_eq_combination childrenC_539_i8 childrenD_539_i8 (1, 1) required_539_i8
    (by decide +kernel) child_required_sub_539_i8 common_sub_539_i8 required_origin_539_i8
theorem envelope_origin_539_i8 : ∀ x ∈ envelope_539_i8,
    x = (1, 1) ∨ ∃ j, x ∈ childrenD_539_i8 j := by decide +kernel
theorem envelope_exact_539_i8 : envelope_539_i8 =
    insert (1, 1) (Finset.univ.biUnion childrenD_539_i8) := by
  exact envelope_eq_combination childrenD_539_i8 (1, 1) envelope_539_i8
    pivot_mem_539_i8 child_envelope_sub_539_i8 envelope_origin_539_i8
def checked_539_i8 : CheckedCard where
  required := required_539_i8
  envelope := envelope_539_i8
  height := height_539_i8
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_539_i8
def height_539_i10 : ℕ := 3
def childrenH_539_i10 : Fin 2 → ℕ := ![height_83, height_281]
theorem height_exact_539_i10 : height_539_i10 = 1 + Finset.univ.sup childrenH_539_i10 := by decide +kernel
theorem required_origin_539_i10 : ∀ x ∈ required_539_i10,
    (∃ j, x ∈ childrenC_539_i10 j) ∨ ∀ j, x ∈ childrenD_539_i10 j := by decide +kernel
theorem required_exact_539_i10 : required_539_i10 =
    ((Finset.univ.biUnion childrenC_539_i10) ∪ commonEnvelope childrenD_539_i10).erase (4, 1) := by
  exact required_eq_combination childrenC_539_i10 childrenD_539_i10 (4, 1) required_539_i10
    (by decide +kernel) child_required_sub_539_i10 common_sub_539_i10 required_origin_539_i10
theorem envelope_origin_539_i10 : ∀ x ∈ envelope_539_i10,
    x = (4, 1) ∨ ∃ j, x ∈ childrenD_539_i10 j := by decide +kernel
theorem envelope_exact_539_i10 : envelope_539_i10 =
    insert (4, 1) (Finset.univ.biUnion childrenD_539_i10) := by
  exact envelope_eq_combination childrenD_539_i10 (4, 1) envelope_539_i10
    pivot_mem_539_i10 child_envelope_sub_539_i10 envelope_origin_539_i10
def checked_539_i10 : CheckedCard where
  required := required_539_i10
  envelope := envelope_539_i10
  height := height_539_i10
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_539_i10
def height_539_i2 : ℕ := 6
def childrenH_539_i2 : Fin 4 → ℕ := ![height_539_i3, height_539_i5, height_539_i8, height_539_i10]
theorem height_exact_539_i2 : height_539_i2 = 1 + Finset.univ.sup childrenH_539_i2 := by decide +kernel
theorem required_origin_539_i2 : ∀ x ∈ required_539_i2,
    (∃ j, x ∈ childrenC_539_i2 j) ∨ ∀ j, x ∈ childrenD_539_i2 j := by decide +kernel
theorem required_exact_539_i2 : required_539_i2 =
    ((Finset.univ.biUnion childrenC_539_i2) ∪ commonEnvelope childrenD_539_i2).erase (2, 1) := by
  exact required_eq_combination childrenC_539_i2 childrenD_539_i2 (2, 1) required_539_i2
    (by decide +kernel) child_required_sub_539_i2 common_sub_539_i2 required_origin_539_i2
theorem envelope_origin_539_i2 : ∀ x ∈ envelope_539_i2,
    x = (2, 1) ∨ ∃ j, x ∈ childrenD_539_i2 j := by decide +kernel
theorem envelope_exact_539_i2 : envelope_539_i2 =
    insert (2, 1) (Finset.univ.biUnion childrenD_539_i2) := by
  exact envelope_eq_combination childrenD_539_i2 (2, 1) envelope_539_i2
    pivot_mem_539_i2 child_envelope_sub_539_i2 envelope_origin_539_i2
def checked_539_i2 : CheckedCard where
  required := required_539_i2
  envelope := envelope_539_i2
  height := height_539_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_539_i2
def height_539_i1 : ℕ := 7
def childrenH_539_i1 : Fin 2 → ℕ := ![height_4, height_539_i2]
theorem height_exact_539_i1 : height_539_i1 = 1 + Finset.univ.sup childrenH_539_i1 := by decide +kernel
theorem required_origin_539_i1 : ∀ x ∈ required_539_i1,
    (∃ j, x ∈ childrenC_539_i1 j) ∨ ∀ j, x ∈ childrenD_539_i1 j := by decide +kernel
theorem required_exact_539_i1 : required_539_i1 =
    ((Finset.univ.biUnion childrenC_539_i1) ∪ commonEnvelope childrenD_539_i1).erase (2, 5) := by
  exact required_eq_combination childrenC_539_i1 childrenD_539_i1 (2, 5) required_539_i1
    (by decide +kernel) child_required_sub_539_i1 common_sub_539_i1 required_origin_539_i1
theorem envelope_origin_539_i1 : ∀ x ∈ envelope_539_i1,
    x = (2, 5) ∨ ∃ j, x ∈ childrenD_539_i1 j := by decide +kernel
theorem envelope_exact_539_i1 : envelope_539_i1 =
    insert (2, 5) (Finset.univ.biUnion childrenD_539_i1) := by
  exact envelope_eq_combination childrenD_539_i1 (2, 5) envelope_539_i1
    pivot_mem_539_i1 child_envelope_sub_539_i1 envelope_origin_539_i1
def checked_539_i1 : CheckedCard where
  required := required_539_i1
  envelope := envelope_539_i1
  height := height_539_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_539_i1
def height_539_i0 : ℕ := 8
def childrenH_539_i0 : Fin 2 → ℕ := ![height_5, height_539_i1]
theorem height_exact_539_i0 : height_539_i0 = 1 + Finset.univ.sup childrenH_539_i0 := by decide +kernel
theorem required_origin_539_i0 : ∀ x ∈ required_539_i0,
    (∃ j, x ∈ childrenC_539_i0 j) ∨ ∀ j, x ∈ childrenD_539_i0 j := by decide +kernel
theorem required_exact_539_i0 : required_539_i0 =
    ((Finset.univ.biUnion childrenC_539_i0) ∪ commonEnvelope childrenD_539_i0).erase (0, 5) := by
  exact required_eq_combination childrenC_539_i0 childrenD_539_i0 (0, 5) required_539_i0
    (by decide +kernel) child_required_sub_539_i0 common_sub_539_i0 required_origin_539_i0
theorem envelope_origin_539_i0 : ∀ x ∈ envelope_539_i0,
    x = (0, 5) ∨ ∃ j, x ∈ childrenD_539_i0 j := by decide +kernel
theorem envelope_exact_539_i0 : envelope_539_i0 =
    insert (0, 5) (Finset.univ.biUnion childrenD_539_i0) := by
  exact envelope_eq_combination childrenD_539_i0 (0, 5) envelope_539_i0
    pivot_mem_539_i0 child_envelope_sub_539_i0 envelope_origin_539_i0
def checked_539_i0 : CheckedCard where
  required := required_539_i0
  envelope := envelope_539_i0
  height := height_539_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_539_i0
def height_539 : ℕ := 9
def childrenH_539 : Fin 2 → ℕ := ![height_6, height_539_i0]
theorem height_exact_539 : height_539 = 1 + Finset.univ.sup childrenH_539 := by decide +kernel
theorem required_origin_539 : ∀ x ∈ required_539,
    (∃ j, x ∈ childrenC_539 j) ∨ ∀ j, x ∈ childrenD_539 j := by decide +kernel
theorem required_exact_539 : required_539 =
    ((Finset.univ.biUnion childrenC_539) ∪ commonEnvelope childrenD_539).erase (1, 9) := by
  exact required_eq_combination childrenC_539 childrenD_539 (1, 9) required_539
    (by decide +kernel) child_required_sub_539 common_sub_539 required_origin_539
theorem envelope_origin_539 : ∀ x ∈ envelope_539,
    x = (1, 9) ∨ ∃ j, x ∈ childrenD_539 j := by decide +kernel
theorem envelope_exact_539 : envelope_539 =
    insert (1, 9) (Finset.univ.biUnion childrenD_539) := by
  exact envelope_eq_combination childrenD_539 (1, 9) envelope_539
    pivot_mem_539 child_envelope_sub_539 envelope_origin_539
def checked_539 : CheckedCard where
  required := required_539
  envelope := envelope_539
  height := height_539
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_539
def height_548 : ℕ := 9
def childrenH_548 : Fin 4 → ℕ := ![height_10, height_52, height_189, height_547]
theorem height_exact_548 : height_548 = 1 + Finset.univ.sup childrenH_548 := by decide +kernel
theorem required_origin_548 : ∀ x ∈ required_548,
    (∃ j, x ∈ childrenC_548 j) ∨ ∀ j, x ∈ childrenD_548 j := by decide +kernel
theorem required_exact_548 : required_548 =
    ((Finset.univ.biUnion childrenC_548) ∪ commonEnvelope childrenD_548).erase (1, 7) := by
  exact required_eq_combination childrenC_548 childrenD_548 (1, 7) required_548
    (by decide +kernel) child_required_sub_548 common_sub_548 required_origin_548
theorem envelope_origin_548 : ∀ x ∈ envelope_548,
    x = (1, 7) ∨ ∃ j, x ∈ childrenD_548 j := by decide +kernel
theorem envelope_exact_548 : envelope_548 =
    insert (1, 7) (Finset.univ.biUnion childrenD_548) := by
  exact envelope_eq_combination childrenD_548 (1, 7) envelope_548
    pivot_mem_548 child_envelope_sub_548 envelope_origin_548
def checked_548 : CheckedCard where
  required := required_548
  envelope := envelope_548
  height := height_548
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_548
def height_549 : ℕ := 9
def childrenH_549 : Fin 4 → ℕ := ![height_10, height_52, height_63, height_547]
theorem height_exact_549 : height_549 = 1 + Finset.univ.sup childrenH_549 := by decide +kernel
theorem required_origin_549 : ∀ x ∈ required_549,
    (∃ j, x ∈ childrenC_549 j) ∨ ∀ j, x ∈ childrenD_549 j := by decide +kernel
theorem required_exact_549 : required_549 =
    ((Finset.univ.biUnion childrenC_549) ∪ commonEnvelope childrenD_549).erase (1, 3) := by
  exact required_eq_combination childrenC_549 childrenD_549 (1, 3) required_549
    (by decide +kernel) child_required_sub_549 common_sub_549 required_origin_549
theorem envelope_origin_549 : ∀ x ∈ envelope_549,
    x = (1, 3) ∨ ∃ j, x ∈ childrenD_549 j := by decide +kernel
theorem envelope_exact_549 : envelope_549 =
    insert (1, 3) (Finset.univ.biUnion childrenD_549) := by
  exact envelope_eq_combination childrenD_549 (1, 3) envelope_549
    pivot_mem_549 child_envelope_sub_549 envelope_origin_549
def checked_549 : CheckedCard where
  required := required_549
  envelope := envelope_549
  height := height_549
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_549
def height_561_i0 : ℕ := 5
def childrenH_561_i0 : Fin 2 → ℕ := ![height_1, height_57]
theorem height_exact_561_i0 : height_561_i0 = 1 + Finset.univ.sup childrenH_561_i0 := by decide +kernel
theorem required_origin_561_i0 : ∀ x ∈ required_561_i0,
    (∃ j, x ∈ childrenC_561_i0 j) ∨ ∀ j, x ∈ childrenD_561_i0 j := by decide +kernel
theorem required_exact_561_i0 : required_561_i0 =
    ((Finset.univ.biUnion childrenC_561_i0) ∪ commonEnvelope childrenD_561_i0).erase (2, 4) := by
  exact required_eq_combination childrenC_561_i0 childrenD_561_i0 (2, 4) required_561_i0
    (by decide +kernel) child_required_sub_561_i0 common_sub_561_i0 required_origin_561_i0
theorem envelope_origin_561_i0 : ∀ x ∈ envelope_561_i0,
    x = (2, 4) ∨ ∃ j, x ∈ childrenD_561_i0 j := by decide +kernel
theorem envelope_exact_561_i0 : envelope_561_i0 =
    insert (2, 4) (Finset.univ.biUnion childrenD_561_i0) := by
  exact envelope_eq_combination childrenD_561_i0 (2, 4) envelope_561_i0
    pivot_mem_561_i0 child_envelope_sub_561_i0 envelope_origin_561_i0
def checked_561_i0 : CheckedCard where
  required := required_561_i0
  envelope := envelope_561_i0
  height := height_561_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_561_i0
def height_561 : ℕ := 9
def childrenH_561 : Fin 4 → ℕ := ![height_154, height_319, height_335, height_561_i0]
theorem height_exact_561 : height_561 = 1 + Finset.univ.sup childrenH_561 := by decide +kernel
theorem required_origin_561 : ∀ x ∈ required_561,
    (∃ j, x ∈ childrenC_561 j) ∨ ∀ j, x ∈ childrenD_561 j := by decide +kernel
theorem required_exact_561 : required_561 =
    ((Finset.univ.biUnion childrenC_561) ∪ commonEnvelope childrenD_561).erase (2, 7) := by
  exact required_eq_combination childrenC_561 childrenD_561 (2, 7) required_561
    (by decide +kernel) child_required_sub_561 common_sub_561 required_origin_561
theorem envelope_origin_561 : ∀ x ∈ envelope_561,
    x = (2, 7) ∨ ∃ j, x ∈ childrenD_561 j := by decide +kernel
theorem envelope_exact_561 : envelope_561 =
    insert (2, 7) (Finset.univ.biUnion childrenD_561) := by
  exact envelope_eq_combination childrenD_561 (2, 7) envelope_561
    pivot_mem_561 child_envelope_sub_561 envelope_origin_561
def checked_561 : CheckedCard where
  required := required_561
  envelope := envelope_561
  height := height_561
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_561
def height_562_i0 : ℕ := 8
def childrenH_562_i0 : Fin 5 → ℕ := ![height_13, height_14, height_33, height_122, height_388]
theorem height_exact_562_i0 : height_562_i0 = 1 + Finset.univ.sup childrenH_562_i0 := by decide +kernel
theorem required_origin_562_i0 : ∀ x ∈ required_562_i0,
    (∃ j, x ∈ childrenC_562_i0 j) ∨ ∀ j, x ∈ childrenD_562_i0 j := by decide +kernel
theorem required_exact_562_i0 : required_562_i0 =
    ((Finset.univ.biUnion childrenC_562_i0) ∪ commonEnvelope childrenD_562_i0).erase (3, 5) := by
  exact required_eq_combination childrenC_562_i0 childrenD_562_i0 (3, 5) required_562_i0
    (by decide +kernel) child_required_sub_562_i0 common_sub_562_i0 required_origin_562_i0
theorem envelope_origin_562_i0 : ∀ x ∈ envelope_562_i0,
    x = (3, 5) ∨ ∃ j, x ∈ childrenD_562_i0 j := by decide +kernel
theorem envelope_exact_562_i0 : envelope_562_i0 =
    insert (3, 5) (Finset.univ.biUnion childrenD_562_i0) := by
  exact envelope_eq_combination childrenD_562_i0 (3, 5) envelope_562_i0
    pivot_mem_562_i0 child_envelope_sub_562_i0 envelope_origin_562_i0
def checked_562_i0 : CheckedCard where
  required := required_562_i0
  envelope := envelope_562_i0
  height := height_562_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_562_i0
def height_562 : ℕ := 9
def childrenH_562 : Fin 3 → ℕ := ![height_52, height_506, height_562_i0]
theorem height_exact_562 : height_562 = 1 + Finset.univ.sup childrenH_562 := by decide +kernel
theorem required_origin_562 : ∀ x ∈ required_562,
    (∃ j, x ∈ childrenC_562 j) ∨ ∀ j, x ∈ childrenD_562 j := by decide +kernel
theorem required_exact_562 : required_562 =
    ((Finset.univ.biUnion childrenC_562) ∪ commonEnvelope childrenD_562).erase (3, 3) := by
  exact required_eq_combination childrenC_562 childrenD_562 (3, 3) required_562
    (by decide +kernel) child_required_sub_562 common_sub_562 required_origin_562
theorem envelope_origin_562 : ∀ x ∈ envelope_562,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_562 j := by decide +kernel
theorem envelope_exact_562 : envelope_562 =
    insert (3, 3) (Finset.univ.biUnion childrenD_562) := by
  exact envelope_eq_combination childrenD_562 (3, 3) envelope_562
    pivot_mem_562 child_envelope_sub_562 envelope_origin_562
def checked_562 : CheckedCard where
  required := required_562
  envelope := envelope_562
  height := height_562
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_562
def height_570_i0 : ℕ := 8
def childrenH_570_i0 : Fin 2 → ℕ := ![height_5, height_446]
theorem height_exact_570_i0 : height_570_i0 = 1 + Finset.univ.sup childrenH_570_i0 := by decide +kernel
theorem required_origin_570_i0 : ∀ x ∈ required_570_i0,
    (∃ j, x ∈ childrenC_570_i0 j) ∨ ∀ j, x ∈ childrenD_570_i0 j := by decide +kernel
theorem required_exact_570_i0 : required_570_i0 =
    ((Finset.univ.biUnion childrenC_570_i0) ∪ commonEnvelope childrenD_570_i0).erase (4, 5) := by
  exact required_eq_combination childrenC_570_i0 childrenD_570_i0 (4, 5) required_570_i0
    (by decide +kernel) child_required_sub_570_i0 common_sub_570_i0 required_origin_570_i0
theorem envelope_origin_570_i0 : ∀ x ∈ envelope_570_i0,
    x = (4, 5) ∨ ∃ j, x ∈ childrenD_570_i0 j := by decide +kernel
theorem envelope_exact_570_i0 : envelope_570_i0 =
    insert (4, 5) (Finset.univ.biUnion childrenD_570_i0) := by
  exact envelope_eq_combination childrenD_570_i0 (4, 5) envelope_570_i0
    pivot_mem_570_i0 child_envelope_sub_570_i0 envelope_origin_570_i0
def checked_570_i0 : CheckedCard where
  required := required_570_i0
  envelope := envelope_570_i0
  height := height_570_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_570_i0
def height_570_i2 : ℕ := 7
def childrenH_570_i2 : Fin 3 → ℕ := ![height_20, height_29, height_331]
theorem height_exact_570_i2 : height_570_i2 = 1 + Finset.univ.sup childrenH_570_i2 := by decide +kernel
theorem required_origin_570_i2 : ∀ x ∈ required_570_i2,
    (∃ j, x ∈ childrenC_570_i2 j) ∨ ∀ j, x ∈ childrenD_570_i2 j := by decide +kernel
theorem required_exact_570_i2 : required_570_i2 =
    ((Finset.univ.biUnion childrenC_570_i2) ∪ commonEnvelope childrenD_570_i2).erase (5, 3) := by
  exact required_eq_combination childrenC_570_i2 childrenD_570_i2 (5, 3) required_570_i2
    (by decide +kernel) child_required_sub_570_i2 common_sub_570_i2 required_origin_570_i2
theorem envelope_origin_570_i2 : ∀ x ∈ envelope_570_i2,
    x = (5, 3) ∨ ∃ j, x ∈ childrenD_570_i2 j := by decide +kernel
theorem envelope_exact_570_i2 : envelope_570_i2 =
    insert (5, 3) (Finset.univ.biUnion childrenD_570_i2) := by
  exact envelope_eq_combination childrenD_570_i2 (5, 3) envelope_570_i2
    pivot_mem_570_i2 child_envelope_sub_570_i2 envelope_origin_570_i2
def checked_570_i2 : CheckedCard where
  required := required_570_i2
  envelope := envelope_570_i2
  height := height_570_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_570_i2
def height_570_i1 : ℕ := 8
def childrenH_570_i1 : Fin 2 → ℕ := ![height_1, height_570_i2]
theorem height_exact_570_i1 : height_570_i1 = 1 + Finset.univ.sup childrenH_570_i1 := by decide +kernel
theorem required_origin_570_i1 : ∀ x ∈ required_570_i1,
    (∃ j, x ∈ childrenC_570_i1 j) ∨ ∀ j, x ∈ childrenD_570_i1 j := by decide +kernel
theorem required_exact_570_i1 : required_570_i1 =
    ((Finset.univ.biUnion childrenC_570_i1) ∪ commonEnvelope childrenD_570_i1).erase (2, 3) := by
  exact required_eq_combination childrenC_570_i1 childrenD_570_i1 (2, 3) required_570_i1
    (by decide +kernel) child_required_sub_570_i1 common_sub_570_i1 required_origin_570_i1
theorem envelope_origin_570_i1 : ∀ x ∈ envelope_570_i1,
    x = (2, 3) ∨ ∃ j, x ∈ childrenD_570_i1 j := by decide +kernel
theorem envelope_exact_570_i1 : envelope_570_i1 =
    insert (2, 3) (Finset.univ.biUnion childrenD_570_i1) := by
  exact envelope_eq_combination childrenD_570_i1 (2, 3) envelope_570_i1
    pivot_mem_570_i1 child_envelope_sub_570_i1 envelope_origin_570_i1
def checked_570_i1 : CheckedCard where
  required := required_570_i1
  envelope := envelope_570_i1
  height := height_570_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_570_i1
def height_570 : ℕ := 9
def childrenH_570 : Fin 4 → ℕ := ![height_150, height_283, height_570_i0, height_570_i1]
theorem height_exact_570 : height_570 = 1 + Finset.univ.sup childrenH_570 := by decide +kernel
theorem required_origin_570 : ∀ x ∈ required_570,
    (∃ j, x ∈ childrenC_570 j) ∨ ∀ j, x ∈ childrenD_570 j := by decide +kernel
theorem required_exact_570 : required_570 =
    ((Finset.univ.biUnion childrenC_570) ∪ commonEnvelope childrenD_570).erase (4, 3) := by
  exact required_eq_combination childrenC_570 childrenD_570 (4, 3) required_570
    (by decide +kernel) child_required_sub_570 common_sub_570 required_origin_570
theorem envelope_origin_570 : ∀ x ∈ envelope_570,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_570 j := by decide +kernel
theorem envelope_exact_570 : envelope_570 =
    insert (4, 3) (Finset.univ.biUnion childrenD_570) := by
  exact envelope_eq_combination childrenD_570 (4, 3) envelope_570
    pivot_mem_570 child_envelope_sub_570 envelope_origin_570
def checked_570 : CheckedCard where
  required := required_570
  envelope := envelope_570
  height := height_570
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_570
end SnakyPrototype.Certificate21

end OAI
