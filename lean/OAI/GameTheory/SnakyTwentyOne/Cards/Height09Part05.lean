import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part03
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part04
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part05
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part02
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part02
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_574_i1 : Finset Cell := ⟨(([(1, 2), (2, 2), (3, 2), (4, 3), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_574_i1 : Finset Cell := ⟨(([(1, 2), (2, 2), (2, 3), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 3), (4, 4), (4, 5), (4, 6), (5, 3), (6, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_574_i1 : Fin 2 → Finset Cell := ![(placed21 1 (1, 2) required_43), (placed21 6 (4, 6) required_64)]
def childrenD_574_i1 : Fin 2 → Finset Cell := ![(placed21 1 (1, 2) envelope_43), (placed21 6 (4, 6) envelope_64)]
theorem common_sub_574_i1 : commonEnvelope childrenD_574_i1 ⊆ insert (3, 3) required_574_i1 := by decide +kernel
theorem child_required_sub_574_i1 : ∀ j, childrenC_574_i1 j ⊆ insert (3, 3) required_574_i1 := by decide +kernel
theorem child_envelope_sub_574_i1 : ∀ j, childrenD_574_i1 j ⊆ envelope_574_i1 := by decide +kernel
theorem pivot_mem_574_i1 : (3, 3) ∈ envelope_574_i1 := by decide +kernel
theorem children_work_574_i1 : ∀ j, Template HasSnaky 3 (childrenC_574_i1 j) (childrenD_574_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_43 1 (1, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_64 6 (4, 6)).mono (by decide +kernel)
theorem row_works_574_i1 : Template HasSnaky 4 required_574_i1 envelope_574_i1 := by
  refine compose HasSnaky 3 childrenC_574_i1 childrenD_574_i1 children_work_574_i1 (3, 3)
    required_574_i1 envelope_574_i1 pivot_mem_574_i1 child_required_sub_574_i1 child_envelope_sub_574_i1 ?_
  intro b hb
  exact common_sub_574_i1 (mem_commonEnvelope childrenD_574_i1 b hb)
def required_574_i3 : Finset Cell := ⟨(([(1, 2), (2, 2), (3, 2), (4, 2), (4, 3), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_574_i3 : Finset Cell := ⟨(([(1, 2), (2, 2), (3, 1), (3, 2), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 1), (5, 4), (5, 5), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_574_i3 : Fin 2 → Finset Cell := ![(placed21 7 (4, 5) required_5), (placed21 0 (1, 1) required_223)]
def childrenD_574_i3 : Fin 2 → Finset Cell := ![(placed21 7 (4, 5) envelope_5), (placed21 0 (1, 1) envelope_223)]
theorem common_sub_574_i3 : commonEnvelope childrenD_574_i3 ⊆ insert (4, 4) required_574_i3 := by decide +kernel
theorem child_required_sub_574_i3 : ∀ j, childrenC_574_i3 j ⊆ insert (4, 4) required_574_i3 := by decide +kernel
theorem child_envelope_sub_574_i3 : ∀ j, childrenD_574_i3 j ⊆ envelope_574_i3 := by decide +kernel
theorem pivot_mem_574_i3 : (4, 4) ∈ envelope_574_i3 := by decide +kernel
theorem children_work_574_i3 : ∀ j, Template HasSnaky 3 (childrenC_574_i3 j) (childrenD_574_i3 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 7 (4, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_223 0 (1, 1)).mono (by decide +kernel)
theorem row_works_574_i3 : Template HasSnaky 4 required_574_i3 envelope_574_i3 := by
  refine compose HasSnaky 3 childrenC_574_i3 childrenD_574_i3 children_work_574_i3 (4, 4)
    required_574_i3 envelope_574_i3 pivot_mem_574_i3 child_required_sub_574_i3 child_envelope_sub_574_i3 ?_
  intro b hb
  exact common_sub_574_i3 (mem_commonEnvelope childrenD_574_i3 b hb)
def required_574_i2 : Finset Cell := ⟨(([(1, 2), (2, 2), (3, 2), (4, 3), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_574_i2 : Finset Cell := ⟨(([(1, 2), (2, 2), (3, 1), (3, 2), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 1), (5, 3), (5, 4), (5, 5), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_574_i2 : Fin 2 → Finset Cell := ![(placed21 0 (1, 2) required_5), required_574_i3]
def childrenD_574_i2 : Fin 2 → Finset Cell := ![(placed21 0 (1, 2) envelope_5), envelope_574_i3]
theorem common_sub_574_i2 : commonEnvelope childrenD_574_i2 ⊆ insert (4, 2) required_574_i2 := by decide +kernel
theorem child_required_sub_574_i2 : ∀ j, childrenC_574_i2 j ⊆ insert (4, 2) required_574_i2 := by decide +kernel
theorem child_envelope_sub_574_i2 : ∀ j, childrenD_574_i2 j ⊆ envelope_574_i2 := by decide +kernel
theorem pivot_mem_574_i2 : (4, 2) ∈ envelope_574_i2 := by decide +kernel
theorem children_work_574_i2 : ∀ j, Template HasSnaky 4 (childrenC_574_i2 j) (childrenD_574_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 0 (1, 2)).mono (by decide +kernel)
  · exact row_works_574_i3.mono (by decide +kernel)
theorem row_works_574_i2 : Template HasSnaky 5 required_574_i2 envelope_574_i2 := by
  refine compose HasSnaky 4 childrenC_574_i2 childrenD_574_i2 children_work_574_i2 (4, 2)
    required_574_i2 envelope_574_i2 pivot_mem_574_i2 child_required_sub_574_i2 child_envelope_sub_574_i2 ?_
  intro b hb
  exact common_sub_574_i2 (mem_commonEnvelope childrenD_574_i2 b hb)
def required_574_i5 : Finset Cell := ⟨(([(2, 2), (3, 2), (4, 3), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_574_i5 : Finset Cell := ⟨(([(1, 2), (2, 2), (3, 1), (3, 2), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 0), (5, 1), (5, 4), (5, 5), (5, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_574_i5 : Fin 2 → Finset Cell := ![(placed21 7 (4, 5) required_5), (placed21 6 (5, 6) required_236)]
def childrenD_574_i5 : Fin 2 → Finset Cell := ![(placed21 7 (4, 5) envelope_5), (placed21 6 (5, 6) envelope_236)]
theorem common_sub_574_i5 : commonEnvelope childrenD_574_i5 ⊆ insert (4, 2) required_574_i5 := by decide +kernel
theorem child_required_sub_574_i5 : ∀ j, childrenC_574_i5 j ⊆ insert (4, 2) required_574_i5 := by decide +kernel
theorem child_envelope_sub_574_i5 : ∀ j, childrenD_574_i5 j ⊆ envelope_574_i5 := by decide +kernel
theorem pivot_mem_574_i5 : (4, 2) ∈ envelope_574_i5 := by decide +kernel
theorem children_work_574_i5 : ∀ j, Template HasSnaky 3 (childrenC_574_i5 j) (childrenD_574_i5 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 7 (4, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_236 6 (5, 6)).mono (by decide +kernel)
theorem row_works_574_i5 : Template HasSnaky 4 required_574_i5 envelope_574_i5 := by
  refine compose HasSnaky 3 childrenC_574_i5 childrenD_574_i5 children_work_574_i5 (4, 2)
    required_574_i5 envelope_574_i5 pivot_mem_574_i5 child_required_sub_574_i5 child_envelope_sub_574_i5 ?_
  intro b hb
  exact common_sub_574_i5 (mem_commonEnvelope childrenD_574_i5 b hb)
def required_574_i4 : Finset Cell := ⟨(([(2, 2), (3, 2), (4, 3), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_574_i4 : Finset Cell := ⟨(([(1, 2), (2, 2), (3, 0), (3, 1), (3, 2), (3, 3), (3, 6), (3, 7), (3, 8), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 0), (5, 1), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_574_i4 : Fin 3 → Finset Cell := ![(placed21 0 (3, 2) required_18), (placed21 6 (4, 6) required_61), required_574_i5]
def childrenD_574_i4 : Fin 3 → Finset Cell := ![(placed21 0 (3, 2) envelope_18), (placed21 6 (4, 6) envelope_61), envelope_574_i5]
theorem common_sub_574_i4 : commonEnvelope childrenD_574_i4 ⊆ insert (4, 4) required_574_i4 := by decide +kernel
theorem child_required_sub_574_i4 : ∀ j, childrenC_574_i4 j ⊆ insert (4, 4) required_574_i4 := by decide +kernel
theorem child_envelope_sub_574_i4 : ∀ j, childrenD_574_i4 j ⊆ envelope_574_i4 := by decide +kernel
theorem pivot_mem_574_i4 : (4, 4) ∈ envelope_574_i4 := by decide +kernel
theorem children_work_574_i4 : ∀ j, Template HasSnaky 4 (childrenC_574_i4 j) (childrenD_574_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_18 0 (3, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_61 6 (4, 6)).mono (by decide +kernel)
  · exact row_works_574_i5.mono (by decide +kernel)
theorem row_works_574_i4 : Template HasSnaky 5 required_574_i4 envelope_574_i4 := by
  refine compose HasSnaky 4 childrenC_574_i4 childrenD_574_i4 children_work_574_i4 (4, 4)
    required_574_i4 envelope_574_i4 pivot_mem_574_i4 child_required_sub_574_i4 child_envelope_sub_574_i4 ?_
  intro b hb
  exact common_sub_574_i4 (mem_commonEnvelope childrenD_574_i4 b hb)
def required_574_i0 : Finset Cell := ⟨(([(1, 2), (2, 2), (4, 3), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_574_i0 : Finset Cell := ⟨(([(1, 2), (2, 2), (2, 3), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 6), (3, 7), (3, 8), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 0), (5, 1), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_574_i0 : Fin 4 → Finset Cell := ![(placed21 1 (1, 2) required_130), required_574_i1, required_574_i2, required_574_i4]
def childrenD_574_i0 : Fin 4 → Finset Cell := ![(placed21 1 (1, 2) envelope_130), envelope_574_i1, envelope_574_i2, envelope_574_i4]
theorem common_sub_574_i0 : commonEnvelope childrenD_574_i0 ⊆ insert (3, 2) required_574_i0 := by decide +kernel
theorem child_required_sub_574_i0 : ∀ j, childrenC_574_i0 j ⊆ insert (3, 2) required_574_i0 := by decide +kernel
theorem child_envelope_sub_574_i0 : ∀ j, childrenD_574_i0 j ⊆ envelope_574_i0 := by decide +kernel
theorem pivot_mem_574_i0 : (3, 2) ∈ envelope_574_i0 := by decide +kernel
theorem children_work_574_i0 : ∀ j, Template HasSnaky 5 (childrenC_574_i0 j) (childrenD_574_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_130 1 (1, 2)).mono (by decide +kernel)
  · exact row_works_574_i1.mono (by decide +kernel)
  · exact row_works_574_i2.mono (by decide +kernel)
  · exact row_works_574_i4.mono (by decide +kernel)
theorem row_works_574_i0 : Template HasSnaky 6 required_574_i0 envelope_574_i0 := by
  refine compose HasSnaky 5 childrenC_574_i0 childrenD_574_i0 children_work_574_i0 (3, 2)
    required_574_i0 envelope_574_i0 pivot_mem_574_i0 child_required_sub_574_i0 child_envelope_sub_574_i0 ?_
  intro b hb
  exact common_sub_574_i0 (mem_commonEnvelope childrenD_574_i0 b hb)
def required_574 : Finset Cell := ⟨(([(1, 2), (1, 5), (2, 2), (2, 5), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_574 : Finset Cell := ⟨(([(0, 4), (0, 6), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 2), (2, 3), (2, 5), (2, 6), (2, 7), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 0), (5, 1), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 3), (6, 4), (6, 5), (6, 6), (7, 4), (7, 5), (7, 6), (8, 4), (8, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_574 : Fin 6 → Finset Cell := ![(placed21 2 (5, 2) required_184), (placed21 1 (0, 2) required_384), (placed21 1 (0, 2) required_385), (placed21 1 (0, 2) required_493), (placed21 1 (0, 2) required_494), required_574_i0]
def childrenD_574 : Fin 6 → Finset Cell := ![(placed21 2 (5, 2) envelope_184), (placed21 1 (0, 2) envelope_384), (placed21 1 (0, 2) envelope_385), (placed21 1 (0, 2) envelope_493), (placed21 1 (0, 2) envelope_494), envelope_574_i0]
theorem common_sub_574 : commonEnvelope childrenD_574 ⊆ insert (4, 5) required_574 := by decide +kernel
theorem child_required_sub_574 : ∀ j, childrenC_574 j ⊆ insert (4, 5) required_574 := by decide +kernel
theorem child_envelope_sub_574 : ∀ j, childrenD_574 j ⊆ envelope_574 := by decide +kernel
theorem pivot_mem_574 : (4, 5) ∈ envelope_574 := by decide +kernel
theorem children_work_574 : ∀ j, Template HasSnaky 8 (childrenC_574 j) (childrenD_574 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_184 2 (5, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_384 1 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_385 1 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_493 1 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_494 1 (0, 2)).mono (by decide +kernel)
  · exact row_works_574_i0.mono (by decide +kernel)
theorem row_works_574 : Template HasSnaky 9 required_574 envelope_574 := by
  refine compose HasSnaky 8 childrenC_574 childrenD_574 children_work_574 (4, 5)
    required_574 envelope_574 pivot_mem_574 child_required_sub_574 child_envelope_sub_574 ?_
  intro b hb
  exact common_sub_574 (mem_commonEnvelope childrenD_574 b hb)
def required_577_i1 : Finset Cell := ⟨(([(1, 2), (2, 2), (3, 2), (3, 3), (4, 2), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_577_i1 : Finset Cell := ⟨(([(0, 4), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 2), (4, 3), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_577_i1 : Fin 2 → Finset Cell := ![(placed21 0 (3, 0) required_15), (placed21 2 (4, 0) required_393)]
def childrenD_577_i1 : Fin 2 → Finset Cell := ![(placed21 0 (3, 0) envelope_15), (placed21 2 (4, 0) envelope_393)]
theorem common_sub_577_i1 : commonEnvelope childrenD_577_i1 ⊆ insert (3, 1) required_577_i1 := by decide +kernel
theorem child_required_sub_577_i1 : ∀ j, childrenC_577_i1 j ⊆ insert (3, 1) required_577_i1 := by decide +kernel
theorem child_envelope_sub_577_i1 : ∀ j, childrenD_577_i1 j ⊆ envelope_577_i1 := by decide +kernel
theorem pivot_mem_577_i1 : (3, 1) ∈ envelope_577_i1 := by decide +kernel
theorem children_work_577_i1 : ∀ j, Template HasSnaky 6 (childrenC_577_i1 j) (childrenD_577_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_15 0 (3, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_393 2 (4, 0)).mono (by decide +kernel)
theorem row_works_577_i1 : Template HasSnaky 7 required_577_i1 envelope_577_i1 := by
  refine compose HasSnaky 6 childrenC_577_i1 childrenD_577_i1 children_work_577_i1 (3, 1)
    required_577_i1 envelope_577_i1 pivot_mem_577_i1 child_required_sub_577_i1 child_envelope_sub_577_i1 ?_
  intro b hb
  exact common_sub_577_i1 (mem_commonEnvelope childrenD_577_i1 b hb)
def required_577_i0 : Finset Cell := ⟨(([(1, 2), (2, 2), (3, 2), (4, 2), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_577_i0 : Finset Cell := ⟨(([(0, 2), (0, 4), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 2), (4, 3), (4, 4), (4, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_577_i0 : Fin 2 → Finset Cell := ![(placed21 0 (0, 2) required_0), required_577_i1]
def childrenD_577_i0 : Fin 2 → Finset Cell := ![(placed21 0 (0, 2) envelope_0), envelope_577_i1]
theorem common_sub_577_i0 : commonEnvelope childrenD_577_i0 ⊆ insert (3, 3) required_577_i0 := by decide +kernel
theorem child_required_sub_577_i0 : ∀ j, childrenC_577_i0 j ⊆ insert (3, 3) required_577_i0 := by decide +kernel
theorem child_envelope_sub_577_i0 : ∀ j, childrenD_577_i0 j ⊆ envelope_577_i0 := by decide +kernel
theorem pivot_mem_577_i0 : (3, 3) ∈ envelope_577_i0 := by decide +kernel
theorem children_work_577_i0 : ∀ j, Template HasSnaky 7 (childrenC_577_i0 j) (childrenD_577_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 0 (0, 2)).mono (by decide +kernel)
  · exact row_works_577_i1.mono (by decide +kernel)
theorem row_works_577_i0 : Template HasSnaky 8 required_577_i0 envelope_577_i0 := by
  refine compose HasSnaky 7 childrenC_577_i0 childrenD_577_i0 children_work_577_i0 (3, 3)
    required_577_i0 envelope_577_i0 pivot_mem_577_i0 child_required_sub_577_i0 child_envelope_sub_577_i0 ?_
  intro b hb
  exact common_sub_577_i0 (mem_commonEnvelope childrenD_577_i0 b hb)
def required_577 : Finset Cell := ⟨(([(1, 2), (2, 2), (3, 2), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_577 : Finset Cell := ⟨(([(0, 2), (0, 4), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 2), (4, 3), (4, 4), (4, 5), (5, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_577 : Fin 2 → Finset Cell := ![(placed21 0 (1, 2) required_5), required_577_i0]
def childrenD_577 : Fin 2 → Finset Cell := ![(placed21 0 (1, 2) envelope_5), envelope_577_i0]
theorem common_sub_577 : commonEnvelope childrenD_577 ⊆ insert (4, 3) required_577 := by decide +kernel
theorem child_required_sub_577 : ∀ j, childrenC_577 j ⊆ insert (4, 3) required_577 := by decide +kernel
theorem child_envelope_sub_577 : ∀ j, childrenD_577 j ⊆ envelope_577 := by decide +kernel
theorem pivot_mem_577 : (4, 3) ∈ envelope_577 := by decide +kernel
theorem children_work_577 : ∀ j, Template HasSnaky 8 (childrenC_577 j) (childrenD_577 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 0 (1, 2)).mono (by decide +kernel)
  · exact row_works_577_i0.mono (by decide +kernel)
theorem row_works_577 : Template HasSnaky 9 required_577 envelope_577 := by
  refine compose HasSnaky 8 childrenC_577 childrenD_577 children_work_577 (4, 3)
    required_577 envelope_577 pivot_mem_577 child_required_sub_577 child_envelope_sub_577 ?_
  intro b hb
  exact common_sub_577 (mem_commonEnvelope childrenD_577 b hb)
def required_584_i1 : Finset Cell := ⟨(([(0, 2), (1, 1), (2, 1), (3, 1), (3, 2), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_584_i1 : Finset Cell := ⟨(([(0, 2), (1, 1), (1, 2), (2, 1), (3, 1), (3, 2), (3, 3), (3, 4), (4, 0), (4, 1), (5, 0)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_584_i1 : Fin 2 → Finset Cell := ![(placed21 2 (4, 1) required_4), (placed21 0 (1, 0) required_121)]
def childrenD_584_i1 : Fin 2 → Finset Cell := ![(placed21 2 (4, 1) envelope_4), (placed21 0 (1, 0) envelope_121)]
theorem common_sub_584_i1 : commonEnvelope childrenD_584_i1 ⊆ insert (4, 1) required_584_i1 := by decide +kernel
theorem child_required_sub_584_i1 : ∀ j, childrenC_584_i1 j ⊆ insert (4, 1) required_584_i1 := by decide +kernel
theorem child_envelope_sub_584_i1 : ∀ j, childrenD_584_i1 j ⊆ envelope_584_i1 := by decide +kernel
theorem pivot_mem_584_i1 : (4, 1) ∈ envelope_584_i1 := by decide +kernel
theorem children_work_584_i1 : ∀ j, Template HasSnaky 2 (childrenC_584_i1 j) (childrenD_584_i1 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_4 2 (4, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_121 0 (1, 0)).mono (by decide +kernel)
theorem row_works_584_i1 : Template HasSnaky 3 required_584_i1 envelope_584_i1 := by
  refine compose HasSnaky 2 childrenC_584_i1 childrenD_584_i1 children_work_584_i1 (4, 1)
    required_584_i1 envelope_584_i1 pivot_mem_584_i1 child_required_sub_584_i1 child_envelope_sub_584_i1 ?_
  intro b hb
  exact common_sub_584_i1 (mem_commonEnvelope childrenD_584_i1 b hb)
def required_584_i2 : Finset Cell := ⟨(([(0, 2), (1, 1), (1, 4), (2, 1), (3, 1), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_584_i2 : Finset Cell := ⟨(([(0, 2), (0, 3), (1, 1), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1), (2, 3), (2, 4), (2, 5), (3, 1), (3, 4), (4, 1), (4, 3), (4, 4), (5, 3), (5, 4), (6, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_584_i2 : Fin 2 → Finset Cell := ![(placed21 2 (4, 1) required_0), required_203]
def childrenD_584_i2 : Fin 2 → Finset Cell := ![(placed21 2 (4, 1) envelope_0), envelope_203]
theorem common_sub_584_i2 : commonEnvelope childrenD_584_i2 ⊆ insert (1, 2) required_584_i2 := by decide +kernel
theorem child_required_sub_584_i2 : ∀ j, childrenC_584_i2 j ⊆ insert (1, 2) required_584_i2 := by decide +kernel
theorem child_envelope_sub_584_i2 : ∀ j, childrenD_584_i2 j ⊆ envelope_584_i2 := by decide +kernel
theorem pivot_mem_584_i2 : (1, 2) ∈ envelope_584_i2 := by decide +kernel
theorem children_work_584_i2 : ∀ j, Template HasSnaky 6 (childrenC_584_i2 j) (childrenD_584_i2 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 2 (4, 1)).mono (by decide +kernel)
  · exact row_works_203.mono (by decide +kernel)
theorem row_works_584_i2 : Template HasSnaky 7 required_584_i2 envelope_584_i2 := by
  refine compose HasSnaky 6 childrenC_584_i2 childrenD_584_i2 children_work_584_i2 (1, 2)
    required_584_i2 envelope_584_i2 pivot_mem_584_i2 child_required_sub_584_i2 child_envelope_sub_584_i2 ?_
  intro b hb
  exact common_sub_584_i2 (mem_commonEnvelope childrenD_584_i2 b hb)
def required_584_i0 : Finset Cell := ⟨(([(0, 2), (1, 1), (1, 4), (2, 1), (3, 1), (3, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_584_i0 : Finset Cell := ⟨(([(0, 2), (0, 3), (1, 1), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1), (2, 3), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 3), (4, 4), (4, 5), (4, 6), (5, 0), (5, 3), (5, 4), (6, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_584_i0 : Fin 3 → Finset Cell := ![(placed21 0 (2, 0) required_39), required_584_i1, required_584_i2]
def childrenD_584_i0 : Fin 3 → Finset Cell := ![(placed21 0 (2, 0) envelope_39), envelope_584_i1, envelope_584_i2]
theorem common_sub_584_i0 : commonEnvelope childrenD_584_i0 ⊆ insert (3, 4) required_584_i0 := by decide +kernel
theorem child_required_sub_584_i0 : ∀ j, childrenC_584_i0 j ⊆ insert (3, 4) required_584_i0 := by decide +kernel
theorem child_envelope_sub_584_i0 : ∀ j, childrenD_584_i0 j ⊆ envelope_584_i0 := by decide +kernel
theorem pivot_mem_584_i0 : (3, 4) ∈ envelope_584_i0 := by decide +kernel
theorem children_work_584_i0 : ∀ j, Template HasSnaky 7 (childrenC_584_i0 j) (childrenD_584_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_39 0 (2, 0)).mono (by decide +kernel)
  · exact row_works_584_i1.mono (by decide +kernel)
  · exact row_works_584_i2.mono (by decide +kernel)
theorem row_works_584_i0 : Template HasSnaky 8 required_584_i0 envelope_584_i0 := by
  refine compose HasSnaky 7 childrenC_584_i0 childrenD_584_i0 children_work_584_i0 (3, 4)
    required_584_i0 envelope_584_i0 pivot_mem_584_i0 child_required_sub_584_i0 child_envelope_sub_584_i0 ?_
  intro b hb
  exact common_sub_584_i0 (mem_commonEnvelope childrenD_584_i0 b hb)
def required_584 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 1), (1, 4), (3, 1), (3, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_584 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 3), (1, 1), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1), (2, 3), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 0), (5, 3), (5, 4), (6, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_584 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) required_5), required_584_i0]
def childrenD_584 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) envelope_5), envelope_584_i0]
theorem common_sub_584 : commonEnvelope childrenD_584 ⊆ insert (2, 1) required_584 := by decide +kernel
theorem child_required_sub_584 : ∀ j, childrenC_584 j ⊆ insert (2, 1) required_584 := by decide +kernel
theorem child_envelope_sub_584 : ∀ j, childrenD_584 j ⊆ envelope_584 := by decide +kernel
theorem pivot_mem_584 : (2, 1) ∈ envelope_584 := by decide +kernel
theorem children_work_584 : ∀ j, Template HasSnaky 8 (childrenC_584 j) (childrenD_584 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 0 (0, 1)).mono (by decide +kernel)
  · exact row_works_584_i0.mono (by decide +kernel)
theorem row_works_584 : Template HasSnaky 9 required_584 envelope_584 := by
  refine compose HasSnaky 8 childrenC_584 childrenD_584 children_work_584 (2, 1)
    required_584 envelope_584 pivot_mem_584 child_required_sub_584 child_envelope_sub_584 ?_
  intro b hb
  exact common_sub_584 (mem_commonEnvelope childrenD_584 b hb)
def height_574_i1 : ℕ := 4
def childrenH_574_i1 : Fin 2 → ℕ := ![height_43, height_64]
theorem height_exact_574_i1 : height_574_i1 = 1 + Finset.univ.sup childrenH_574_i1 := by decide +kernel
theorem required_origin_574_i1 : ∀ x ∈ required_574_i1,
    (∃ j, x ∈ childrenC_574_i1 j) ∨ ∀ j, x ∈ childrenD_574_i1 j := by decide +kernel
theorem required_exact_574_i1 : required_574_i1 =
    ((Finset.univ.biUnion childrenC_574_i1) ∪ commonEnvelope childrenD_574_i1).erase (3, 3) := by
  exact required_eq_combination childrenC_574_i1 childrenD_574_i1 (3, 3) required_574_i1
    (by decide +kernel) child_required_sub_574_i1 common_sub_574_i1 required_origin_574_i1
theorem envelope_origin_574_i1 : ∀ x ∈ envelope_574_i1,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_574_i1 j := by decide +kernel
theorem envelope_exact_574_i1 : envelope_574_i1 =
    insert (3, 3) (Finset.univ.biUnion childrenD_574_i1) := by
  exact envelope_eq_combination childrenD_574_i1 (3, 3) envelope_574_i1
    pivot_mem_574_i1 child_envelope_sub_574_i1 envelope_origin_574_i1
def checked_574_i1 : CheckedCard where
  required := required_574_i1
  envelope := envelope_574_i1
  height := height_574_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_574_i1
def height_574_i3 : ℕ := 4
def childrenH_574_i3 : Fin 2 → ℕ := ![height_5, height_223]
theorem height_exact_574_i3 : height_574_i3 = 1 + Finset.univ.sup childrenH_574_i3 := by decide +kernel
theorem required_origin_574_i3 : ∀ x ∈ required_574_i3,
    (∃ j, x ∈ childrenC_574_i3 j) ∨ ∀ j, x ∈ childrenD_574_i3 j := by decide +kernel
theorem required_exact_574_i3 : required_574_i3 =
    ((Finset.univ.biUnion childrenC_574_i3) ∪ commonEnvelope childrenD_574_i3).erase (4, 4) := by
  exact required_eq_combination childrenC_574_i3 childrenD_574_i3 (4, 4) required_574_i3
    (by decide +kernel) child_required_sub_574_i3 common_sub_574_i3 required_origin_574_i3
theorem envelope_origin_574_i3 : ∀ x ∈ envelope_574_i3,
    x = (4, 4) ∨ ∃ j, x ∈ childrenD_574_i3 j := by decide +kernel
theorem envelope_exact_574_i3 : envelope_574_i3 =
    insert (4, 4) (Finset.univ.biUnion childrenD_574_i3) := by
  exact envelope_eq_combination childrenD_574_i3 (4, 4) envelope_574_i3
    pivot_mem_574_i3 child_envelope_sub_574_i3 envelope_origin_574_i3
def checked_574_i3 : CheckedCard where
  required := required_574_i3
  envelope := envelope_574_i3
  height := height_574_i3
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_574_i3
def height_574_i2 : ℕ := 5
def childrenH_574_i2 : Fin 2 → ℕ := ![height_5, height_574_i3]
theorem height_exact_574_i2 : height_574_i2 = 1 + Finset.univ.sup childrenH_574_i2 := by decide +kernel
theorem required_origin_574_i2 : ∀ x ∈ required_574_i2,
    (∃ j, x ∈ childrenC_574_i2 j) ∨ ∀ j, x ∈ childrenD_574_i2 j := by decide +kernel
theorem required_exact_574_i2 : required_574_i2 =
    ((Finset.univ.biUnion childrenC_574_i2) ∪ commonEnvelope childrenD_574_i2).erase (4, 2) := by
  exact required_eq_combination childrenC_574_i2 childrenD_574_i2 (4, 2) required_574_i2
    (by decide +kernel) child_required_sub_574_i2 common_sub_574_i2 required_origin_574_i2
theorem envelope_origin_574_i2 : ∀ x ∈ envelope_574_i2,
    x = (4, 2) ∨ ∃ j, x ∈ childrenD_574_i2 j := by decide +kernel
theorem envelope_exact_574_i2 : envelope_574_i2 =
    insert (4, 2) (Finset.univ.biUnion childrenD_574_i2) := by
  exact envelope_eq_combination childrenD_574_i2 (4, 2) envelope_574_i2
    pivot_mem_574_i2 child_envelope_sub_574_i2 envelope_origin_574_i2
def checked_574_i2 : CheckedCard where
  required := required_574_i2
  envelope := envelope_574_i2
  height := height_574_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_574_i2
def height_574_i5 : ℕ := 4
def childrenH_574_i5 : Fin 2 → ℕ := ![height_5, height_236]
theorem height_exact_574_i5 : height_574_i5 = 1 + Finset.univ.sup childrenH_574_i5 := by decide +kernel
theorem required_origin_574_i5 : ∀ x ∈ required_574_i5,
    (∃ j, x ∈ childrenC_574_i5 j) ∨ ∀ j, x ∈ childrenD_574_i5 j := by decide +kernel
theorem required_exact_574_i5 : required_574_i5 =
    ((Finset.univ.biUnion childrenC_574_i5) ∪ commonEnvelope childrenD_574_i5).erase (4, 2) := by
  exact required_eq_combination childrenC_574_i5 childrenD_574_i5 (4, 2) required_574_i5
    (by decide +kernel) child_required_sub_574_i5 common_sub_574_i5 required_origin_574_i5
theorem envelope_origin_574_i5 : ∀ x ∈ envelope_574_i5,
    x = (4, 2) ∨ ∃ j, x ∈ childrenD_574_i5 j := by decide +kernel
theorem envelope_exact_574_i5 : envelope_574_i5 =
    insert (4, 2) (Finset.univ.biUnion childrenD_574_i5) := by
  exact envelope_eq_combination childrenD_574_i5 (4, 2) envelope_574_i5
    pivot_mem_574_i5 child_envelope_sub_574_i5 envelope_origin_574_i5
def checked_574_i5 : CheckedCard where
  required := required_574_i5
  envelope := envelope_574_i5
  height := height_574_i5
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_574_i5
def height_574_i4 : ℕ := 5
def childrenH_574_i4 : Fin 3 → ℕ := ![height_18, height_61, height_574_i5]
theorem height_exact_574_i4 : height_574_i4 = 1 + Finset.univ.sup childrenH_574_i4 := by decide +kernel
theorem required_origin_574_i4 : ∀ x ∈ required_574_i4,
    (∃ j, x ∈ childrenC_574_i4 j) ∨ ∀ j, x ∈ childrenD_574_i4 j := by decide +kernel
theorem required_exact_574_i4 : required_574_i4 =
    ((Finset.univ.biUnion childrenC_574_i4) ∪ commonEnvelope childrenD_574_i4).erase (4, 4) := by
  exact required_eq_combination childrenC_574_i4 childrenD_574_i4 (4, 4) required_574_i4
    (by decide +kernel) child_required_sub_574_i4 common_sub_574_i4 required_origin_574_i4
theorem envelope_origin_574_i4 : ∀ x ∈ envelope_574_i4,
    x = (4, 4) ∨ ∃ j, x ∈ childrenD_574_i4 j := by decide +kernel
theorem envelope_exact_574_i4 : envelope_574_i4 =
    insert (4, 4) (Finset.univ.biUnion childrenD_574_i4) := by
  exact envelope_eq_combination childrenD_574_i4 (4, 4) envelope_574_i4
    pivot_mem_574_i4 child_envelope_sub_574_i4 envelope_origin_574_i4
def checked_574_i4 : CheckedCard where
  required := required_574_i4
  envelope := envelope_574_i4
  height := height_574_i4
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_574_i4
def height_574_i0 : ℕ := 6
def childrenH_574_i0 : Fin 4 → ℕ := ![height_130, height_574_i1, height_574_i2, height_574_i4]
theorem height_exact_574_i0 : height_574_i0 = 1 + Finset.univ.sup childrenH_574_i0 := by decide +kernel
theorem required_origin_574_i0 : ∀ x ∈ required_574_i0,
    (∃ j, x ∈ childrenC_574_i0 j) ∨ ∀ j, x ∈ childrenD_574_i0 j := by decide +kernel
theorem required_exact_574_i0 : required_574_i0 =
    ((Finset.univ.biUnion childrenC_574_i0) ∪ commonEnvelope childrenD_574_i0).erase (3, 2) := by
  exact required_eq_combination childrenC_574_i0 childrenD_574_i0 (3, 2) required_574_i0
    (by decide +kernel) child_required_sub_574_i0 common_sub_574_i0 required_origin_574_i0
theorem envelope_origin_574_i0 : ∀ x ∈ envelope_574_i0,
    x = (3, 2) ∨ ∃ j, x ∈ childrenD_574_i0 j := by decide +kernel
theorem envelope_exact_574_i0 : envelope_574_i0 =
    insert (3, 2) (Finset.univ.biUnion childrenD_574_i0) := by
  exact envelope_eq_combination childrenD_574_i0 (3, 2) envelope_574_i0
    pivot_mem_574_i0 child_envelope_sub_574_i0 envelope_origin_574_i0
def checked_574_i0 : CheckedCard where
  required := required_574_i0
  envelope := envelope_574_i0
  height := height_574_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_574_i0
def height_574 : ℕ := 9
def childrenH_574 : Fin 6 → ℕ := ![height_184, height_384, height_385, height_493, height_494, height_574_i0]
theorem height_exact_574 : height_574 = 1 + Finset.univ.sup childrenH_574 := by decide +kernel
theorem required_origin_574 : ∀ x ∈ required_574,
    (∃ j, x ∈ childrenC_574 j) ∨ ∀ j, x ∈ childrenD_574 j := by decide +kernel
theorem required_exact_574 : required_574 =
    ((Finset.univ.biUnion childrenC_574) ∪ commonEnvelope childrenD_574).erase (4, 5) := by
  exact required_eq_combination childrenC_574 childrenD_574 (4, 5) required_574
    (by decide +kernel) child_required_sub_574 common_sub_574 required_origin_574
theorem envelope_origin_574 : ∀ x ∈ envelope_574,
    x = (4, 5) ∨ ∃ j, x ∈ childrenD_574 j := by decide +kernel
theorem envelope_exact_574 : envelope_574 =
    insert (4, 5) (Finset.univ.biUnion childrenD_574) := by
  exact envelope_eq_combination childrenD_574 (4, 5) envelope_574
    pivot_mem_574 child_envelope_sub_574 envelope_origin_574
def checked_574 : CheckedCard where
  required := required_574
  envelope := envelope_574
  height := height_574
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_574
def height_577_i1 : ℕ := 7
def childrenH_577_i1 : Fin 2 → ℕ := ![height_15, height_393]
theorem height_exact_577_i1 : height_577_i1 = 1 + Finset.univ.sup childrenH_577_i1 := by decide +kernel
theorem required_origin_577_i1 : ∀ x ∈ required_577_i1,
    (∃ j, x ∈ childrenC_577_i1 j) ∨ ∀ j, x ∈ childrenD_577_i1 j := by decide +kernel
theorem required_exact_577_i1 : required_577_i1 =
    ((Finset.univ.biUnion childrenC_577_i1) ∪ commonEnvelope childrenD_577_i1).erase (3, 1) := by
  exact required_eq_combination childrenC_577_i1 childrenD_577_i1 (3, 1) required_577_i1
    (by decide +kernel) child_required_sub_577_i1 common_sub_577_i1 required_origin_577_i1
theorem envelope_origin_577_i1 : ∀ x ∈ envelope_577_i1,
    x = (3, 1) ∨ ∃ j, x ∈ childrenD_577_i1 j := by decide +kernel
theorem envelope_exact_577_i1 : envelope_577_i1 =
    insert (3, 1) (Finset.univ.biUnion childrenD_577_i1) := by
  exact envelope_eq_combination childrenD_577_i1 (3, 1) envelope_577_i1
    pivot_mem_577_i1 child_envelope_sub_577_i1 envelope_origin_577_i1
def checked_577_i1 : CheckedCard where
  required := required_577_i1
  envelope := envelope_577_i1
  height := height_577_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_577_i1
def height_577_i0 : ℕ := 8
def childrenH_577_i0 : Fin 2 → ℕ := ![height_0, height_577_i1]
theorem height_exact_577_i0 : height_577_i0 = 1 + Finset.univ.sup childrenH_577_i0 := by decide +kernel
theorem required_origin_577_i0 : ∀ x ∈ required_577_i0,
    (∃ j, x ∈ childrenC_577_i0 j) ∨ ∀ j, x ∈ childrenD_577_i0 j := by decide +kernel
theorem required_exact_577_i0 : required_577_i0 =
    ((Finset.univ.biUnion childrenC_577_i0) ∪ commonEnvelope childrenD_577_i0).erase (3, 3) := by
  exact required_eq_combination childrenC_577_i0 childrenD_577_i0 (3, 3) required_577_i0
    (by decide +kernel) child_required_sub_577_i0 common_sub_577_i0 required_origin_577_i0
theorem envelope_origin_577_i0 : ∀ x ∈ envelope_577_i0,
    x = (3, 3) ∨ ∃ j, x ∈ childrenD_577_i0 j := by decide +kernel
theorem envelope_exact_577_i0 : envelope_577_i0 =
    insert (3, 3) (Finset.univ.biUnion childrenD_577_i0) := by
  exact envelope_eq_combination childrenD_577_i0 (3, 3) envelope_577_i0
    pivot_mem_577_i0 child_envelope_sub_577_i0 envelope_origin_577_i0
def checked_577_i0 : CheckedCard where
  required := required_577_i0
  envelope := envelope_577_i0
  height := height_577_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_577_i0
def height_577 : ℕ := 9
def childrenH_577 : Fin 2 → ℕ := ![height_5, height_577_i0]
theorem height_exact_577 : height_577 = 1 + Finset.univ.sup childrenH_577 := by decide +kernel
theorem required_origin_577 : ∀ x ∈ required_577,
    (∃ j, x ∈ childrenC_577 j) ∨ ∀ j, x ∈ childrenD_577 j := by decide +kernel
theorem required_exact_577 : required_577 =
    ((Finset.univ.biUnion childrenC_577) ∪ commonEnvelope childrenD_577).erase (4, 3) := by
  exact required_eq_combination childrenC_577 childrenD_577 (4, 3) required_577
    (by decide +kernel) child_required_sub_577 common_sub_577 required_origin_577
theorem envelope_origin_577 : ∀ x ∈ envelope_577,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_577 j := by decide +kernel
theorem envelope_exact_577 : envelope_577 =
    insert (4, 3) (Finset.univ.biUnion childrenD_577) := by
  exact envelope_eq_combination childrenD_577 (4, 3) envelope_577
    pivot_mem_577 child_envelope_sub_577 envelope_origin_577
def checked_577 : CheckedCard where
  required := required_577
  envelope := envelope_577
  height := height_577
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_577
def height_584_i1 : ℕ := 3
def childrenH_584_i1 : Fin 2 → ℕ := ![height_4, height_121]
theorem height_exact_584_i1 : height_584_i1 = 1 + Finset.univ.sup childrenH_584_i1 := by decide +kernel
theorem required_origin_584_i1 : ∀ x ∈ required_584_i1,
    (∃ j, x ∈ childrenC_584_i1 j) ∨ ∀ j, x ∈ childrenD_584_i1 j := by decide +kernel
theorem required_exact_584_i1 : required_584_i1 =
    ((Finset.univ.biUnion childrenC_584_i1) ∪ commonEnvelope childrenD_584_i1).erase (4, 1) := by
  exact required_eq_combination childrenC_584_i1 childrenD_584_i1 (4, 1) required_584_i1
    (by decide +kernel) child_required_sub_584_i1 common_sub_584_i1 required_origin_584_i1
theorem envelope_origin_584_i1 : ∀ x ∈ envelope_584_i1,
    x = (4, 1) ∨ ∃ j, x ∈ childrenD_584_i1 j := by decide +kernel
theorem envelope_exact_584_i1 : envelope_584_i1 =
    insert (4, 1) (Finset.univ.biUnion childrenD_584_i1) := by
  exact envelope_eq_combination childrenD_584_i1 (4, 1) envelope_584_i1
    pivot_mem_584_i1 child_envelope_sub_584_i1 envelope_origin_584_i1
def checked_584_i1 : CheckedCard where
  required := required_584_i1
  envelope := envelope_584_i1
  height := height_584_i1
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_584_i1
def height_584_i2 : ℕ := 7
def childrenH_584_i2 : Fin 2 → ℕ := ![height_0, height_203]
theorem height_exact_584_i2 : height_584_i2 = 1 + Finset.univ.sup childrenH_584_i2 := by decide +kernel
theorem required_origin_584_i2 : ∀ x ∈ required_584_i2,
    (∃ j, x ∈ childrenC_584_i2 j) ∨ ∀ j, x ∈ childrenD_584_i2 j := by decide +kernel
theorem required_exact_584_i2 : required_584_i2 =
    ((Finset.univ.biUnion childrenC_584_i2) ∪ commonEnvelope childrenD_584_i2).erase (1, 2) := by
  exact required_eq_combination childrenC_584_i2 childrenD_584_i2 (1, 2) required_584_i2
    (by decide +kernel) child_required_sub_584_i2 common_sub_584_i2 required_origin_584_i2
theorem envelope_origin_584_i2 : ∀ x ∈ envelope_584_i2,
    x = (1, 2) ∨ ∃ j, x ∈ childrenD_584_i2 j := by decide +kernel
theorem envelope_exact_584_i2 : envelope_584_i2 =
    insert (1, 2) (Finset.univ.biUnion childrenD_584_i2) := by
  exact envelope_eq_combination childrenD_584_i2 (1, 2) envelope_584_i2
    pivot_mem_584_i2 child_envelope_sub_584_i2 envelope_origin_584_i2
def checked_584_i2 : CheckedCard where
  required := required_584_i2
  envelope := envelope_584_i2
  height := height_584_i2
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_584_i2
def height_584_i0 : ℕ := 8
def childrenH_584_i0 : Fin 3 → ℕ := ![height_39, height_584_i1, height_584_i2]
theorem height_exact_584_i0 : height_584_i0 = 1 + Finset.univ.sup childrenH_584_i0 := by decide +kernel
theorem required_origin_584_i0 : ∀ x ∈ required_584_i0,
    (∃ j, x ∈ childrenC_584_i0 j) ∨ ∀ j, x ∈ childrenD_584_i0 j := by decide +kernel
theorem required_exact_584_i0 : required_584_i0 =
    ((Finset.univ.biUnion childrenC_584_i0) ∪ commonEnvelope childrenD_584_i0).erase (3, 4) := by
  exact required_eq_combination childrenC_584_i0 childrenD_584_i0 (3, 4) required_584_i0
    (by decide +kernel) child_required_sub_584_i0 common_sub_584_i0 required_origin_584_i0
theorem envelope_origin_584_i0 : ∀ x ∈ envelope_584_i0,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_584_i0 j := by decide +kernel
theorem envelope_exact_584_i0 : envelope_584_i0 =
    insert (3, 4) (Finset.univ.biUnion childrenD_584_i0) := by
  exact envelope_eq_combination childrenD_584_i0 (3, 4) envelope_584_i0
    pivot_mem_584_i0 child_envelope_sub_584_i0 envelope_origin_584_i0
def checked_584_i0 : CheckedCard where
  required := required_584_i0
  envelope := envelope_584_i0
  height := height_584_i0
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_584_i0
def height_584 : ℕ := 9
def childrenH_584 : Fin 2 → ℕ := ![height_5, height_584_i0]
theorem height_exact_584 : height_584 = 1 + Finset.univ.sup childrenH_584 := by decide +kernel
theorem required_origin_584 : ∀ x ∈ required_584,
    (∃ j, x ∈ childrenC_584 j) ∨ ∀ j, x ∈ childrenD_584 j := by decide +kernel
theorem required_exact_584 : required_584 =
    ((Finset.univ.biUnion childrenC_584) ∪ commonEnvelope childrenD_584).erase (2, 1) := by
  exact required_eq_combination childrenC_584 childrenD_584 (2, 1) required_584
    (by decide +kernel) child_required_sub_584 common_sub_584 required_origin_584
theorem envelope_origin_584 : ∀ x ∈ envelope_584,
    x = (2, 1) ∨ ∃ j, x ∈ childrenD_584 j := by decide +kernel
theorem envelope_exact_584 : envelope_584 =
    insert (2, 1) (Finset.univ.biUnion childrenD_584) := by
  exact envelope_eq_combination childrenD_584 (2, 1) envelope_584
    pivot_mem_584 child_envelope_sub_584 envelope_origin_584
def checked_584 : CheckedCard where
  required := required_584
  envelope := envelope_584
  height := height_584
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_584
end SnakyPrototype.Certificate21

end OAI
