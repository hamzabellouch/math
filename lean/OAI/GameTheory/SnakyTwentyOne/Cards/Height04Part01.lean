import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_10 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 2), (1, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_10 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 4), (0, 5), (0, 6), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 4), (2, 5), (2, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_10 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) required_5), (placed21 1 (0, 1) required_8)]
def childrenD_10 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) envelope_5), (placed21 1 (0, 1) envelope_8)]
theorem common_sub_10 : commonEnvelope childrenD_10 ⊆ insert (1, 4) required_10 := by decide +kernel
theorem child_required_sub_10 : ∀ j, childrenC_10 j ⊆ insert (1, 4) required_10 := by decide +kernel
theorem child_envelope_sub_10 : ∀ j, childrenD_10 j ⊆ envelope_10 := by decide +kernel
theorem pivot_mem_10 : (1, 4) ∈ envelope_10 := by decide +kernel
theorem children_work_10 : ∀ j, Template HasSnaky 3 (childrenC_10 j) (childrenD_10 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 7 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_8 1 (0, 1)).mono (by decide +kernel)
theorem row_works_10 : Template HasSnaky 4 required_10 envelope_10 := by
  refine compose HasSnaky 3 childrenC_10 childrenD_10 children_work_10 (1, 4)
    required_10 envelope_10 pivot_mem_10 child_required_sub_10 child_envelope_sub_10 ?_
  intro b hb
  exact common_sub_10 (mem_commonEnvelope childrenD_10 b hb)
def required_12 : Finset Cell := ⟨(([(1, 2), (1, 3), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_12 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 4), (0, 5), (0, 6), (0, 7), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 4), (2, 5), (2, 6), (2, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_12 : Fin 3 → Finset Cell := ![(placed21 6 (1, 6) required_7), (placed21 1 (0, 2) required_8), (placed21 6 (2, 6) required_9)]
def childrenD_12 : Fin 3 → Finset Cell := ![(placed21 6 (1, 6) envelope_7), (placed21 1 (0, 2) envelope_8), (placed21 6 (2, 6) envelope_9)]
theorem common_sub_12 : commonEnvelope childrenD_12 ⊆ insert (1, 5) required_12 := by decide +kernel
theorem child_required_sub_12 : ∀ j, childrenC_12 j ⊆ insert (1, 5) required_12 := by decide +kernel
theorem child_envelope_sub_12 : ∀ j, childrenD_12 j ⊆ envelope_12 := by decide +kernel
theorem pivot_mem_12 : (1, 5) ∈ envelope_12 := by decide +kernel
theorem children_work_12 : ∀ j, Template HasSnaky 3 (childrenC_12 j) (childrenD_12 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 6 (1, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_8 1 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_9 6 (2, 6)).mono (by decide +kernel)
theorem row_works_12 : Template HasSnaky 4 required_12 envelope_12 := by
  refine compose HasSnaky 3 childrenC_12 childrenD_12 children_work_12 (1, 5)
    required_12 envelope_12 pivot_mem_12 child_required_sub_12 child_envelope_sub_12 ?_
  intro b hb
  exact common_sub_12 (mem_commonEnvelope childrenD_12 b hb)
def required_13 : Finset Cell := ⟨(([(1, 2), (1, 3), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_13 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (0, 5), (0, 6), (0, 7), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 4), (2, 5), (2, 6), (2, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_13 : Fin 3 → Finset Cell := ![(placed21 2 (1, 1) required_7), (placed21 1 (0, 2) required_8), (placed21 6 (2, 6) required_9)]
def childrenD_13 : Fin 3 → Finset Cell := ![(placed21 2 (1, 1) envelope_7), (placed21 1 (0, 2) envelope_8), (placed21 6 (2, 6) envelope_9)]
theorem common_sub_13 : commonEnvelope childrenD_13 ⊆ insert (1, 5) required_13 := by decide +kernel
theorem child_required_sub_13 : ∀ j, childrenC_13 j ⊆ insert (1, 5) required_13 := by decide +kernel
theorem child_envelope_sub_13 : ∀ j, childrenD_13 j ⊆ envelope_13 := by decide +kernel
theorem pivot_mem_13 : (1, 5) ∈ envelope_13 := by decide +kernel
theorem children_work_13 : ∀ j, Template HasSnaky 3 (childrenC_13 j) (childrenD_13 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 2 (1, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_8 1 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_9 6 (2, 6)).mono (by decide +kernel)
theorem row_works_13 : Template HasSnaky 4 required_13 envelope_13 := by
  refine compose HasSnaky 3 childrenC_13 childrenD_13 children_work_13 (1, 5)
    required_13 envelope_13 pivot_mem_13 child_required_sub_13 child_envelope_sub_13 ?_
  intro b hb
  exact common_sub_13 (mem_commonEnvelope childrenD_13 b hb)
def required_14 : Finset Cell := ⟨(([(1, 2), (1, 3), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_14 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 5), (2, 6), (2, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_14 : Fin 3 → Finset Cell := ![(placed21 6 (1, 6) required_7), (placed21 1 (0, 2) required_8), (placed21 0 (0, 1) required_9)]
def childrenD_14 : Fin 3 → Finset Cell := ![(placed21 6 (1, 6) envelope_7), (placed21 1 (0, 2) envelope_8), (placed21 0 (0, 1) envelope_9)]
theorem common_sub_14 : commonEnvelope childrenD_14 ⊆ insert (1, 5) required_14 := by decide +kernel
theorem child_required_sub_14 : ∀ j, childrenC_14 j ⊆ insert (1, 5) required_14 := by decide +kernel
theorem child_envelope_sub_14 : ∀ j, childrenD_14 j ⊆ envelope_14 := by decide +kernel
theorem pivot_mem_14 : (1, 5) ∈ envelope_14 := by decide +kernel
theorem children_work_14 : ∀ j, Template HasSnaky 3 (childrenC_14 j) (childrenD_14 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 6 (1, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_8 1 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_9 0 (0, 1)).mono (by decide +kernel)
theorem row_works_14 : Template HasSnaky 4 required_14 envelope_14 := by
  refine compose HasSnaky 3 childrenC_14 childrenD_14 children_work_14 (1, 5)
    required_14 envelope_14 pivot_mem_14 child_required_sub_14 child_envelope_sub_14 ?_
  intro b hb
  exact common_sub_14 (mem_commonEnvelope childrenD_14 b hb)
def required_17 : Finset Cell := ⟨(([(0, 1), (1, 0), (1, 1), (1, 2), (1, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_17 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 4), (0, 5), (0, 6), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_17 : Fin 2 → Finset Cell := ![(placed21 0 (1, 0) required_6), (placed21 2 (1, 1) required_16)]
def childrenD_17 : Fin 2 → Finset Cell := ![(placed21 0 (1, 0) envelope_6), (placed21 2 (1, 1) envelope_16)]
theorem common_sub_17 : commonEnvelope childrenD_17 ⊆ insert (1, 4) required_17 := by decide +kernel
theorem child_required_sub_17 : ∀ j, childrenC_17 j ⊆ insert (1, 4) required_17 := by decide +kernel
theorem child_envelope_sub_17 : ∀ j, childrenD_17 j ⊆ envelope_17 := by decide +kernel
theorem pivot_mem_17 : (1, 4) ∈ envelope_17 := by decide +kernel
theorem children_work_17 : ∀ j, Template HasSnaky 3 (childrenC_17 j) (childrenD_17 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_6 0 (1, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_16 2 (1, 1)).mono (by decide +kernel)
theorem row_works_17 : Template HasSnaky 4 required_17 envelope_17 := by
  refine compose HasSnaky 3 childrenC_17 childrenD_17 children_work_17 (1, 4)
    required_17 envelope_17 pivot_mem_17 child_required_sub_17 child_envelope_sub_17 ?_
  intro b hb
  exact common_sub_17 (mem_commonEnvelope childrenD_17 b hb)
def required_18 : Finset Cell := ⟨(([(0, 0), (1, 1), (1, 2), (1, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_18 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 4), (0, 5), (0, 6), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 4), (2, 5), (2, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_18 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) required_4), (placed21 1 (0, 1) required_8)]
def childrenD_18 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) envelope_4), (placed21 1 (0, 1) envelope_8)]
theorem common_sub_18 : commonEnvelope childrenD_18 ⊆ insert (1, 4) required_18 := by decide +kernel
theorem child_required_sub_18 : ∀ j, childrenC_18 j ⊆ insert (1, 4) required_18 := by decide +kernel
theorem child_envelope_sub_18 : ∀ j, childrenD_18 j ⊆ envelope_18 := by decide +kernel
theorem pivot_mem_18 : (1, 4) ∈ envelope_18 := by decide +kernel
theorem children_work_18 : ∀ j, Template HasSnaky 3 (childrenC_18 j) (childrenD_18 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_4 7 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_8 1 (0, 1)).mono (by decide +kernel)
theorem row_works_18 : Template HasSnaky 4 required_18 envelope_18 := by
  refine compose HasSnaky 3 childrenC_18 childrenD_18 children_work_18 (1, 4)
    required_18 envelope_18 pivot_mem_18 child_required_sub_18 child_envelope_sub_18 ?_
  intro b hb
  exact common_sub_18 (mem_commonEnvelope childrenD_18 b hb)
def required_26 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (3, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_26 : Finset Cell := ⟨(([(0, 0), (0, 1), (1, 0), (1, 1), (2, 0), (2, 1), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2), (5, 0), (5, 1), (5, 2), (6, 0)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_26 : Fin 2 → Finset Cell := ![(placed21 1 (0, 1) required_6), (placed21 3 (0, 1) required_7)]
def childrenD_26 : Fin 2 → Finset Cell := ![(placed21 1 (0, 1) envelope_6), (placed21 3 (0, 1) envelope_7)]
theorem common_sub_26 : commonEnvelope childrenD_26 ⊆ insert (4, 1) required_26 := by decide +kernel
theorem child_required_sub_26 : ∀ j, childrenC_26 j ⊆ insert (4, 1) required_26 := by decide +kernel
theorem child_envelope_sub_26 : ∀ j, childrenD_26 j ⊆ envelope_26 := by decide +kernel
theorem pivot_mem_26 : (4, 1) ∈ envelope_26 := by decide +kernel
theorem children_work_26 : ∀ j, Template HasSnaky 3 (childrenC_26 j) (childrenD_26 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_6 1 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_7 3 (0, 1)).mono (by decide +kernel)
theorem row_works_26 : Template HasSnaky 4 required_26 envelope_26 := by
  refine compose HasSnaky 3 childrenC_26 childrenD_26 children_work_26 (4, 1)
    required_26 envelope_26 pivot_mem_26 child_required_sub_26 child_envelope_sub_26 ?_
  intro b hb
  exact common_sub_26 (mem_commonEnvelope childrenD_26 b hb)
def required_27 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 3), (1, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_27 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 0), (1, 1), (1, 2), (1, 4), (1, 5), (1, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_27 : Fin 2 → Finset Cell := ![(placed21 3 (0, 4) required_5), (placed21 0 (0, 1) required_16)]
def childrenD_27 : Fin 2 → Finset Cell := ![(placed21 3 (0, 4) envelope_5), (placed21 0 (0, 1) envelope_16)]
theorem common_sub_27 : commonEnvelope childrenD_27 ⊆ insert (0, 4) required_27 := by decide +kernel
theorem child_required_sub_27 : ∀ j, childrenC_27 j ⊆ insert (0, 4) required_27 := by decide +kernel
theorem child_envelope_sub_27 : ∀ j, childrenD_27 j ⊆ envelope_27 := by decide +kernel
theorem pivot_mem_27 : (0, 4) ∈ envelope_27 := by decide +kernel
theorem children_work_27 : ∀ j, Template HasSnaky 3 (childrenC_27 j) (childrenD_27 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 3 (0, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_16 0 (0, 1)).mono (by decide +kernel)
theorem row_works_27 : Template HasSnaky 4 required_27 envelope_27 := by
  refine compose HasSnaky 3 childrenC_27 childrenD_27 children_work_27 (0, 4)
    required_27 envelope_27 pivot_mem_27 child_required_sub_27 child_envelope_sub_27 ?_
  intro b hb
  exact common_sub_27 (mem_commonEnvelope childrenD_27 b hb)
def required_31 : Finset Cell := ⟨(([(1, 2), (1, 3), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_31 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 5), (0, 6), (0, 7), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 0), (2, 1), (2, 2), (2, 5), (2, 6), (2, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_31 : Fin 2 → Finset Cell := ![(placed21 1 (0, 2) required_8), (placed21 3 (0, 5) required_8)]
def childrenD_31 : Fin 2 → Finset Cell := ![(placed21 1 (0, 2) envelope_8), (placed21 3 (0, 5) envelope_8)]
theorem common_sub_31 : commonEnvelope childrenD_31 ⊆ insert (1, 5) required_31 := by decide +kernel
theorem child_required_sub_31 : ∀ j, childrenC_31 j ⊆ insert (1, 5) required_31 := by decide +kernel
theorem child_envelope_sub_31 : ∀ j, childrenD_31 j ⊆ envelope_31 := by decide +kernel
theorem pivot_mem_31 : (1, 5) ∈ envelope_31 := by decide +kernel
theorem children_work_31 : ∀ j, Template HasSnaky 3 (childrenC_31 j) (childrenD_31 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_8 1 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_8 3 (0, 5)).mono (by decide +kernel)
theorem row_works_31 : Template HasSnaky 4 required_31 envelope_31 := by
  refine compose HasSnaky 3 childrenC_31 childrenD_31 children_work_31 (1, 5)
    required_31 envelope_31 pivot_mem_31 child_required_sub_31 child_envelope_sub_31 ?_
  intro b hb
  exact common_sub_31 (mem_commonEnvelope childrenD_31 b hb)
def required_33 : Finset Cell := ⟨(([(1, 2), (1, 3), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_33 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (0, 5), (0, 6), (0, 7), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 0), (2, 1), (2, 2), (2, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_33 : Fin 3 → Finset Cell := ![(placed21 2 (1, 1) required_7), (placed21 3 (0, 5) required_8), (placed21 2 (2, 1) required_9)]
def childrenD_33 : Fin 3 → Finset Cell := ![(placed21 2 (1, 1) envelope_7), (placed21 3 (0, 5) envelope_8), (placed21 2 (2, 1) envelope_9)]
theorem common_sub_33 : commonEnvelope childrenD_33 ⊆ insert (1, 5) required_33 := by decide +kernel
theorem child_required_sub_33 : ∀ j, childrenC_33 j ⊆ insert (1, 5) required_33 := by decide +kernel
theorem child_envelope_sub_33 : ∀ j, childrenD_33 j ⊆ envelope_33 := by decide +kernel
theorem pivot_mem_33 : (1, 5) ∈ envelope_33 := by decide +kernel
theorem children_work_33 : ∀ j, Template HasSnaky 3 (childrenC_33 j) (childrenD_33 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_7 2 (1, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_8 3 (0, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_9 2 (2, 1)).mono (by decide +kernel)
theorem row_works_33 : Template HasSnaky 4 required_33 envelope_33 := by
  refine compose HasSnaky 3 childrenC_33 childrenD_33 children_work_33 (1, 5)
    required_33 envelope_33 pivot_mem_33 child_required_sub_33 child_envelope_sub_33 ?_
  intro b hb
  exact common_sub_33 (mem_commonEnvelope childrenD_33 b hb)
def required_39 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 2), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_39 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 4), (0, 5), (0, 6), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 4), (2, 5), (2, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_39 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) required_5), (placed21 1 (0, 1) required_8)]
def childrenD_39 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) envelope_5), (placed21 1 (0, 1) envelope_8)]
theorem common_sub_39 : commonEnvelope childrenD_39 ⊆ insert (1, 3) required_39 := by decide +kernel
theorem child_required_sub_39 : ∀ j, childrenC_39 j ⊆ insert (1, 3) required_39 := by decide +kernel
theorem child_envelope_sub_39 : ∀ j, childrenD_39 j ⊆ envelope_39 := by decide +kernel
theorem pivot_mem_39 : (1, 3) ∈ envelope_39 := by decide +kernel
theorem children_work_39 : ∀ j, Template HasSnaky 3 (childrenC_39 j) (childrenD_39 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 7 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_8 1 (0, 1)).mono (by decide +kernel)
theorem row_works_39 : Template HasSnaky 4 required_39 envelope_39 := by
  refine compose HasSnaky 3 childrenC_39 childrenD_39 children_work_39 (1, 3)
    required_39 envelope_39 pivot_mem_39 child_required_sub_39 child_envelope_sub_39 ?_
  intro b hb
  exact common_sub_39 (mem_commonEnvelope childrenD_39 b hb)
def required_41 : Finset Cell := ⟨(([(0, 1), (1, 0), (1, 1), (1, 2), (1, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_41 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 4), (2, 5), (2, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_41 : Fin 2 → Finset Cell := ![(placed21 2 (1, 0) required_6), (placed21 1 (0, 1) required_24)]
def childrenD_41 : Fin 2 → Finset Cell := ![(placed21 2 (1, 0) envelope_6), (placed21 1 (0, 1) envelope_24)]
theorem common_sub_41 : commonEnvelope childrenD_41 ⊆ insert (1, 4) required_41 := by decide +kernel
theorem child_required_sub_41 : ∀ j, childrenC_41 j ⊆ insert (1, 4) required_41 := by decide +kernel
theorem child_envelope_sub_41 : ∀ j, childrenD_41 j ⊆ envelope_41 := by decide +kernel
theorem pivot_mem_41 : (1, 4) ∈ envelope_41 := by decide +kernel
theorem children_work_41 : ∀ j, Template HasSnaky 3 (childrenC_41 j) (childrenD_41 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_6 2 (1, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_24 1 (0, 1)).mono (by decide +kernel)
theorem row_works_41 : Template HasSnaky 4 required_41 envelope_41 := by
  refine compose HasSnaky 3 childrenC_41 childrenD_41 children_work_41 (1, 4)
    required_41 envelope_41 pivot_mem_41 child_required_sub_41 child_envelope_sub_41 ?_
  intro b hb
  exact common_sub_41 (mem_commonEnvelope childrenD_41 b hb)
def required_42 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 2), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_42 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 4), (2, 5), (2, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_42 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) required_5), (placed21 1 (0, 1) required_24)]
def childrenD_42 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) envelope_5), (placed21 1 (0, 1) envelope_24)]
theorem common_sub_42 : commonEnvelope childrenD_42 ⊆ insert (1, 3) required_42 := by decide +kernel
theorem child_required_sub_42 : ∀ j, childrenC_42 j ⊆ insert (1, 3) required_42 := by decide +kernel
theorem child_envelope_sub_42 : ∀ j, childrenD_42 j ⊆ envelope_42 := by decide +kernel
theorem pivot_mem_42 : (1, 3) ∈ envelope_42 := by decide +kernel
theorem children_work_42 : ∀ j, Template HasSnaky 3 (childrenC_42 j) (childrenD_42 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 7 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_24 1 (0, 1)).mono (by decide +kernel)
theorem row_works_42 : Template HasSnaky 4 required_42 envelope_42 := by
  refine compose HasSnaky 3 childrenC_42 childrenD_42 children_work_42 (1, 3)
    required_42 envelope_42 pivot_mem_42 child_required_sub_42 child_envelope_sub_42 ?_
  intro b hb
  exact common_sub_42 (mem_commonEnvelope childrenD_42 b hb)
def required_46 : Finset Cell := ⟨(([(0, 2), (1, 2), (2, 1), (2, 2), (3, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_46 : Finset Cell := ⟨(([(0, 2), (1, 2), (2, 0), (2, 1), (2, 2), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 1), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_46 : Fin 2 → Finset Cell := ![(placed21 4 (0, 2) required_5), required_45]
def childrenD_46 : Fin 2 → Finset Cell := ![(placed21 4 (0, 2) envelope_5), envelope_45]
theorem common_sub_46 : commonEnvelope childrenD_46 ⊆ insert (3, 1) required_46 := by decide +kernel
theorem child_required_sub_46 : ∀ j, childrenC_46 j ⊆ insert (3, 1) required_46 := by decide +kernel
theorem child_envelope_sub_46 : ∀ j, childrenD_46 j ⊆ envelope_46 := by decide +kernel
theorem pivot_mem_46 : (3, 1) ∈ envelope_46 := by decide +kernel
theorem children_work_46 : ∀ j, Template HasSnaky 3 (childrenC_46 j) (childrenD_46 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 4 (0, 2)).mono (by decide +kernel)
  · exact row_works_45.mono (by decide +kernel)
theorem row_works_46 : Template HasSnaky 4 required_46 envelope_46 := by
  refine compose HasSnaky 3 childrenC_46 childrenD_46 children_work_46 (3, 1)
    required_46 envelope_46 pivot_mem_46 child_required_sub_46 child_envelope_sub_46 ?_
  intro b hb
  exact common_sub_46 (mem_commonEnvelope childrenD_46 b hb)
def required_48 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 2), (1, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_48 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 4), (2, 5), (2, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_48 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) required_5), (placed21 1 (0, 1) required_24)]
def childrenD_48 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) envelope_5), (placed21 1 (0, 1) envelope_24)]
theorem common_sub_48 : commonEnvelope childrenD_48 ⊆ insert (1, 4) required_48 := by decide +kernel
theorem child_required_sub_48 : ∀ j, childrenC_48 j ⊆ insert (1, 4) required_48 := by decide +kernel
theorem child_envelope_sub_48 : ∀ j, childrenD_48 j ⊆ envelope_48 := by decide +kernel
theorem pivot_mem_48 : (1, 4) ∈ envelope_48 := by decide +kernel
theorem children_work_48 : ∀ j, Template HasSnaky 3 (childrenC_48 j) (childrenD_48 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 7 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_24 1 (0, 1)).mono (by decide +kernel)
theorem row_works_48 : Template HasSnaky 4 required_48 envelope_48 := by
  refine compose HasSnaky 3 childrenC_48 childrenD_48 children_work_48 (1, 4)
    required_48 envelope_48 pivot_mem_48 child_required_sub_48 child_envelope_sub_48 ?_
  intro b hb
  exact common_sub_48 (mem_commonEnvelope childrenD_48 b hb)
def required_49 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (3, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_49 : Finset Cell := ⟨(([(0, 0), (0, 1), (1, 0), (1, 1), (2, 0), (2, 1), (3, 0), (3, 1), (4, 0), (4, 1), (4, 2), (5, 0), (5, 1), (5, 2), (6, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_49 : Fin 2 → Finset Cell := ![(placed21 3 (0, 1) required_6), (placed21 1 (0, 0) required_9)]
def childrenD_49 : Fin 2 → Finset Cell := ![(placed21 3 (0, 1) envelope_6), (placed21 1 (0, 0) envelope_9)]
theorem common_sub_49 : commonEnvelope childrenD_49 ⊆ insert (4, 1) required_49 := by decide +kernel
theorem child_required_sub_49 : ∀ j, childrenC_49 j ⊆ insert (4, 1) required_49 := by decide +kernel
theorem child_envelope_sub_49 : ∀ j, childrenD_49 j ⊆ envelope_49 := by decide +kernel
theorem pivot_mem_49 : (4, 1) ∈ envelope_49 := by decide +kernel
theorem children_work_49 : ∀ j, Template HasSnaky 3 (childrenC_49 j) (childrenD_49 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_6 3 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_9 1 (0, 0)).mono (by decide +kernel)
theorem row_works_49 : Template HasSnaky 4 required_49 envelope_49 := by
  refine compose HasSnaky 3 childrenC_49 childrenD_49 children_work_49 (4, 1)
    required_49 envelope_49 pivot_mem_49 child_required_sub_49 child_envelope_sub_49 ?_
  intro b hb
  exact common_sub_49 (mem_commonEnvelope childrenD_49 b hb)
def required_50 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 3), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_50 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 4), (0, 5), (0, 6), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 4), (2, 5), (2, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_50 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) required_5), (placed21 1 (0, 1) required_8)]
def childrenD_50 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) envelope_5), (placed21 1 (0, 1) envelope_8)]
theorem common_sub_50 : commonEnvelope childrenD_50 ⊆ insert (1, 2) required_50 := by decide +kernel
theorem child_required_sub_50 : ∀ j, childrenC_50 j ⊆ insert (1, 2) required_50 := by decide +kernel
theorem child_envelope_sub_50 : ∀ j, childrenD_50 j ⊆ envelope_50 := by decide +kernel
theorem pivot_mem_50 : (1, 2) ∈ envelope_50 := by decide +kernel
theorem children_work_50 : ∀ j, Template HasSnaky 3 (childrenC_50 j) (childrenD_50 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 7 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_8 1 (0, 1)).mono (by decide +kernel)
theorem row_works_50 : Template HasSnaky 4 required_50 envelope_50 := by
  refine compose HasSnaky 3 childrenC_50 childrenD_50 children_work_50 (1, 2)
    required_50 envelope_50 pivot_mem_50 child_required_sub_50 child_envelope_sub_50 ?_
  intro b hb
  exact common_sub_50 (mem_commonEnvelope childrenD_50 b hb)
def required_55 : Finset Cell := ⟨(([(0, 3), (1, 3), (2, 2), (2, 3), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_55 : Finset Cell := ⟨(([(0, 3), (1, 3), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, 3), (3, 4), (3, 5), (3, 6), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_55 : Fin 2 → Finset Cell := ![(placed21 0 (0, 3) required_5), (placed21 0 (2, 0) required_53)]
def childrenD_55 : Fin 2 → Finset Cell := ![(placed21 0 (0, 3) envelope_5), (placed21 0 (2, 0) envelope_53)]
theorem common_sub_55 : commonEnvelope childrenD_55 ⊆ insert (3, 4) required_55 := by decide +kernel
theorem child_required_sub_55 : ∀ j, childrenC_55 j ⊆ insert (3, 4) required_55 := by decide +kernel
theorem child_envelope_sub_55 : ∀ j, childrenD_55 j ⊆ envelope_55 := by decide +kernel
theorem pivot_mem_55 : (3, 4) ∈ envelope_55 := by decide +kernel
theorem children_work_55 : ∀ j, Template HasSnaky 3 (childrenC_55 j) (childrenD_55 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 0 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_53 0 (2, 0)).mono (by decide +kernel)
theorem row_works_55 : Template HasSnaky 4 required_55 envelope_55 := by
  refine compose HasSnaky 3 childrenC_55 childrenD_55 children_work_55 (3, 4)
    required_55 envelope_55 pivot_mem_55 child_required_sub_55 child_envelope_sub_55 ?_
  intro b hb
  exact common_sub_55 (mem_commonEnvelope childrenD_55 b hb)
def required_56 : Finset Cell := ⟨(([(0, 3), (1, 3), (2, 2), (2, 3), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_56 : Finset Cell := ⟨(([(0, 3), (1, 3), (2, 0), (2, 1), (2, 2), (2, 3), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_56 : Fin 2 → Finset Cell := ![(placed21 0 (0, 3) required_5), (placed21 6 (3, 6) required_53)]
def childrenD_56 : Fin 2 → Finset Cell := ![(placed21 0 (0, 3) envelope_5), (placed21 6 (3, 6) envelope_53)]
theorem common_sub_56 : commonEnvelope childrenD_56 ⊆ insert (3, 4) required_56 := by decide +kernel
theorem child_required_sub_56 : ∀ j, childrenC_56 j ⊆ insert (3, 4) required_56 := by decide +kernel
theorem child_envelope_sub_56 : ∀ j, childrenD_56 j ⊆ envelope_56 := by decide +kernel
theorem pivot_mem_56 : (3, 4) ∈ envelope_56 := by decide +kernel
theorem children_work_56 : ∀ j, Template HasSnaky 3 (childrenC_56 j) (childrenD_56 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 0 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_53 6 (3, 6)).mono (by decide +kernel)
theorem row_works_56 : Template HasSnaky 4 required_56 envelope_56 := by
  refine compose HasSnaky 3 childrenC_56 childrenD_56 children_work_56 (3, 4)
    required_56 envelope_56 pivot_mem_56 child_required_sub_56 child_envelope_sub_56 ?_
  intro b hb
  exact common_sub_56 (mem_commonEnvelope childrenD_56 b hb)
def required_57 : Finset Cell := ⟨(([(1, 3), (2, 2), (2, 3), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_57 : Finset Cell := ⟨(([(0, 3), (1, 3), (2, 0), (2, 1), (2, 2), (2, 3), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 3), (4, 4), (5, 4), (6, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_57 : Fin 2 → Finset Cell := ![(placed21 1 (0, 3) required_52), (placed21 6 (3, 6) required_53)]
def childrenD_57 : Fin 2 → Finset Cell := ![(placed21 1 (0, 3) envelope_52), (placed21 6 (3, 6) envelope_53)]
theorem common_sub_57 : commonEnvelope childrenD_57 ⊆ insert (3, 4) required_57 := by decide +kernel
theorem child_required_sub_57 : ∀ j, childrenC_57 j ⊆ insert (3, 4) required_57 := by decide +kernel
theorem child_envelope_sub_57 : ∀ j, childrenD_57 j ⊆ envelope_57 := by decide +kernel
theorem pivot_mem_57 : (3, 4) ∈ envelope_57 := by decide +kernel
theorem children_work_57 : ∀ j, Template HasSnaky 3 (childrenC_57 j) (childrenD_57 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_52 1 (0, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_53 6 (3, 6)).mono (by decide +kernel)
theorem row_works_57 : Template HasSnaky 4 required_57 envelope_57 := by
  refine compose HasSnaky 3 childrenC_57 childrenD_57 children_work_57 (3, 4)
    required_57 envelope_57 pivot_mem_57 child_required_sub_57 child_envelope_sub_57 ?_
  intro b hb
  exact common_sub_57 (mem_commonEnvelope childrenD_57 b hb)
def required_58 : Finset Cell := ⟨(([(0, 2), (1, 2), (3, 1), (3, 2), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_58 : Finset Cell := ⟨(([(0, 2), (1, 2), (2, 2), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 3), (4, 4), (4, 5), (4, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_58 : Fin 2 → Finset Cell := ![(placed21 0 (0, 2) required_2), (placed21 0 (3, 0) required_52)]
def childrenD_58 : Fin 2 → Finset Cell := ![(placed21 0 (0, 2) envelope_2), (placed21 0 (3, 0) envelope_52)]
theorem common_sub_58 : commonEnvelope childrenD_58 ⊆ insert (4, 3) required_58 := by decide +kernel
theorem child_required_sub_58 : ∀ j, childrenC_58 j ⊆ insert (4, 3) required_58 := by decide +kernel
theorem child_envelope_sub_58 : ∀ j, childrenD_58 j ⊆ envelope_58 := by decide +kernel
theorem pivot_mem_58 : (4, 3) ∈ envelope_58 := by decide +kernel
theorem children_work_58 : ∀ j, Template HasSnaky 3 (childrenC_58 j) (childrenD_58 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_2 0 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_52 0 (3, 0)).mono (by decide +kernel)
theorem row_works_58 : Template HasSnaky 4 required_58 envelope_58 := by
  refine compose HasSnaky 3 childrenC_58 childrenD_58 children_work_58 (4, 3)
    required_58 envelope_58 pivot_mem_58 child_required_sub_58 child_envelope_sub_58 ?_
  intro b hb
  exact common_sub_58 (mem_commonEnvelope childrenD_58 b hb)
def required_60 : Finset Cell := ⟨(([(1, 1), (1, 2), (1, 3), (2, 2), (3, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_60 : Finset Cell := ⟨(([(0, 3), (0, 4), (0, 5), (0, 6), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, 2), (3, 2), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_60 : Fin 2 → Finset Cell := ![(placed21 2 (4, 2) required_0), (placed21 2 (1, 0) required_52)]
def childrenD_60 : Fin 2 → Finset Cell := ![(placed21 2 (4, 2) envelope_0), (placed21 2 (1, 0) envelope_52)]
theorem common_sub_60 : commonEnvelope childrenD_60 ⊆ insert (0, 3) required_60 := by decide +kernel
theorem child_required_sub_60 : ∀ j, childrenC_60 j ⊆ insert (0, 3) required_60 := by decide +kernel
theorem child_envelope_sub_60 : ∀ j, childrenD_60 j ⊆ envelope_60 := by decide +kernel
theorem pivot_mem_60 : (0, 3) ∈ envelope_60 := by decide +kernel
theorem children_work_60 : ∀ j, Template HasSnaky 3 (childrenC_60 j) (childrenD_60 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 2 (4, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_52 2 (1, 0)).mono (by decide +kernel)
theorem row_works_60 : Template HasSnaky 4 required_60 envelope_60 := by
  refine compose HasSnaky 3 childrenC_60 childrenD_60 children_work_60 (0, 3)
    required_60 envelope_60 pivot_mem_60 child_required_sub_60 child_envelope_sub_60 ?_
  intro b hb
  exact common_sub_60 (mem_commonEnvelope childrenD_60 b hb)
def required_63 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 2), (1, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_63 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5), (2, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_63 : Fin 3 → Finset Cell := ![(placed21 2 (1, 1) required_16), (placed21 1 (0, 1) required_24), (placed21 4 (0, 5) required_62)]
def childrenD_63 : Fin 3 → Finset Cell := ![(placed21 2 (1, 1) envelope_16), (placed21 1 (0, 1) envelope_24), (placed21 4 (0, 5) envelope_62)]
theorem common_sub_63 : commonEnvelope childrenD_63 ⊆ insert (1, 4) required_63 := by decide +kernel
theorem child_required_sub_63 : ∀ j, childrenC_63 j ⊆ insert (1, 4) required_63 := by decide +kernel
theorem child_envelope_sub_63 : ∀ j, childrenD_63 j ⊆ envelope_63 := by decide +kernel
theorem pivot_mem_63 : (1, 4) ∈ envelope_63 := by decide +kernel
theorem children_work_63 : ∀ j, Template HasSnaky 3 (childrenC_63 j) (childrenD_63 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_16 2 (1, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_24 1 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_62 4 (0, 5)).mono (by decide +kernel)
theorem row_works_63 : Template HasSnaky 4 required_63 envelope_63 := by
  refine compose HasSnaky 3 childrenC_63 childrenD_63 children_work_63 (1, 4)
    required_63 envelope_63 pivot_mem_63 child_required_sub_63 child_envelope_sub_63 ?_
  intro b hb
  exact common_sub_63 (mem_commonEnvelope childrenD_63 b hb)
def required_65 : Finset Cell := ⟨(([(0, 3), (0, 4), (1, 2), (1, 3), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_65 : Finset Cell := ⟨(([(0, 3), (0, 4), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 0), (2, 1), (2, 2), (2, 5), (2, 6), (2, 7)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_65 : Fin 2 → Finset Cell := ![(placed21 0 (0, 2) required_20), (placed21 4 (0, 5) required_20)]
def childrenD_65 : Fin 2 → Finset Cell := ![(placed21 0 (0, 2) envelope_20), (placed21 4 (0, 5) envelope_20)]
theorem common_sub_65 : commonEnvelope childrenD_65 ⊆ insert (1, 5) required_65 := by decide +kernel
theorem child_required_sub_65 : ∀ j, childrenC_65 j ⊆ insert (1, 5) required_65 := by decide +kernel
theorem child_envelope_sub_65 : ∀ j, childrenD_65 j ⊆ envelope_65 := by decide +kernel
theorem pivot_mem_65 : (1, 5) ∈ envelope_65 := by decide +kernel
theorem children_work_65 : ∀ j, Template HasSnaky 3 (childrenC_65 j) (childrenD_65 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_20 0 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_20 4 (0, 5)).mono (by decide +kernel)
theorem row_works_65 : Template HasSnaky 4 required_65 envelope_65 := by
  refine compose HasSnaky 3 childrenC_65 childrenD_65 children_work_65 (1, 5)
    required_65 envelope_65 pivot_mem_65 child_required_sub_65 child_envelope_sub_65 ?_
  intro b hb
  exact common_sub_65 (mem_commonEnvelope childrenD_65 b hb)
def height_10 : ℕ := 4
def childrenH_10 : Fin 2 → ℕ := ![height_5, height_8]
theorem height_exact_10 : height_10 = 1 + Finset.univ.sup childrenH_10 := by decide +kernel
theorem required_origin_10 : ∀ x ∈ required_10,
    (∃ j, x ∈ childrenC_10 j) ∨ ∀ j, x ∈ childrenD_10 j := by decide +kernel
theorem required_exact_10 : required_10 =
    ((Finset.univ.biUnion childrenC_10) ∪ commonEnvelope childrenD_10).erase (1, 4) := by
  exact required_eq_combination childrenC_10 childrenD_10 (1, 4) required_10
    (by decide +kernel) child_required_sub_10 common_sub_10 required_origin_10
theorem envelope_origin_10 : ∀ x ∈ envelope_10,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_10 j := by decide +kernel
theorem envelope_exact_10 : envelope_10 =
    insert (1, 4) (Finset.univ.biUnion childrenD_10) := by
  exact envelope_eq_combination childrenD_10 (1, 4) envelope_10
    pivot_mem_10 child_envelope_sub_10 envelope_origin_10
def checked_10 : CheckedCard where
  required := required_10
  envelope := envelope_10
  height := height_10
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_10
def height_12 : ℕ := 4
def childrenH_12 : Fin 3 → ℕ := ![height_7, height_8, height_9]
theorem height_exact_12 : height_12 = 1 + Finset.univ.sup childrenH_12 := by decide +kernel
theorem required_origin_12 : ∀ x ∈ required_12,
    (∃ j, x ∈ childrenC_12 j) ∨ ∀ j, x ∈ childrenD_12 j := by decide +kernel
theorem required_exact_12 : required_12 =
    ((Finset.univ.biUnion childrenC_12) ∪ commonEnvelope childrenD_12).erase (1, 5) := by
  exact required_eq_combination childrenC_12 childrenD_12 (1, 5) required_12
    (by decide +kernel) child_required_sub_12 common_sub_12 required_origin_12
theorem envelope_origin_12 : ∀ x ∈ envelope_12,
    x = (1, 5) ∨ ∃ j, x ∈ childrenD_12 j := by decide +kernel
theorem envelope_exact_12 : envelope_12 =
    insert (1, 5) (Finset.univ.biUnion childrenD_12) := by
  exact envelope_eq_combination childrenD_12 (1, 5) envelope_12
    pivot_mem_12 child_envelope_sub_12 envelope_origin_12
def checked_12 : CheckedCard where
  required := required_12
  envelope := envelope_12
  height := height_12
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_12
def height_13 : ℕ := 4
def childrenH_13 : Fin 3 → ℕ := ![height_7, height_8, height_9]
theorem height_exact_13 : height_13 = 1 + Finset.univ.sup childrenH_13 := by decide +kernel
theorem required_origin_13 : ∀ x ∈ required_13,
    (∃ j, x ∈ childrenC_13 j) ∨ ∀ j, x ∈ childrenD_13 j := by decide +kernel
theorem required_exact_13 : required_13 =
    ((Finset.univ.biUnion childrenC_13) ∪ commonEnvelope childrenD_13).erase (1, 5) := by
  exact required_eq_combination childrenC_13 childrenD_13 (1, 5) required_13
    (by decide +kernel) child_required_sub_13 common_sub_13 required_origin_13
theorem envelope_origin_13 : ∀ x ∈ envelope_13,
    x = (1, 5) ∨ ∃ j, x ∈ childrenD_13 j := by decide +kernel
theorem envelope_exact_13 : envelope_13 =
    insert (1, 5) (Finset.univ.biUnion childrenD_13) := by
  exact envelope_eq_combination childrenD_13 (1, 5) envelope_13
    pivot_mem_13 child_envelope_sub_13 envelope_origin_13
def checked_13 : CheckedCard where
  required := required_13
  envelope := envelope_13
  height := height_13
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_13
def height_14 : ℕ := 4
def childrenH_14 : Fin 3 → ℕ := ![height_7, height_8, height_9]
theorem height_exact_14 : height_14 = 1 + Finset.univ.sup childrenH_14 := by decide +kernel
theorem required_origin_14 : ∀ x ∈ required_14,
    (∃ j, x ∈ childrenC_14 j) ∨ ∀ j, x ∈ childrenD_14 j := by decide +kernel
theorem required_exact_14 : required_14 =
    ((Finset.univ.biUnion childrenC_14) ∪ commonEnvelope childrenD_14).erase (1, 5) := by
  exact required_eq_combination childrenC_14 childrenD_14 (1, 5) required_14
    (by decide +kernel) child_required_sub_14 common_sub_14 required_origin_14
theorem envelope_origin_14 : ∀ x ∈ envelope_14,
    x = (1, 5) ∨ ∃ j, x ∈ childrenD_14 j := by decide +kernel
theorem envelope_exact_14 : envelope_14 =
    insert (1, 5) (Finset.univ.biUnion childrenD_14) := by
  exact envelope_eq_combination childrenD_14 (1, 5) envelope_14
    pivot_mem_14 child_envelope_sub_14 envelope_origin_14
def checked_14 : CheckedCard where
  required := required_14
  envelope := envelope_14
  height := height_14
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_14
def height_17 : ℕ := 4
def childrenH_17 : Fin 2 → ℕ := ![height_6, height_16]
theorem height_exact_17 : height_17 = 1 + Finset.univ.sup childrenH_17 := by decide +kernel
theorem required_origin_17 : ∀ x ∈ required_17,
    (∃ j, x ∈ childrenC_17 j) ∨ ∀ j, x ∈ childrenD_17 j := by decide +kernel
theorem required_exact_17 : required_17 =
    ((Finset.univ.biUnion childrenC_17) ∪ commonEnvelope childrenD_17).erase (1, 4) := by
  exact required_eq_combination childrenC_17 childrenD_17 (1, 4) required_17
    (by decide +kernel) child_required_sub_17 common_sub_17 required_origin_17
theorem envelope_origin_17 : ∀ x ∈ envelope_17,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_17 j := by decide +kernel
theorem envelope_exact_17 : envelope_17 =
    insert (1, 4) (Finset.univ.biUnion childrenD_17) := by
  exact envelope_eq_combination childrenD_17 (1, 4) envelope_17
    pivot_mem_17 child_envelope_sub_17 envelope_origin_17
def checked_17 : CheckedCard where
  required := required_17
  envelope := envelope_17
  height := height_17
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_17
def height_18 : ℕ := 4
def childrenH_18 : Fin 2 → ℕ := ![height_4, height_8]
theorem height_exact_18 : height_18 = 1 + Finset.univ.sup childrenH_18 := by decide +kernel
theorem required_origin_18 : ∀ x ∈ required_18,
    (∃ j, x ∈ childrenC_18 j) ∨ ∀ j, x ∈ childrenD_18 j := by decide +kernel
theorem required_exact_18 : required_18 =
    ((Finset.univ.biUnion childrenC_18) ∪ commonEnvelope childrenD_18).erase (1, 4) := by
  exact required_eq_combination childrenC_18 childrenD_18 (1, 4) required_18
    (by decide +kernel) child_required_sub_18 common_sub_18 required_origin_18
theorem envelope_origin_18 : ∀ x ∈ envelope_18,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_18 j := by decide +kernel
theorem envelope_exact_18 : envelope_18 =
    insert (1, 4) (Finset.univ.biUnion childrenD_18) := by
  exact envelope_eq_combination childrenD_18 (1, 4) envelope_18
    pivot_mem_18 child_envelope_sub_18 envelope_origin_18
def checked_18 : CheckedCard where
  required := required_18
  envelope := envelope_18
  height := height_18
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_18
def height_26 : ℕ := 4
def childrenH_26 : Fin 2 → ℕ := ![height_6, height_7]
theorem height_exact_26 : height_26 = 1 + Finset.univ.sup childrenH_26 := by decide +kernel
theorem required_origin_26 : ∀ x ∈ required_26,
    (∃ j, x ∈ childrenC_26 j) ∨ ∀ j, x ∈ childrenD_26 j := by decide +kernel
theorem required_exact_26 : required_26 =
    ((Finset.univ.biUnion childrenC_26) ∪ commonEnvelope childrenD_26).erase (4, 1) := by
  exact required_eq_combination childrenC_26 childrenD_26 (4, 1) required_26
    (by decide +kernel) child_required_sub_26 common_sub_26 required_origin_26
theorem envelope_origin_26 : ∀ x ∈ envelope_26,
    x = (4, 1) ∨ ∃ j, x ∈ childrenD_26 j := by decide +kernel
theorem envelope_exact_26 : envelope_26 =
    insert (4, 1) (Finset.univ.biUnion childrenD_26) := by
  exact envelope_eq_combination childrenD_26 (4, 1) envelope_26
    pivot_mem_26 child_envelope_sub_26 envelope_origin_26
def checked_26 : CheckedCard where
  required := required_26
  envelope := envelope_26
  height := height_26
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_26
def height_27 : ℕ := 4
def childrenH_27 : Fin 2 → ℕ := ![height_5, height_16]
theorem height_exact_27 : height_27 = 1 + Finset.univ.sup childrenH_27 := by decide +kernel
theorem required_origin_27 : ∀ x ∈ required_27,
    (∃ j, x ∈ childrenC_27 j) ∨ ∀ j, x ∈ childrenD_27 j := by decide +kernel
theorem required_exact_27 : required_27 =
    ((Finset.univ.biUnion childrenC_27) ∪ commonEnvelope childrenD_27).erase (0, 4) := by
  exact required_eq_combination childrenC_27 childrenD_27 (0, 4) required_27
    (by decide +kernel) child_required_sub_27 common_sub_27 required_origin_27
theorem envelope_origin_27 : ∀ x ∈ envelope_27,
    x = (0, 4) ∨ ∃ j, x ∈ childrenD_27 j := by decide +kernel
theorem envelope_exact_27 : envelope_27 =
    insert (0, 4) (Finset.univ.biUnion childrenD_27) := by
  exact envelope_eq_combination childrenD_27 (0, 4) envelope_27
    pivot_mem_27 child_envelope_sub_27 envelope_origin_27
def checked_27 : CheckedCard where
  required := required_27
  envelope := envelope_27
  height := height_27
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_27
def height_31 : ℕ := 4
def childrenH_31 : Fin 2 → ℕ := ![height_8, height_8]
theorem height_exact_31 : height_31 = 1 + Finset.univ.sup childrenH_31 := by decide +kernel
theorem required_origin_31 : ∀ x ∈ required_31,
    (∃ j, x ∈ childrenC_31 j) ∨ ∀ j, x ∈ childrenD_31 j := by decide +kernel
theorem required_exact_31 : required_31 =
    ((Finset.univ.biUnion childrenC_31) ∪ commonEnvelope childrenD_31).erase (1, 5) := by
  exact required_eq_combination childrenC_31 childrenD_31 (1, 5) required_31
    (by decide +kernel) child_required_sub_31 common_sub_31 required_origin_31
theorem envelope_origin_31 : ∀ x ∈ envelope_31,
    x = (1, 5) ∨ ∃ j, x ∈ childrenD_31 j := by decide +kernel
theorem envelope_exact_31 : envelope_31 =
    insert (1, 5) (Finset.univ.biUnion childrenD_31) := by
  exact envelope_eq_combination childrenD_31 (1, 5) envelope_31
    pivot_mem_31 child_envelope_sub_31 envelope_origin_31
def checked_31 : CheckedCard where
  required := required_31
  envelope := envelope_31
  height := height_31
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_31
def height_33 : ℕ := 4
def childrenH_33 : Fin 3 → ℕ := ![height_7, height_8, height_9]
theorem height_exact_33 : height_33 = 1 + Finset.univ.sup childrenH_33 := by decide +kernel
theorem required_origin_33 : ∀ x ∈ required_33,
    (∃ j, x ∈ childrenC_33 j) ∨ ∀ j, x ∈ childrenD_33 j := by decide +kernel
theorem required_exact_33 : required_33 =
    ((Finset.univ.biUnion childrenC_33) ∪ commonEnvelope childrenD_33).erase (1, 5) := by
  exact required_eq_combination childrenC_33 childrenD_33 (1, 5) required_33
    (by decide +kernel) child_required_sub_33 common_sub_33 required_origin_33
theorem envelope_origin_33 : ∀ x ∈ envelope_33,
    x = (1, 5) ∨ ∃ j, x ∈ childrenD_33 j := by decide +kernel
theorem envelope_exact_33 : envelope_33 =
    insert (1, 5) (Finset.univ.biUnion childrenD_33) := by
  exact envelope_eq_combination childrenD_33 (1, 5) envelope_33
    pivot_mem_33 child_envelope_sub_33 envelope_origin_33
def checked_33 : CheckedCard where
  required := required_33
  envelope := envelope_33
  height := height_33
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_33
def height_39 : ℕ := 4
def childrenH_39 : Fin 2 → ℕ := ![height_5, height_8]
theorem height_exact_39 : height_39 = 1 + Finset.univ.sup childrenH_39 := by decide +kernel
theorem required_origin_39 : ∀ x ∈ required_39,
    (∃ j, x ∈ childrenC_39 j) ∨ ∀ j, x ∈ childrenD_39 j := by decide +kernel
theorem required_exact_39 : required_39 =
    ((Finset.univ.biUnion childrenC_39) ∪ commonEnvelope childrenD_39).erase (1, 3) := by
  exact required_eq_combination childrenC_39 childrenD_39 (1, 3) required_39
    (by decide +kernel) child_required_sub_39 common_sub_39 required_origin_39
theorem envelope_origin_39 : ∀ x ∈ envelope_39,
    x = (1, 3) ∨ ∃ j, x ∈ childrenD_39 j := by decide +kernel
theorem envelope_exact_39 : envelope_39 =
    insert (1, 3) (Finset.univ.biUnion childrenD_39) := by
  exact envelope_eq_combination childrenD_39 (1, 3) envelope_39
    pivot_mem_39 child_envelope_sub_39 envelope_origin_39
def checked_39 : CheckedCard where
  required := required_39
  envelope := envelope_39
  height := height_39
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_39
def height_41 : ℕ := 4
def childrenH_41 : Fin 2 → ℕ := ![height_6, height_24]
theorem height_exact_41 : height_41 = 1 + Finset.univ.sup childrenH_41 := by decide +kernel
theorem required_origin_41 : ∀ x ∈ required_41,
    (∃ j, x ∈ childrenC_41 j) ∨ ∀ j, x ∈ childrenD_41 j := by decide +kernel
theorem required_exact_41 : required_41 =
    ((Finset.univ.biUnion childrenC_41) ∪ commonEnvelope childrenD_41).erase (1, 4) := by
  exact required_eq_combination childrenC_41 childrenD_41 (1, 4) required_41
    (by decide +kernel) child_required_sub_41 common_sub_41 required_origin_41
theorem envelope_origin_41 : ∀ x ∈ envelope_41,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_41 j := by decide +kernel
theorem envelope_exact_41 : envelope_41 =
    insert (1, 4) (Finset.univ.biUnion childrenD_41) := by
  exact envelope_eq_combination childrenD_41 (1, 4) envelope_41
    pivot_mem_41 child_envelope_sub_41 envelope_origin_41
def checked_41 : CheckedCard where
  required := required_41
  envelope := envelope_41
  height := height_41
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_41
def height_42 : ℕ := 4
def childrenH_42 : Fin 2 → ℕ := ![height_5, height_24]
theorem height_exact_42 : height_42 = 1 + Finset.univ.sup childrenH_42 := by decide +kernel
theorem required_origin_42 : ∀ x ∈ required_42,
    (∃ j, x ∈ childrenC_42 j) ∨ ∀ j, x ∈ childrenD_42 j := by decide +kernel
theorem required_exact_42 : required_42 =
    ((Finset.univ.biUnion childrenC_42) ∪ commonEnvelope childrenD_42).erase (1, 3) := by
  exact required_eq_combination childrenC_42 childrenD_42 (1, 3) required_42
    (by decide +kernel) child_required_sub_42 common_sub_42 required_origin_42
theorem envelope_origin_42 : ∀ x ∈ envelope_42,
    x = (1, 3) ∨ ∃ j, x ∈ childrenD_42 j := by decide +kernel
theorem envelope_exact_42 : envelope_42 =
    insert (1, 3) (Finset.univ.biUnion childrenD_42) := by
  exact envelope_eq_combination childrenD_42 (1, 3) envelope_42
    pivot_mem_42 child_envelope_sub_42 envelope_origin_42
def checked_42 : CheckedCard where
  required := required_42
  envelope := envelope_42
  height := height_42
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_42
def height_46 : ℕ := 4
def childrenH_46 : Fin 2 → ℕ := ![height_5, height_45]
theorem height_exact_46 : height_46 = 1 + Finset.univ.sup childrenH_46 := by decide +kernel
theorem required_origin_46 : ∀ x ∈ required_46,
    (∃ j, x ∈ childrenC_46 j) ∨ ∀ j, x ∈ childrenD_46 j := by decide +kernel
theorem required_exact_46 : required_46 =
    ((Finset.univ.biUnion childrenC_46) ∪ commonEnvelope childrenD_46).erase (3, 1) := by
  exact required_eq_combination childrenC_46 childrenD_46 (3, 1) required_46
    (by decide +kernel) child_required_sub_46 common_sub_46 required_origin_46
theorem envelope_origin_46 : ∀ x ∈ envelope_46,
    x = (3, 1) ∨ ∃ j, x ∈ childrenD_46 j := by decide +kernel
theorem envelope_exact_46 : envelope_46 =
    insert (3, 1) (Finset.univ.biUnion childrenD_46) := by
  exact envelope_eq_combination childrenD_46 (3, 1) envelope_46
    pivot_mem_46 child_envelope_sub_46 envelope_origin_46
def checked_46 : CheckedCard where
  required := required_46
  envelope := envelope_46
  height := height_46
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_46
def height_48 : ℕ := 4
def childrenH_48 : Fin 2 → ℕ := ![height_5, height_24]
theorem height_exact_48 : height_48 = 1 + Finset.univ.sup childrenH_48 := by decide +kernel
theorem required_origin_48 : ∀ x ∈ required_48,
    (∃ j, x ∈ childrenC_48 j) ∨ ∀ j, x ∈ childrenD_48 j := by decide +kernel
theorem required_exact_48 : required_48 =
    ((Finset.univ.biUnion childrenC_48) ∪ commonEnvelope childrenD_48).erase (1, 4) := by
  exact required_eq_combination childrenC_48 childrenD_48 (1, 4) required_48
    (by decide +kernel) child_required_sub_48 common_sub_48 required_origin_48
theorem envelope_origin_48 : ∀ x ∈ envelope_48,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_48 j := by decide +kernel
theorem envelope_exact_48 : envelope_48 =
    insert (1, 4) (Finset.univ.biUnion childrenD_48) := by
  exact envelope_eq_combination childrenD_48 (1, 4) envelope_48
    pivot_mem_48 child_envelope_sub_48 envelope_origin_48
def checked_48 : CheckedCard where
  required := required_48
  envelope := envelope_48
  height := height_48
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_48
def height_49 : ℕ := 4
def childrenH_49 : Fin 2 → ℕ := ![height_6, height_9]
theorem height_exact_49 : height_49 = 1 + Finset.univ.sup childrenH_49 := by decide +kernel
theorem required_origin_49 : ∀ x ∈ required_49,
    (∃ j, x ∈ childrenC_49 j) ∨ ∀ j, x ∈ childrenD_49 j := by decide +kernel
theorem required_exact_49 : required_49 =
    ((Finset.univ.biUnion childrenC_49) ∪ commonEnvelope childrenD_49).erase (4, 1) := by
  exact required_eq_combination childrenC_49 childrenD_49 (4, 1) required_49
    (by decide +kernel) child_required_sub_49 common_sub_49 required_origin_49
theorem envelope_origin_49 : ∀ x ∈ envelope_49,
    x = (4, 1) ∨ ∃ j, x ∈ childrenD_49 j := by decide +kernel
theorem envelope_exact_49 : envelope_49 =
    insert (4, 1) (Finset.univ.biUnion childrenD_49) := by
  exact envelope_eq_combination childrenD_49 (4, 1) envelope_49
    pivot_mem_49 child_envelope_sub_49 envelope_origin_49
def checked_49 : CheckedCard where
  required := required_49
  envelope := envelope_49
  height := height_49
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_49
def height_50 : ℕ := 4
def childrenH_50 : Fin 2 → ℕ := ![height_5, height_8]
theorem height_exact_50 : height_50 = 1 + Finset.univ.sup childrenH_50 := by decide +kernel
theorem required_origin_50 : ∀ x ∈ required_50,
    (∃ j, x ∈ childrenC_50 j) ∨ ∀ j, x ∈ childrenD_50 j := by decide +kernel
theorem required_exact_50 : required_50 =
    ((Finset.univ.biUnion childrenC_50) ∪ commonEnvelope childrenD_50).erase (1, 2) := by
  exact required_eq_combination childrenC_50 childrenD_50 (1, 2) required_50
    (by decide +kernel) child_required_sub_50 common_sub_50 required_origin_50
theorem envelope_origin_50 : ∀ x ∈ envelope_50,
    x = (1, 2) ∨ ∃ j, x ∈ childrenD_50 j := by decide +kernel
theorem envelope_exact_50 : envelope_50 =
    insert (1, 2) (Finset.univ.biUnion childrenD_50) := by
  exact envelope_eq_combination childrenD_50 (1, 2) envelope_50
    pivot_mem_50 child_envelope_sub_50 envelope_origin_50
def checked_50 : CheckedCard where
  required := required_50
  envelope := envelope_50
  height := height_50
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_50
def height_55 : ℕ := 4
def childrenH_55 : Fin 2 → ℕ := ![height_5, height_53]
theorem height_exact_55 : height_55 = 1 + Finset.univ.sup childrenH_55 := by decide +kernel
theorem required_origin_55 : ∀ x ∈ required_55,
    (∃ j, x ∈ childrenC_55 j) ∨ ∀ j, x ∈ childrenD_55 j := by decide +kernel
theorem required_exact_55 : required_55 =
    ((Finset.univ.biUnion childrenC_55) ∪ commonEnvelope childrenD_55).erase (3, 4) := by
  exact required_eq_combination childrenC_55 childrenD_55 (3, 4) required_55
    (by decide +kernel) child_required_sub_55 common_sub_55 required_origin_55
theorem envelope_origin_55 : ∀ x ∈ envelope_55,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_55 j := by decide +kernel
theorem envelope_exact_55 : envelope_55 =
    insert (3, 4) (Finset.univ.biUnion childrenD_55) := by
  exact envelope_eq_combination childrenD_55 (3, 4) envelope_55
    pivot_mem_55 child_envelope_sub_55 envelope_origin_55
def checked_55 : CheckedCard where
  required := required_55
  envelope := envelope_55
  height := height_55
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_55
def height_56 : ℕ := 4
def childrenH_56 : Fin 2 → ℕ := ![height_5, height_53]
theorem height_exact_56 : height_56 = 1 + Finset.univ.sup childrenH_56 := by decide +kernel
theorem required_origin_56 : ∀ x ∈ required_56,
    (∃ j, x ∈ childrenC_56 j) ∨ ∀ j, x ∈ childrenD_56 j := by decide +kernel
theorem required_exact_56 : required_56 =
    ((Finset.univ.biUnion childrenC_56) ∪ commonEnvelope childrenD_56).erase (3, 4) := by
  exact required_eq_combination childrenC_56 childrenD_56 (3, 4) required_56
    (by decide +kernel) child_required_sub_56 common_sub_56 required_origin_56
theorem envelope_origin_56 : ∀ x ∈ envelope_56,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_56 j := by decide +kernel
theorem envelope_exact_56 : envelope_56 =
    insert (3, 4) (Finset.univ.biUnion childrenD_56) := by
  exact envelope_eq_combination childrenD_56 (3, 4) envelope_56
    pivot_mem_56 child_envelope_sub_56 envelope_origin_56
def checked_56 : CheckedCard where
  required := required_56
  envelope := envelope_56
  height := height_56
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_56
def height_57 : ℕ := 4
def childrenH_57 : Fin 2 → ℕ := ![height_52, height_53]
theorem height_exact_57 : height_57 = 1 + Finset.univ.sup childrenH_57 := by decide +kernel
theorem required_origin_57 : ∀ x ∈ required_57,
    (∃ j, x ∈ childrenC_57 j) ∨ ∀ j, x ∈ childrenD_57 j := by decide +kernel
theorem required_exact_57 : required_57 =
    ((Finset.univ.biUnion childrenC_57) ∪ commonEnvelope childrenD_57).erase (3, 4) := by
  exact required_eq_combination childrenC_57 childrenD_57 (3, 4) required_57
    (by decide +kernel) child_required_sub_57 common_sub_57 required_origin_57
theorem envelope_origin_57 : ∀ x ∈ envelope_57,
    x = (3, 4) ∨ ∃ j, x ∈ childrenD_57 j := by decide +kernel
theorem envelope_exact_57 : envelope_57 =
    insert (3, 4) (Finset.univ.biUnion childrenD_57) := by
  exact envelope_eq_combination childrenD_57 (3, 4) envelope_57
    pivot_mem_57 child_envelope_sub_57 envelope_origin_57
def checked_57 : CheckedCard where
  required := required_57
  envelope := envelope_57
  height := height_57
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_57
def height_58 : ℕ := 4
def childrenH_58 : Fin 2 → ℕ := ![height_2, height_52]
theorem height_exact_58 : height_58 = 1 + Finset.univ.sup childrenH_58 := by decide +kernel
theorem required_origin_58 : ∀ x ∈ required_58,
    (∃ j, x ∈ childrenC_58 j) ∨ ∀ j, x ∈ childrenD_58 j := by decide +kernel
theorem required_exact_58 : required_58 =
    ((Finset.univ.biUnion childrenC_58) ∪ commonEnvelope childrenD_58).erase (4, 3) := by
  exact required_eq_combination childrenC_58 childrenD_58 (4, 3) required_58
    (by decide +kernel) child_required_sub_58 common_sub_58 required_origin_58
theorem envelope_origin_58 : ∀ x ∈ envelope_58,
    x = (4, 3) ∨ ∃ j, x ∈ childrenD_58 j := by decide +kernel
theorem envelope_exact_58 : envelope_58 =
    insert (4, 3) (Finset.univ.biUnion childrenD_58) := by
  exact envelope_eq_combination childrenD_58 (4, 3) envelope_58
    pivot_mem_58 child_envelope_sub_58 envelope_origin_58
def checked_58 : CheckedCard where
  required := required_58
  envelope := envelope_58
  height := height_58
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_58
def height_60 : ℕ := 4
def childrenH_60 : Fin 2 → ℕ := ![height_0, height_52]
theorem height_exact_60 : height_60 = 1 + Finset.univ.sup childrenH_60 := by decide +kernel
theorem required_origin_60 : ∀ x ∈ required_60,
    (∃ j, x ∈ childrenC_60 j) ∨ ∀ j, x ∈ childrenD_60 j := by decide +kernel
theorem required_exact_60 : required_60 =
    ((Finset.univ.biUnion childrenC_60) ∪ commonEnvelope childrenD_60).erase (0, 3) := by
  exact required_eq_combination childrenC_60 childrenD_60 (0, 3) required_60
    (by decide +kernel) child_required_sub_60 common_sub_60 required_origin_60
theorem envelope_origin_60 : ∀ x ∈ envelope_60,
    x = (0, 3) ∨ ∃ j, x ∈ childrenD_60 j := by decide +kernel
theorem envelope_exact_60 : envelope_60 =
    insert (0, 3) (Finset.univ.biUnion childrenD_60) := by
  exact envelope_eq_combination childrenD_60 (0, 3) envelope_60
    pivot_mem_60 child_envelope_sub_60 envelope_origin_60
def checked_60 : CheckedCard where
  required := required_60
  envelope := envelope_60
  height := height_60
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_60
def height_63 : ℕ := 4
def childrenH_63 : Fin 3 → ℕ := ![height_16, height_24, height_62]
theorem height_exact_63 : height_63 = 1 + Finset.univ.sup childrenH_63 := by decide +kernel
theorem required_origin_63 : ∀ x ∈ required_63,
    (∃ j, x ∈ childrenC_63 j) ∨ ∀ j, x ∈ childrenD_63 j := by decide +kernel
theorem required_exact_63 : required_63 =
    ((Finset.univ.biUnion childrenC_63) ∪ commonEnvelope childrenD_63).erase (1, 4) := by
  exact required_eq_combination childrenC_63 childrenD_63 (1, 4) required_63
    (by decide +kernel) child_required_sub_63 common_sub_63 required_origin_63
theorem envelope_origin_63 : ∀ x ∈ envelope_63,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_63 j := by decide +kernel
theorem envelope_exact_63 : envelope_63 =
    insert (1, 4) (Finset.univ.biUnion childrenD_63) := by
  exact envelope_eq_combination childrenD_63 (1, 4) envelope_63
    pivot_mem_63 child_envelope_sub_63 envelope_origin_63
def checked_63 : CheckedCard where
  required := required_63
  envelope := envelope_63
  height := height_63
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_63
def height_65 : ℕ := 4
def childrenH_65 : Fin 2 → ℕ := ![height_20, height_20]
theorem height_exact_65 : height_65 = 1 + Finset.univ.sup childrenH_65 := by decide +kernel
theorem required_origin_65 : ∀ x ∈ required_65,
    (∃ j, x ∈ childrenC_65 j) ∨ ∀ j, x ∈ childrenD_65 j := by decide +kernel
theorem required_exact_65 : required_65 =
    ((Finset.univ.biUnion childrenC_65) ∪ commonEnvelope childrenD_65).erase (1, 5) := by
  exact required_eq_combination childrenC_65 childrenD_65 (1, 5) required_65
    (by decide +kernel) child_required_sub_65 common_sub_65 required_origin_65
theorem envelope_origin_65 : ∀ x ∈ envelope_65,
    x = (1, 5) ∨ ∃ j, x ∈ childrenD_65 j := by decide +kernel
theorem envelope_exact_65 : envelope_65 =
    insert (1, 5) (Finset.univ.biUnion childrenD_65) := by
  exact envelope_eq_combination childrenD_65 (1, 5) envelope_65
    pivot_mem_65 child_envelope_sub_65 envelope_origin_65
def checked_65 : CheckedCard where
  required := required_65
  envelope := envelope_65
  height := height_65
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_65
end SnakyPrototype.Certificate21

end OAI
