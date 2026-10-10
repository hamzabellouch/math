import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_6 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (0, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_6 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 3), (1, 4), (1, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_6 : Fin 2 → Finset Cell := ![(placed21 1 (0, 0) required_4), (placed21 1 (0, 1) required_5)]
def childrenD_6 : Fin 2 → Finset Cell := ![(placed21 1 (0, 0) envelope_4), (placed21 1 (0, 1) envelope_5)]
theorem common_sub_6 : commonEnvelope childrenD_6 ⊆ insert (1, 4) required_6 := by decide +kernel
theorem child_required_sub_6 : ∀ j, childrenC_6 j ⊆ insert (1, 4) required_6 := by decide +kernel
theorem child_envelope_sub_6 : ∀ j, childrenD_6 j ⊆ envelope_6 := by decide +kernel
theorem pivot_mem_6 : (1, 4) ∈ envelope_6 := by decide +kernel
theorem children_work_6 : ∀ j, Template HasSnaky 1 (childrenC_6 j) (childrenD_6 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_4 1 (0, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_5 1 (0, 1)).mono (by decide +kernel)
theorem row_works_6 : Template HasSnaky 2 required_6 envelope_6 := by
  refine compose HasSnaky 1 childrenC_6 childrenD_6 children_work_6 (1, 4)
    required_6 envelope_6 pivot_mem_6 child_required_sub_6 child_envelope_sub_6 ?_
  intro b hb
  exact common_sub_6 (mem_commonEnvelope childrenD_6 b hb)
def required_11 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 3), (0, 4), (1, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_11 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 0), (1, 1), (1, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_11 : Fin 2 → Finset Cell := ![(placed21 3 (0, 5) required_0), (placed21 3 (0, 4) required_5)]
def childrenD_11 : Fin 2 → Finset Cell := ![(placed21 3 (0, 5) envelope_0), (placed21 3 (0, 4) envelope_5)]
theorem common_sub_11 : commonEnvelope childrenD_11 ⊆ insert (1, 1) required_11 := by decide +kernel
theorem child_required_sub_11 : ∀ j, childrenC_11 j ⊆ insert (1, 1) required_11 := by decide +kernel
theorem child_envelope_sub_11 : ∀ j, childrenD_11 j ⊆ envelope_11 := by decide +kernel
theorem pivot_mem_11 : (1, 1) ∈ envelope_11 := by decide +kernel
theorem children_work_11 : ∀ j, Template HasSnaky 1 (childrenC_11 j) (childrenD_11 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 3 (0, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_5 3 (0, 4)).mono (by decide +kernel)
theorem row_works_11 : Template HasSnaky 2 required_11 envelope_11 := by
  refine compose HasSnaky 1 childrenC_11 childrenD_11 children_work_11 (1, 1)
    required_11 envelope_11 pivot_mem_11 child_required_sub_11 child_envelope_sub_11 ?_
  intro b hb
  exact common_sub_11 (mem_commonEnvelope childrenD_11 b hb)
def required_15 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 3), (1, 2), (1, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_15 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (1, 4), (1, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_15 : Fin 2 → Finset Cell := ![(placed21 1 (0, 0) required_0), (placed21 7 (1, 5) required_0)]
def childrenD_15 : Fin 2 → Finset Cell := ![(placed21 1 (0, 0) envelope_0), (placed21 7 (1, 5) envelope_0)]
theorem common_sub_15 : commonEnvelope childrenD_15 ⊆ insert (1, 4) required_15 := by decide +kernel
theorem child_required_sub_15 : ∀ j, childrenC_15 j ⊆ insert (1, 4) required_15 := by decide +kernel
theorem child_envelope_sub_15 : ∀ j, childrenD_15 j ⊆ envelope_15 := by decide +kernel
theorem pivot_mem_15 : (1, 4) ∈ envelope_15 := by decide +kernel
theorem children_work_15 : ∀ j, Template HasSnaky 1 (childrenC_15 j) (childrenD_15 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 1 (0, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_0 7 (1, 5)).mono (by decide +kernel)
theorem row_works_15 : Template HasSnaky 2 required_15 envelope_15 := by
  refine compose HasSnaky 1 childrenC_15 childrenD_15 children_work_15 (1, 4)
    required_15 envelope_15 pivot_mem_15 child_required_sub_15 child_envelope_sub_15 ?_
  intro b hb
  exact common_sub_15 (mem_commonEnvelope childrenD_15 b hb)
def required_22 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 4), (1, 1), (1, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_22 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 0), (1, 1), (1, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_22 : Fin 2 → Finset Cell := ![(placed21 3 (0, 5) required_0), (placed21 3 (0, 4) required_5)]
def childrenD_22 : Fin 2 → Finset Cell := ![(placed21 3 (0, 5) envelope_0), (placed21 3 (0, 4) envelope_5)]
theorem common_sub_22 : commonEnvelope childrenD_22 ⊆ insert (0, 3) required_22 := by decide +kernel
theorem child_required_sub_22 : ∀ j, childrenC_22 j ⊆ insert (0, 3) required_22 := by decide +kernel
theorem child_envelope_sub_22 : ∀ j, childrenD_22 j ⊆ envelope_22 := by decide +kernel
theorem pivot_mem_22 : (0, 3) ∈ envelope_22 := by decide +kernel
theorem children_work_22 : ∀ j, Template HasSnaky 1 (childrenC_22 j) (childrenD_22 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 3 (0, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_5 3 (0, 4)).mono (by decide +kernel)
theorem row_works_22 : Template HasSnaky 2 required_22 envelope_22 := by
  refine compose HasSnaky 1 childrenC_22 childrenD_22 children_work_22 (0, 3)
    required_22 envelope_22 pivot_mem_22 child_required_sub_22 child_envelope_sub_22 ?_
  intro b hb
  exact common_sub_22 (mem_commonEnvelope childrenD_22 b hb)
def required_23 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 3), (1, 1), (1, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_23 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 0), (1, 1), (1, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_23 : Fin 2 → Finset Cell := ![(placed21 3 (0, 5) required_0), (placed21 3 (0, 4) required_5)]
def childrenD_23 : Fin 2 → Finset Cell := ![(placed21 3 (0, 5) envelope_0), (placed21 3 (0, 4) envelope_5)]
theorem common_sub_23 : commonEnvelope childrenD_23 ⊆ insert (0, 4) required_23 := by decide +kernel
theorem child_required_sub_23 : ∀ j, childrenC_23 j ⊆ insert (0, 4) required_23 := by decide +kernel
theorem child_envelope_sub_23 : ∀ j, childrenD_23 j ⊆ envelope_23 := by decide +kernel
theorem pivot_mem_23 : (0, 4) ∈ envelope_23 := by decide +kernel
theorem children_work_23 : ∀ j, Template HasSnaky 1 (childrenC_23 j) (childrenD_23 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 3 (0, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_5 3 (0, 4)).mono (by decide +kernel)
theorem row_works_23 : Template HasSnaky 2 required_23 envelope_23 := by
  refine compose HasSnaky 1 childrenC_23 childrenD_23 children_work_23 (0, 4)
    required_23 envelope_23 pivot_mem_23 child_required_sub_23 child_envelope_sub_23 ?_
  intro b hb
  exact common_sub_23 (mem_commonEnvelope childrenD_23 b hb)
def required_25 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (2, 3), (2, 4), (3, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_25 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (2, 2), (2, 3), (2, 4), (3, 0), (3, 1), (4, 0)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_25 : Fin 2 → Finset Cell := ![(placed21 3 (2, 4) required_2), (placed21 4 (0, 1) required_5)]
def childrenD_25 : Fin 2 → Finset Cell := ![(placed21 3 (2, 4) envelope_2), (placed21 4 (0, 1) envelope_5)]
theorem common_sub_25 : commonEnvelope childrenD_25 ⊆ insert (3, 0) required_25 := by decide +kernel
theorem child_required_sub_25 : ∀ j, childrenC_25 j ⊆ insert (3, 0) required_25 := by decide +kernel
theorem child_envelope_sub_25 : ∀ j, childrenD_25 j ⊆ envelope_25 := by decide +kernel
theorem pivot_mem_25 : (3, 0) ∈ envelope_25 := by decide +kernel
theorem children_work_25 : ∀ j, Template HasSnaky 1 (childrenC_25 j) (childrenD_25 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_2 3 (2, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_5 4 (0, 1)).mono (by decide +kernel)
theorem row_works_25 : Template HasSnaky 2 required_25 envelope_25 := by
  refine compose HasSnaky 1 childrenC_25 childrenD_25 children_work_25 (3, 0)
    required_25 envelope_25 pivot_mem_25 child_required_sub_25 child_envelope_sub_25 ?_
  intro b hb
  exact common_sub_25 (mem_commonEnvelope childrenD_25 b hb)
def required_28 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 3), (1, 4), (2, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_28 : Finset Cell := ⟨(([(0, 0), (0, 1), (1, 1), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_28 : Fin 2 → Finset Cell := ![(placed21 3 (1, 4) required_5), (placed21 7 (1, 4) required_5)]
def childrenD_28 : Fin 2 → Finset Cell := ![(placed21 3 (1, 4) envelope_5), (placed21 7 (1, 4) envelope_5)]
theorem common_sub_28 : commonEnvelope childrenD_28 ⊆ insert (1, 2) required_28 := by decide +kernel
theorem child_required_sub_28 : ∀ j, childrenC_28 j ⊆ insert (1, 2) required_28 := by decide +kernel
theorem child_envelope_sub_28 : ∀ j, childrenD_28 j ⊆ envelope_28 := by decide +kernel
theorem pivot_mem_28 : (1, 2) ∈ envelope_28 := by decide +kernel
theorem children_work_28 : ∀ j, Template HasSnaky 1 (childrenC_28 j) (childrenD_28 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 3 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_5 7 (1, 4)).mono (by decide +kernel)
theorem row_works_28 : Template HasSnaky 2 required_28 envelope_28 := by
  refine compose HasSnaky 1 childrenC_28 childrenD_28 children_work_28 (1, 2)
    required_28 envelope_28 pivot_mem_28 child_required_sub_28 child_envelope_sub_28 ?_
  intro b hb
  exact common_sub_28 (mem_commonEnvelope childrenD_28 b hb)
def required_30 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 3), (1, 0), (1, 1), (1, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_30 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 0), (1, 1), (1, 3), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_30 : Fin 2 → Finset Cell := ![(placed21 3 (0, 4) required_0), (placed21 1 (0, 0) required_5)]
def childrenD_30 : Fin 2 → Finset Cell := ![(placed21 3 (0, 4) envelope_0), (placed21 1 (0, 0) envelope_5)]
theorem common_sub_30 : commonEnvelope childrenD_30 ⊆ insert (0, 2) required_30 := by decide +kernel
theorem child_required_sub_30 : ∀ j, childrenC_30 j ⊆ insert (0, 2) required_30 := by decide +kernel
theorem child_envelope_sub_30 : ∀ j, childrenD_30 j ⊆ envelope_30 := by decide +kernel
theorem pivot_mem_30 : (0, 2) ∈ envelope_30 := by decide +kernel
theorem children_work_30 : ∀ j, Template HasSnaky 1 (childrenC_30 j) (childrenD_30 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 3 (0, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_5 1 (0, 0)).mono (by decide +kernel)
theorem row_works_30 : Template HasSnaky 2 required_30 envelope_30 := by
  refine compose HasSnaky 1 childrenC_30 childrenD_30 children_work_30 (0, 2)
    required_30 envelope_30 pivot_mem_30 child_required_sub_30 child_envelope_sub_30 ?_
  intro b hb
  exact common_sub_30 (mem_commonEnvelope childrenD_30 b hb)
def required_32 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (2, 2), (2, 3), (3, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_32 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (2, 2), (2, 3), (2, 4), (3, 0), (3, 1), (4, 0)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_32 : Fin 2 → Finset Cell := ![(placed21 3 (2, 4) required_0), (placed21 4 (0, 1) required_5)]
def childrenD_32 : Fin 2 → Finset Cell := ![(placed21 3 (2, 4) envelope_0), (placed21 4 (0, 1) envelope_5)]
theorem common_sub_32 : commonEnvelope childrenD_32 ⊆ insert (3, 0) required_32 := by decide +kernel
theorem child_required_sub_32 : ∀ j, childrenC_32 j ⊆ insert (3, 0) required_32 := by decide +kernel
theorem child_envelope_sub_32 : ∀ j, childrenD_32 j ⊆ envelope_32 := by decide +kernel
theorem pivot_mem_32 : (3, 0) ∈ envelope_32 := by decide +kernel
theorem children_work_32 : ∀ j, Template HasSnaky 1 (childrenC_32 j) (childrenD_32 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 3 (2, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_5 4 (0, 1)).mono (by decide +kernel)
theorem row_works_32 : Template HasSnaky 2 required_32 envelope_32 := by
  refine compose HasSnaky 1 childrenC_32 childrenD_32 children_work_32 (3, 0)
    required_32 envelope_32 pivot_mem_32 child_required_sub_32 child_envelope_sub_32 ?_
  intro b hb
  exact common_sub_32 (mem_commonEnvelope childrenD_32 b hb)
def required_34 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 4), (1, 1), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_34 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 3), (0, 4), (1, 0), (1, 1), (1, 4), (1, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_34 : Fin 2 → Finset Cell := ![(placed21 1 (0, 1) required_5), (placed21 3 (0, 4) required_5)]
def childrenD_34 : Fin 2 → Finset Cell := ![(placed21 1 (0, 1) envelope_5), (placed21 3 (0, 4) envelope_5)]
theorem common_sub_34 : commonEnvelope childrenD_34 ⊆ insert (0, 3) required_34 := by decide +kernel
theorem child_required_sub_34 : ∀ j, childrenC_34 j ⊆ insert (0, 3) required_34 := by decide +kernel
theorem child_envelope_sub_34 : ∀ j, childrenD_34 j ⊆ envelope_34 := by decide +kernel
theorem pivot_mem_34 : (0, 3) ∈ envelope_34 := by decide +kernel
theorem children_work_34 : ∀ j, Template HasSnaky 1 (childrenC_34 j) (childrenD_34 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 1 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_5 3 (0, 4)).mono (by decide +kernel)
theorem row_works_34 : Template HasSnaky 2 required_34 envelope_34 := by
  refine compose HasSnaky 1 childrenC_34 childrenD_34 children_work_34 (0, 3)
    required_34 envelope_34 pivot_mem_34 child_required_sub_34 child_envelope_sub_34 ?_
  intro b hb
  exact common_sub_34 (mem_commonEnvelope childrenD_34 b hb)
def required_35 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 0), (2, 1), (3, 1), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_35 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 0), (2, 1), (3, 1), (3, 2), (3, 3), (3, 4), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_35 : Fin 2 → Finset Cell := ![(placed21 7 (3, 4) required_1), (placed21 0 (0, 1) required_5)]
def childrenD_35 : Fin 2 → Finset Cell := ![(placed21 7 (3, 4) envelope_1), (placed21 0 (0, 1) envelope_5)]
theorem common_sub_35 : commonEnvelope childrenD_35 ⊆ insert (3, 2) required_35 := by decide +kernel
theorem child_required_sub_35 : ∀ j, childrenC_35 j ⊆ insert (3, 2) required_35 := by decide +kernel
theorem child_envelope_sub_35 : ∀ j, childrenD_35 j ⊆ envelope_35 := by decide +kernel
theorem pivot_mem_35 : (3, 2) ∈ envelope_35 := by decide +kernel
theorem children_work_35 : ∀ j, Template HasSnaky 1 (childrenC_35 j) (childrenD_35 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_1 7 (3, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_5 0 (0, 1)).mono (by decide +kernel)
theorem row_works_35 : Template HasSnaky 2 required_35 envelope_35 := by
  refine compose HasSnaky 1 childrenC_35 childrenD_35 children_work_35 (3, 2)
    required_35 envelope_35 pivot_mem_35 child_required_sub_35 child_envelope_sub_35 ?_
  intro b hb
  exact common_sub_35 (mem_commonEnvelope childrenD_35 b hb)
def required_36 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 3), (1, 1), (1, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_36 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (1, 1), (1, 2), (1, 3), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_36 : Fin 2 → Finset Cell := ![(placed21 1 (0, 0) required_2), (placed21 7 (1, 4) required_2)]
def childrenD_36 : Fin 2 → Finset Cell := ![(placed21 1 (0, 0) envelope_2), (placed21 7 (1, 4) envelope_2)]
theorem common_sub_36 : commonEnvelope childrenD_36 ⊆ insert (1, 4) required_36 := by decide +kernel
theorem child_required_sub_36 : ∀ j, childrenC_36 j ⊆ insert (1, 4) required_36 := by decide +kernel
theorem child_envelope_sub_36 : ∀ j, childrenD_36 j ⊆ envelope_36 := by decide +kernel
theorem pivot_mem_36 : (1, 4) ∈ envelope_36 := by decide +kernel
theorem children_work_36 : ∀ j, Template HasSnaky 1 (childrenC_36 j) (childrenD_36 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_2 1 (0, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_2 7 (1, 4)).mono (by decide +kernel)
theorem row_works_36 : Template HasSnaky 2 required_36 envelope_36 := by
  refine compose HasSnaky 1 childrenC_36 childrenD_36 children_work_36 (1, 4)
    required_36 envelope_36 pivot_mem_36 child_required_sub_36 child_envelope_sub_36 ?_
  intro b hb
  exact common_sub_36 (mem_commonEnvelope childrenD_36 b hb)
def required_38 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 0), (2, 1), (3, 1), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_38 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 0), (2, 1), (3, 1), (3, 2), (3, 3), (3, 4), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_38 : Fin 2 → Finset Cell := ![(placed21 7 (3, 4) required_0), (placed21 0 (0, 1) required_5)]
def childrenD_38 : Fin 2 → Finset Cell := ![(placed21 7 (3, 4) envelope_0), (placed21 0 (0, 1) envelope_5)]
theorem common_sub_38 : commonEnvelope childrenD_38 ⊆ insert (3, 2) required_38 := by decide +kernel
theorem child_required_sub_38 : ∀ j, childrenC_38 j ⊆ insert (3, 2) required_38 := by decide +kernel
theorem child_envelope_sub_38 : ∀ j, childrenD_38 j ⊆ envelope_38 := by decide +kernel
theorem pivot_mem_38 : (3, 2) ∈ envelope_38 := by decide +kernel
theorem children_work_38 : ∀ j, Template HasSnaky 1 (childrenC_38 j) (childrenD_38 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 7 (3, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_5 0 (0, 1)).mono (by decide +kernel)
theorem row_works_38 : Template HasSnaky 2 required_38 envelope_38 := by
  refine compose HasSnaky 1 childrenC_38 childrenD_38 children_work_38 (3, 2)
    required_38 envelope_38 pivot_mem_38 child_required_sub_38 child_envelope_sub_38 ?_
  intro b hb
  exact common_sub_38 (mem_commonEnvelope childrenD_38 b hb)
def required_40 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 2), (1, 4), (2, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_40 : Finset Cell := ⟨(([(0, 0), (0, 1), (1, 1), (1, 2), (1, 3), (1, 4), (2, 4), (2, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_40 : Fin 2 → Finset Cell := ![(placed21 1 (1, 1) required_5), (placed21 7 (1, 4) required_5)]
def childrenD_40 : Fin 2 → Finset Cell := ![(placed21 1 (1, 1) envelope_5), (placed21 7 (1, 4) envelope_5)]
theorem common_sub_40 : commonEnvelope childrenD_40 ⊆ insert (1, 3) required_40 := by decide +kernel
theorem child_required_sub_40 : ∀ j, childrenC_40 j ⊆ insert (1, 3) required_40 := by decide +kernel
theorem child_envelope_sub_40 : ∀ j, childrenD_40 j ⊆ envelope_40 := by decide +kernel
theorem pivot_mem_40 : (1, 3) ∈ envelope_40 := by decide +kernel
theorem children_work_40 : ∀ j, Template HasSnaky 1 (childrenC_40 j) (childrenD_40 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 1 (1, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_5 7 (1, 4)).mono (by decide +kernel)
theorem row_works_40 : Template HasSnaky 2 required_40 envelope_40 := by
  refine compose HasSnaky 1 childrenC_40 childrenD_40 children_work_40 (1, 3)
    required_40 envelope_40 pivot_mem_40 child_required_sub_40 child_envelope_sub_40 ?_
  intro b hb
  exact common_sub_40 (mem_commonEnvelope childrenD_40 b hb)
def required_43 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (1, 2), (1, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_43 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_43 : Fin 2 → Finset Cell := ![(placed21 7 (1, 5) required_0), (placed21 7 (1, 4) required_3)]
def childrenD_43 : Fin 2 → Finset Cell := ![(placed21 7 (1, 5) envelope_0), (placed21 7 (1, 4) envelope_3)]
theorem common_sub_43 : commonEnvelope childrenD_43 ⊆ insert (1, 4) required_43 := by decide +kernel
theorem child_required_sub_43 : ∀ j, childrenC_43 j ⊆ insert (1, 4) required_43 := by decide +kernel
theorem child_envelope_sub_43 : ∀ j, childrenD_43 j ⊆ envelope_43 := by decide +kernel
theorem pivot_mem_43 : (1, 4) ∈ envelope_43 := by decide +kernel
theorem children_work_43 : ∀ j, Template HasSnaky 1 (childrenC_43 j) (childrenD_43 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 7 (1, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_3 7 (1, 4)).mono (by decide +kernel)
theorem row_works_43 : Template HasSnaky 2 required_43 envelope_43 := by
  refine compose HasSnaky 1 childrenC_43 childrenD_43 children_work_43 (1, 4)
    required_43 envelope_43 pivot_mem_43 child_required_sub_43 child_envelope_sub_43 ?_
  intro b hb
  exact common_sub_43 (mem_commonEnvelope childrenD_43 b hb)
def required_51 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (1, 2), (1, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_51 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (1, 4), (1, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_51 : Fin 2 → Finset Cell := ![(placed21 7 (1, 5) required_0), (placed21 1 (0, 0) required_3)]
def childrenD_51 : Fin 2 → Finset Cell := ![(placed21 7 (1, 5) envelope_0), (placed21 1 (0, 0) envelope_3)]
theorem common_sub_51 : commonEnvelope childrenD_51 ⊆ insert (1, 4) required_51 := by decide +kernel
theorem child_required_sub_51 : ∀ j, childrenC_51 j ⊆ insert (1, 4) required_51 := by decide +kernel
theorem child_envelope_sub_51 : ∀ j, childrenD_51 j ⊆ envelope_51 := by decide +kernel
theorem pivot_mem_51 : (1, 4) ∈ envelope_51 := by decide +kernel
theorem children_work_51 : ∀ j, Template HasSnaky 1 (childrenC_51 j) (childrenD_51 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 7 (1, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_3 1 (0, 0)).mono (by decide +kernel)
theorem row_works_51 : Template HasSnaky 2 required_51 envelope_51 := by
  refine compose HasSnaky 1 childrenC_51 childrenD_51 children_work_51 (1, 4)
    required_51 envelope_51 pivot_mem_51 child_required_sub_51 child_envelope_sub_51 ?_
  intro b hb
  exact common_sub_51 (mem_commonEnvelope childrenD_51 b hb)
def required_66 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 1), (1, 2), (1, 3), (2, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_66 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_66 : Fin 2 → Finset Cell := ![(placed21 7 (1, 5) required_0), (placed21 3 (1, 4) required_5)]
def childrenD_66 : Fin 2 → Finset Cell := ![(placed21 7 (1, 5) envelope_0), (placed21 3 (1, 4) envelope_5)]
theorem common_sub_66 : commonEnvelope childrenD_66 ⊆ insert (1, 4) required_66 := by decide +kernel
theorem child_required_sub_66 : ∀ j, childrenC_66 j ⊆ insert (1, 4) required_66 := by decide +kernel
theorem child_envelope_sub_66 : ∀ j, childrenD_66 j ⊆ envelope_66 := by decide +kernel
theorem pivot_mem_66 : (1, 4) ∈ envelope_66 := by decide +kernel
theorem children_work_66 : ∀ j, Template HasSnaky 1 (childrenC_66 j) (childrenD_66 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 7 (1, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_5 3 (1, 4)).mono (by decide +kernel)
theorem row_works_66 : Template HasSnaky 2 required_66 envelope_66 := by
  refine compose HasSnaky 1 childrenC_66 childrenD_66 children_work_66 (1, 4)
    required_66 envelope_66 pivot_mem_66 child_required_sub_66 child_envelope_sub_66 ?_
  intro b hb
  exact common_sub_66 (mem_commonEnvelope childrenD_66 b hb)
def required_68 : Finset Cell := ⟨(([(0, 0), (0, 3), (1, 3), (1, 4), (1, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_68 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (1, 3), (1, 4), (1, 5), (1, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_68 : Fin 2 → Finset Cell := ![(placed21 7 (1, 6) required_0), (placed21 1 (0, 0) required_1)]
def childrenD_68 : Fin 2 → Finset Cell := ![(placed21 7 (1, 6) envelope_0), (placed21 1 (0, 0) envelope_1)]
theorem common_sub_68 : commonEnvelope childrenD_68 ⊆ insert (0, 2) required_68 := by decide +kernel
theorem child_required_sub_68 : ∀ j, childrenC_68 j ⊆ insert (0, 2) required_68 := by decide +kernel
theorem child_envelope_sub_68 : ∀ j, childrenD_68 j ⊆ envelope_68 := by decide +kernel
theorem pivot_mem_68 : (0, 2) ∈ envelope_68 := by decide +kernel
theorem children_work_68 : ∀ j, Template HasSnaky 1 (childrenC_68 j) (childrenD_68 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 7 (1, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_1 1 (0, 0)).mono (by decide +kernel)
theorem row_works_68 : Template HasSnaky 2 required_68 envelope_68 := by
  refine compose HasSnaky 1 childrenC_68 childrenD_68 children_work_68 (0, 2)
    required_68 envelope_68 pivot_mem_68 child_required_sub_68 child_envelope_sub_68 ?_
  intro b hb
  exact common_sub_68 (mem_commonEnvelope childrenD_68 b hb)
def required_70 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (1, 1), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_70 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (1, 1), (1, 2), (1, 3), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_70 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) required_2), (placed21 1 (0, 0) required_3)]
def childrenD_70 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) envelope_2), (placed21 1 (0, 0) envelope_3)]
theorem common_sub_70 : commonEnvelope childrenD_70 ⊆ insert (1, 3) required_70 := by decide +kernel
theorem child_required_sub_70 : ∀ j, childrenC_70 j ⊆ insert (1, 3) required_70 := by decide +kernel
theorem child_envelope_sub_70 : ∀ j, childrenD_70 j ⊆ envelope_70 := by decide +kernel
theorem pivot_mem_70 : (1, 3) ∈ envelope_70 := by decide +kernel
theorem children_work_70 : ∀ j, Template HasSnaky 1 (childrenC_70 j) (childrenD_70 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_2 7 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_3 1 (0, 0)).mono (by decide +kernel)
theorem row_works_70 : Template HasSnaky 2 required_70 envelope_70 := by
  refine compose HasSnaky 1 childrenC_70 childrenD_70 children_work_70 (1, 3)
    required_70 envelope_70 pivot_mem_70 child_required_sub_70 child_envelope_sub_70 ?_
  intro b hb
  exact common_sub_70 (mem_commonEnvelope childrenD_70 b hb)
def required_76 : Finset Cell := ⟨(([(0, 0), (1, 1), (1, 2), (1, 3), (2, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_76 : Finset Cell := ⟨(([(0, 0), (0, 1), (1, 1), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_76 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) required_4), (placed21 3 (1, 4) required_5)]
def childrenD_76 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) envelope_4), (placed21 3 (1, 4) envelope_5)]
theorem common_sub_76 : commonEnvelope childrenD_76 ⊆ insert (1, 4) required_76 := by decide +kernel
theorem child_required_sub_76 : ∀ j, childrenC_76 j ⊆ insert (1, 4) required_76 := by decide +kernel
theorem child_envelope_sub_76 : ∀ j, childrenD_76 j ⊆ envelope_76 := by decide +kernel
theorem pivot_mem_76 : (1, 4) ∈ envelope_76 := by decide +kernel
theorem children_work_76 : ∀ j, Template HasSnaky 1 (childrenC_76 j) (childrenD_76 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_4 7 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_5 3 (1, 4)).mono (by decide +kernel)
theorem row_works_76 : Template HasSnaky 2 required_76 envelope_76 := by
  refine compose HasSnaky 1 childrenC_76 childrenD_76 children_work_76 (1, 4)
    required_76 envelope_76 pivot_mem_76 child_required_sub_76 child_envelope_sub_76 ?_
  intro b hb
  exact common_sub_76 (mem_commonEnvelope childrenD_76 b hb)
def required_77 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 2), (1, 3), (1, 4), (3, 2), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_77 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1), (3, 1), (3, 2), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_77 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) required_3), (placed21 3 (1, 4) required_5)]
def childrenD_77 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) envelope_3), (placed21 3 (1, 4) envelope_5)]
theorem common_sub_77 : commonEnvelope childrenD_77 ⊆ insert (2, 1) required_77 := by decide +kernel
theorem child_required_sub_77 : ∀ j, childrenC_77 j ⊆ insert (2, 1) required_77 := by decide +kernel
theorem child_envelope_sub_77 : ∀ j, childrenD_77 j ⊆ envelope_77 := by decide +kernel
theorem pivot_mem_77 : (2, 1) ∈ envelope_77 := by decide +kernel
theorem children_work_77 : ∀ j, Template HasSnaky 1 (childrenC_77 j) (childrenD_77 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_3 0 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_5 3 (1, 4)).mono (by decide +kernel)
theorem row_works_77 : Template HasSnaky 2 required_77 envelope_77 := by
  refine compose HasSnaky 1 childrenC_77 childrenD_77 children_work_77 (2, 1)
    required_77 envelope_77 pivot_mem_77 child_required_sub_77 child_envelope_sub_77 ?_
  intro b hb
  exact common_sub_77 (mem_commonEnvelope childrenD_77 b hb)
def required_80 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 2), (1, 4), (2, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_80 : Finset Cell := ⟨(([(0, 0), (0, 1), (1, 1), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_80 : Fin 2 → Finset Cell := ![(placed21 3 (1, 4) required_5), (placed21 7 (1, 4) required_5)]
def childrenD_80 : Fin 2 → Finset Cell := ![(placed21 3 (1, 4) envelope_5), (placed21 7 (1, 4) envelope_5)]
theorem common_sub_80 : commonEnvelope childrenD_80 ⊆ insert (1, 3) required_80 := by decide +kernel
theorem child_required_sub_80 : ∀ j, childrenC_80 j ⊆ insert (1, 3) required_80 := by decide +kernel
theorem child_envelope_sub_80 : ∀ j, childrenD_80 j ⊆ envelope_80 := by decide +kernel
theorem pivot_mem_80 : (1, 3) ∈ envelope_80 := by decide +kernel
theorem children_work_80 : ∀ j, Template HasSnaky 1 (childrenC_80 j) (childrenD_80 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 3 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_5 7 (1, 4)).mono (by decide +kernel)
theorem row_works_80 : Template HasSnaky 2 required_80 envelope_80 := by
  refine compose HasSnaky 1 childrenC_80 childrenD_80 children_work_80 (1, 3)
    required_80 envelope_80 pivot_mem_80 child_required_sub_80 child_envelope_sub_80 ?_
  intro b hb
  exact common_sub_80 (mem_commonEnvelope childrenD_80 b hb)
def required_83 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 2), (1, 3), (2, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_83 : Finset Cell := ⟨(([(0, 0), (0, 1), (1, 1), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_83 : Fin 2 → Finset Cell := ![(placed21 3 (1, 4) required_5), (placed21 7 (1, 4) required_5)]
def childrenD_83 : Fin 2 → Finset Cell := ![(placed21 3 (1, 4) envelope_5), (placed21 7 (1, 4) envelope_5)]
theorem common_sub_83 : commonEnvelope childrenD_83 ⊆ insert (1, 4) required_83 := by decide +kernel
theorem child_required_sub_83 : ∀ j, childrenC_83 j ⊆ insert (1, 4) required_83 := by decide +kernel
theorem child_envelope_sub_83 : ∀ j, childrenD_83 j ⊆ envelope_83 := by decide +kernel
theorem pivot_mem_83 : (1, 4) ∈ envelope_83 := by decide +kernel
theorem children_work_83 : ∀ j, Template HasSnaky 1 (childrenC_83 j) (childrenD_83 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 3 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_5 7 (1, 4)).mono (by decide +kernel)
theorem row_works_83 : Template HasSnaky 2 required_83 envelope_83 := by
  refine compose HasSnaky 1 childrenC_83 childrenD_83 children_work_83 (1, 4)
    required_83 envelope_83 pivot_mem_83 child_required_sub_83 child_envelope_sub_83 ?_
  intro b hb
  exact common_sub_83 (mem_commonEnvelope childrenD_83 b hb)
def required_94 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_94 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 0), (1, 1), (1, 3), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_94 : Fin 2 → Finset Cell := ![(placed21 3 (0, 4) required_0), (placed21 1 (0, 0) required_5)]
def childrenD_94 : Fin 2 → Finset Cell := ![(placed21 3 (0, 4) envelope_0), (placed21 1 (0, 0) envelope_5)]
theorem common_sub_94 : commonEnvelope childrenD_94 ⊆ insert (0, 3) required_94 := by decide +kernel
theorem child_required_sub_94 : ∀ j, childrenC_94 j ⊆ insert (0, 3) required_94 := by decide +kernel
theorem child_envelope_sub_94 : ∀ j, childrenD_94 j ⊆ envelope_94 := by decide +kernel
theorem pivot_mem_94 : (0, 3) ∈ envelope_94 := by decide +kernel
theorem children_work_94 : ∀ j, Template HasSnaky 1 (childrenC_94 j) (childrenD_94 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 3 (0, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_5 1 (0, 0)).mono (by decide +kernel)
theorem row_works_94 : Template HasSnaky 2 required_94 envelope_94 := by
  refine compose HasSnaky 1 childrenC_94 childrenD_94 children_work_94 (0, 3)
    required_94 envelope_94 pivot_mem_94 child_required_sub_94 child_envelope_sub_94 ?_
  intro b hb
  exact common_sub_94 (mem_commonEnvelope childrenD_94 b hb)
def height_6 : ℕ := 2
def childrenH_6 : Fin 2 → ℕ := ![height_4, height_5]
theorem height_exact_6 : height_6 = 1 + Finset.univ.sup childrenH_6 := by decide +kernel
theorem required_origin_6 : ∀ x ∈ required_6,
    (∃ j, x ∈ childrenC_6 j) ∨ ∀ j, x ∈ childrenD_6 j := by decide +kernel
theorem required_exact_6 : required_6 =
    ((Finset.univ.biUnion childrenC_6) ∪ commonEnvelope childrenD_6).erase (1, 4) := by
  exact required_eq_combination childrenC_6 childrenD_6 (1, 4) required_6
    (by decide +kernel) child_required_sub_6 common_sub_6 required_origin_6
theorem envelope_origin_6 : ∀ x ∈ envelope_6,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_6 j := by decide +kernel
theorem envelope_exact_6 : envelope_6 =
    insert (1, 4) (Finset.univ.biUnion childrenD_6) := by
  exact envelope_eq_combination childrenD_6 (1, 4) envelope_6
    pivot_mem_6 child_envelope_sub_6 envelope_origin_6
def checked_6 : CheckedCard where
  required := required_6
  envelope := envelope_6
  height := height_6
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_6
def height_11 : ℕ := 2
def childrenH_11 : Fin 2 → ℕ := ![height_0, height_5]
theorem height_exact_11 : height_11 = 1 + Finset.univ.sup childrenH_11 := by decide +kernel
theorem required_origin_11 : ∀ x ∈ required_11,
    (∃ j, x ∈ childrenC_11 j) ∨ ∀ j, x ∈ childrenD_11 j := by decide +kernel
theorem required_exact_11 : required_11 =
    ((Finset.univ.biUnion childrenC_11) ∪ commonEnvelope childrenD_11).erase (1, 1) := by
  exact required_eq_combination childrenC_11 childrenD_11 (1, 1) required_11
    (by decide +kernel) child_required_sub_11 common_sub_11 required_origin_11
theorem envelope_origin_11 : ∀ x ∈ envelope_11,
    x = (1, 1) ∨ ∃ j, x ∈ childrenD_11 j := by decide +kernel
theorem envelope_exact_11 : envelope_11 =
    insert (1, 1) (Finset.univ.biUnion childrenD_11) := by
  exact envelope_eq_combination childrenD_11 (1, 1) envelope_11
    pivot_mem_11 child_envelope_sub_11 envelope_origin_11
def checked_11 : CheckedCard where
  required := required_11
  envelope := envelope_11
  height := height_11
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_11
def height_15 : ℕ := 2
def childrenH_15 : Fin 2 → ℕ := ![height_0, height_0]
theorem height_exact_15 : height_15 = 1 + Finset.univ.sup childrenH_15 := by decide +kernel
theorem required_origin_15 : ∀ x ∈ required_15,
    (∃ j, x ∈ childrenC_15 j) ∨ ∀ j, x ∈ childrenD_15 j := by decide +kernel
theorem required_exact_15 : required_15 =
    ((Finset.univ.biUnion childrenC_15) ∪ commonEnvelope childrenD_15).erase (1, 4) := by
  exact required_eq_combination childrenC_15 childrenD_15 (1, 4) required_15
    (by decide +kernel) child_required_sub_15 common_sub_15 required_origin_15
theorem envelope_origin_15 : ∀ x ∈ envelope_15,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_15 j := by decide +kernel
theorem envelope_exact_15 : envelope_15 =
    insert (1, 4) (Finset.univ.biUnion childrenD_15) := by
  exact envelope_eq_combination childrenD_15 (1, 4) envelope_15
    pivot_mem_15 child_envelope_sub_15 envelope_origin_15
def checked_15 : CheckedCard where
  required := required_15
  envelope := envelope_15
  height := height_15
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_15
def height_22 : ℕ := 2
def childrenH_22 : Fin 2 → ℕ := ![height_0, height_5]
theorem height_exact_22 : height_22 = 1 + Finset.univ.sup childrenH_22 := by decide +kernel
theorem required_origin_22 : ∀ x ∈ required_22,
    (∃ j, x ∈ childrenC_22 j) ∨ ∀ j, x ∈ childrenD_22 j := by decide +kernel
theorem required_exact_22 : required_22 =
    ((Finset.univ.biUnion childrenC_22) ∪ commonEnvelope childrenD_22).erase (0, 3) := by
  exact required_eq_combination childrenC_22 childrenD_22 (0, 3) required_22
    (by decide +kernel) child_required_sub_22 common_sub_22 required_origin_22
theorem envelope_origin_22 : ∀ x ∈ envelope_22,
    x = (0, 3) ∨ ∃ j, x ∈ childrenD_22 j := by decide +kernel
theorem envelope_exact_22 : envelope_22 =
    insert (0, 3) (Finset.univ.biUnion childrenD_22) := by
  exact envelope_eq_combination childrenD_22 (0, 3) envelope_22
    pivot_mem_22 child_envelope_sub_22 envelope_origin_22
def checked_22 : CheckedCard where
  required := required_22
  envelope := envelope_22
  height := height_22
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_22
def height_23 : ℕ := 2
def childrenH_23 : Fin 2 → ℕ := ![height_0, height_5]
theorem height_exact_23 : height_23 = 1 + Finset.univ.sup childrenH_23 := by decide +kernel
theorem required_origin_23 : ∀ x ∈ required_23,
    (∃ j, x ∈ childrenC_23 j) ∨ ∀ j, x ∈ childrenD_23 j := by decide +kernel
theorem required_exact_23 : required_23 =
    ((Finset.univ.biUnion childrenC_23) ∪ commonEnvelope childrenD_23).erase (0, 4) := by
  exact required_eq_combination childrenC_23 childrenD_23 (0, 4) required_23
    (by decide +kernel) child_required_sub_23 common_sub_23 required_origin_23
theorem envelope_origin_23 : ∀ x ∈ envelope_23,
    x = (0, 4) ∨ ∃ j, x ∈ childrenD_23 j := by decide +kernel
theorem envelope_exact_23 : envelope_23 =
    insert (0, 4) (Finset.univ.biUnion childrenD_23) := by
  exact envelope_eq_combination childrenD_23 (0, 4) envelope_23
    pivot_mem_23 child_envelope_sub_23 envelope_origin_23
def checked_23 : CheckedCard where
  required := required_23
  envelope := envelope_23
  height := height_23
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_23
def height_25 : ℕ := 2
def childrenH_25 : Fin 2 → ℕ := ![height_2, height_5]
theorem height_exact_25 : height_25 = 1 + Finset.univ.sup childrenH_25 := by decide +kernel
theorem required_origin_25 : ∀ x ∈ required_25,
    (∃ j, x ∈ childrenC_25 j) ∨ ∀ j, x ∈ childrenD_25 j := by decide +kernel
theorem required_exact_25 : required_25 =
    ((Finset.univ.biUnion childrenC_25) ∪ commonEnvelope childrenD_25).erase (3, 0) := by
  exact required_eq_combination childrenC_25 childrenD_25 (3, 0) required_25
    (by decide +kernel) child_required_sub_25 common_sub_25 required_origin_25
theorem envelope_origin_25 : ∀ x ∈ envelope_25,
    x = (3, 0) ∨ ∃ j, x ∈ childrenD_25 j := by decide +kernel
theorem envelope_exact_25 : envelope_25 =
    insert (3, 0) (Finset.univ.biUnion childrenD_25) := by
  exact envelope_eq_combination childrenD_25 (3, 0) envelope_25
    pivot_mem_25 child_envelope_sub_25 envelope_origin_25
def checked_25 : CheckedCard where
  required := required_25
  envelope := envelope_25
  height := height_25
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_25
def height_28 : ℕ := 2
def childrenH_28 : Fin 2 → ℕ := ![height_5, height_5]
theorem height_exact_28 : height_28 = 1 + Finset.univ.sup childrenH_28 := by decide +kernel
theorem required_origin_28 : ∀ x ∈ required_28,
    (∃ j, x ∈ childrenC_28 j) ∨ ∀ j, x ∈ childrenD_28 j := by decide +kernel
theorem required_exact_28 : required_28 =
    ((Finset.univ.biUnion childrenC_28) ∪ commonEnvelope childrenD_28).erase (1, 2) := by
  exact required_eq_combination childrenC_28 childrenD_28 (1, 2) required_28
    (by decide +kernel) child_required_sub_28 common_sub_28 required_origin_28
theorem envelope_origin_28 : ∀ x ∈ envelope_28,
    x = (1, 2) ∨ ∃ j, x ∈ childrenD_28 j := by decide +kernel
theorem envelope_exact_28 : envelope_28 =
    insert (1, 2) (Finset.univ.biUnion childrenD_28) := by
  exact envelope_eq_combination childrenD_28 (1, 2) envelope_28
    pivot_mem_28 child_envelope_sub_28 envelope_origin_28
def checked_28 : CheckedCard where
  required := required_28
  envelope := envelope_28
  height := height_28
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_28
def height_30 : ℕ := 2
def childrenH_30 : Fin 2 → ℕ := ![height_0, height_5]
theorem height_exact_30 : height_30 = 1 + Finset.univ.sup childrenH_30 := by decide +kernel
theorem required_origin_30 : ∀ x ∈ required_30,
    (∃ j, x ∈ childrenC_30 j) ∨ ∀ j, x ∈ childrenD_30 j := by decide +kernel
theorem required_exact_30 : required_30 =
    ((Finset.univ.biUnion childrenC_30) ∪ commonEnvelope childrenD_30).erase (0, 2) := by
  exact required_eq_combination childrenC_30 childrenD_30 (0, 2) required_30
    (by decide +kernel) child_required_sub_30 common_sub_30 required_origin_30
theorem envelope_origin_30 : ∀ x ∈ envelope_30,
    x = (0, 2) ∨ ∃ j, x ∈ childrenD_30 j := by decide +kernel
theorem envelope_exact_30 : envelope_30 =
    insert (0, 2) (Finset.univ.biUnion childrenD_30) := by
  exact envelope_eq_combination childrenD_30 (0, 2) envelope_30
    pivot_mem_30 child_envelope_sub_30 envelope_origin_30
def checked_30 : CheckedCard where
  required := required_30
  envelope := envelope_30
  height := height_30
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_30
def height_32 : ℕ := 2
def childrenH_32 : Fin 2 → ℕ := ![height_0, height_5]
theorem height_exact_32 : height_32 = 1 + Finset.univ.sup childrenH_32 := by decide +kernel
theorem required_origin_32 : ∀ x ∈ required_32,
    (∃ j, x ∈ childrenC_32 j) ∨ ∀ j, x ∈ childrenD_32 j := by decide +kernel
theorem required_exact_32 : required_32 =
    ((Finset.univ.biUnion childrenC_32) ∪ commonEnvelope childrenD_32).erase (3, 0) := by
  exact required_eq_combination childrenC_32 childrenD_32 (3, 0) required_32
    (by decide +kernel) child_required_sub_32 common_sub_32 required_origin_32
theorem envelope_origin_32 : ∀ x ∈ envelope_32,
    x = (3, 0) ∨ ∃ j, x ∈ childrenD_32 j := by decide +kernel
theorem envelope_exact_32 : envelope_32 =
    insert (3, 0) (Finset.univ.biUnion childrenD_32) := by
  exact envelope_eq_combination childrenD_32 (3, 0) envelope_32
    pivot_mem_32 child_envelope_sub_32 envelope_origin_32
def checked_32 : CheckedCard where
  required := required_32
  envelope := envelope_32
  height := height_32
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_32
def height_34 : ℕ := 2
def childrenH_34 : Fin 2 → ℕ := ![height_5, height_5]
theorem height_exact_34 : height_34 = 1 + Finset.univ.sup childrenH_34 := by decide +kernel
theorem required_origin_34 : ∀ x ∈ required_34,
    (∃ j, x ∈ childrenC_34 j) ∨ ∀ j, x ∈ childrenD_34 j := by decide +kernel
theorem required_exact_34 : required_34 =
    ((Finset.univ.biUnion childrenC_34) ∪ commonEnvelope childrenD_34).erase (0, 3) := by
  exact required_eq_combination childrenC_34 childrenD_34 (0, 3) required_34
    (by decide +kernel) child_required_sub_34 common_sub_34 required_origin_34
theorem envelope_origin_34 : ∀ x ∈ envelope_34,
    x = (0, 3) ∨ ∃ j, x ∈ childrenD_34 j := by decide +kernel
theorem envelope_exact_34 : envelope_34 =
    insert (0, 3) (Finset.univ.biUnion childrenD_34) := by
  exact envelope_eq_combination childrenD_34 (0, 3) envelope_34
    pivot_mem_34 child_envelope_sub_34 envelope_origin_34
def checked_34 : CheckedCard where
  required := required_34
  envelope := envelope_34
  height := height_34
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_34
def height_35 : ℕ := 2
def childrenH_35 : Fin 2 → ℕ := ![height_1, height_5]
theorem height_exact_35 : height_35 = 1 + Finset.univ.sup childrenH_35 := by decide +kernel
theorem required_origin_35 : ∀ x ∈ required_35,
    (∃ j, x ∈ childrenC_35 j) ∨ ∀ j, x ∈ childrenD_35 j := by decide +kernel
theorem required_exact_35 : required_35 =
    ((Finset.univ.biUnion childrenC_35) ∪ commonEnvelope childrenD_35).erase (3, 2) := by
  exact required_eq_combination childrenC_35 childrenD_35 (3, 2) required_35
    (by decide +kernel) child_required_sub_35 common_sub_35 required_origin_35
theorem envelope_origin_35 : ∀ x ∈ envelope_35,
    x = (3, 2) ∨ ∃ j, x ∈ childrenD_35 j := by decide +kernel
theorem envelope_exact_35 : envelope_35 =
    insert (3, 2) (Finset.univ.biUnion childrenD_35) := by
  exact envelope_eq_combination childrenD_35 (3, 2) envelope_35
    pivot_mem_35 child_envelope_sub_35 envelope_origin_35
def checked_35 : CheckedCard where
  required := required_35
  envelope := envelope_35
  height := height_35
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_35
def height_36 : ℕ := 2
def childrenH_36 : Fin 2 → ℕ := ![height_2, height_2]
theorem height_exact_36 : height_36 = 1 + Finset.univ.sup childrenH_36 := by decide +kernel
theorem required_origin_36 : ∀ x ∈ required_36,
    (∃ j, x ∈ childrenC_36 j) ∨ ∀ j, x ∈ childrenD_36 j := by decide +kernel
theorem required_exact_36 : required_36 =
    ((Finset.univ.biUnion childrenC_36) ∪ commonEnvelope childrenD_36).erase (1, 4) := by
  exact required_eq_combination childrenC_36 childrenD_36 (1, 4) required_36
    (by decide +kernel) child_required_sub_36 common_sub_36 required_origin_36
theorem envelope_origin_36 : ∀ x ∈ envelope_36,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_36 j := by decide +kernel
theorem envelope_exact_36 : envelope_36 =
    insert (1, 4) (Finset.univ.biUnion childrenD_36) := by
  exact envelope_eq_combination childrenD_36 (1, 4) envelope_36
    pivot_mem_36 child_envelope_sub_36 envelope_origin_36
def checked_36 : CheckedCard where
  required := required_36
  envelope := envelope_36
  height := height_36
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_36
def height_38 : ℕ := 2
def childrenH_38 : Fin 2 → ℕ := ![height_0, height_5]
theorem height_exact_38 : height_38 = 1 + Finset.univ.sup childrenH_38 := by decide +kernel
theorem required_origin_38 : ∀ x ∈ required_38,
    (∃ j, x ∈ childrenC_38 j) ∨ ∀ j, x ∈ childrenD_38 j := by decide +kernel
theorem required_exact_38 : required_38 =
    ((Finset.univ.biUnion childrenC_38) ∪ commonEnvelope childrenD_38).erase (3, 2) := by
  exact required_eq_combination childrenC_38 childrenD_38 (3, 2) required_38
    (by decide +kernel) child_required_sub_38 common_sub_38 required_origin_38
theorem envelope_origin_38 : ∀ x ∈ envelope_38,
    x = (3, 2) ∨ ∃ j, x ∈ childrenD_38 j := by decide +kernel
theorem envelope_exact_38 : envelope_38 =
    insert (3, 2) (Finset.univ.biUnion childrenD_38) := by
  exact envelope_eq_combination childrenD_38 (3, 2) envelope_38
    pivot_mem_38 child_envelope_sub_38 envelope_origin_38
def checked_38 : CheckedCard where
  required := required_38
  envelope := envelope_38
  height := height_38
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_38
def height_40 : ℕ := 2
def childrenH_40 : Fin 2 → ℕ := ![height_5, height_5]
theorem height_exact_40 : height_40 = 1 + Finset.univ.sup childrenH_40 := by decide +kernel
theorem required_origin_40 : ∀ x ∈ required_40,
    (∃ j, x ∈ childrenC_40 j) ∨ ∀ j, x ∈ childrenD_40 j := by decide +kernel
theorem required_exact_40 : required_40 =
    ((Finset.univ.biUnion childrenC_40) ∪ commonEnvelope childrenD_40).erase (1, 3) := by
  exact required_eq_combination childrenC_40 childrenD_40 (1, 3) required_40
    (by decide +kernel) child_required_sub_40 common_sub_40 required_origin_40
theorem envelope_origin_40 : ∀ x ∈ envelope_40,
    x = (1, 3) ∨ ∃ j, x ∈ childrenD_40 j := by decide +kernel
theorem envelope_exact_40 : envelope_40 =
    insert (1, 3) (Finset.univ.biUnion childrenD_40) := by
  exact envelope_eq_combination childrenD_40 (1, 3) envelope_40
    pivot_mem_40 child_envelope_sub_40 envelope_origin_40
def checked_40 : CheckedCard where
  required := required_40
  envelope := envelope_40
  height := height_40
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_40
def height_43 : ℕ := 2
def childrenH_43 : Fin 2 → ℕ := ![height_0, height_3]
theorem height_exact_43 : height_43 = 1 + Finset.univ.sup childrenH_43 := by decide +kernel
theorem required_origin_43 : ∀ x ∈ required_43,
    (∃ j, x ∈ childrenC_43 j) ∨ ∀ j, x ∈ childrenD_43 j := by decide +kernel
theorem required_exact_43 : required_43 =
    ((Finset.univ.biUnion childrenC_43) ∪ commonEnvelope childrenD_43).erase (1, 4) := by
  exact required_eq_combination childrenC_43 childrenD_43 (1, 4) required_43
    (by decide +kernel) child_required_sub_43 common_sub_43 required_origin_43
theorem envelope_origin_43 : ∀ x ∈ envelope_43,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_43 j := by decide +kernel
theorem envelope_exact_43 : envelope_43 =
    insert (1, 4) (Finset.univ.biUnion childrenD_43) := by
  exact envelope_eq_combination childrenD_43 (1, 4) envelope_43
    pivot_mem_43 child_envelope_sub_43 envelope_origin_43
def checked_43 : CheckedCard where
  required := required_43
  envelope := envelope_43
  height := height_43
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_43
def height_51 : ℕ := 2
def childrenH_51 : Fin 2 → ℕ := ![height_0, height_3]
theorem height_exact_51 : height_51 = 1 + Finset.univ.sup childrenH_51 := by decide +kernel
theorem required_origin_51 : ∀ x ∈ required_51,
    (∃ j, x ∈ childrenC_51 j) ∨ ∀ j, x ∈ childrenD_51 j := by decide +kernel
theorem required_exact_51 : required_51 =
    ((Finset.univ.biUnion childrenC_51) ∪ commonEnvelope childrenD_51).erase (1, 4) := by
  exact required_eq_combination childrenC_51 childrenD_51 (1, 4) required_51
    (by decide +kernel) child_required_sub_51 common_sub_51 required_origin_51
theorem envelope_origin_51 : ∀ x ∈ envelope_51,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_51 j := by decide +kernel
theorem envelope_exact_51 : envelope_51 =
    insert (1, 4) (Finset.univ.biUnion childrenD_51) := by
  exact envelope_eq_combination childrenD_51 (1, 4) envelope_51
    pivot_mem_51 child_envelope_sub_51 envelope_origin_51
def checked_51 : CheckedCard where
  required := required_51
  envelope := envelope_51
  height := height_51
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_51
def height_66 : ℕ := 2
def childrenH_66 : Fin 2 → ℕ := ![height_0, height_5]
theorem height_exact_66 : height_66 = 1 + Finset.univ.sup childrenH_66 := by decide +kernel
theorem required_origin_66 : ∀ x ∈ required_66,
    (∃ j, x ∈ childrenC_66 j) ∨ ∀ j, x ∈ childrenD_66 j := by decide +kernel
theorem required_exact_66 : required_66 =
    ((Finset.univ.biUnion childrenC_66) ∪ commonEnvelope childrenD_66).erase (1, 4) := by
  exact required_eq_combination childrenC_66 childrenD_66 (1, 4) required_66
    (by decide +kernel) child_required_sub_66 common_sub_66 required_origin_66
theorem envelope_origin_66 : ∀ x ∈ envelope_66,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_66 j := by decide +kernel
theorem envelope_exact_66 : envelope_66 =
    insert (1, 4) (Finset.univ.biUnion childrenD_66) := by
  exact envelope_eq_combination childrenD_66 (1, 4) envelope_66
    pivot_mem_66 child_envelope_sub_66 envelope_origin_66
def checked_66 : CheckedCard where
  required := required_66
  envelope := envelope_66
  height := height_66
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_66
def height_68 : ℕ := 2
def childrenH_68 : Fin 2 → ℕ := ![height_0, height_1]
theorem height_exact_68 : height_68 = 1 + Finset.univ.sup childrenH_68 := by decide +kernel
theorem required_origin_68 : ∀ x ∈ required_68,
    (∃ j, x ∈ childrenC_68 j) ∨ ∀ j, x ∈ childrenD_68 j := by decide +kernel
theorem required_exact_68 : required_68 =
    ((Finset.univ.biUnion childrenC_68) ∪ commonEnvelope childrenD_68).erase (0, 2) := by
  exact required_eq_combination childrenC_68 childrenD_68 (0, 2) required_68
    (by decide +kernel) child_required_sub_68 common_sub_68 required_origin_68
theorem envelope_origin_68 : ∀ x ∈ envelope_68,
    x = (0, 2) ∨ ∃ j, x ∈ childrenD_68 j := by decide +kernel
theorem envelope_exact_68 : envelope_68 =
    insert (0, 2) (Finset.univ.biUnion childrenD_68) := by
  exact envelope_eq_combination childrenD_68 (0, 2) envelope_68
    pivot_mem_68 child_envelope_sub_68 envelope_origin_68
def checked_68 : CheckedCard where
  required := required_68
  envelope := envelope_68
  height := height_68
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_68
def height_70 : ℕ := 2
def childrenH_70 : Fin 2 → ℕ := ![height_2, height_3]
theorem height_exact_70 : height_70 = 1 + Finset.univ.sup childrenH_70 := by decide +kernel
theorem required_origin_70 : ∀ x ∈ required_70,
    (∃ j, x ∈ childrenC_70 j) ∨ ∀ j, x ∈ childrenD_70 j := by decide +kernel
theorem required_exact_70 : required_70 =
    ((Finset.univ.biUnion childrenC_70) ∪ commonEnvelope childrenD_70).erase (1, 3) := by
  exact required_eq_combination childrenC_70 childrenD_70 (1, 3) required_70
    (by decide +kernel) child_required_sub_70 common_sub_70 required_origin_70
theorem envelope_origin_70 : ∀ x ∈ envelope_70,
    x = (1, 3) ∨ ∃ j, x ∈ childrenD_70 j := by decide +kernel
theorem envelope_exact_70 : envelope_70 =
    insert (1, 3) (Finset.univ.biUnion childrenD_70) := by
  exact envelope_eq_combination childrenD_70 (1, 3) envelope_70
    pivot_mem_70 child_envelope_sub_70 envelope_origin_70
def checked_70 : CheckedCard where
  required := required_70
  envelope := envelope_70
  height := height_70
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_70
def height_76 : ℕ := 2
def childrenH_76 : Fin 2 → ℕ := ![height_4, height_5]
theorem height_exact_76 : height_76 = 1 + Finset.univ.sup childrenH_76 := by decide +kernel
theorem required_origin_76 : ∀ x ∈ required_76,
    (∃ j, x ∈ childrenC_76 j) ∨ ∀ j, x ∈ childrenD_76 j := by decide +kernel
theorem required_exact_76 : required_76 =
    ((Finset.univ.biUnion childrenC_76) ∪ commonEnvelope childrenD_76).erase (1, 4) := by
  exact required_eq_combination childrenC_76 childrenD_76 (1, 4) required_76
    (by decide +kernel) child_required_sub_76 common_sub_76 required_origin_76
theorem envelope_origin_76 : ∀ x ∈ envelope_76,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_76 j := by decide +kernel
theorem envelope_exact_76 : envelope_76 =
    insert (1, 4) (Finset.univ.biUnion childrenD_76) := by
  exact envelope_eq_combination childrenD_76 (1, 4) envelope_76
    pivot_mem_76 child_envelope_sub_76 envelope_origin_76
def checked_76 : CheckedCard where
  required := required_76
  envelope := envelope_76
  height := height_76
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_76
def height_77 : ℕ := 2
def childrenH_77 : Fin 2 → ℕ := ![height_3, height_5]
theorem height_exact_77 : height_77 = 1 + Finset.univ.sup childrenH_77 := by decide +kernel
theorem required_origin_77 : ∀ x ∈ required_77,
    (∃ j, x ∈ childrenC_77 j) ∨ ∀ j, x ∈ childrenD_77 j := by decide +kernel
theorem required_exact_77 : required_77 =
    ((Finset.univ.biUnion childrenC_77) ∪ commonEnvelope childrenD_77).erase (2, 1) := by
  exact required_eq_combination childrenC_77 childrenD_77 (2, 1) required_77
    (by decide +kernel) child_required_sub_77 common_sub_77 required_origin_77
theorem envelope_origin_77 : ∀ x ∈ envelope_77,
    x = (2, 1) ∨ ∃ j, x ∈ childrenD_77 j := by decide +kernel
theorem envelope_exact_77 : envelope_77 =
    insert (2, 1) (Finset.univ.biUnion childrenD_77) := by
  exact envelope_eq_combination childrenD_77 (2, 1) envelope_77
    pivot_mem_77 child_envelope_sub_77 envelope_origin_77
def checked_77 : CheckedCard where
  required := required_77
  envelope := envelope_77
  height := height_77
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_77
def height_80 : ℕ := 2
def childrenH_80 : Fin 2 → ℕ := ![height_5, height_5]
theorem height_exact_80 : height_80 = 1 + Finset.univ.sup childrenH_80 := by decide +kernel
theorem required_origin_80 : ∀ x ∈ required_80,
    (∃ j, x ∈ childrenC_80 j) ∨ ∀ j, x ∈ childrenD_80 j := by decide +kernel
theorem required_exact_80 : required_80 =
    ((Finset.univ.biUnion childrenC_80) ∪ commonEnvelope childrenD_80).erase (1, 3) := by
  exact required_eq_combination childrenC_80 childrenD_80 (1, 3) required_80
    (by decide +kernel) child_required_sub_80 common_sub_80 required_origin_80
theorem envelope_origin_80 : ∀ x ∈ envelope_80,
    x = (1, 3) ∨ ∃ j, x ∈ childrenD_80 j := by decide +kernel
theorem envelope_exact_80 : envelope_80 =
    insert (1, 3) (Finset.univ.biUnion childrenD_80) := by
  exact envelope_eq_combination childrenD_80 (1, 3) envelope_80
    pivot_mem_80 child_envelope_sub_80 envelope_origin_80
def checked_80 : CheckedCard where
  required := required_80
  envelope := envelope_80
  height := height_80
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_80
def height_83 : ℕ := 2
def childrenH_83 : Fin 2 → ℕ := ![height_5, height_5]
theorem height_exact_83 : height_83 = 1 + Finset.univ.sup childrenH_83 := by decide +kernel
theorem required_origin_83 : ∀ x ∈ required_83,
    (∃ j, x ∈ childrenC_83 j) ∨ ∀ j, x ∈ childrenD_83 j := by decide +kernel
theorem required_exact_83 : required_83 =
    ((Finset.univ.biUnion childrenC_83) ∪ commonEnvelope childrenD_83).erase (1, 4) := by
  exact required_eq_combination childrenC_83 childrenD_83 (1, 4) required_83
    (by decide +kernel) child_required_sub_83 common_sub_83 required_origin_83
theorem envelope_origin_83 : ∀ x ∈ envelope_83,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_83 j := by decide +kernel
theorem envelope_exact_83 : envelope_83 =
    insert (1, 4) (Finset.univ.biUnion childrenD_83) := by
  exact envelope_eq_combination childrenD_83 (1, 4) envelope_83
    pivot_mem_83 child_envelope_sub_83 envelope_origin_83
def checked_83 : CheckedCard where
  required := required_83
  envelope := envelope_83
  height := height_83
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_83
def height_94 : ℕ := 2
def childrenH_94 : Fin 2 → ℕ := ![height_0, height_5]
theorem height_exact_94 : height_94 = 1 + Finset.univ.sup childrenH_94 := by decide +kernel
theorem required_origin_94 : ∀ x ∈ required_94,
    (∃ j, x ∈ childrenC_94 j) ∨ ∀ j, x ∈ childrenD_94 j := by decide +kernel
theorem required_exact_94 : required_94 =
    ((Finset.univ.biUnion childrenC_94) ∪ commonEnvelope childrenD_94).erase (0, 3) := by
  exact required_eq_combination childrenC_94 childrenD_94 (0, 3) required_94
    (by decide +kernel) child_required_sub_94 common_sub_94 required_origin_94
theorem envelope_origin_94 : ∀ x ∈ envelope_94,
    x = (0, 3) ∨ ∃ j, x ∈ childrenD_94 j := by decide +kernel
theorem envelope_exact_94 : envelope_94 =
    insert (0, 3) (Finset.univ.biUnion childrenD_94) := by
  exact envelope_eq_combination childrenD_94 (0, 3) envelope_94
    pivot_mem_94 child_envelope_sub_94 envelope_origin_94
def checked_94 : CheckedCard where
  required := required_94
  envelope := envelope_94
  height := height_94
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_94
end SnakyPrototype.Certificate21

end OAI
