import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_96 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (2, 4), (3, 1), (3, 2), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_96 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (2, 3), (2, 4), (3, 0), (3, 1), (3, 2), (3, 3), (4, 0)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_96 : Fin 2 → Finset Cell := ![(placed21 5 (3, 0) required_4), (placed21 4 (0, 1) required_5)]
def childrenD_96 : Fin 2 → Finset Cell := ![(placed21 5 (3, 0) envelope_4), (placed21 4 (0, 1) envelope_5)]
theorem common_sub_96 : commonEnvelope childrenD_96 ⊆ insert (3, 0) required_96 := by decide +kernel
theorem child_required_sub_96 : ∀ j, childrenC_96 j ⊆ insert (3, 0) required_96 := by decide +kernel
theorem child_envelope_sub_96 : ∀ j, childrenD_96 j ⊆ envelope_96 := by decide +kernel
theorem pivot_mem_96 : (3, 0) ∈ envelope_96 := by decide +kernel
theorem children_work_96 : ∀ j, Template HasSnaky 1 (childrenC_96 j) (childrenD_96 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_4 5 (3, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_5 4 (0, 1)).mono (by decide +kernel)
theorem row_works_96 : Template HasSnaky 2 required_96 envelope_96 := by
  refine compose HasSnaky 1 childrenC_96 childrenD_96 children_work_96 (3, 0)
    required_96 envelope_96 pivot_mem_96 child_required_sub_96 child_envelope_sub_96 ?_
  intro b hb
  exact common_sub_96 (mem_commonEnvelope childrenD_96 b hb)
def required_102 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 1), (1, 2), (1, 4), (2, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_102 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_102 : Fin 2 → Finset Cell := ![(placed21 7 (1, 5) required_0), (placed21 3 (1, 4) required_5)]
def childrenD_102 : Fin 2 → Finset Cell := ![(placed21 7 (1, 5) envelope_0), (placed21 3 (1, 4) envelope_5)]
theorem common_sub_102 : commonEnvelope childrenD_102 ⊆ insert (1, 3) required_102 := by decide +kernel
theorem child_required_sub_102 : ∀ j, childrenC_102 j ⊆ insert (1, 3) required_102 := by decide +kernel
theorem child_envelope_sub_102 : ∀ j, childrenD_102 j ⊆ envelope_102 := by decide +kernel
theorem pivot_mem_102 : (1, 3) ∈ envelope_102 := by decide +kernel
theorem children_work_102 : ∀ j, Template HasSnaky 1 (childrenC_102 j) (childrenD_102 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 7 (1, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_5 3 (1, 4)).mono (by decide +kernel)
theorem row_works_102 : Template HasSnaky 2 required_102 envelope_102 := by
  refine compose HasSnaky 1 childrenC_102 childrenD_102 children_work_102 (1, 3)
    required_102 envelope_102 pivot_mem_102 child_required_sub_102 child_envelope_sub_102 ?_
  intro b hb
  exact common_sub_102 (mem_commonEnvelope childrenD_102 b hb)
def required_121 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (2, 2), (2, 4), (3, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_121 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (2, 2), (2, 3), (2, 4), (3, 0), (3, 1), (4, 0)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_121 : Fin 2 → Finset Cell := ![(placed21 3 (2, 4) required_1), (placed21 4 (0, 1) required_5)]
def childrenD_121 : Fin 2 → Finset Cell := ![(placed21 3 (2, 4) envelope_1), (placed21 4 (0, 1) envelope_5)]
theorem common_sub_121 : commonEnvelope childrenD_121 ⊆ insert (3, 0) required_121 := by decide +kernel
theorem child_required_sub_121 : ∀ j, childrenC_121 j ⊆ insert (3, 0) required_121 := by decide +kernel
theorem child_envelope_sub_121 : ∀ j, childrenD_121 j ⊆ envelope_121 := by decide +kernel
theorem pivot_mem_121 : (3, 0) ∈ envelope_121 := by decide +kernel
theorem children_work_121 : ∀ j, Template HasSnaky 1 (childrenC_121 j) (childrenD_121 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_1 3 (2, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_5 4 (0, 1)).mono (by decide +kernel)
theorem row_works_121 : Template HasSnaky 2 required_121 envelope_121 := by
  refine compose HasSnaky 1 childrenC_121 childrenD_121 children_work_121 (3, 0)
    required_121 envelope_121 pivot_mem_121 child_required_sub_121 child_envelope_sub_121 ?_
  intro b hb
  exact common_sub_121 (mem_commonEnvelope childrenD_121 b hb)
def required_123 : Finset Cell := ⟨(([(0, 0), (0, 2), (1, 1), (2, 1), (3, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_123 : Finset Cell := ⟨(([(0, 0), (0, 2), (1, 0), (1, 1), (1, 2), (2, 1), (3, 1), (4, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_123 : Fin 2 → Finset Cell := ![(placed21 2 (4, 1) required_4), (placed21 6 (4, 1) required_4)]
def childrenD_123 : Fin 2 → Finset Cell := ![(placed21 2 (4, 1) envelope_4), (placed21 6 (4, 1) envelope_4)]
theorem common_sub_123 : commonEnvelope childrenD_123 ⊆ insert (4, 1) required_123 := by decide +kernel
theorem child_required_sub_123 : ∀ j, childrenC_123 j ⊆ insert (4, 1) required_123 := by decide +kernel
theorem child_envelope_sub_123 : ∀ j, childrenD_123 j ⊆ envelope_123 := by decide +kernel
theorem pivot_mem_123 : (4, 1) ∈ envelope_123 := by decide +kernel
theorem children_work_123 : ∀ j, Template HasSnaky 1 (childrenC_123 j) (childrenD_123 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_4 2 (4, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_4 6 (4, 1)).mono (by decide +kernel)
theorem row_works_123 : Template HasSnaky 2 required_123 envelope_123 := by
  refine compose HasSnaky 1 childrenC_123 childrenD_123 children_work_123 (4, 1)
    required_123 envelope_123 pivot_mem_123 child_required_sub_123 child_envelope_sub_123 ?_
  intro b hb
  exact common_sub_123 (mem_commonEnvelope childrenD_123 b hb)
def required_129 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (1, 3), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_129 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_129 : Fin 2 → Finset Cell := ![(placed21 7 (1, 5) required_0), (placed21 7 (1, 4) required_3)]
def childrenD_129 : Fin 2 → Finset Cell := ![(placed21 7 (1, 5) envelope_0), (placed21 7 (1, 4) envelope_3)]
theorem common_sub_129 : commonEnvelope childrenD_129 ⊆ insert (1, 2) required_129 := by decide +kernel
theorem child_required_sub_129 : ∀ j, childrenC_129 j ⊆ insert (1, 2) required_129 := by decide +kernel
theorem child_envelope_sub_129 : ∀ j, childrenD_129 j ⊆ envelope_129 := by decide +kernel
theorem pivot_mem_129 : (1, 2) ∈ envelope_129 := by decide +kernel
theorem children_work_129 : ∀ j, Template HasSnaky 1 (childrenC_129 j) (childrenD_129 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 7 (1, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_3 7 (1, 4)).mono (by decide +kernel)
theorem row_works_129 : Template HasSnaky 2 required_129 envelope_129 := by
  refine compose HasSnaky 1 childrenC_129 childrenD_129 children_work_129 (1, 2)
    required_129 envelope_129 pivot_mem_129 child_required_sub_129 child_envelope_sub_129 ?_
  intro b hb
  exact common_sub_129 (mem_commonEnvelope childrenD_129 b hb)
def required_138 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (1, 2), (1, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_138 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (1, 1), (1, 2), (1, 3), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_138 : Fin 2 → Finset Cell := ![(placed21 1 (0, 0) required_3), (placed21 7 (1, 4) required_3)]
def childrenD_138 : Fin 2 → Finset Cell := ![(placed21 1 (0, 0) envelope_3), (placed21 7 (1, 4) envelope_3)]
theorem common_sub_138 : commonEnvelope childrenD_138 ⊆ insert (1, 4) required_138 := by decide +kernel
theorem child_required_sub_138 : ∀ j, childrenC_138 j ⊆ insert (1, 4) required_138 := by decide +kernel
theorem child_envelope_sub_138 : ∀ j, childrenD_138 j ⊆ envelope_138 := by decide +kernel
theorem pivot_mem_138 : (1, 4) ∈ envelope_138 := by decide +kernel
theorem children_work_138 : ∀ j, Template HasSnaky 1 (childrenC_138 j) (childrenD_138 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_3 1 (0, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_3 7 (1, 4)).mono (by decide +kernel)
theorem row_works_138 : Template HasSnaky 2 required_138 envelope_138 := by
  refine compose HasSnaky 1 childrenC_138 childrenD_138 children_work_138 (1, 4)
    required_138 envelope_138 pivot_mem_138 child_required_sub_138 child_envelope_sub_138 ?_
  intro b hb
  exact common_sub_138 (mem_commonEnvelope childrenD_138 b hb)
def required_146 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 2), (1, 3), (1, 4), (3, 1), (3, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_146 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1), (3, 1), (3, 2), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_146 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) required_5), (placed21 3 (1, 4) required_5)]
def childrenD_146 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) envelope_5), (placed21 3 (1, 4) envelope_5)]
theorem common_sub_146 : commonEnvelope childrenD_146 ⊆ insert (2, 1) required_146 := by decide +kernel
theorem child_required_sub_146 : ∀ j, childrenC_146 j ⊆ insert (2, 1) required_146 := by decide +kernel
theorem child_envelope_sub_146 : ∀ j, childrenD_146 j ⊆ envelope_146 := by decide +kernel
theorem pivot_mem_146 : (2, 1) ∈ envelope_146 := by decide +kernel
theorem children_work_146 : ∀ j, Template HasSnaky 1 (childrenC_146 j) (childrenD_146 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 0 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_5 3 (1, 4)).mono (by decide +kernel)
theorem row_works_146 : Template HasSnaky 2 required_146 envelope_146 := by
  refine compose HasSnaky 1 childrenC_146 childrenD_146 children_work_146 (2, 1)
    required_146 envelope_146 pivot_mem_146 child_required_sub_146 child_envelope_sub_146 ?_
  intro b hb
  exact common_sub_146 (mem_commonEnvelope childrenD_146 b hb)
def required_153 : Finset Cell := ⟨(([(0, 0), (1, 1), (1, 2), (1, 3), (2, 3), (3, 3), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_153 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 4), (1, 1), (1, 2), (1, 3), (1, 4), (2, 3), (3, 3), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_153 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) required_4), (placed21 2 (4, 3) required_5)]
def childrenD_153 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) envelope_4), (placed21 2 (4, 3) envelope_5)]
theorem common_sub_153 : commonEnvelope childrenD_153 ⊆ insert (1, 4) required_153 := by decide +kernel
theorem child_required_sub_153 : ∀ j, childrenC_153 j ⊆ insert (1, 4) required_153 := by decide +kernel
theorem child_envelope_sub_153 : ∀ j, childrenD_153 j ⊆ envelope_153 := by decide +kernel
theorem pivot_mem_153 : (1, 4) ∈ envelope_153 := by decide +kernel
theorem children_work_153 : ∀ j, Template HasSnaky 1 (childrenC_153 j) (childrenD_153 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_4 7 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_5 2 (4, 3)).mono (by decide +kernel)
theorem row_works_153 : Template HasSnaky 2 required_153 envelope_153 := by
  refine compose HasSnaky 1 childrenC_153 childrenD_153 children_work_153 (1, 4)
    required_153 envelope_153 pivot_mem_153 child_required_sub_153 child_envelope_sub_153 ?_
  intro b hb
  exact common_sub_153 (mem_commonEnvelope childrenD_153 b hb)
def required_154 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (1, 2), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_154 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_154 : Fin 2 → Finset Cell := ![(placed21 7 (1, 5) required_0), (placed21 7 (1, 4) required_3)]
def childrenD_154 : Fin 2 → Finset Cell := ![(placed21 7 (1, 5) envelope_0), (placed21 7 (1, 4) envelope_3)]
theorem common_sub_154 : commonEnvelope childrenD_154 ⊆ insert (1, 3) required_154 := by decide +kernel
theorem child_required_sub_154 : ∀ j, childrenC_154 j ⊆ insert (1, 3) required_154 := by decide +kernel
theorem child_envelope_sub_154 : ∀ j, childrenD_154 j ⊆ envelope_154 := by decide +kernel
theorem pivot_mem_154 : (1, 3) ∈ envelope_154 := by decide +kernel
theorem children_work_154 : ∀ j, Template HasSnaky 1 (childrenC_154 j) (childrenD_154 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 7 (1, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_3 7 (1, 4)).mono (by decide +kernel)
theorem row_works_154 : Template HasSnaky 2 required_154 envelope_154 := by
  refine compose HasSnaky 1 childrenC_154 childrenD_154 children_work_154 (1, 3)
    required_154 envelope_154 pivot_mem_154 child_required_sub_154 child_envelope_sub_154 ?_
  intro b hb
  exact common_sub_154 (mem_commonEnvelope childrenD_154 b hb)
def required_156 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (2, 3), (2, 4), (3, 0)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_156 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (2, 2), (2, 3), (2, 4), (3, 0), (3, 1), (4, 0)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_156 : Fin 2 → Finset Cell := ![(placed21 3 (2, 4) required_2), (placed21 4 (0, 1) required_5)]
def childrenD_156 : Fin 2 → Finset Cell := ![(placed21 3 (2, 4) envelope_2), (placed21 4 (0, 1) envelope_5)]
theorem common_sub_156 : commonEnvelope childrenD_156 ⊆ insert (3, 1) required_156 := by decide +kernel
theorem child_required_sub_156 : ∀ j, childrenC_156 j ⊆ insert (3, 1) required_156 := by decide +kernel
theorem child_envelope_sub_156 : ∀ j, childrenD_156 j ⊆ envelope_156 := by decide +kernel
theorem pivot_mem_156 : (3, 1) ∈ envelope_156 := by decide +kernel
theorem children_work_156 : ∀ j, Template HasSnaky 1 (childrenC_156 j) (childrenD_156 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_2 3 (2, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_5 4 (0, 1)).mono (by decide +kernel)
theorem row_works_156 : Template HasSnaky 2 required_156 envelope_156 := by
  refine compose HasSnaky 1 childrenC_156 childrenD_156 children_work_156 (3, 1)
    required_156 envelope_156 pivot_mem_156 child_required_sub_156 child_envelope_sub_156 ?_
  intro b hb
  exact common_sub_156 (mem_commonEnvelope childrenD_156 b hb)
def required_169 : Finset Cell := ⟨(([(0, 0), (0, 2), (0, 3), (1, 3), (1, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_169 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (1, 3), (1, 4), (1, 5), (1, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_169 : Fin 2 → Finset Cell := ![(placed21 1 (0, 0) required_1), (placed21 7 (1, 6) required_1)]
def childrenD_169 : Fin 2 → Finset Cell := ![(placed21 1 (0, 0) envelope_1), (placed21 7 (1, 6) envelope_1)]
theorem common_sub_169 : commonEnvelope childrenD_169 ⊆ insert (1, 4) required_169 := by decide +kernel
theorem child_required_sub_169 : ∀ j, childrenC_169 j ⊆ insert (1, 4) required_169 := by decide +kernel
theorem child_envelope_sub_169 : ∀ j, childrenD_169 j ⊆ envelope_169 := by decide +kernel
theorem pivot_mem_169 : (1, 4) ∈ envelope_169 := by decide +kernel
theorem children_work_169 : ∀ j, Template HasSnaky 1 (childrenC_169 j) (childrenD_169 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_1 1 (0, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_1 7 (1, 6)).mono (by decide +kernel)
theorem row_works_169 : Template HasSnaky 2 required_169 envelope_169 := by
  refine compose HasSnaky 1 childrenC_169 childrenD_169 children_work_169 (1, 4)
    required_169 envelope_169 pivot_mem_169 child_required_sub_169 child_envelope_sub_169 ?_
  intro b hb
  exact common_sub_169 (mem_commonEnvelope childrenD_169 b hb)
def required_170 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 3), (1, 3), (1, 4), (3, 2), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_170 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 3), (1, 1), (1, 2), (1, 3), (1, 4), (2, 2), (3, 2), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_170 : Fin 2 → Finset Cell := ![(placed21 2 (4, 2) required_2), (placed21 7 (1, 4) required_3)]
def childrenD_170 : Fin 2 → Finset Cell := ![(placed21 2 (4, 2) envelope_2), (placed21 7 (1, 4) envelope_3)]
theorem common_sub_170 : commonEnvelope childrenD_170 ⊆ insert (1, 2) required_170 := by decide +kernel
theorem child_required_sub_170 : ∀ j, childrenC_170 j ⊆ insert (1, 2) required_170 := by decide +kernel
theorem child_envelope_sub_170 : ∀ j, childrenD_170 j ⊆ envelope_170 := by decide +kernel
theorem pivot_mem_170 : (1, 2) ∈ envelope_170 := by decide +kernel
theorem children_work_170 : ∀ j, Template HasSnaky 1 (childrenC_170 j) (childrenD_170 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_2 2 (4, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_3 7 (1, 4)).mono (by decide +kernel)
theorem row_works_170 : Template HasSnaky 2 required_170 envelope_170 := by
  refine compose HasSnaky 1 childrenC_170 childrenD_170 children_work_170 (1, 2)
    required_170 envelope_170 pivot_mem_170 child_required_sub_170 child_envelope_sub_170 ?_
  intro b hb
  exact common_sub_170 (mem_commonEnvelope childrenD_170 b hb)
def required_200 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (1, 2), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_200 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (1, 1), (1, 2), (1, 3), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_200 : Fin 2 → Finset Cell := ![(placed21 1 (0, 0) required_3), (placed21 7 (1, 4) required_3)]
def childrenD_200 : Fin 2 → Finset Cell := ![(placed21 1 (0, 0) envelope_3), (placed21 7 (1, 4) envelope_3)]
theorem common_sub_200 : commonEnvelope childrenD_200 ⊆ insert (1, 3) required_200 := by decide +kernel
theorem child_required_sub_200 : ∀ j, childrenC_200 j ⊆ insert (1, 3) required_200 := by decide +kernel
theorem child_envelope_sub_200 : ∀ j, childrenD_200 j ⊆ envelope_200 := by decide +kernel
theorem pivot_mem_200 : (1, 3) ∈ envelope_200 := by decide +kernel
theorem children_work_200 : ∀ j, Template HasSnaky 1 (childrenC_200 j) (childrenD_200 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_3 1 (0, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_3 7 (1, 4)).mono (by decide +kernel)
theorem row_works_200 : Template HasSnaky 2 required_200 envelope_200 := by
  refine compose HasSnaky 1 childrenC_200 childrenD_200 children_work_200 (1, 3)
    required_200 envelope_200 pivot_mem_200 child_required_sub_200 child_envelope_sub_200 ?_
  intro b hb
  exact common_sub_200 (mem_commonEnvelope childrenD_200 b hb)
def required_210 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 2), (1, 4), (2, 1), (3, 1), (4, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_210 : Finset Cell := ⟨(([(0, 0), (0, 1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, 1), (3, 1), (4, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_210 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) required_1), (placed21 6 (4, 1) required_4)]
def childrenD_210 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) envelope_1), (placed21 6 (4, 1) envelope_4)]
theorem common_sub_210 : commonEnvelope childrenD_210 ⊆ insert (0, 0) required_210 := by decide +kernel
theorem child_required_sub_210 : ∀ j, childrenC_210 j ⊆ insert (0, 0) required_210 := by decide +kernel
theorem child_envelope_sub_210 : ∀ j, childrenD_210 j ⊆ envelope_210 := by decide +kernel
theorem pivot_mem_210 : (0, 0) ∈ envelope_210 := by decide +kernel
theorem children_work_210 : ∀ j, Template HasSnaky 1 (childrenC_210 j) (childrenD_210 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_1 7 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_4 6 (4, 1)).mono (by decide +kernel)
theorem row_works_210 : Template HasSnaky 2 required_210 envelope_210 := by
  refine compose HasSnaky 1 childrenC_210 childrenD_210 children_work_210 (0, 0)
    required_210 envelope_210 pivot_mem_210 child_required_sub_210 child_envelope_sub_210 ?_
  intro b hb
  exact common_sub_210 (mem_commonEnvelope childrenD_210 b hb)
def required_220 : Finset Cell := ⟨(([(0, 2), (1, 1), (1, 2), (2, 1), (2, 2), (2, 3), (2, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_220 : Finset Cell := ⟨(([(0, 2), (1, 1), (1, 2), (2, 1), (2, 2), (2, 3), (2, 4), (3, 0), (3, 1), (4, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_220 : Fin 2 → Finset Cell := ![(placed21 2 (4, 1) required_0), (placed21 3 (2, 4) required_5)]
def childrenD_220 : Fin 2 → Finset Cell := ![(placed21 2 (4, 1) envelope_0), (placed21 3 (2, 4) envelope_5)]
theorem common_sub_220 : commonEnvelope childrenD_220 ⊆ insert (3, 1) required_220 := by decide +kernel
theorem child_required_sub_220 : ∀ j, childrenC_220 j ⊆ insert (3, 1) required_220 := by decide +kernel
theorem child_envelope_sub_220 : ∀ j, childrenD_220 j ⊆ envelope_220 := by decide +kernel
theorem pivot_mem_220 : (3, 1) ∈ envelope_220 := by decide +kernel
theorem children_work_220 : ∀ j, Template HasSnaky 1 (childrenC_220 j) (childrenD_220 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 2 (4, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_5 3 (2, 4)).mono (by decide +kernel)
theorem row_works_220 : Template HasSnaky 2 required_220 envelope_220 := by
  refine compose HasSnaky 1 childrenC_220 childrenD_220 children_work_220 (3, 1)
    required_220 envelope_220 pivot_mem_220 child_required_sub_220 child_envelope_sub_220 ?_
  intro b hb
  exact common_sub_220 (mem_commonEnvelope childrenD_220 b hb)
def required_224 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (3, 2), (3, 3), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_224 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 0), (2, 1), (3, 1), (3, 2), (3, 3), (3, 4), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_224 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) required_5), (placed21 7 (3, 4) required_5)]
def childrenD_224 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) envelope_5), (placed21 7 (3, 4) envelope_5)]
theorem common_sub_224 : commonEnvelope childrenD_224 ⊆ insert (3, 1) required_224 := by decide +kernel
theorem child_required_sub_224 : ∀ j, childrenC_224 j ⊆ insert (3, 1) required_224 := by decide +kernel
theorem child_envelope_sub_224 : ∀ j, childrenD_224 j ⊆ envelope_224 := by decide +kernel
theorem pivot_mem_224 : (3, 1) ∈ envelope_224 := by decide +kernel
theorem children_work_224 : ∀ j, Template HasSnaky 1 (childrenC_224 j) (childrenD_224 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 0 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_5 7 (3, 4)).mono (by decide +kernel)
theorem row_works_224 : Template HasSnaky 2 required_224 envelope_224 := by
  refine compose HasSnaky 1 childrenC_224 childrenD_224 children_work_224 (3, 1)
    required_224 envelope_224 pivot_mem_224 child_required_sub_224 child_envelope_sub_224 ?_
  intro b hb
  exact common_sub_224 (mem_commonEnvelope childrenD_224 b hb)
def required_244 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 2), (1, 3), (2, 3), (3, 3), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_244 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 4), (1, 1), (1, 2), (1, 3), (1, 4), (2, 3), (3, 3), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_244 : Fin 2 → Finset Cell := ![(placed21 2 (4, 3) required_5), (placed21 7 (1, 4) required_5)]
def childrenD_244 : Fin 2 → Finset Cell := ![(placed21 2 (4, 3) envelope_5), (placed21 7 (1, 4) envelope_5)]
theorem common_sub_244 : commonEnvelope childrenD_244 ⊆ insert (1, 4) required_244 := by decide +kernel
theorem child_required_sub_244 : ∀ j, childrenC_244 j ⊆ insert (1, 4) required_244 := by decide +kernel
theorem child_envelope_sub_244 : ∀ j, childrenD_244 j ⊆ envelope_244 := by decide +kernel
theorem pivot_mem_244 : (1, 4) ∈ envelope_244 := by decide +kernel
theorem children_work_244 : ∀ j, Template HasSnaky 1 (childrenC_244 j) (childrenD_244 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 2 (4, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_5 7 (1, 4)).mono (by decide +kernel)
theorem row_works_244 : Template HasSnaky 2 required_244 envelope_244 := by
  refine compose HasSnaky 1 childrenC_244 childrenD_244 children_work_244 (1, 4)
    required_244 envelope_244 pivot_mem_244 child_required_sub_244 child_envelope_sub_244 ?_
  intro b hb
  exact common_sub_244 (mem_commonEnvelope childrenD_244 b hb)
def required_281 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 4), (1, 4), (3, 3), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_281 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 3), (1, 4), (2, 3), (3, 3), (4, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_281 : Fin 2 → Finset Cell := ![(placed21 2 (4, 3) required_2), (placed21 1 (0, 0) required_3)]
def childrenD_281 : Fin 2 → Finset Cell := ![(placed21 2 (4, 3) envelope_2), (placed21 1 (0, 0) envelope_3)]
theorem common_sub_281 : commonEnvelope childrenD_281 ⊆ insert (1, 3) required_281 := by decide +kernel
theorem child_required_sub_281 : ∀ j, childrenC_281 j ⊆ insert (1, 3) required_281 := by decide +kernel
theorem child_envelope_sub_281 : ∀ j, childrenD_281 j ⊆ envelope_281 := by decide +kernel
theorem pivot_mem_281 : (1, 3) ∈ envelope_281 := by decide +kernel
theorem children_work_281 : ∀ j, Template HasSnaky 1 (childrenC_281 j) (childrenD_281 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_2 2 (4, 3)).mono (by decide +kernel)
  · exact (placed21_template row_works_3 1 (0, 0)).mono (by decide +kernel)
theorem row_works_281 : Template HasSnaky 2 required_281 envelope_281 := by
  refine compose HasSnaky 1 childrenC_281 childrenD_281 children_work_281 (1, 3)
    required_281 envelope_281 pivot_mem_281 child_required_sub_281 child_envelope_sub_281 ?_
  intro b hb
  exact common_sub_281 (mem_commonEnvelope childrenD_281 b hb)
def height_96 : ℕ := 2
def childrenH_96 : Fin 2 → ℕ := ![height_4, height_5]
theorem height_exact_96 : height_96 = 1 + Finset.univ.sup childrenH_96 := by decide +kernel
theorem required_origin_96 : ∀ x ∈ required_96,
    (∃ j, x ∈ childrenC_96 j) ∨ ∀ j, x ∈ childrenD_96 j := by decide +kernel
theorem required_exact_96 : required_96 =
    ((Finset.univ.biUnion childrenC_96) ∪ commonEnvelope childrenD_96).erase (3, 0) := by
  exact required_eq_combination childrenC_96 childrenD_96 (3, 0) required_96
    (by decide +kernel) child_required_sub_96 common_sub_96 required_origin_96
theorem envelope_origin_96 : ∀ x ∈ envelope_96,
    x = (3, 0) ∨ ∃ j, x ∈ childrenD_96 j := by decide +kernel
theorem envelope_exact_96 : envelope_96 =
    insert (3, 0) (Finset.univ.biUnion childrenD_96) := by
  exact envelope_eq_combination childrenD_96 (3, 0) envelope_96
    pivot_mem_96 child_envelope_sub_96 envelope_origin_96
def checked_96 : CheckedCard where
  required := required_96
  envelope := envelope_96
  height := height_96
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_96
def height_102 : ℕ := 2
def childrenH_102 : Fin 2 → ℕ := ![height_0, height_5]
theorem height_exact_102 : height_102 = 1 + Finset.univ.sup childrenH_102 := by decide +kernel
theorem required_origin_102 : ∀ x ∈ required_102,
    (∃ j, x ∈ childrenC_102 j) ∨ ∀ j, x ∈ childrenD_102 j := by decide +kernel
theorem required_exact_102 : required_102 =
    ((Finset.univ.biUnion childrenC_102) ∪ commonEnvelope childrenD_102).erase (1, 3) := by
  exact required_eq_combination childrenC_102 childrenD_102 (1, 3) required_102
    (by decide +kernel) child_required_sub_102 common_sub_102 required_origin_102
theorem envelope_origin_102 : ∀ x ∈ envelope_102,
    x = (1, 3) ∨ ∃ j, x ∈ childrenD_102 j := by decide +kernel
theorem envelope_exact_102 : envelope_102 =
    insert (1, 3) (Finset.univ.biUnion childrenD_102) := by
  exact envelope_eq_combination childrenD_102 (1, 3) envelope_102
    pivot_mem_102 child_envelope_sub_102 envelope_origin_102
def checked_102 : CheckedCard where
  required := required_102
  envelope := envelope_102
  height := height_102
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_102
def height_121 : ℕ := 2
def childrenH_121 : Fin 2 → ℕ := ![height_1, height_5]
theorem height_exact_121 : height_121 = 1 + Finset.univ.sup childrenH_121 := by decide +kernel
theorem required_origin_121 : ∀ x ∈ required_121,
    (∃ j, x ∈ childrenC_121 j) ∨ ∀ j, x ∈ childrenD_121 j := by decide +kernel
theorem required_exact_121 : required_121 =
    ((Finset.univ.biUnion childrenC_121) ∪ commonEnvelope childrenD_121).erase (3, 0) := by
  exact required_eq_combination childrenC_121 childrenD_121 (3, 0) required_121
    (by decide +kernel) child_required_sub_121 common_sub_121 required_origin_121
theorem envelope_origin_121 : ∀ x ∈ envelope_121,
    x = (3, 0) ∨ ∃ j, x ∈ childrenD_121 j := by decide +kernel
theorem envelope_exact_121 : envelope_121 =
    insert (3, 0) (Finset.univ.biUnion childrenD_121) := by
  exact envelope_eq_combination childrenD_121 (3, 0) envelope_121
    pivot_mem_121 child_envelope_sub_121 envelope_origin_121
def checked_121 : CheckedCard where
  required := required_121
  envelope := envelope_121
  height := height_121
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_121
def height_123 : ℕ := 2
def childrenH_123 : Fin 2 → ℕ := ![height_4, height_4]
theorem height_exact_123 : height_123 = 1 + Finset.univ.sup childrenH_123 := by decide +kernel
theorem required_origin_123 : ∀ x ∈ required_123,
    (∃ j, x ∈ childrenC_123 j) ∨ ∀ j, x ∈ childrenD_123 j := by decide +kernel
theorem required_exact_123 : required_123 =
    ((Finset.univ.biUnion childrenC_123) ∪ commonEnvelope childrenD_123).erase (4, 1) := by
  exact required_eq_combination childrenC_123 childrenD_123 (4, 1) required_123
    (by decide +kernel) child_required_sub_123 common_sub_123 required_origin_123
theorem envelope_origin_123 : ∀ x ∈ envelope_123,
    x = (4, 1) ∨ ∃ j, x ∈ childrenD_123 j := by decide +kernel
theorem envelope_exact_123 : envelope_123 =
    insert (4, 1) (Finset.univ.biUnion childrenD_123) := by
  exact envelope_eq_combination childrenD_123 (4, 1) envelope_123
    pivot_mem_123 child_envelope_sub_123 envelope_origin_123
def checked_123 : CheckedCard where
  required := required_123
  envelope := envelope_123
  height := height_123
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_123
def height_129 : ℕ := 2
def childrenH_129 : Fin 2 → ℕ := ![height_0, height_3]
theorem height_exact_129 : height_129 = 1 + Finset.univ.sup childrenH_129 := by decide +kernel
theorem required_origin_129 : ∀ x ∈ required_129,
    (∃ j, x ∈ childrenC_129 j) ∨ ∀ j, x ∈ childrenD_129 j := by decide +kernel
theorem required_exact_129 : required_129 =
    ((Finset.univ.biUnion childrenC_129) ∪ commonEnvelope childrenD_129).erase (1, 2) := by
  exact required_eq_combination childrenC_129 childrenD_129 (1, 2) required_129
    (by decide +kernel) child_required_sub_129 common_sub_129 required_origin_129
theorem envelope_origin_129 : ∀ x ∈ envelope_129,
    x = (1, 2) ∨ ∃ j, x ∈ childrenD_129 j := by decide +kernel
theorem envelope_exact_129 : envelope_129 =
    insert (1, 2) (Finset.univ.biUnion childrenD_129) := by
  exact envelope_eq_combination childrenD_129 (1, 2) envelope_129
    pivot_mem_129 child_envelope_sub_129 envelope_origin_129
def checked_129 : CheckedCard where
  required := required_129
  envelope := envelope_129
  height := height_129
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_129
def height_138 : ℕ := 2
def childrenH_138 : Fin 2 → ℕ := ![height_3, height_3]
theorem height_exact_138 : height_138 = 1 + Finset.univ.sup childrenH_138 := by decide +kernel
theorem required_origin_138 : ∀ x ∈ required_138,
    (∃ j, x ∈ childrenC_138 j) ∨ ∀ j, x ∈ childrenD_138 j := by decide +kernel
theorem required_exact_138 : required_138 =
    ((Finset.univ.biUnion childrenC_138) ∪ commonEnvelope childrenD_138).erase (1, 4) := by
  exact required_eq_combination childrenC_138 childrenD_138 (1, 4) required_138
    (by decide +kernel) child_required_sub_138 common_sub_138 required_origin_138
theorem envelope_origin_138 : ∀ x ∈ envelope_138,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_138 j := by decide +kernel
theorem envelope_exact_138 : envelope_138 =
    insert (1, 4) (Finset.univ.biUnion childrenD_138) := by
  exact envelope_eq_combination childrenD_138 (1, 4) envelope_138
    pivot_mem_138 child_envelope_sub_138 envelope_origin_138
def checked_138 : CheckedCard where
  required := required_138
  envelope := envelope_138
  height := height_138
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_138
def height_146 : ℕ := 2
def childrenH_146 : Fin 2 → ℕ := ![height_5, height_5]
theorem height_exact_146 : height_146 = 1 + Finset.univ.sup childrenH_146 := by decide +kernel
theorem required_origin_146 : ∀ x ∈ required_146,
    (∃ j, x ∈ childrenC_146 j) ∨ ∀ j, x ∈ childrenD_146 j := by decide +kernel
theorem required_exact_146 : required_146 =
    ((Finset.univ.biUnion childrenC_146) ∪ commonEnvelope childrenD_146).erase (2, 1) := by
  exact required_eq_combination childrenC_146 childrenD_146 (2, 1) required_146
    (by decide +kernel) child_required_sub_146 common_sub_146 required_origin_146
theorem envelope_origin_146 : ∀ x ∈ envelope_146,
    x = (2, 1) ∨ ∃ j, x ∈ childrenD_146 j := by decide +kernel
theorem envelope_exact_146 : envelope_146 =
    insert (2, 1) (Finset.univ.biUnion childrenD_146) := by
  exact envelope_eq_combination childrenD_146 (2, 1) envelope_146
    pivot_mem_146 child_envelope_sub_146 envelope_origin_146
def checked_146 : CheckedCard where
  required := required_146
  envelope := envelope_146
  height := height_146
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_146
def height_153 : ℕ := 2
def childrenH_153 : Fin 2 → ℕ := ![height_4, height_5]
theorem height_exact_153 : height_153 = 1 + Finset.univ.sup childrenH_153 := by decide +kernel
theorem required_origin_153 : ∀ x ∈ required_153,
    (∃ j, x ∈ childrenC_153 j) ∨ ∀ j, x ∈ childrenD_153 j := by decide +kernel
theorem required_exact_153 : required_153 =
    ((Finset.univ.biUnion childrenC_153) ∪ commonEnvelope childrenD_153).erase (1, 4) := by
  exact required_eq_combination childrenC_153 childrenD_153 (1, 4) required_153
    (by decide +kernel) child_required_sub_153 common_sub_153 required_origin_153
theorem envelope_origin_153 : ∀ x ∈ envelope_153,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_153 j := by decide +kernel
theorem envelope_exact_153 : envelope_153 =
    insert (1, 4) (Finset.univ.biUnion childrenD_153) := by
  exact envelope_eq_combination childrenD_153 (1, 4) envelope_153
    pivot_mem_153 child_envelope_sub_153 envelope_origin_153
def checked_153 : CheckedCard where
  required := required_153
  envelope := envelope_153
  height := height_153
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_153
def height_154 : ℕ := 2
def childrenH_154 : Fin 2 → ℕ := ![height_0, height_3]
theorem height_exact_154 : height_154 = 1 + Finset.univ.sup childrenH_154 := by decide +kernel
theorem required_origin_154 : ∀ x ∈ required_154,
    (∃ j, x ∈ childrenC_154 j) ∨ ∀ j, x ∈ childrenD_154 j := by decide +kernel
theorem required_exact_154 : required_154 =
    ((Finset.univ.biUnion childrenC_154) ∪ commonEnvelope childrenD_154).erase (1, 3) := by
  exact required_eq_combination childrenC_154 childrenD_154 (1, 3) required_154
    (by decide +kernel) child_required_sub_154 common_sub_154 required_origin_154
theorem envelope_origin_154 : ∀ x ∈ envelope_154,
    x = (1, 3) ∨ ∃ j, x ∈ childrenD_154 j := by decide +kernel
theorem envelope_exact_154 : envelope_154 =
    insert (1, 3) (Finset.univ.biUnion childrenD_154) := by
  exact envelope_eq_combination childrenD_154 (1, 3) envelope_154
    pivot_mem_154 child_envelope_sub_154 envelope_origin_154
def checked_154 : CheckedCard where
  required := required_154
  envelope := envelope_154
  height := height_154
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_154
def height_156 : ℕ := 2
def childrenH_156 : Fin 2 → ℕ := ![height_2, height_5]
theorem height_exact_156 : height_156 = 1 + Finset.univ.sup childrenH_156 := by decide +kernel
theorem required_origin_156 : ∀ x ∈ required_156,
    (∃ j, x ∈ childrenC_156 j) ∨ ∀ j, x ∈ childrenD_156 j := by decide +kernel
theorem required_exact_156 : required_156 =
    ((Finset.univ.biUnion childrenC_156) ∪ commonEnvelope childrenD_156).erase (3, 1) := by
  exact required_eq_combination childrenC_156 childrenD_156 (3, 1) required_156
    (by decide +kernel) child_required_sub_156 common_sub_156 required_origin_156
theorem envelope_origin_156 : ∀ x ∈ envelope_156,
    x = (3, 1) ∨ ∃ j, x ∈ childrenD_156 j := by decide +kernel
theorem envelope_exact_156 : envelope_156 =
    insert (3, 1) (Finset.univ.biUnion childrenD_156) := by
  exact envelope_eq_combination childrenD_156 (3, 1) envelope_156
    pivot_mem_156 child_envelope_sub_156 envelope_origin_156
def checked_156 : CheckedCard where
  required := required_156
  envelope := envelope_156
  height := height_156
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_156
def height_169 : ℕ := 2
def childrenH_169 : Fin 2 → ℕ := ![height_1, height_1]
theorem height_exact_169 : height_169 = 1 + Finset.univ.sup childrenH_169 := by decide +kernel
theorem required_origin_169 : ∀ x ∈ required_169,
    (∃ j, x ∈ childrenC_169 j) ∨ ∀ j, x ∈ childrenD_169 j := by decide +kernel
theorem required_exact_169 : required_169 =
    ((Finset.univ.biUnion childrenC_169) ∪ commonEnvelope childrenD_169).erase (1, 4) := by
  exact required_eq_combination childrenC_169 childrenD_169 (1, 4) required_169
    (by decide +kernel) child_required_sub_169 common_sub_169 required_origin_169
theorem envelope_origin_169 : ∀ x ∈ envelope_169,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_169 j := by decide +kernel
theorem envelope_exact_169 : envelope_169 =
    insert (1, 4) (Finset.univ.biUnion childrenD_169) := by
  exact envelope_eq_combination childrenD_169 (1, 4) envelope_169
    pivot_mem_169 child_envelope_sub_169 envelope_origin_169
def checked_169 : CheckedCard where
  required := required_169
  envelope := envelope_169
  height := height_169
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_169
def height_170 : ℕ := 2
def childrenH_170 : Fin 2 → ℕ := ![height_2, height_3]
theorem height_exact_170 : height_170 = 1 + Finset.univ.sup childrenH_170 := by decide +kernel
theorem required_origin_170 : ∀ x ∈ required_170,
    (∃ j, x ∈ childrenC_170 j) ∨ ∀ j, x ∈ childrenD_170 j := by decide +kernel
theorem required_exact_170 : required_170 =
    ((Finset.univ.biUnion childrenC_170) ∪ commonEnvelope childrenD_170).erase (1, 2) := by
  exact required_eq_combination childrenC_170 childrenD_170 (1, 2) required_170
    (by decide +kernel) child_required_sub_170 common_sub_170 required_origin_170
theorem envelope_origin_170 : ∀ x ∈ envelope_170,
    x = (1, 2) ∨ ∃ j, x ∈ childrenD_170 j := by decide +kernel
theorem envelope_exact_170 : envelope_170 =
    insert (1, 2) (Finset.univ.biUnion childrenD_170) := by
  exact envelope_eq_combination childrenD_170 (1, 2) envelope_170
    pivot_mem_170 child_envelope_sub_170 envelope_origin_170
def checked_170 : CheckedCard where
  required := required_170
  envelope := envelope_170
  height := height_170
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_170
def height_200 : ℕ := 2
def childrenH_200 : Fin 2 → ℕ := ![height_3, height_3]
theorem height_exact_200 : height_200 = 1 + Finset.univ.sup childrenH_200 := by decide +kernel
theorem required_origin_200 : ∀ x ∈ required_200,
    (∃ j, x ∈ childrenC_200 j) ∨ ∀ j, x ∈ childrenD_200 j := by decide +kernel
theorem required_exact_200 : required_200 =
    ((Finset.univ.biUnion childrenC_200) ∪ commonEnvelope childrenD_200).erase (1, 3) := by
  exact required_eq_combination childrenC_200 childrenD_200 (1, 3) required_200
    (by decide +kernel) child_required_sub_200 common_sub_200 required_origin_200
theorem envelope_origin_200 : ∀ x ∈ envelope_200,
    x = (1, 3) ∨ ∃ j, x ∈ childrenD_200 j := by decide +kernel
theorem envelope_exact_200 : envelope_200 =
    insert (1, 3) (Finset.univ.biUnion childrenD_200) := by
  exact envelope_eq_combination childrenD_200 (1, 3) envelope_200
    pivot_mem_200 child_envelope_sub_200 envelope_origin_200
def checked_200 : CheckedCard where
  required := required_200
  envelope := envelope_200
  height := height_200
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_200
def height_210 : ℕ := 2
def childrenH_210 : Fin 2 → ℕ := ![height_1, height_4]
theorem height_exact_210 : height_210 = 1 + Finset.univ.sup childrenH_210 := by decide +kernel
theorem required_origin_210 : ∀ x ∈ required_210,
    (∃ j, x ∈ childrenC_210 j) ∨ ∀ j, x ∈ childrenD_210 j := by decide +kernel
theorem required_exact_210 : required_210 =
    ((Finset.univ.biUnion childrenC_210) ∪ commonEnvelope childrenD_210).erase (0, 0) := by
  exact required_eq_combination childrenC_210 childrenD_210 (0, 0) required_210
    (by decide +kernel) child_required_sub_210 common_sub_210 required_origin_210
theorem envelope_origin_210 : ∀ x ∈ envelope_210,
    x = (0, 0) ∨ ∃ j, x ∈ childrenD_210 j := by decide +kernel
theorem envelope_exact_210 : envelope_210 =
    insert (0, 0) (Finset.univ.biUnion childrenD_210) := by
  exact envelope_eq_combination childrenD_210 (0, 0) envelope_210
    pivot_mem_210 child_envelope_sub_210 envelope_origin_210
def checked_210 : CheckedCard where
  required := required_210
  envelope := envelope_210
  height := height_210
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_210
def height_220 : ℕ := 2
def childrenH_220 : Fin 2 → ℕ := ![height_0, height_5]
theorem height_exact_220 : height_220 = 1 + Finset.univ.sup childrenH_220 := by decide +kernel
theorem required_origin_220 : ∀ x ∈ required_220,
    (∃ j, x ∈ childrenC_220 j) ∨ ∀ j, x ∈ childrenD_220 j := by decide +kernel
theorem required_exact_220 : required_220 =
    ((Finset.univ.biUnion childrenC_220) ∪ commonEnvelope childrenD_220).erase (3, 1) := by
  exact required_eq_combination childrenC_220 childrenD_220 (3, 1) required_220
    (by decide +kernel) child_required_sub_220 common_sub_220 required_origin_220
theorem envelope_origin_220 : ∀ x ∈ envelope_220,
    x = (3, 1) ∨ ∃ j, x ∈ childrenD_220 j := by decide +kernel
theorem envelope_exact_220 : envelope_220 =
    insert (3, 1) (Finset.univ.biUnion childrenD_220) := by
  exact envelope_eq_combination childrenD_220 (3, 1) envelope_220
    pivot_mem_220 child_envelope_sub_220 envelope_origin_220
def checked_220 : CheckedCard where
  required := required_220
  envelope := envelope_220
  height := height_220
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_220
def height_224 : ℕ := 2
def childrenH_224 : Fin 2 → ℕ := ![height_5, height_5]
theorem height_exact_224 : height_224 = 1 + Finset.univ.sup childrenH_224 := by decide +kernel
theorem required_origin_224 : ∀ x ∈ required_224,
    (∃ j, x ∈ childrenC_224 j) ∨ ∀ j, x ∈ childrenD_224 j := by decide +kernel
theorem required_exact_224 : required_224 =
    ((Finset.univ.biUnion childrenC_224) ∪ commonEnvelope childrenD_224).erase (3, 1) := by
  exact required_eq_combination childrenC_224 childrenD_224 (3, 1) required_224
    (by decide +kernel) child_required_sub_224 common_sub_224 required_origin_224
theorem envelope_origin_224 : ∀ x ∈ envelope_224,
    x = (3, 1) ∨ ∃ j, x ∈ childrenD_224 j := by decide +kernel
theorem envelope_exact_224 : envelope_224 =
    insert (3, 1) (Finset.univ.biUnion childrenD_224) := by
  exact envelope_eq_combination childrenD_224 (3, 1) envelope_224
    pivot_mem_224 child_envelope_sub_224 envelope_origin_224
def checked_224 : CheckedCard where
  required := required_224
  envelope := envelope_224
  height := height_224
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_224
def height_244 : ℕ := 2
def childrenH_244 : Fin 2 → ℕ := ![height_5, height_5]
theorem height_exact_244 : height_244 = 1 + Finset.univ.sup childrenH_244 := by decide +kernel
theorem required_origin_244 : ∀ x ∈ required_244,
    (∃ j, x ∈ childrenC_244 j) ∨ ∀ j, x ∈ childrenD_244 j := by decide +kernel
theorem required_exact_244 : required_244 =
    ((Finset.univ.biUnion childrenC_244) ∪ commonEnvelope childrenD_244).erase (1, 4) := by
  exact required_eq_combination childrenC_244 childrenD_244 (1, 4) required_244
    (by decide +kernel) child_required_sub_244 common_sub_244 required_origin_244
theorem envelope_origin_244 : ∀ x ∈ envelope_244,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_244 j := by decide +kernel
theorem envelope_exact_244 : envelope_244 =
    insert (1, 4) (Finset.univ.biUnion childrenD_244) := by
  exact envelope_eq_combination childrenD_244 (1, 4) envelope_244
    pivot_mem_244 child_envelope_sub_244 envelope_origin_244
def checked_244 : CheckedCard where
  required := required_244
  envelope := envelope_244
  height := height_244
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_244
def height_281 : ℕ := 2
def childrenH_281 : Fin 2 → ℕ := ![height_2, height_3]
theorem height_exact_281 : height_281 = 1 + Finset.univ.sup childrenH_281 := by decide +kernel
theorem required_origin_281 : ∀ x ∈ required_281,
    (∃ j, x ∈ childrenC_281 j) ∨ ∀ j, x ∈ childrenD_281 j := by decide +kernel
theorem required_exact_281 : required_281 =
    ((Finset.univ.biUnion childrenC_281) ∪ commonEnvelope childrenD_281).erase (1, 3) := by
  exact required_eq_combination childrenC_281 childrenD_281 (1, 3) required_281
    (by decide +kernel) child_required_sub_281 common_sub_281 required_origin_281
theorem envelope_origin_281 : ∀ x ∈ envelope_281,
    x = (1, 3) ∨ ∃ j, x ∈ childrenD_281 j := by decide +kernel
theorem envelope_exact_281 : envelope_281 =
    insert (1, 3) (Finset.univ.biUnion childrenD_281) := by
  exact envelope_eq_combination childrenD_281 (1, 3) envelope_281
    pivot_mem_281 child_envelope_sub_281 envelope_origin_281
def checked_281 : CheckedCard where
  required := required_281
  envelope := envelope_281
  height := height_281
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_281
end SnakyPrototype.Certificate21

end OAI
