import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part02
import OAI.GameTheory.SnakyTwentyOne.Certificate.Operations
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game

namespace OAI

namespace SnakyPrototype.Certificate21
def required_108 : Finset Cell := ⟨(([(1, 2), (1, 3), (2, 2), (2, 3), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_108 : Finset Cell := ⟨(([(0, 1), (1, 0), (1, 1), (1, 2), (1, 3), (2, 2), (2, 3), (2, 4), (2, 5), (3, 2), (4, 2), (5, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_108 : Fin 2 → Finset Cell := ![(placed21 0 (1, 0) required_15), (placed21 3 (0, 3) required_102)]
def childrenD_108 : Fin 2 → Finset Cell := ![(placed21 0 (1, 0) envelope_15), (placed21 3 (0, 3) envelope_102)]
theorem common_sub_108 : commonEnvelope childrenD_108 ⊆ insert (1, 1) required_108 := by decide +kernel
theorem child_required_sub_108 : ∀ j, childrenC_108 j ⊆ insert (1, 1) required_108 := by decide +kernel
theorem child_envelope_sub_108 : ∀ j, childrenD_108 j ⊆ envelope_108 := by decide +kernel
theorem pivot_mem_108 : (1, 1) ∈ envelope_108 := by decide +kernel
theorem children_work_108 : ∀ j, Template HasSnaky 2 (childrenC_108 j) (childrenD_108 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_15 0 (1, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_102 3 (0, 3)).mono (by decide +kernel)
theorem row_works_108 : Template HasSnaky 3 required_108 envelope_108 := by
  refine compose HasSnaky 2 childrenC_108 childrenD_108 children_work_108 (1, 1)
    required_108 envelope_108 pivot_mem_108 child_required_sub_108 child_envelope_sub_108 ?_
  intro b hb
  exact common_sub_108 (mem_commonEnvelope childrenD_108 b hb)
def required_113 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_113 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, 2), (1, 3), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_113 : Fin 2 → Finset Cell := ![(placed21 1 (0, 0) required_0), (placed21 0 (0, 2) required_23)]
def childrenD_113 : Fin 2 → Finset Cell := ![(placed21 1 (0, 0) envelope_0), (placed21 0 (0, 2) envelope_23)]
theorem common_sub_113 : commonEnvelope childrenD_113 ⊆ insert (1, 3) required_113 := by decide +kernel
theorem child_required_sub_113 : ∀ j, childrenC_113 j ⊆ insert (1, 3) required_113 := by decide +kernel
theorem child_envelope_sub_113 : ∀ j, childrenD_113 j ⊆ envelope_113 := by decide +kernel
theorem pivot_mem_113 : (1, 3) ∈ envelope_113 := by decide +kernel
theorem children_work_113 : ∀ j, Template HasSnaky 2 (childrenC_113 j) (childrenD_113 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 1 (0, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_23 0 (0, 2)).mono (by decide +kernel)
theorem row_works_113 : Template HasSnaky 3 required_113 envelope_113 := by
  refine compose HasSnaky 2 childrenC_113 childrenD_113 children_work_113 (1, 3)
    required_113 envelope_113 pivot_mem_113 child_required_sub_113 child_envelope_sub_113 ?_
  intro b hb
  exact common_sub_113 (mem_commonEnvelope childrenD_113 b hb)
def required_124 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 2), (1, 3), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_124 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_124 : Fin 2 → Finset Cell := ![(placed21 3 (1, 4) required_5), (placed21 1 (0, 1) required_123)]
def childrenD_124 : Fin 2 → Finset Cell := ![(placed21 3 (1, 4) envelope_5), (placed21 1 (0, 1) envelope_123)]
theorem common_sub_124 : commonEnvelope childrenD_124 ⊆ insert (2, 1) required_124 := by decide +kernel
theorem child_required_sub_124 : ∀ j, childrenC_124 j ⊆ insert (2, 1) required_124 := by decide +kernel
theorem child_envelope_sub_124 : ∀ j, childrenD_124 j ⊆ envelope_124 := by decide +kernel
theorem pivot_mem_124 : (2, 1) ∈ envelope_124 := by decide +kernel
theorem children_work_124 : ∀ j, Template HasSnaky 2 (childrenC_124 j) (childrenD_124 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 3 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_123 1 (0, 1)).mono (by decide +kernel)
theorem row_works_124 : Template HasSnaky 3 required_124 envelope_124 := by
  refine compose HasSnaky 2 childrenC_124 childrenD_124 children_work_124 (2, 1)
    required_124 envelope_124 pivot_mem_124 child_required_sub_124 child_envelope_sub_124 ?_
  intro b hb
  exact common_sub_124 (mem_commonEnvelope childrenD_124 b hb)
def required_126 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 3), (1, 4), (2, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_126 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 1), (2, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_126 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) required_5), (placed21 1 (0, 1) required_123)]
def childrenD_126 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) envelope_5), (placed21 1 (0, 1) envelope_123)]
theorem common_sub_126 : commonEnvelope childrenD_126 ⊆ insert (1, 2) required_126 := by decide +kernel
theorem child_required_sub_126 : ∀ j, childrenC_126 j ⊆ insert (1, 2) required_126 := by decide +kernel
theorem child_envelope_sub_126 : ∀ j, childrenD_126 j ⊆ envelope_126 := by decide +kernel
theorem pivot_mem_126 : (1, 2) ∈ envelope_126 := by decide +kernel
theorem children_work_126 : ∀ j, Template HasSnaky 2 (childrenC_126 j) (childrenD_126 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 7 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_123 1 (0, 1)).mono (by decide +kernel)
theorem row_works_126 : Template HasSnaky 3 required_126 envelope_126 := by
  refine compose HasSnaky 2 childrenC_126 childrenD_126 children_work_126 (1, 2)
    required_126 envelope_126 pivot_mem_126 child_required_sub_126 child_envelope_sub_126 ?_
  intro b hb
  exact common_sub_126 (mem_commonEnvelope childrenD_126 b hb)
def required_130 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (1, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_130 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_130 : Fin 2 → Finset Cell := ![(placed21 1 (0, 0) required_3), required_129]
def childrenD_130 : Fin 2 → Finset Cell := ![(placed21 1 (0, 0) envelope_3), envelope_129]
theorem common_sub_130 : commonEnvelope childrenD_130 ⊆ insert (1, 4) required_130 := by decide +kernel
theorem child_required_sub_130 : ∀ j, childrenC_130 j ⊆ insert (1, 4) required_130 := by decide +kernel
theorem child_envelope_sub_130 : ∀ j, childrenD_130 j ⊆ envelope_130 := by decide +kernel
theorem pivot_mem_130 : (1, 4) ∈ envelope_130 := by decide +kernel
theorem children_work_130 : ∀ j, Template HasSnaky 2 (childrenC_130 j) (childrenD_130 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_3 1 (0, 0)).mono (by decide +kernel)
  · exact row_works_129.mono (by decide +kernel)
theorem row_works_130 : Template HasSnaky 3 required_130 envelope_130 := by
  refine compose HasSnaky 2 childrenC_130 childrenD_130 children_work_130 (1, 4)
    required_130 envelope_130 pivot_mem_130 child_required_sub_130 child_envelope_sub_130 ?_
  intro b hb
  exact common_sub_130 (mem_commonEnvelope childrenD_130 b hb)
def required_131 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 3), (1, 2), (2, 2), (3, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_131 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (1, 4), (1, 5), (2, 2), (3, 2), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_131 : Fin 2 → Finset Cell := ![(placed21 2 (4, 2) required_0), required_15]
def childrenD_131 : Fin 2 → Finset Cell := ![(placed21 2 (4, 2) envelope_0), envelope_15]
theorem common_sub_131 : commonEnvelope childrenD_131 ⊆ insert (1, 3) required_131 := by decide +kernel
theorem child_required_sub_131 : ∀ j, childrenC_131 j ⊆ insert (1, 3) required_131 := by decide +kernel
theorem child_envelope_sub_131 : ∀ j, childrenD_131 j ⊆ envelope_131 := by decide +kernel
theorem pivot_mem_131 : (1, 3) ∈ envelope_131 := by decide +kernel
theorem children_work_131 : ∀ j, Template HasSnaky 2 (childrenC_131 j) (childrenD_131 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 2 (4, 2)).mono (by decide +kernel)
  · exact row_works_15.mono (by decide +kernel)
theorem row_works_131 : Template HasSnaky 3 required_131 envelope_131 := by
  refine compose HasSnaky 2 childrenC_131 childrenD_131 children_work_131 (1, 3)
    required_131 envelope_131 pivot_mem_131 child_required_sub_131 child_envelope_sub_131 ?_
  intro b hb
  exact common_sub_131 (mem_commonEnvelope childrenD_131 b hb)
def required_139 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 3), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_139 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (1, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_139 : Fin 2 → Finset Cell := ![(placed21 1 (0, 0) required_0), (placed21 0 (0, 1) required_138)]
def childrenD_139 : Fin 2 → Finset Cell := ![(placed21 1 (0, 0) envelope_0), (placed21 0 (0, 1) envelope_138)]
theorem common_sub_139 : commonEnvelope childrenD_139 ⊆ insert (1, 3) required_139 := by decide +kernel
theorem child_required_sub_139 : ∀ j, childrenC_139 j ⊆ insert (1, 3) required_139 := by decide +kernel
theorem child_envelope_sub_139 : ∀ j, childrenD_139 j ⊆ envelope_139 := by decide +kernel
theorem pivot_mem_139 : (1, 3) ∈ envelope_139 := by decide +kernel
theorem children_work_139 : ∀ j, Template HasSnaky 2 (childrenC_139 j) (childrenD_139 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 1 (0, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_138 0 (0, 1)).mono (by decide +kernel)
theorem row_works_139 : Template HasSnaky 3 required_139 envelope_139 := by
  refine compose HasSnaky 2 childrenC_139 childrenD_139 children_work_139 (1, 3)
    required_139 envelope_139 pivot_mem_139 child_required_sub_139 child_envelope_sub_139 ?_
  intro b hb
  exact common_sub_139 (mem_commonEnvelope childrenD_139 b hb)
def required_140 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 3), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_140 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_140 : Fin 2 → Finset Cell := ![(placed21 1 (0, 0) required_0), (placed21 0 (0, 1) required_43)]
def childrenD_140 : Fin 2 → Finset Cell := ![(placed21 1 (0, 0) envelope_0), (placed21 0 (0, 1) envelope_43)]
theorem common_sub_140 : commonEnvelope childrenD_140 ⊆ insert (1, 3) required_140 := by decide +kernel
theorem child_required_sub_140 : ∀ j, childrenC_140 j ⊆ insert (1, 3) required_140 := by decide +kernel
theorem child_envelope_sub_140 : ∀ j, childrenD_140 j ⊆ envelope_140 := by decide +kernel
theorem pivot_mem_140 : (1, 3) ∈ envelope_140 := by decide +kernel
theorem children_work_140 : ∀ j, Template HasSnaky 2 (childrenC_140 j) (childrenD_140 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 1 (0, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_43 0 (0, 1)).mono (by decide +kernel)
theorem row_works_140 : Template HasSnaky 3 required_140 envelope_140 := by
  refine compose HasSnaky 2 childrenC_140 childrenD_140 children_work_140 (1, 3)
    required_140 envelope_140 pivot_mem_140 child_required_sub_140 child_envelope_sub_140 ?_
  intro b hb
  exact common_sub_140 (mem_commonEnvelope childrenD_140 b hb)
def required_143 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 0), (2, 1), (3, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_143 : Finset Cell := ⟨(([(0, 0), (0, 1), (1, 0), (1, 1), (2, 0), (2, 1), (3, 1), (3, 2), (4, 1), (4, 2), (5, 1), (5, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_143 : Fin 2 → Finset Cell := ![(placed21 1 (0, 1) required_6), (placed21 3 (0, 1) required_11)]
def childrenD_143 : Fin 2 → Finset Cell := ![(placed21 1 (0, 1) envelope_6), (placed21 3 (0, 1) envelope_11)]
theorem common_sub_143 : commonEnvelope childrenD_143 ⊆ insert (4, 1) required_143 := by decide +kernel
theorem child_required_sub_143 : ∀ j, childrenC_143 j ⊆ insert (4, 1) required_143 := by decide +kernel
theorem child_envelope_sub_143 : ∀ j, childrenD_143 j ⊆ envelope_143 := by decide +kernel
theorem pivot_mem_143 : (4, 1) ∈ envelope_143 := by decide +kernel
theorem children_work_143 : ∀ j, Template HasSnaky 2 (childrenC_143 j) (childrenD_143 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_6 1 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_11 3 (0, 1)).mono (by decide +kernel)
theorem row_works_143 : Template HasSnaky 3 required_143 envelope_143 := by
  refine compose HasSnaky 2 childrenC_143 childrenD_143 children_work_143 (4, 1)
    required_143 envelope_143 pivot_mem_143 child_required_sub_143 child_envelope_sub_143 ?_
  intro b hb
  exact common_sub_143 (mem_commonEnvelope childrenD_143 b hb)
def required_157 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (3, 1), (3, 3), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_157 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 0), (4, 1), (5, 0)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_157 : Fin 2 → Finset Cell := ![(placed21 4 (0, 1) required_4), (placed21 0 (1, 0) required_156)]
def childrenD_157 : Fin 2 → Finset Cell := ![(placed21 4 (0, 1) envelope_4), (placed21 0 (1, 0) envelope_156)]
theorem common_sub_157 : commonEnvelope childrenD_157 ⊆ insert (4, 0) required_157 := by decide +kernel
theorem child_required_sub_157 : ∀ j, childrenC_157 j ⊆ insert (4, 0) required_157 := by decide +kernel
theorem child_envelope_sub_157 : ∀ j, childrenD_157 j ⊆ envelope_157 := by decide +kernel
theorem pivot_mem_157 : (4, 0) ∈ envelope_157 := by decide +kernel
theorem children_work_157 : ∀ j, Template HasSnaky 2 (childrenC_157 j) (childrenD_157 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_4 4 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_156 0 (1, 0)).mono (by decide +kernel)
theorem row_works_157 : Template HasSnaky 3 required_157 envelope_157 := by
  refine compose HasSnaky 2 childrenC_157 childrenD_157 children_work_157 (4, 0)
    required_157 envelope_157 pivot_mem_157 child_required_sub_157 child_envelope_sub_157 ?_
  intro b hb
  exact common_sub_157 (mem_commonEnvelope childrenD_157 b hb)
def required_158 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 3), (0, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_158 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 0), (1, 1), (1, 2), (1, 4), (1, 5), (1, 6)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_158 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) required_6), (placed21 4 (0, 5) required_6)]
def childrenD_158 : Fin 2 → Finset Cell := ![(placed21 0 (0, 1) envelope_6), (placed21 4 (0, 5) envelope_6)]
theorem common_sub_158 : commonEnvelope childrenD_158 ⊆ insert (0, 4) required_158 := by decide +kernel
theorem child_required_sub_158 : ∀ j, childrenC_158 j ⊆ insert (0, 4) required_158 := by decide +kernel
theorem child_envelope_sub_158 : ∀ j, childrenD_158 j ⊆ envelope_158 := by decide +kernel
theorem pivot_mem_158 : (0, 4) ∈ envelope_158 := by decide +kernel
theorem children_work_158 : ∀ j, Template HasSnaky 2 (childrenC_158 j) (childrenD_158 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_6 0 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_6 4 (0, 5)).mono (by decide +kernel)
theorem row_works_158 : Template HasSnaky 3 required_158 envelope_158 := by
  refine compose HasSnaky 2 childrenC_158 childrenD_158 children_work_158 (0, 4)
    required_158 envelope_158 pivot_mem_158 child_required_sub_158 child_envelope_sub_158 ?_
  intro b hb
  exact common_sub_158 (mem_commonEnvelope childrenD_158 b hb)
def required_159 : Finset Cell := ⟨(([(1, 1), (1, 2), (2, 1), (2, 2), (2, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_159 : Finset Cell := ⟨(([(0, 2), (1, 1), (1, 2), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (4, 1), (5, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_159 : Fin 2 → Finset Cell := ![(placed21 1 (0, 1) required_23), (placed21 0 (1, 0) required_66)]
def childrenD_159 : Fin 2 → Finset Cell := ![(placed21 1 (0, 1) envelope_23), (placed21 0 (1, 0) envelope_66)]
theorem common_sub_159 : commonEnvelope childrenD_159 ⊆ insert (3, 1) required_159 := by decide +kernel
theorem child_required_sub_159 : ∀ j, childrenC_159 j ⊆ insert (3, 1) required_159 := by decide +kernel
theorem child_envelope_sub_159 : ∀ j, childrenD_159 j ⊆ envelope_159 := by decide +kernel
theorem pivot_mem_159 : (3, 1) ∈ envelope_159 := by decide +kernel
theorem children_work_159 : ∀ j, Template HasSnaky 2 (childrenC_159 j) (childrenD_159 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_23 1 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_66 0 (1, 0)).mono (by decide +kernel)
theorem row_works_159 : Template HasSnaky 3 required_159 envelope_159 := by
  refine compose HasSnaky 2 childrenC_159 childrenD_159 children_work_159 (3, 1)
    required_159 envelope_159 pivot_mem_159 child_required_sub_159 child_envelope_sub_159 ?_
  intro b hb
  exact common_sub_159 (mem_commonEnvelope childrenD_159 b hb)
def required_160 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 3), (1, 4), (2, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_160 : Finset Cell := ⟨(([(0, 0), (0, 1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (2, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_160 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) required_5), (placed21 4 (1, 5) required_11)]
def childrenD_160 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) envelope_5), (placed21 4 (1, 5) envelope_11)]
theorem common_sub_160 : commonEnvelope childrenD_160 ⊆ insert (1, 2) required_160 := by decide +kernel
theorem child_required_sub_160 : ∀ j, childrenC_160 j ⊆ insert (1, 2) required_160 := by decide +kernel
theorem child_envelope_sub_160 : ∀ j, childrenD_160 j ⊆ envelope_160 := by decide +kernel
theorem pivot_mem_160 : (1, 2) ∈ envelope_160 := by decide +kernel
theorem children_work_160 : ∀ j, Template HasSnaky 2 (childrenC_160 j) (childrenD_160 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 7 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_11 4 (1, 5)).mono (by decide +kernel)
theorem row_works_160 : Template HasSnaky 3 required_160 envelope_160 := by
  refine compose HasSnaky 2 childrenC_160 childrenD_160 children_work_160 (1, 2)
    required_160 envelope_160 pivot_mem_160 child_required_sub_160 child_envelope_sub_160 ?_
  intro b hb
  exact common_sub_160 (mem_commonEnvelope childrenD_160 b hb)
def required_163 : Finset Cell := ⟨(([(0, 0), (0, 1), (1, 3), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_163 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_163 : Fin 2 → Finset Cell := ![(placed21 1 (0, 0) required_3), required_129]
def childrenD_163 : Fin 2 → Finset Cell := ![(placed21 1 (0, 0) envelope_3), envelope_129]
theorem common_sub_163 : commonEnvelope childrenD_163 ⊆ insert (0, 2) required_163 := by decide +kernel
theorem child_required_sub_163 : ∀ j, childrenC_163 j ⊆ insert (0, 2) required_163 := by decide +kernel
theorem child_envelope_sub_163 : ∀ j, childrenD_163 j ⊆ envelope_163 := by decide +kernel
theorem pivot_mem_163 : (0, 2) ∈ envelope_163 := by decide +kernel
theorem children_work_163 : ∀ j, Template HasSnaky 2 (childrenC_163 j) (childrenD_163 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_3 1 (0, 0)).mono (by decide +kernel)
  · exact row_works_129.mono (by decide +kernel)
theorem row_works_163 : Template HasSnaky 3 required_163 envelope_163 := by
  refine compose HasSnaky 2 childrenC_163 childrenD_163 children_work_163 (0, 2)
    required_163 envelope_163 pivot_mem_163 child_required_sub_163 child_envelope_sub_163 ?_
  intro b hb
  exact common_sub_163 (mem_commonEnvelope childrenD_163 b hb)
def required_177 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 3), (1, 2), (2, 2), (3, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_177 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 0), (1, 1), (1, 2), (2, 2), (3, 2), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_177 : Fin 2 → Finset Cell := ![(placed21 6 (4, 2) required_0), required_23]
def childrenD_177 : Fin 2 → Finset Cell := ![(placed21 6 (4, 2) envelope_0), envelope_23]
theorem common_sub_177 : commonEnvelope childrenD_177 ⊆ insert (1, 1) required_177 := by decide +kernel
theorem child_required_sub_177 : ∀ j, childrenC_177 j ⊆ insert (1, 1) required_177 := by decide +kernel
theorem child_envelope_sub_177 : ∀ j, childrenD_177 j ⊆ envelope_177 := by decide +kernel
theorem pivot_mem_177 : (1, 1) ∈ envelope_177 := by decide +kernel
theorem children_work_177 : ∀ j, Template HasSnaky 2 (childrenC_177 j) (childrenD_177 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 6 (4, 2)).mono (by decide +kernel)
  · exact row_works_23.mono (by decide +kernel)
theorem row_works_177 : Template HasSnaky 3 required_177 envelope_177 := by
  refine compose HasSnaky 2 childrenC_177 childrenD_177 children_work_177 (1, 1)
    required_177 envelope_177 pivot_mem_177 child_required_sub_177 child_envelope_sub_177 ?_
  intro b hb
  exact common_sub_177 (mem_commonEnvelope childrenD_177 b hb)
def required_198 : Finset Cell := ⟨(([(0, 2), (0, 3), (1, 1), (1, 2), (1, 3), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_198 : Finset Cell := ⟨(([(0, 2), (0, 3), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 0), (2, 1), (2, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_198 : Fin 2 → Finset Cell := ![(placed21 7 (1, 6) required_0), (placed21 4 (1, 5) required_6)]
def childrenD_198 : Fin 2 → Finset Cell := ![(placed21 7 (1, 6) envelope_0), (placed21 4 (1, 5) envelope_6)]
theorem common_sub_198 : commonEnvelope childrenD_198 ⊆ insert (1, 5) required_198 := by decide +kernel
theorem child_required_sub_198 : ∀ j, childrenC_198 j ⊆ insert (1, 5) required_198 := by decide +kernel
theorem child_envelope_sub_198 : ∀ j, childrenD_198 j ⊆ envelope_198 := by decide +kernel
theorem pivot_mem_198 : (1, 5) ∈ envelope_198 := by decide +kernel
theorem children_work_198 : ∀ j, Template HasSnaky 2 (childrenC_198 j) (childrenD_198 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 7 (1, 6)).mono (by decide +kernel)
  · exact (placed21_template row_works_6 4 (1, 5)).mono (by decide +kernel)
theorem row_works_198 : Template HasSnaky 3 required_198 envelope_198 := by
  refine compose HasSnaky 2 childrenC_198 childrenD_198 children_work_198 (1, 5)
    required_198 envelope_198 pivot_mem_198 child_required_sub_198 child_envelope_sub_198 ?_
  intro b hb
  exact common_sub_198 (mem_commonEnvelope childrenD_198 b hb)
def required_201 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (2, 3), (3, 1), (3, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_201 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (2, 3), (2, 4), (3, 0), (3, 1), (3, 2), (3, 3), (4, 0), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_201 : Fin 2 → Finset Cell := ![(placed21 4 (0, 1) required_5), (placed21 5 (4, 0) required_146)]
def childrenD_201 : Fin 2 → Finset Cell := ![(placed21 4 (0, 1) envelope_5), (placed21 5 (4, 0) envelope_146)]
theorem common_sub_201 : commonEnvelope childrenD_201 ⊆ insert (3, 0) required_201 := by decide +kernel
theorem child_required_sub_201 : ∀ j, childrenC_201 j ⊆ insert (3, 0) required_201 := by decide +kernel
theorem child_envelope_sub_201 : ∀ j, childrenD_201 j ⊆ envelope_201 := by decide +kernel
theorem pivot_mem_201 : (3, 0) ∈ envelope_201 := by decide +kernel
theorem children_work_201 : ∀ j, Template HasSnaky 2 (childrenC_201 j) (childrenD_201 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 4 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_146 5 (4, 0)).mono (by decide +kernel)
theorem row_works_201 : Template HasSnaky 3 required_201 envelope_201 := by
  refine compose HasSnaky 2 childrenC_201 childrenD_201 children_work_201 (3, 0)
    required_201 envelope_201 pivot_mem_201 child_required_sub_201 child_envelope_sub_201 ?_
  intro b hb
  exact common_sub_201 (mem_commonEnvelope childrenD_201 b hb)
def required_205 : Finset Cell := ⟨(([(0, 3), (0, 4), (1, 1), (1, 2), (1, 3), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_205 : Finset Cell := ⟨(([(0, 2), (0, 3), (0, 4), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 0), (2, 1), (2, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_205 : Fin 2 → Finset Cell := ![(placed21 4 (1, 5) required_6), (placed21 2 (1, 2) required_23)]
def childrenD_205 : Fin 2 → Finset Cell := ![(placed21 4 (1, 5) envelope_6), (placed21 2 (1, 2) envelope_23)]
theorem common_sub_205 : commonEnvelope childrenD_205 ⊆ insert (1, 5) required_205 := by decide +kernel
theorem child_required_sub_205 : ∀ j, childrenC_205 j ⊆ insert (1, 5) required_205 := by decide +kernel
theorem child_envelope_sub_205 : ∀ j, childrenD_205 j ⊆ envelope_205 := by decide +kernel
theorem pivot_mem_205 : (1, 5) ∈ envelope_205 := by decide +kernel
theorem children_work_205 : ∀ j, Template HasSnaky 2 (childrenC_205 j) (childrenD_205 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_6 4 (1, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_23 2 (1, 2)).mono (by decide +kernel)
theorem row_works_205 : Template HasSnaky 3 required_205 envelope_205 := by
  refine compose HasSnaky 2 childrenC_205 childrenD_205 children_work_205 (1, 5)
    required_205 envelope_205 pivot_mem_205 child_required_sub_205 child_envelope_sub_205 ?_
  intro b hb
  exact common_sub_205 (mem_commonEnvelope childrenD_205 b hb)
def required_207 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (2, 3), (2, 4), (3, 0)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_207 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (2, 3), (2, 4), (3, 0), (3, 1), (3, 2), (3, 3), (4, 0), (4, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_207 : Fin 2 → Finset Cell := ![(placed21 4 (0, 1) required_5), (placed21 5 (4, 0) required_77)]
def childrenD_207 : Fin 2 → Finset Cell := ![(placed21 4 (0, 1) envelope_5), (placed21 5 (4, 0) envelope_77)]
theorem common_sub_207 : commonEnvelope childrenD_207 ⊆ insert (3, 1) required_207 := by decide +kernel
theorem child_required_sub_207 : ∀ j, childrenC_207 j ⊆ insert (3, 1) required_207 := by decide +kernel
theorem child_envelope_sub_207 : ∀ j, childrenD_207 j ⊆ envelope_207 := by decide +kernel
theorem pivot_mem_207 : (3, 1) ∈ envelope_207 := by decide +kernel
theorem children_work_207 : ∀ j, Template HasSnaky 2 (childrenC_207 j) (childrenD_207 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 4 (0, 1)).mono (by decide +kernel)
  · exact (placed21_template row_works_77 5 (4, 0)).mono (by decide +kernel)
theorem row_works_207 : Template HasSnaky 3 required_207 envelope_207 := by
  refine compose HasSnaky 2 childrenC_207 childrenD_207 children_work_207 (3, 1)
    required_207 envelope_207 pivot_mem_207 child_required_sub_207 child_envelope_sub_207 ?_
  intro b hb
  exact common_sub_207 (mem_commonEnvelope childrenD_207 b hb)
def required_209 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 2), (1, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_209 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (0, 3), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_209 : Fin 2 → Finset Cell := ![(placed21 7 (1, 5) required_0), (placed21 6 (1, 4) required_138)]
def childrenD_209 : Fin 2 → Finset Cell := ![(placed21 7 (1, 5) envelope_0), (placed21 6 (1, 4) envelope_138)]
theorem common_sub_209 : commonEnvelope childrenD_209 ⊆ insert (1, 4) required_209 := by decide +kernel
theorem child_required_sub_209 : ∀ j, childrenC_209 j ⊆ insert (1, 4) required_209 := by decide +kernel
theorem child_envelope_sub_209 : ∀ j, childrenD_209 j ⊆ envelope_209 := by decide +kernel
theorem pivot_mem_209 : (1, 4) ∈ envelope_209 := by decide +kernel
theorem children_work_209 : ∀ j, Template HasSnaky 2 (childrenC_209 j) (childrenD_209 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 7 (1, 5)).mono (by decide +kernel)
  · exact (placed21_template row_works_138 6 (1, 4)).mono (by decide +kernel)
theorem row_works_209 : Template HasSnaky 3 required_209 envelope_209 := by
  refine compose HasSnaky 2 childrenC_209 childrenD_209 children_work_209 (1, 4)
    required_209 envelope_209 pivot_mem_209 child_required_sub_209 child_envelope_sub_209 ?_
  intro b hb
  exact common_sub_209 (mem_commonEnvelope childrenD_209 b hb)
def required_212 : Finset Cell := ⟨(([(0, 1), (1, 1), (1, 2), (1, 3), (2, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_212 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 1), (2, 2)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_212 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) required_5), (placed21 0 (0, 1) required_76)]
def childrenD_212 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) envelope_5), (placed21 0 (0, 1) envelope_76)]
theorem common_sub_212 : commonEnvelope childrenD_212 ⊆ insert (1, 4) required_212 := by decide +kernel
theorem child_required_sub_212 : ∀ j, childrenC_212 j ⊆ insert (1, 4) required_212 := by decide +kernel
theorem child_envelope_sub_212 : ∀ j, childrenD_212 j ⊆ envelope_212 := by decide +kernel
theorem pivot_mem_212 : (1, 4) ∈ envelope_212 := by decide +kernel
theorem children_work_212 : ∀ j, Template HasSnaky 2 (childrenC_212 j) (childrenD_212 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 7 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_76 0 (0, 1)).mono (by decide +kernel)
theorem row_works_212 : Template HasSnaky 3 required_212 envelope_212 := by
  refine compose HasSnaky 2 childrenC_212 childrenD_212 children_work_212 (1, 4)
    required_212 envelope_212 pivot_mem_212 child_required_sub_212 child_envelope_sub_212 ?_
  intro b hb
  exact common_sub_212 (mem_commonEnvelope childrenD_212 b hb)
def required_215 : Finset Cell := ⟨(([(0, 2), (1, 2), (2, 2), (3, 2), (3, 3), (3, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_215 : Finset Cell := ⟨(([(0, 2), (1, 2), (2, 0), (2, 1), (2, 2), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 1)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_215 : Fin 2 → Finset Cell := ![(placed21 4 (0, 2) required_5), (placed21 2 (3, 0) required_11)]
def childrenD_215 : Fin 2 → Finset Cell := ![(placed21 4 (0, 2) envelope_5), (placed21 2 (3, 0) envelope_11)]
theorem common_sub_215 : commonEnvelope childrenD_215 ⊆ insert (3, 1) required_215 := by decide +kernel
theorem child_required_sub_215 : ∀ j, childrenC_215 j ⊆ insert (3, 1) required_215 := by decide +kernel
theorem child_envelope_sub_215 : ∀ j, childrenD_215 j ⊆ envelope_215 := by decide +kernel
theorem pivot_mem_215 : (3, 1) ∈ envelope_215 := by decide +kernel
theorem children_work_215 : ∀ j, Template HasSnaky 2 (childrenC_215 j) (childrenD_215 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 4 (0, 2)).mono (by decide +kernel)
  · exact (placed21_template row_works_11 2 (3, 0)).mono (by decide +kernel)
theorem row_works_215 : Template HasSnaky 3 required_215 envelope_215 := by
  refine compose HasSnaky 2 childrenC_215 childrenD_215 children_work_215 (3, 1)
    required_215 envelope_215 pivot_mem_215 child_required_sub_215 child_envelope_sub_215 ?_
  intro b hb
  exact common_sub_215 (mem_commonEnvelope childrenD_215 b hb)
def required_218 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 3), (1, 1), (1, 3), (2, 3)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_218 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 3), (0, 4), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_218 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) required_0), (placed21 4 (0, 4) required_83)]
def childrenD_218 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) envelope_0), (placed21 4 (0, 4) envelope_83)]
theorem common_sub_218 : commonEnvelope childrenD_218 ⊆ insert (1, 2) required_218 := by decide +kernel
theorem child_required_sub_218 : ∀ j, childrenC_218 j ⊆ insert (1, 2) required_218 := by decide +kernel
theorem child_envelope_sub_218 : ∀ j, childrenD_218 j ⊆ envelope_218 := by decide +kernel
theorem pivot_mem_218 : (1, 2) ∈ envelope_218 := by decide +kernel
theorem children_work_218 : ∀ j, Template HasSnaky 2 (childrenC_218 j) (childrenD_218 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_0 7 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_83 4 (0, 4)).mono (by decide +kernel)
theorem row_works_218 : Template HasSnaky 3 required_218 envelope_218 := by
  refine compose HasSnaky 2 childrenC_218 childrenD_218 children_work_218 (1, 2)
    required_218 envelope_218 pivot_mem_218 child_required_sub_218 child_envelope_sub_218 ?_
  intro b hb
  exact common_sub_218 (mem_commonEnvelope childrenD_218 b hb)
def required_219 : Finset Cell := ⟨(([(0, 0), (0, 3), (1, 2), (1, 3), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def envelope_219 : Finset Cell := ⟨(([(0, 0), (0, 1), (0, 3), (0, 4), (0, 5), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4)] : List Cell) : Multiset Cell), by decide +kernel⟩
def childrenC_219 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) required_4), (placed21 6 (1, 5) required_11)]
def childrenD_219 : Fin 2 → Finset Cell := ![(placed21 7 (1, 4) envelope_4), (placed21 6 (1, 5) envelope_11)]
theorem common_sub_219 : commonEnvelope childrenD_219 ⊆ insert (1, 1) required_219 := by decide +kernel
theorem child_required_sub_219 : ∀ j, childrenC_219 j ⊆ insert (1, 1) required_219 := by decide +kernel
theorem child_envelope_sub_219 : ∀ j, childrenD_219 j ⊆ envelope_219 := by decide +kernel
theorem pivot_mem_219 : (1, 1) ∈ envelope_219 := by decide +kernel
theorem children_work_219 : ∀ j, Template HasSnaky 2 (childrenC_219 j) (childrenD_219 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_4 7 (1, 4)).mono (by decide +kernel)
  · exact (placed21_template row_works_11 6 (1, 5)).mono (by decide +kernel)
theorem row_works_219 : Template HasSnaky 3 required_219 envelope_219 := by
  refine compose HasSnaky 2 childrenC_219 childrenD_219 children_work_219 (1, 1)
    required_219 envelope_219 pivot_mem_219 child_required_sub_219 child_envelope_sub_219 ?_
  intro b hb
  exact common_sub_219 (mem_commonEnvelope childrenD_219 b hb)
def height_108 : ℕ := 3
def childrenH_108 : Fin 2 → ℕ := ![height_15, height_102]
theorem height_exact_108 : height_108 = 1 + Finset.univ.sup childrenH_108 := by decide +kernel
theorem required_origin_108 : ∀ x ∈ required_108,
    (∃ j, x ∈ childrenC_108 j) ∨ ∀ j, x ∈ childrenD_108 j := by decide +kernel
theorem required_exact_108 : required_108 =
    ((Finset.univ.biUnion childrenC_108) ∪ commonEnvelope childrenD_108).erase (1, 1) := by
  exact required_eq_combination childrenC_108 childrenD_108 (1, 1) required_108
    (by decide +kernel) child_required_sub_108 common_sub_108 required_origin_108
theorem envelope_origin_108 : ∀ x ∈ envelope_108,
    x = (1, 1) ∨ ∃ j, x ∈ childrenD_108 j := by decide +kernel
theorem envelope_exact_108 : envelope_108 =
    insert (1, 1) (Finset.univ.biUnion childrenD_108) := by
  exact envelope_eq_combination childrenD_108 (1, 1) envelope_108
    pivot_mem_108 child_envelope_sub_108 envelope_origin_108
def checked_108 : CheckedCard where
  required := required_108
  envelope := envelope_108
  height := height_108
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_108
def height_113 : ℕ := 3
def childrenH_113 : Fin 2 → ℕ := ![height_0, height_23]
theorem height_exact_113 : height_113 = 1 + Finset.univ.sup childrenH_113 := by decide +kernel
theorem required_origin_113 : ∀ x ∈ required_113,
    (∃ j, x ∈ childrenC_113 j) ∨ ∀ j, x ∈ childrenD_113 j := by decide +kernel
theorem required_exact_113 : required_113 =
    ((Finset.univ.biUnion childrenC_113) ∪ commonEnvelope childrenD_113).erase (1, 3) := by
  exact required_eq_combination childrenC_113 childrenD_113 (1, 3) required_113
    (by decide +kernel) child_required_sub_113 common_sub_113 required_origin_113
theorem envelope_origin_113 : ∀ x ∈ envelope_113,
    x = (1, 3) ∨ ∃ j, x ∈ childrenD_113 j := by decide +kernel
theorem envelope_exact_113 : envelope_113 =
    insert (1, 3) (Finset.univ.biUnion childrenD_113) := by
  exact envelope_eq_combination childrenD_113 (1, 3) envelope_113
    pivot_mem_113 child_envelope_sub_113 envelope_origin_113
def checked_113 : CheckedCard where
  required := required_113
  envelope := envelope_113
  height := height_113
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_113
def height_124 : ℕ := 3
def childrenH_124 : Fin 2 → ℕ := ![height_5, height_123]
theorem height_exact_124 : height_124 = 1 + Finset.univ.sup childrenH_124 := by decide +kernel
theorem required_origin_124 : ∀ x ∈ required_124,
    (∃ j, x ∈ childrenC_124 j) ∨ ∀ j, x ∈ childrenD_124 j := by decide +kernel
theorem required_exact_124 : required_124 =
    ((Finset.univ.biUnion childrenC_124) ∪ commonEnvelope childrenD_124).erase (2, 1) := by
  exact required_eq_combination childrenC_124 childrenD_124 (2, 1) required_124
    (by decide +kernel) child_required_sub_124 common_sub_124 required_origin_124
theorem envelope_origin_124 : ∀ x ∈ envelope_124,
    x = (2, 1) ∨ ∃ j, x ∈ childrenD_124 j := by decide +kernel
theorem envelope_exact_124 : envelope_124 =
    insert (2, 1) (Finset.univ.biUnion childrenD_124) := by
  exact envelope_eq_combination childrenD_124 (2, 1) envelope_124
    pivot_mem_124 child_envelope_sub_124 envelope_origin_124
def checked_124 : CheckedCard where
  required := required_124
  envelope := envelope_124
  height := height_124
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_124
def height_126 : ℕ := 3
def childrenH_126 : Fin 2 → ℕ := ![height_5, height_123]
theorem height_exact_126 : height_126 = 1 + Finset.univ.sup childrenH_126 := by decide +kernel
theorem required_origin_126 : ∀ x ∈ required_126,
    (∃ j, x ∈ childrenC_126 j) ∨ ∀ j, x ∈ childrenD_126 j := by decide +kernel
theorem required_exact_126 : required_126 =
    ((Finset.univ.biUnion childrenC_126) ∪ commonEnvelope childrenD_126).erase (1, 2) := by
  exact required_eq_combination childrenC_126 childrenD_126 (1, 2) required_126
    (by decide +kernel) child_required_sub_126 common_sub_126 required_origin_126
theorem envelope_origin_126 : ∀ x ∈ envelope_126,
    x = (1, 2) ∨ ∃ j, x ∈ childrenD_126 j := by decide +kernel
theorem envelope_exact_126 : envelope_126 =
    insert (1, 2) (Finset.univ.biUnion childrenD_126) := by
  exact envelope_eq_combination childrenD_126 (1, 2) envelope_126
    pivot_mem_126 child_envelope_sub_126 envelope_origin_126
def checked_126 : CheckedCard where
  required := required_126
  envelope := envelope_126
  height := height_126
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_126
def height_130 : ℕ := 3
def childrenH_130 : Fin 2 → ℕ := ![height_3, height_129]
theorem height_exact_130 : height_130 = 1 + Finset.univ.sup childrenH_130 := by decide +kernel
theorem required_origin_130 : ∀ x ∈ required_130,
    (∃ j, x ∈ childrenC_130 j) ∨ ∀ j, x ∈ childrenD_130 j := by decide +kernel
theorem required_exact_130 : required_130 =
    ((Finset.univ.biUnion childrenC_130) ∪ commonEnvelope childrenD_130).erase (1, 4) := by
  exact required_eq_combination childrenC_130 childrenD_130 (1, 4) required_130
    (by decide +kernel) child_required_sub_130 common_sub_130 required_origin_130
theorem envelope_origin_130 : ∀ x ∈ envelope_130,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_130 j := by decide +kernel
theorem envelope_exact_130 : envelope_130 =
    insert (1, 4) (Finset.univ.biUnion childrenD_130) := by
  exact envelope_eq_combination childrenD_130 (1, 4) envelope_130
    pivot_mem_130 child_envelope_sub_130 envelope_origin_130
def checked_130 : CheckedCard where
  required := required_130
  envelope := envelope_130
  height := height_130
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_130
def height_131 : ℕ := 3
def childrenH_131 : Fin 2 → ℕ := ![height_0, height_15]
theorem height_exact_131 : height_131 = 1 + Finset.univ.sup childrenH_131 := by decide +kernel
theorem required_origin_131 : ∀ x ∈ required_131,
    (∃ j, x ∈ childrenC_131 j) ∨ ∀ j, x ∈ childrenD_131 j := by decide +kernel
theorem required_exact_131 : required_131 =
    ((Finset.univ.biUnion childrenC_131) ∪ commonEnvelope childrenD_131).erase (1, 3) := by
  exact required_eq_combination childrenC_131 childrenD_131 (1, 3) required_131
    (by decide +kernel) child_required_sub_131 common_sub_131 required_origin_131
theorem envelope_origin_131 : ∀ x ∈ envelope_131,
    x = (1, 3) ∨ ∃ j, x ∈ childrenD_131 j := by decide +kernel
theorem envelope_exact_131 : envelope_131 =
    insert (1, 3) (Finset.univ.biUnion childrenD_131) := by
  exact envelope_eq_combination childrenD_131 (1, 3) envelope_131
    pivot_mem_131 child_envelope_sub_131 envelope_origin_131
def checked_131 : CheckedCard where
  required := required_131
  envelope := envelope_131
  height := height_131
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_131
def height_139 : ℕ := 3
def childrenH_139 : Fin 2 → ℕ := ![height_0, height_138]
theorem height_exact_139 : height_139 = 1 + Finset.univ.sup childrenH_139 := by decide +kernel
theorem required_origin_139 : ∀ x ∈ required_139,
    (∃ j, x ∈ childrenC_139 j) ∨ ∀ j, x ∈ childrenD_139 j := by decide +kernel
theorem required_exact_139 : required_139 =
    ((Finset.univ.biUnion childrenC_139) ∪ commonEnvelope childrenD_139).erase (1, 3) := by
  exact required_eq_combination childrenC_139 childrenD_139 (1, 3) required_139
    (by decide +kernel) child_required_sub_139 common_sub_139 required_origin_139
theorem envelope_origin_139 : ∀ x ∈ envelope_139,
    x = (1, 3) ∨ ∃ j, x ∈ childrenD_139 j := by decide +kernel
theorem envelope_exact_139 : envelope_139 =
    insert (1, 3) (Finset.univ.biUnion childrenD_139) := by
  exact envelope_eq_combination childrenD_139 (1, 3) envelope_139
    pivot_mem_139 child_envelope_sub_139 envelope_origin_139
def checked_139 : CheckedCard where
  required := required_139
  envelope := envelope_139
  height := height_139
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_139
def height_140 : ℕ := 3
def childrenH_140 : Fin 2 → ℕ := ![height_0, height_43]
theorem height_exact_140 : height_140 = 1 + Finset.univ.sup childrenH_140 := by decide +kernel
theorem required_origin_140 : ∀ x ∈ required_140,
    (∃ j, x ∈ childrenC_140 j) ∨ ∀ j, x ∈ childrenD_140 j := by decide +kernel
theorem required_exact_140 : required_140 =
    ((Finset.univ.biUnion childrenC_140) ∪ commonEnvelope childrenD_140).erase (1, 3) := by
  exact required_eq_combination childrenC_140 childrenD_140 (1, 3) required_140
    (by decide +kernel) child_required_sub_140 common_sub_140 required_origin_140
theorem envelope_origin_140 : ∀ x ∈ envelope_140,
    x = (1, 3) ∨ ∃ j, x ∈ childrenD_140 j := by decide +kernel
theorem envelope_exact_140 : envelope_140 =
    insert (1, 3) (Finset.univ.biUnion childrenD_140) := by
  exact envelope_eq_combination childrenD_140 (1, 3) envelope_140
    pivot_mem_140 child_envelope_sub_140 envelope_origin_140
def checked_140 : CheckedCard where
  required := required_140
  envelope := envelope_140
  height := height_140
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_140
def height_143 : ℕ := 3
def childrenH_143 : Fin 2 → ℕ := ![height_6, height_11]
theorem height_exact_143 : height_143 = 1 + Finset.univ.sup childrenH_143 := by decide +kernel
theorem required_origin_143 : ∀ x ∈ required_143,
    (∃ j, x ∈ childrenC_143 j) ∨ ∀ j, x ∈ childrenD_143 j := by decide +kernel
theorem required_exact_143 : required_143 =
    ((Finset.univ.biUnion childrenC_143) ∪ commonEnvelope childrenD_143).erase (4, 1) := by
  exact required_eq_combination childrenC_143 childrenD_143 (4, 1) required_143
    (by decide +kernel) child_required_sub_143 common_sub_143 required_origin_143
theorem envelope_origin_143 : ∀ x ∈ envelope_143,
    x = (4, 1) ∨ ∃ j, x ∈ childrenD_143 j := by decide +kernel
theorem envelope_exact_143 : envelope_143 =
    insert (4, 1) (Finset.univ.biUnion childrenD_143) := by
  exact envelope_eq_combination childrenD_143 (4, 1) envelope_143
    pivot_mem_143 child_envelope_sub_143 envelope_origin_143
def checked_143 : CheckedCard where
  required := required_143
  envelope := envelope_143
  height := height_143
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_143
def height_157 : ℕ := 3
def childrenH_157 : Fin 2 → ℕ := ![height_4, height_156]
theorem height_exact_157 : height_157 = 1 + Finset.univ.sup childrenH_157 := by decide +kernel
theorem required_origin_157 : ∀ x ∈ required_157,
    (∃ j, x ∈ childrenC_157 j) ∨ ∀ j, x ∈ childrenD_157 j := by decide +kernel
theorem required_exact_157 : required_157 =
    ((Finset.univ.biUnion childrenC_157) ∪ commonEnvelope childrenD_157).erase (4, 0) := by
  exact required_eq_combination childrenC_157 childrenD_157 (4, 0) required_157
    (by decide +kernel) child_required_sub_157 common_sub_157 required_origin_157
theorem envelope_origin_157 : ∀ x ∈ envelope_157,
    x = (4, 0) ∨ ∃ j, x ∈ childrenD_157 j := by decide +kernel
theorem envelope_exact_157 : envelope_157 =
    insert (4, 0) (Finset.univ.biUnion childrenD_157) := by
  exact envelope_eq_combination childrenD_157 (4, 0) envelope_157
    pivot_mem_157 child_envelope_sub_157 envelope_origin_157
def checked_157 : CheckedCard where
  required := required_157
  envelope := envelope_157
  height := height_157
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_157
def height_158 : ℕ := 3
def childrenH_158 : Fin 2 → ℕ := ![height_6, height_6]
theorem height_exact_158 : height_158 = 1 + Finset.univ.sup childrenH_158 := by decide +kernel
theorem required_origin_158 : ∀ x ∈ required_158,
    (∃ j, x ∈ childrenC_158 j) ∨ ∀ j, x ∈ childrenD_158 j := by decide +kernel
theorem required_exact_158 : required_158 =
    ((Finset.univ.biUnion childrenC_158) ∪ commonEnvelope childrenD_158).erase (0, 4) := by
  exact required_eq_combination childrenC_158 childrenD_158 (0, 4) required_158
    (by decide +kernel) child_required_sub_158 common_sub_158 required_origin_158
theorem envelope_origin_158 : ∀ x ∈ envelope_158,
    x = (0, 4) ∨ ∃ j, x ∈ childrenD_158 j := by decide +kernel
theorem envelope_exact_158 : envelope_158 =
    insert (0, 4) (Finset.univ.biUnion childrenD_158) := by
  exact envelope_eq_combination childrenD_158 (0, 4) envelope_158
    pivot_mem_158 child_envelope_sub_158 envelope_origin_158
def checked_158 : CheckedCard where
  required := required_158
  envelope := envelope_158
  height := height_158
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_158
def height_159 : ℕ := 3
def childrenH_159 : Fin 2 → ℕ := ![height_23, height_66]
theorem height_exact_159 : height_159 = 1 + Finset.univ.sup childrenH_159 := by decide +kernel
theorem required_origin_159 : ∀ x ∈ required_159,
    (∃ j, x ∈ childrenC_159 j) ∨ ∀ j, x ∈ childrenD_159 j := by decide +kernel
theorem required_exact_159 : required_159 =
    ((Finset.univ.biUnion childrenC_159) ∪ commonEnvelope childrenD_159).erase (3, 1) := by
  exact required_eq_combination childrenC_159 childrenD_159 (3, 1) required_159
    (by decide +kernel) child_required_sub_159 common_sub_159 required_origin_159
theorem envelope_origin_159 : ∀ x ∈ envelope_159,
    x = (3, 1) ∨ ∃ j, x ∈ childrenD_159 j := by decide +kernel
theorem envelope_exact_159 : envelope_159 =
    insert (3, 1) (Finset.univ.biUnion childrenD_159) := by
  exact envelope_eq_combination childrenD_159 (3, 1) envelope_159
    pivot_mem_159 child_envelope_sub_159 envelope_origin_159
def checked_159 : CheckedCard where
  required := required_159
  envelope := envelope_159
  height := height_159
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_159
def height_160 : ℕ := 3
def childrenH_160 : Fin 2 → ℕ := ![height_5, height_11]
theorem height_exact_160 : height_160 = 1 + Finset.univ.sup childrenH_160 := by decide +kernel
theorem required_origin_160 : ∀ x ∈ required_160,
    (∃ j, x ∈ childrenC_160 j) ∨ ∀ j, x ∈ childrenD_160 j := by decide +kernel
theorem required_exact_160 : required_160 =
    ((Finset.univ.biUnion childrenC_160) ∪ commonEnvelope childrenD_160).erase (1, 2) := by
  exact required_eq_combination childrenC_160 childrenD_160 (1, 2) required_160
    (by decide +kernel) child_required_sub_160 common_sub_160 required_origin_160
theorem envelope_origin_160 : ∀ x ∈ envelope_160,
    x = (1, 2) ∨ ∃ j, x ∈ childrenD_160 j := by decide +kernel
theorem envelope_exact_160 : envelope_160 =
    insert (1, 2) (Finset.univ.biUnion childrenD_160) := by
  exact envelope_eq_combination childrenD_160 (1, 2) envelope_160
    pivot_mem_160 child_envelope_sub_160 envelope_origin_160
def checked_160 : CheckedCard where
  required := required_160
  envelope := envelope_160
  height := height_160
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_160
def height_163 : ℕ := 3
def childrenH_163 : Fin 2 → ℕ := ![height_3, height_129]
theorem height_exact_163 : height_163 = 1 + Finset.univ.sup childrenH_163 := by decide +kernel
theorem required_origin_163 : ∀ x ∈ required_163,
    (∃ j, x ∈ childrenC_163 j) ∨ ∀ j, x ∈ childrenD_163 j := by decide +kernel
theorem required_exact_163 : required_163 =
    ((Finset.univ.biUnion childrenC_163) ∪ commonEnvelope childrenD_163).erase (0, 2) := by
  exact required_eq_combination childrenC_163 childrenD_163 (0, 2) required_163
    (by decide +kernel) child_required_sub_163 common_sub_163 required_origin_163
theorem envelope_origin_163 : ∀ x ∈ envelope_163,
    x = (0, 2) ∨ ∃ j, x ∈ childrenD_163 j := by decide +kernel
theorem envelope_exact_163 : envelope_163 =
    insert (0, 2) (Finset.univ.biUnion childrenD_163) := by
  exact envelope_eq_combination childrenD_163 (0, 2) envelope_163
    pivot_mem_163 child_envelope_sub_163 envelope_origin_163
def checked_163 : CheckedCard where
  required := required_163
  envelope := envelope_163
  height := height_163
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_163
def height_177 : ℕ := 3
def childrenH_177 : Fin 2 → ℕ := ![height_0, height_23]
theorem height_exact_177 : height_177 = 1 + Finset.univ.sup childrenH_177 := by decide +kernel
theorem required_origin_177 : ∀ x ∈ required_177,
    (∃ j, x ∈ childrenC_177 j) ∨ ∀ j, x ∈ childrenD_177 j := by decide +kernel
theorem required_exact_177 : required_177 =
    ((Finset.univ.biUnion childrenC_177) ∪ commonEnvelope childrenD_177).erase (1, 1) := by
  exact required_eq_combination childrenC_177 childrenD_177 (1, 1) required_177
    (by decide +kernel) child_required_sub_177 common_sub_177 required_origin_177
theorem envelope_origin_177 : ∀ x ∈ envelope_177,
    x = (1, 1) ∨ ∃ j, x ∈ childrenD_177 j := by decide +kernel
theorem envelope_exact_177 : envelope_177 =
    insert (1, 1) (Finset.univ.biUnion childrenD_177) := by
  exact envelope_eq_combination childrenD_177 (1, 1) envelope_177
    pivot_mem_177 child_envelope_sub_177 envelope_origin_177
def checked_177 : CheckedCard where
  required := required_177
  envelope := envelope_177
  height := height_177
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_177
def height_198 : ℕ := 3
def childrenH_198 : Fin 2 → ℕ := ![height_0, height_6]
theorem height_exact_198 : height_198 = 1 + Finset.univ.sup childrenH_198 := by decide +kernel
theorem required_origin_198 : ∀ x ∈ required_198,
    (∃ j, x ∈ childrenC_198 j) ∨ ∀ j, x ∈ childrenD_198 j := by decide +kernel
theorem required_exact_198 : required_198 =
    ((Finset.univ.biUnion childrenC_198) ∪ commonEnvelope childrenD_198).erase (1, 5) := by
  exact required_eq_combination childrenC_198 childrenD_198 (1, 5) required_198
    (by decide +kernel) child_required_sub_198 common_sub_198 required_origin_198
theorem envelope_origin_198 : ∀ x ∈ envelope_198,
    x = (1, 5) ∨ ∃ j, x ∈ childrenD_198 j := by decide +kernel
theorem envelope_exact_198 : envelope_198 =
    insert (1, 5) (Finset.univ.biUnion childrenD_198) := by
  exact envelope_eq_combination childrenD_198 (1, 5) envelope_198
    pivot_mem_198 child_envelope_sub_198 envelope_origin_198
def checked_198 : CheckedCard where
  required := required_198
  envelope := envelope_198
  height := height_198
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_198
def height_201 : ℕ := 3
def childrenH_201 : Fin 2 → ℕ := ![height_5, height_146]
theorem height_exact_201 : height_201 = 1 + Finset.univ.sup childrenH_201 := by decide +kernel
theorem required_origin_201 : ∀ x ∈ required_201,
    (∃ j, x ∈ childrenC_201 j) ∨ ∀ j, x ∈ childrenD_201 j := by decide +kernel
theorem required_exact_201 : required_201 =
    ((Finset.univ.biUnion childrenC_201) ∪ commonEnvelope childrenD_201).erase (3, 0) := by
  exact required_eq_combination childrenC_201 childrenD_201 (3, 0) required_201
    (by decide +kernel) child_required_sub_201 common_sub_201 required_origin_201
theorem envelope_origin_201 : ∀ x ∈ envelope_201,
    x = (3, 0) ∨ ∃ j, x ∈ childrenD_201 j := by decide +kernel
theorem envelope_exact_201 : envelope_201 =
    insert (3, 0) (Finset.univ.biUnion childrenD_201) := by
  exact envelope_eq_combination childrenD_201 (3, 0) envelope_201
    pivot_mem_201 child_envelope_sub_201 envelope_origin_201
def checked_201 : CheckedCard where
  required := required_201
  envelope := envelope_201
  height := height_201
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_201
def height_205 : ℕ := 3
def childrenH_205 : Fin 2 → ℕ := ![height_6, height_23]
theorem height_exact_205 : height_205 = 1 + Finset.univ.sup childrenH_205 := by decide +kernel
theorem required_origin_205 : ∀ x ∈ required_205,
    (∃ j, x ∈ childrenC_205 j) ∨ ∀ j, x ∈ childrenD_205 j := by decide +kernel
theorem required_exact_205 : required_205 =
    ((Finset.univ.biUnion childrenC_205) ∪ commonEnvelope childrenD_205).erase (1, 5) := by
  exact required_eq_combination childrenC_205 childrenD_205 (1, 5) required_205
    (by decide +kernel) child_required_sub_205 common_sub_205 required_origin_205
theorem envelope_origin_205 : ∀ x ∈ envelope_205,
    x = (1, 5) ∨ ∃ j, x ∈ childrenD_205 j := by decide +kernel
theorem envelope_exact_205 : envelope_205 =
    insert (1, 5) (Finset.univ.biUnion childrenD_205) := by
  exact envelope_eq_combination childrenD_205 (1, 5) envelope_205
    pivot_mem_205 child_envelope_sub_205 envelope_origin_205
def checked_205 : CheckedCard where
  required := required_205
  envelope := envelope_205
  height := height_205
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_205
def height_207 : ℕ := 3
def childrenH_207 : Fin 2 → ℕ := ![height_5, height_77]
theorem height_exact_207 : height_207 = 1 + Finset.univ.sup childrenH_207 := by decide +kernel
theorem required_origin_207 : ∀ x ∈ required_207,
    (∃ j, x ∈ childrenC_207 j) ∨ ∀ j, x ∈ childrenD_207 j := by decide +kernel
theorem required_exact_207 : required_207 =
    ((Finset.univ.biUnion childrenC_207) ∪ commonEnvelope childrenD_207).erase (3, 1) := by
  exact required_eq_combination childrenC_207 childrenD_207 (3, 1) required_207
    (by decide +kernel) child_required_sub_207 common_sub_207 required_origin_207
theorem envelope_origin_207 : ∀ x ∈ envelope_207,
    x = (3, 1) ∨ ∃ j, x ∈ childrenD_207 j := by decide +kernel
theorem envelope_exact_207 : envelope_207 =
    insert (3, 1) (Finset.univ.biUnion childrenD_207) := by
  exact envelope_eq_combination childrenD_207 (3, 1) envelope_207
    pivot_mem_207 child_envelope_sub_207 envelope_origin_207
def checked_207 : CheckedCard where
  required := required_207
  envelope := envelope_207
  height := height_207
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_207
def height_209 : ℕ := 3
def childrenH_209 : Fin 2 → ℕ := ![height_0, height_138]
theorem height_exact_209 : height_209 = 1 + Finset.univ.sup childrenH_209 := by decide +kernel
theorem required_origin_209 : ∀ x ∈ required_209,
    (∃ j, x ∈ childrenC_209 j) ∨ ∀ j, x ∈ childrenD_209 j := by decide +kernel
theorem required_exact_209 : required_209 =
    ((Finset.univ.biUnion childrenC_209) ∪ commonEnvelope childrenD_209).erase (1, 4) := by
  exact required_eq_combination childrenC_209 childrenD_209 (1, 4) required_209
    (by decide +kernel) child_required_sub_209 common_sub_209 required_origin_209
theorem envelope_origin_209 : ∀ x ∈ envelope_209,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_209 j := by decide +kernel
theorem envelope_exact_209 : envelope_209 =
    insert (1, 4) (Finset.univ.biUnion childrenD_209) := by
  exact envelope_eq_combination childrenD_209 (1, 4) envelope_209
    pivot_mem_209 child_envelope_sub_209 envelope_origin_209
def checked_209 : CheckedCard where
  required := required_209
  envelope := envelope_209
  height := height_209
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_209
def height_212 : ℕ := 3
def childrenH_212 : Fin 2 → ℕ := ![height_5, height_76]
theorem height_exact_212 : height_212 = 1 + Finset.univ.sup childrenH_212 := by decide +kernel
theorem required_origin_212 : ∀ x ∈ required_212,
    (∃ j, x ∈ childrenC_212 j) ∨ ∀ j, x ∈ childrenD_212 j := by decide +kernel
theorem required_exact_212 : required_212 =
    ((Finset.univ.biUnion childrenC_212) ∪ commonEnvelope childrenD_212).erase (1, 4) := by
  exact required_eq_combination childrenC_212 childrenD_212 (1, 4) required_212
    (by decide +kernel) child_required_sub_212 common_sub_212 required_origin_212
theorem envelope_origin_212 : ∀ x ∈ envelope_212,
    x = (1, 4) ∨ ∃ j, x ∈ childrenD_212 j := by decide +kernel
theorem envelope_exact_212 : envelope_212 =
    insert (1, 4) (Finset.univ.biUnion childrenD_212) := by
  exact envelope_eq_combination childrenD_212 (1, 4) envelope_212
    pivot_mem_212 child_envelope_sub_212 envelope_origin_212
def checked_212 : CheckedCard where
  required := required_212
  envelope := envelope_212
  height := height_212
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_212
def height_215 : ℕ := 3
def childrenH_215 : Fin 2 → ℕ := ![height_5, height_11]
theorem height_exact_215 : height_215 = 1 + Finset.univ.sup childrenH_215 := by decide +kernel
theorem required_origin_215 : ∀ x ∈ required_215,
    (∃ j, x ∈ childrenC_215 j) ∨ ∀ j, x ∈ childrenD_215 j := by decide +kernel
theorem required_exact_215 : required_215 =
    ((Finset.univ.biUnion childrenC_215) ∪ commonEnvelope childrenD_215).erase (3, 1) := by
  exact required_eq_combination childrenC_215 childrenD_215 (3, 1) required_215
    (by decide +kernel) child_required_sub_215 common_sub_215 required_origin_215
theorem envelope_origin_215 : ∀ x ∈ envelope_215,
    x = (3, 1) ∨ ∃ j, x ∈ childrenD_215 j := by decide +kernel
theorem envelope_exact_215 : envelope_215 =
    insert (3, 1) (Finset.univ.biUnion childrenD_215) := by
  exact envelope_eq_combination childrenD_215 (3, 1) envelope_215
    pivot_mem_215 child_envelope_sub_215 envelope_origin_215
def checked_215 : CheckedCard where
  required := required_215
  envelope := envelope_215
  height := height_215
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_215
def height_218 : ℕ := 3
def childrenH_218 : Fin 2 → ℕ := ![height_0, height_83]
theorem height_exact_218 : height_218 = 1 + Finset.univ.sup childrenH_218 := by decide +kernel
theorem required_origin_218 : ∀ x ∈ required_218,
    (∃ j, x ∈ childrenC_218 j) ∨ ∀ j, x ∈ childrenD_218 j := by decide +kernel
theorem required_exact_218 : required_218 =
    ((Finset.univ.biUnion childrenC_218) ∪ commonEnvelope childrenD_218).erase (1, 2) := by
  exact required_eq_combination childrenC_218 childrenD_218 (1, 2) required_218
    (by decide +kernel) child_required_sub_218 common_sub_218 required_origin_218
theorem envelope_origin_218 : ∀ x ∈ envelope_218,
    x = (1, 2) ∨ ∃ j, x ∈ childrenD_218 j := by decide +kernel
theorem envelope_exact_218 : envelope_218 =
    insert (1, 2) (Finset.univ.biUnion childrenD_218) := by
  exact envelope_eq_combination childrenD_218 (1, 2) envelope_218
    pivot_mem_218 child_envelope_sub_218 envelope_origin_218
def checked_218 : CheckedCard where
  required := required_218
  envelope := envelope_218
  height := height_218
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_218
def height_219 : ℕ := 3
def childrenH_219 : Fin 2 → ℕ := ![height_4, height_11]
theorem height_exact_219 : height_219 = 1 + Finset.univ.sup childrenH_219 := by decide +kernel
theorem required_origin_219 : ∀ x ∈ required_219,
    (∃ j, x ∈ childrenC_219 j) ∨ ∀ j, x ∈ childrenD_219 j := by decide +kernel
theorem required_exact_219 : required_219 =
    ((Finset.univ.biUnion childrenC_219) ∪ commonEnvelope childrenD_219).erase (1, 1) := by
  exact required_eq_combination childrenC_219 childrenD_219 (1, 1) required_219
    (by decide +kernel) child_required_sub_219 common_sub_219 required_origin_219
theorem envelope_origin_219 : ∀ x ∈ envelope_219,
    x = (1, 1) ∨ ∃ j, x ∈ childrenD_219 j := by decide +kernel
theorem envelope_exact_219 : envelope_219 =
    insert (1, 1) (Finset.univ.biUnion childrenD_219) := by
  exact envelope_eq_combination childrenD_219 (1, 1) envelope_219
    pivot_mem_219 child_envelope_sub_219 envelope_origin_219
def checked_219 : CheckedCard where
  required := required_219
  envelope := envelope_219
  height := height_219
  required_sub_envelope := by decide +kernel
  height_positive := by decide +kernel
  height_le_twenty_one := by decide +kernel
  works := row_works_219
end SnakyPrototype.Certificate21

end OAI
