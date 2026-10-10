import OAI.GameTheory.SnakyConditional.Templates.Level03Part02
import OAI.GameTheory.SnakyConditional.Templates.Level05Part01
import OAI.GameTheory.SnakyConditional.Templates.Level05Part02
import OAI.GameTheory.SnakyConditional.Templates.Level05Part05
import OAI.GameTheory.SnakyConditional.Templates.Level05Part07
import OAI.GameTheory.SnakyConditional.Templates.Level05Part08

namespace OAI

namespace SnakyConditional
def required_103 : Finset Cell := ⟨(([(1, -3), (1, -2), (1, -1), (1, 0), (3, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_103 : Finset Cell := ⟨(([(-1, 0), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, -1), (2, 0), (2, 1), (3, -1), (4, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_103 : Fin 2 → Finset Cell := ![(placedSet 3 (0, 1) required_6), (placedSet 0 (2, 0) required_71)]
def childrenD_103 : Fin 2 → Finset Cell := ![(placedSet 3 (0, 1) envelope_6), (placedSet 0 (2, 0) envelope_71)]
theorem common_sub_103 : commonEnvelope childrenD_103 ⊆ insert (0, 0) required_103 := by decide
theorem child_required_sub_103 : ∀ j, childrenC_103 j ⊆ insert (0, 0) required_103 := by decide
theorem child_envelope_sub_103 : ∀ j, childrenD_103 j ⊆ envelope_103 := by decide
theorem pivot_mem_103 : (0, 0) ∈ envelope_103 := by decide
theorem children_work_103 : ∀ j, Template HasSnaky 3 (childrenC_103 j) (childrenD_103 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 3 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_71 0 (2, 0)).mono (by decide)
theorem row_works_103 : Template HasSnaky 4 required_103 envelope_103 := by
  refine compose HasSnaky 3 childrenC_103 childrenD_103 children_work_103 (0, 0)
    required_103 envelope_103 pivot_mem_103 child_required_sub_103 child_envelope_sub_103 ?_
  intro b hb; exact common_sub_103 (mem_commonEnvelope childrenD_103 b hb)
def required_105 : Finset Cell := ⟨(([(-2, 0), (-1, 0), (-1, 1), (-1, 2), (-1, 3)] : List Cell) : Multiset Cell), by decide⟩
def envelope_105 : Finset Cell := ⟨(([(-3, 0), (-2, 0), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (1, 1), (2, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_105 : Fin 2 → Finset Cell := ![(placedSet 5 (0, -1) required_6), (placedSet 0 (0, 1) required_77)]
def childrenD_105 : Fin 2 → Finset Cell := ![(placedSet 5 (0, -1) envelope_6), (placedSet 0 (0, 1) envelope_77)]
theorem common_sub_105 : commonEnvelope childrenD_105 ⊆ insert (0, 0) required_105 := by decide
theorem child_required_sub_105 : ∀ j, childrenC_105 j ⊆ insert (0, 0) required_105 := by decide
theorem child_envelope_sub_105 : ∀ j, childrenD_105 j ⊆ envelope_105 := by decide
theorem pivot_mem_105 : (0, 0) ∈ envelope_105 := by decide
theorem children_work_105 : ∀ j, Template HasSnaky 3 (childrenC_105 j) (childrenD_105 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 5 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_77 0 (0, 1)).mono (by decide)
theorem row_works_105 : Template HasSnaky 4 required_105 envelope_105 := by
  refine compose HasSnaky 3 childrenC_105 childrenD_105 children_work_105 (0, 0)
    required_105 envelope_105 pivot_mem_105 child_required_sub_105 child_envelope_sub_105 ?_
  intro b hb; exact common_sub_105 (mem_commonEnvelope childrenD_105 b hb)
def required_106 : Finset Cell := ⟨(([(-2, -1), (-1, -3), (-1, -2), (-1, -1), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_106 : Finset Cell := ⟨(([(-4, -1), (-3, -1), (-2, -1), (-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, 0), (0, 1), (1, 0), (2, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_106 : Fin 2 → Finset Cell := ![(placedSet 1 (0, 1) required_6), (placedSet 6 (1, 0) required_36)]
def childrenD_106 : Fin 2 → Finset Cell := ![(placedSet 1 (0, 1) envelope_6), (placedSet 6 (1, 0) envelope_36)]
theorem common_sub_106 : commonEnvelope childrenD_106 ⊆ insert (0, 0) required_106 := by decide
theorem child_required_sub_106 : ∀ j, childrenC_106 j ⊆ insert (0, 0) required_106 := by decide
theorem child_envelope_sub_106 : ∀ j, childrenD_106 j ⊆ envelope_106 := by decide
theorem pivot_mem_106 : (0, 0) ∈ envelope_106 := by decide
theorem children_work_106 : ∀ j, Template HasSnaky 3 (childrenC_106 j) (childrenD_106 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 1 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_36 6 (1, 0)).mono (by decide)
theorem row_works_106 : Template HasSnaky 4 required_106 envelope_106 := by
  refine compose HasSnaky 3 childrenC_106 childrenD_106 children_work_106 (0, 0)
    required_106 envelope_106 pivot_mem_106 child_required_sub_106 child_envelope_sub_106 ?_
  intro b hb; exact common_sub_106 (mem_commonEnvelope childrenD_106 b hb)
def required_113 : Finset Cell := ⟨(([(-1, -1), (0, -1), (1, 0), (1, 1), (2, 1), (3, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_113 : Finset Cell := ⟨(([(-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (2, 0), (2, 1), (3, 0), (3, 1), (4, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_113 : Fin 2 → Finset Cell := ![(placedSet 6 (2, 0) required_1), (placedSet 6 (3, 1) required_36)]
def childrenD_113 : Fin 2 → Finset Cell := ![(placedSet 6 (2, 0) envelope_1), (placedSet 6 (3, 1) envelope_36)]
theorem common_sub_113 : commonEnvelope childrenD_113 ⊆ insert (0, 0) required_113 := by decide
theorem child_required_sub_113 : ∀ j, childrenC_113 j ⊆ insert (0, 0) required_113 := by decide
theorem child_envelope_sub_113 : ∀ j, childrenD_113 j ⊆ envelope_113 := by decide
theorem pivot_mem_113 : (0, 0) ∈ envelope_113 := by decide
theorem children_work_113 : ∀ j, Template HasSnaky 3 (childrenC_113 j) (childrenD_113 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_1 6 (2, 0)).mono (by decide)
  · exact (placed_template_map row_works_36 6 (3, 1)).mono (by decide)
theorem row_works_113 : Template HasSnaky 4 required_113 envelope_113 := by
  refine compose HasSnaky 3 childrenC_113 childrenD_113 children_work_113 (0, 0)
    required_113 envelope_113 pivot_mem_113 child_required_sub_113 child_envelope_sub_113 ?_
  intro b hb; exact common_sub_113 (mem_commonEnvelope childrenD_113 b hb)
def required_116 : Finset Cell := ⟨(([(-2, 1), (-1, -2), (-1, -1), (-1, 1), (0, -1), (0, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_116 : Finset Cell := ⟨(([(-3, 1), (-2, 1), (-1, -2), (-1, -1), (-1, 1), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (2, 0), (3, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_116 : Fin 2 → Finset Cell := ![(placedSet 7 (0, 2) required_0), (placedSet 2 (1, 0) required_24)]
def childrenD_116 : Fin 2 → Finset Cell := ![(placedSet 7 (0, 2) envelope_0), (placedSet 2 (1, 0) envelope_24)]
theorem common_sub_116 : commonEnvelope childrenD_116 ⊆ insert (0, 0) required_116 := by decide
theorem child_required_sub_116 : ∀ j, childrenC_116 j ⊆ insert (0, 0) required_116 := by decide
theorem child_envelope_sub_116 : ∀ j, childrenD_116 j ⊆ envelope_116 := by decide
theorem pivot_mem_116 : (0, 0) ∈ envelope_116 := by decide
theorem children_work_116 : ∀ j, Template HasSnaky 3 (childrenC_116 j) (childrenD_116 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_0 7 (0, 2)).mono (by decide)
  · exact (placed_template_map row_works_24 2 (1, 0)).mono (by decide)
theorem row_works_116 : Template HasSnaky 4 required_116 envelope_116 := by
  refine compose HasSnaky 3 childrenC_116 childrenD_116 children_work_116 (0, 0)
    required_116 envelope_116 pivot_mem_116 child_required_sub_116 child_envelope_sub_116 ?_
  intro b hb; exact common_sub_116 (mem_commonEnvelope childrenD_116 b hb)
def required_118 : Finset Cell := ⟨(([(-2, -1), (-1, -4), (-1, -1), (0, -3), (0, -2), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_118 : Finset Cell := ⟨(([(-2, -1), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (0, -3), (0, -2), (0, -1), (0, 0), (1, 0), (1, 1), (2, 0), (3, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_118 : Fin 2 → Finset Cell := ![(placedSet 7 (-1, -3) required_4), (placedSet 1 (1, 0) required_61)]
def childrenD_118 : Fin 2 → Finset Cell := ![(placedSet 7 (-1, -3) envelope_4), (placedSet 1 (1, 0) envelope_61)]
theorem common_sub_118 : commonEnvelope childrenD_118 ⊆ insert (0, 0) required_118 := by decide
theorem child_required_sub_118 : ∀ j, childrenC_118 j ⊆ insert (0, 0) required_118 := by decide
theorem child_envelope_sub_118 : ∀ j, childrenD_118 j ⊆ envelope_118 := by decide
theorem pivot_mem_118 : (0, 0) ∈ envelope_118 := by decide
theorem children_work_118 : ∀ j, Template HasSnaky 3 (childrenC_118 j) (childrenD_118 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_4 7 (-1, -3)).mono (by decide)
  · exact (placed_template_map row_works_61 1 (1, 0)).mono (by decide)
theorem row_works_118 : Template HasSnaky 4 required_118 envelope_118 := by
  refine compose HasSnaky 3 childrenC_118 childrenD_118 children_work_118 (0, 0)
    required_118 envelope_118 pivot_mem_118 child_required_sub_118 child_envelope_sub_118 ?_
  intro b hb; exact common_sub_118 (mem_commonEnvelope childrenD_118 b hb)
def required_121 : Finset Cell := ⟨(([(-1, -2), (-1, -1), (0, -4), (0, -3), (0, -2), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_121 : Finset Cell := ⟨(([(-1, -3), (-1, -2), (-1, -1), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -1), (1, 0), (1, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_121 : Fin 2 → Finset Cell := ![(placedSet 3 (0, 1) required_9), (placedSet 1 (1, 0) required_7)]
def childrenD_121 : Fin 2 → Finset Cell := ![(placedSet 3 (0, 1) envelope_9), (placedSet 1 (1, 0) envelope_7)]
theorem common_sub_121 : commonEnvelope childrenD_121 ⊆ insert (0, 0) required_121 := by decide
theorem child_required_sub_121 : ∀ j, childrenC_121 j ⊆ insert (0, 0) required_121 := by decide
theorem child_envelope_sub_121 : ∀ j, childrenD_121 j ⊆ envelope_121 := by decide
theorem pivot_mem_121 : (0, 0) ∈ envelope_121 := by decide
theorem children_work_121 : ∀ j, Template HasSnaky 3 (childrenC_121 j) (childrenD_121 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_9 3 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_7 1 (1, 0)).mono (by decide)
theorem row_works_121 : Template HasSnaky 4 required_121 envelope_121 := by
  refine compose HasSnaky 3 childrenC_121 childrenD_121 children_work_121 (0, 0)
    required_121 envelope_121 pivot_mem_121 child_required_sub_121 child_envelope_sub_121 ?_
  intro b hb; exact common_sub_121 (mem_commonEnvelope childrenD_121 b hb)
end SnakyConditional

end OAI
