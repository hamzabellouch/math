import OAI.GameTheory.SnakyConditional.Templates.Level03Part01
import OAI.GameTheory.SnakyConditional.Templates.Level03Part04

namespace OAI

namespace SnakyConditional
def required_22 : Finset Cell := ⟨(([(-2, 0), (-1, 0), (0, 1), (1, 1), (2, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_22 : Finset Cell := ⟨(([(-2, 0), (-1, 0), (0, 0), (0, 1), (1, 0), (1, 1), (2, 1), (3, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_22 : Fin 2 → Finset Cell := ![(placedSet 6 (3, 1) required_0), (placedSet 0 (1, 0) required_3)]
def childrenD_22 : Fin 2 → Finset Cell := ![(placedSet 6 (3, 1) envelope_0), (placedSet 0 (1, 0) envelope_3)]
theorem common_sub_22 : commonEnvelope childrenD_22 ⊆ insert (0, 0) required_22 := by decide
theorem child_required_sub_22 : ∀ j, childrenC_22 j ⊆ insert (0, 0) required_22 := by decide
theorem child_envelope_sub_22 : ∀ j, childrenD_22 j ⊆ envelope_22 := by decide
theorem pivot_mem_22 : (0, 0) ∈ envelope_22 := by decide
theorem children_work_22 : ∀ j, Template HasSnaky 1 (childrenC_22 j) (childrenD_22 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_0 6 (3, 1)).mono (by decide)
  · exact (placed_template_map row_works_3 0 (1, 0)).mono (by decide)
theorem row_works_22 : Template HasSnaky 2 required_22 envelope_22 := by
  refine compose HasSnaky 1 childrenC_22 childrenD_22 children_work_22 (0, 0)
    required_22 envelope_22 pivot_mem_22 child_required_sub_22 child_envelope_sub_22 ?_
  intro b hb; exact common_sub_22 (mem_commonEnvelope childrenD_22 b hb)
def required_23 : Finset Cell := ⟨(([(-2, -1), (-1, -1), (-1, 0), (0, -1), (1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_23 : Finset Cell := ⟨(([(-3, -1), (-2, -1), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, 0), (2, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_23 : Fin 2 → Finset Cell := ![(placedSet 6 (2, 0) required_0), (placedSet 0 (-3, -1) required_0)]
def childrenD_23 : Fin 2 → Finset Cell := ![(placedSet 6 (2, 0) envelope_0), (placedSet 0 (-3, -1) envelope_0)]
theorem common_sub_23 : commonEnvelope childrenD_23 ⊆ insert (0, 0) required_23 := by decide
theorem child_required_sub_23 : ∀ j, childrenC_23 j ⊆ insert (0, 0) required_23 := by decide
theorem child_envelope_sub_23 : ∀ j, childrenD_23 j ⊆ envelope_23 := by decide
theorem pivot_mem_23 : (0, 0) ∈ envelope_23 := by decide
theorem children_work_23 : ∀ j, Template HasSnaky 1 (childrenC_23 j) (childrenD_23 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_0 6 (2, 0)).mono (by decide)
  · exact (placed_template_map row_works_0 0 (-3, -1)).mono (by decide)
theorem row_works_23 : Template HasSnaky 2 required_23 envelope_23 := by
  refine compose HasSnaky 1 childrenC_23 childrenD_23 children_work_23 (0, 0)
    required_23 envelope_23 pivot_mem_23 child_required_sub_23 child_envelope_sub_23 ?_
  intro b hb; exact common_sub_23 (mem_commonEnvelope childrenD_23 b hb)
end SnakyConditional

end OAI
