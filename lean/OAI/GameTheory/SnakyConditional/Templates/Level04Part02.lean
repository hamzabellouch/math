import OAI.GameTheory.SnakyConditional.Templates.Level03Part01
import OAI.GameTheory.SnakyConditional.Templates.Level03Part04

namespace OAI

namespace SnakyConditional
def required_12 : Finset Cell := ⟨(([(-3, -1), (-2, -1), (-2, 0), (-1, -1), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_12 : Finset Cell := ⟨(([(-4, -1), (-3, -1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, 0), (1, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_12 : Fin 2 → Finset Cell := ![(placedSet 6 (1, 0) required_0), (placedSet 0 (-4, -1) required_0)]
def childrenD_12 : Fin 2 → Finset Cell := ![(placedSet 6 (1, 0) envelope_0), (placedSet 0 (-4, -1) envelope_0)]
theorem common_sub_12 : commonEnvelope childrenD_12 ⊆ insert (0, 0) required_12 := by decide
theorem child_required_sub_12 : ∀ j, childrenC_12 j ⊆ insert (0, 0) required_12 := by decide
theorem child_envelope_sub_12 : ∀ j, childrenD_12 j ⊆ envelope_12 := by decide
theorem pivot_mem_12 : (0, 0) ∈ envelope_12 := by decide
theorem children_work_12 : ∀ j, Template HasSnaky 1 (childrenC_12 j) (childrenD_12 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_0 6 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_0 0 (-4, -1)).mono (by decide)
theorem row_works_12 : Template HasSnaky 2 required_12 envelope_12 := by
  refine compose HasSnaky 1 childrenC_12 childrenD_12 children_work_12 (0, 0)
    required_12 envelope_12 pivot_mem_12 child_required_sub_12 child_envelope_sub_12 ?_
  intro b hb; exact common_sub_12 (mem_commonEnvelope childrenD_12 b hb)
def required_14 : Finset Cell := ⟨(([(-4, -1), (-3, -1), (-2, -1), (-2, 0), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_14 : Finset Cell := ⟨(([(-4, -1), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, 0), (0, 0), (1, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_14 : Fin 2 → Finset Cell := ![(placedSet 6 (1, 0) required_0), (placedSet 6 (-3, 0) required_3)]
def childrenD_14 : Fin 2 → Finset Cell := ![(placedSet 6 (1, 0) envelope_0), (placedSet 6 (-3, 0) envelope_3)]
theorem common_sub_14 : commonEnvelope childrenD_14 ⊆ insert (0, 0) required_14 := by decide
theorem child_required_sub_14 : ∀ j, childrenC_14 j ⊆ insert (0, 0) required_14 := by decide
theorem child_envelope_sub_14 : ∀ j, childrenD_14 j ⊆ envelope_14 := by decide
theorem pivot_mem_14 : (0, 0) ∈ envelope_14 := by decide
theorem children_work_14 : ∀ j, Template HasSnaky 1 (childrenC_14 j) (childrenD_14 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_0 6 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_3 6 (-3, 0)).mono (by decide)
theorem row_works_14 : Template HasSnaky 2 required_14 envelope_14 := by
  refine compose HasSnaky 1 childrenC_14 childrenD_14 children_work_14 (0, 0)
    required_14 envelope_14 pivot_mem_14 child_required_sub_14 child_envelope_sub_14 ?_
  intro b hb; exact common_sub_14 (mem_commonEnvelope childrenD_14 b hb)
end SnakyConditional

end OAI
