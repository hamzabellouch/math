import OAI.GameTheory.SnakyConditional.Templates.Level03Part01
import OAI.GameTheory.SnakyConditional.Templates.Level03Part04

namespace OAI

namespace SnakyConditional
def required_17 : Finset Cell := ⟨(([(-4, -1), (-3, -1), (-2, -1), (-2, 0), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_17 : Finset Cell := ⟨(([(-4, -1), (-3, -1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, 0), (1, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_17 : Fin 2 → Finset Cell := ![(placedSet 6 (1, 0) required_0), (placedSet 0 (-1, -1) required_3)]
def childrenD_17 : Fin 2 → Finset Cell := ![(placedSet 6 (1, 0) envelope_0), (placedSet 0 (-1, -1) envelope_3)]
theorem common_sub_17 : commonEnvelope childrenD_17 ⊆ insert (0, 0) required_17 := by decide
theorem child_required_sub_17 : ∀ j, childrenC_17 j ⊆ insert (0, 0) required_17 := by decide
theorem child_envelope_sub_17 : ∀ j, childrenD_17 j ⊆ envelope_17 := by decide
theorem pivot_mem_17 : (0, 0) ∈ envelope_17 := by decide
theorem children_work_17 : ∀ j, Template HasSnaky 1 (childrenC_17 j) (childrenD_17 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_0 6 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_3 0 (-1, -1)).mono (by decide)
theorem row_works_17 : Template HasSnaky 2 required_17 envelope_17 := by
  refine compose HasSnaky 1 childrenC_17 childrenD_17 children_work_17 (0, 0)
    required_17 envelope_17 pivot_mem_17 child_required_sub_17 child_envelope_sub_17 ?_
  intro b hb; exact common_sub_17 (mem_commonEnvelope childrenD_17 b hb)
def required_18 : Finset Cell := ⟨(([(-3, -1), (-2, -1), (-1, -1), (-1, 0), (1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_18 : Finset Cell := ⟨(([(-3, -1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_18 : Fin 2 → Finset Cell := ![(placedSet 6 (-2, 0) required_3), (placedSet 0 (0, -1) required_3)]
def childrenD_18 : Fin 2 → Finset Cell := ![(placedSet 6 (-2, 0) envelope_3), (placedSet 0 (0, -1) envelope_3)]
theorem common_sub_18 : commonEnvelope childrenD_18 ⊆ insert (0, 0) required_18 := by decide
theorem child_required_sub_18 : ∀ j, childrenC_18 j ⊆ insert (0, 0) required_18 := by decide
theorem child_envelope_sub_18 : ∀ j, childrenD_18 j ⊆ envelope_18 := by decide
theorem pivot_mem_18 : (0, 0) ∈ envelope_18 := by decide
theorem children_work_18 : ∀ j, Template HasSnaky 1 (childrenC_18 j) (childrenD_18 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_3 6 (-2, 0)).mono (by decide)
  · exact (placed_template_map row_works_3 0 (0, -1)).mono (by decide)
theorem row_works_18 : Template HasSnaky 2 required_18 envelope_18 := by
  refine compose HasSnaky 1 childrenC_18 childrenD_18 children_work_18 (0, 0)
    required_18 envelope_18 pivot_mem_18 child_required_sub_18 child_envelope_sub_18 ?_
  intro b hb; exact common_sub_18 (mem_commonEnvelope childrenD_18 b hb)
end SnakyConditional

end OAI
