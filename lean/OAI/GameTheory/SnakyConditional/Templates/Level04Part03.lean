import OAI.GameTheory.SnakyConditional.Templates.Level03Part01
import OAI.GameTheory.SnakyConditional.Templates.Level03Part04

namespace OAI

namespace SnakyConditional
def required_15 : Finset Cell := ⟨(([(-3, -1), (-2, -1), (-1, -1), (-1, 0), (1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_15 : Finset Cell := ⟨(([(-3, -1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, 0), (1, 0), (2, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_15 : Fin 2 → Finset Cell := ![(placedSet 6 (2, 0) required_0), (placedSet 6 (-2, 0) required_3)]
def childrenD_15 : Fin 2 → Finset Cell := ![(placedSet 6 (2, 0) envelope_0), (placedSet 6 (-2, 0) envelope_3)]
theorem common_sub_15 : commonEnvelope childrenD_15 ⊆ insert (0, 0) required_15 := by decide
theorem child_required_sub_15 : ∀ j, childrenC_15 j ⊆ insert (0, 0) required_15 := by decide
theorem child_envelope_sub_15 : ∀ j, childrenD_15 j ⊆ envelope_15 := by decide
theorem pivot_mem_15 : (0, 0) ∈ envelope_15 := by decide
theorem children_work_15 : ∀ j, Template HasSnaky 1 (childrenC_15 j) (childrenD_15 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_0 6 (2, 0)).mono (by decide)
  · exact (placed_template_map row_works_3 6 (-2, 0)).mono (by decide)
theorem row_works_15 : Template HasSnaky 2 required_15 envelope_15 := by
  refine compose HasSnaky 1 childrenC_15 childrenD_15 children_work_15 (0, 0)
    required_15 envelope_15 pivot_mem_15 child_required_sub_15 child_envelope_sub_15 ?_
  intro b hb; exact common_sub_15 (mem_commonEnvelope childrenD_15 b hb)
def required_16 : Finset Cell := ⟨(([(-2, -1), (-1, -1), (0, -1), (1, 0), (2, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_16 : Finset Cell := ⟨(([(-2, -1), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, 0), (2, 0), (3, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_16 : Fin 2 → Finset Cell := ![(placedSet 6 (-1, 0) required_3), (placedSet 6 (3, 0) required_0)]
def childrenD_16 : Fin 2 → Finset Cell := ![(placedSet 6 (-1, 0) envelope_3), (placedSet 6 (3, 0) envelope_0)]
theorem common_sub_16 : commonEnvelope childrenD_16 ⊆ insert (0, 0) required_16 := by decide
theorem child_required_sub_16 : ∀ j, childrenC_16 j ⊆ insert (0, 0) required_16 := by decide
theorem child_envelope_sub_16 : ∀ j, childrenD_16 j ⊆ envelope_16 := by decide
theorem pivot_mem_16 : (0, 0) ∈ envelope_16 := by decide
theorem children_work_16 : ∀ j, Template HasSnaky 1 (childrenC_16 j) (childrenD_16 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_3 6 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_0 6 (3, 0)).mono (by decide)
theorem row_works_16 : Template HasSnaky 2 required_16 envelope_16 := by
  refine compose HasSnaky 1 childrenC_16 childrenD_16 children_work_16 (0, 0)
    required_16 envelope_16 pivot_mem_16 child_required_sub_16 child_envelope_sub_16 ?_
  intro b hb; exact common_sub_16 (mem_commonEnvelope childrenD_16 b hb)
end SnakyConditional

end OAI
