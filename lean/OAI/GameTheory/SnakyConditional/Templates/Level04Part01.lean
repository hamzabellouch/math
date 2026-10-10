import OAI.GameTheory.SnakyConditional.Templates.Level03Part01
import OAI.GameTheory.SnakyConditional.Templates.Level03Part03

namespace OAI

namespace SnakyConditional
def required_6 : Finset Cell := ⟨(([(-4, -1), (-3, -1), (-2, -1), (-1, -1), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_6 : Finset Cell := ⟨(([(-4, -1), (-3, -1), (-2, -1), (-1, -1), (-1, 0), (0, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_6 : Fin 1 → Finset Cell := ![(placedSet 0 (-4, -1) required_0)]
def childrenD_6 : Fin 1 → Finset Cell := ![(placedSet 0 (-4, -1) envelope_0)]
theorem common_sub_6 : commonEnvelope childrenD_6 ⊆ insert (0, 0) required_6 := by decide
theorem child_required_sub_6 : ∀ j, childrenC_6 j ⊆ insert (0, 0) required_6 := by decide
theorem child_envelope_sub_6 : ∀ j, childrenD_6 j ⊆ envelope_6 := by decide
theorem pivot_mem_6 : (0, 0) ∈ envelope_6 := by decide
theorem children_work_6 : ∀ j, Template HasSnaky 1 (childrenC_6 j) (childrenD_6 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_0 0 (-4, -1)).mono (by decide)
theorem row_works_6 : Template HasSnaky 2 required_6 envelope_6 := by
  refine compose HasSnaky 1 childrenC_6 childrenD_6 children_work_6 (0, 0)
    required_6 envelope_6 pivot_mem_6 child_required_sub_6 child_envelope_sub_6 ?_
  intro b hb; exact common_sub_6 (mem_commonEnvelope childrenD_6 b hb)
def required_10 : Finset Cell := ⟨(([(-4, -1), (-3, -1), (-3, 0), (-1, -1), (-1, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_10 : Finset Cell := ⟨(([(-4, -1), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, 0)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_10 : Fin 2 → Finset Cell := ![(placedSet 0 (-2, -1) required_2), (placedSet 6 (-2, 0) required_2)]
def childrenD_10 : Fin 2 → Finset Cell := ![(placedSet 0 (-2, -1) envelope_2), (placedSet 6 (-2, 0) envelope_2)]
theorem common_sub_10 : commonEnvelope childrenD_10 ⊆ insert (0, 0) required_10 := by decide
theorem child_required_sub_10 : ∀ j, childrenC_10 j ⊆ insert (0, 0) required_10 := by decide
theorem child_envelope_sub_10 : ∀ j, childrenD_10 j ⊆ envelope_10 := by decide
theorem pivot_mem_10 : (0, 0) ∈ envelope_10 := by decide
theorem children_work_10 : ∀ j, Template HasSnaky 1 (childrenC_10 j) (childrenD_10 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_2 0 (-2, -1)).mono (by decide)
  · exact (placed_template_map row_works_2 6 (-2, 0)).mono (by decide)
theorem row_works_10 : Template HasSnaky 2 required_10 envelope_10 := by
  refine compose HasSnaky 1 childrenC_10 childrenD_10 children_work_10 (0, 0)
    required_10 envelope_10 pivot_mem_10 child_required_sub_10 child_envelope_sub_10 ?_
  intro b hb; exact common_sub_10 (mem_commonEnvelope childrenD_10 b hb)
end SnakyConditional

end OAI
