import OAI.GameTheory.SnakyConditional.Templates.Level17Part04

namespace OAI

namespace SnakyConditional
def required_477 : Finset Cell := ⟨(([(0, -3), (0, -2), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_477 : Finset Cell := ⟨(([(-5, -3), (-5, -2), (-5, -1), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-1, -7), (-1, -6), (-1, -5), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -6), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -7), (1, -6), (1, -5), (1, -4), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -6), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (6, -4), (6, -3), (6, -2), (6, -1), (7, -4), (7, -3), (7, -2), (7, -1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_477 : Fin 4 → Finset Cell := ![(placedSet 1 (0, 1) required_55), (placedSet 7 (0, 1) required_154), (placedSet 3 (0, -4) required_154), (placedSet 2 (1, 0) required_471)]
def childrenD_477 : Fin 4 → Finset Cell := ![(placedSet 1 (0, 1) envelope_55), (placedSet 7 (0, 1) envelope_154), (placedSet 3 (0, -4) envelope_154), (placedSet 2 (1, 0) envelope_471)]
theorem common_sub_477 : commonEnvelope childrenD_477 ⊆ insert (0, 0) required_477 := by decide
theorem child_required_sub_477 : ∀ j, childrenC_477 j ⊆ insert (0, 0) required_477 := by decide
theorem child_envelope_sub_477 : ∀ j, childrenD_477 j ⊆ envelope_477 := by decide
theorem pivot_mem_477 : (0, 0) ∈ envelope_477 := by decide
theorem children_work_477 : ∀ j, Template HasSnaky 15 (childrenC_477 j) (childrenD_477 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_55 1 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_154 7 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_154 3 (0, -4)).mono (by decide)
  · exact (placed_template_map row_works_471 2 (1, 0)).mono (by decide)
theorem row_works_477 : Template HasSnaky 16 required_477 envelope_477 := by
  refine compose HasSnaky 15 childrenC_477 childrenD_477 children_work_477 (0, 0)
    required_477 envelope_477 pivot_mem_477 child_required_sub_477 child_envelope_sub_477 ?_
  intro b hb; exact common_sub_477 (mem_commonEnvelope childrenD_477 b hb)
end SnakyConditional

end OAI
