import OAI.GameTheory.SnakyConditional.Templates.Level17Part01

namespace OAI

namespace SnakyConditional
def required_442 : Finset Cell := ⟨(([(0, -4), (0, -3), (0, -2), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_442 : Finset Cell := ⟨(([(-3, -2), (-2, -2), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (6, 0), (6, 1), (6, 2), (6, 3), (7, 0), (7, 1), (7, 2), (7, 3)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_442 : Fin 4 → Finset Cell := ![(placedSet 0 (-1, 1) required_63), (placedSet 1 (1, 0) required_7), (placedSet 0 (0, 1) required_433), (placedSet 0 (-1, -2) required_201)]
def childrenD_442 : Fin 4 → Finset Cell := ![(placedSet 0 (-1, 1) envelope_63), (placedSet 1 (1, 0) envelope_7), (placedSet 0 (0, 1) envelope_433), (placedSet 0 (-1, -2) envelope_201)]
theorem common_sub_442 : commonEnvelope childrenD_442 ⊆ insert (0, 0) required_442 := by decide
theorem child_required_sub_442 : ∀ j, childrenC_442 j ⊆ insert (0, 0) required_442 := by decide
theorem child_envelope_sub_442 : ∀ j, childrenD_442 j ⊆ envelope_442 := by decide
theorem pivot_mem_442 : (0, 0) ∈ envelope_442 := by decide
theorem children_work_442 : ∀ j, Template HasSnaky 15 (childrenC_442 j) (childrenD_442 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_63 0 (-1, 1)).mono (by decide)
  · exact (placed_template_map row_works_7 1 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_433 0 (0, 1)).mono (by decide)
  · exact (placed_template_map row_works_201 0 (-1, -2)).mono (by decide)
theorem row_works_442 : Template HasSnaky 16 required_442 envelope_442 := by
  refine compose HasSnaky 15 childrenC_442 childrenD_442 children_work_442 (0, 0)
    required_442 envelope_442 pivot_mem_442 child_required_sub_442 child_envelope_sub_442 ?_
  intro b hb; exact common_sub_442 (mem_commonEnvelope childrenD_442 b hb)
end SnakyConditional

end OAI
