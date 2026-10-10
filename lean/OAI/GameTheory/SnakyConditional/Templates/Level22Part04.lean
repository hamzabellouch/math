import OAI.GameTheory.SnakyConditional.Templates.Level21Part02

namespace OAI

namespace SnakyConditional
def required_459 : Finset Cell := ⟨(([(-1, -1), (0, -2), (0, -1), (1, -1), (2, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_459 : Finset Cell := ⟨(([(-4, 1), (-4, 3), (-3, -1), (-3, 1), (-3, 2), (-3, 3), (-2, -1), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -2), (3, -1), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, -2), (4, -1), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, -2), (5, 1), (5, 2), (5, 3), (6, 1), (6, 3)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_459 : Fin 3 → Finset Cell := ![(placedSet 2 (3, -1) required_97), (placedSet 0 (1, 0) required_448), (placedSet 2 (3, -1) required_65)]
def childrenD_459 : Fin 3 → Finset Cell := ![(placedSet 2 (3, -1) envelope_97), (placedSet 0 (1, 0) envelope_448), (placedSet 2 (3, -1) envelope_65)]
theorem common_sub_459 : commonEnvelope childrenD_459 ⊆ insert (0, 0) required_459 := by decide
theorem child_required_sub_459 : ∀ j, childrenC_459 j ⊆ insert (0, 0) required_459 := by decide
theorem child_envelope_sub_459 : ∀ j, childrenD_459 j ⊆ envelope_459 := by decide
theorem pivot_mem_459 : (0, 0) ∈ envelope_459 := by decide
theorem children_work_459 : ∀ j, Template HasSnaky 19 (childrenC_459 j) (childrenD_459 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_97 2 (3, -1)).mono (by decide)
  · exact (placed_template_map row_works_448 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_65 2 (3, -1)).mono (by decide)
theorem row_works_459 : Template HasSnaky 20 required_459 envelope_459 := by
  refine compose HasSnaky 19 childrenC_459 childrenD_459 children_work_459 (0, 0)
    required_459 envelope_459 pivot_mem_459 child_required_sub_459 child_envelope_sub_459 ?_
  intro b hb; exact common_sub_459 (mem_commonEnvelope childrenD_459 b hb)
end SnakyConditional

end OAI
