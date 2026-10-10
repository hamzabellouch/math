import OAI.GameTheory.SnakyConditional.Templates.Level17Part03

namespace OAI

namespace SnakyConditional
def required_449 : Finset Cell := ⟨(([(-1, -3), (-1, -2), (-1, 0), (0, -4), (0, -3), (0, -2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_449 : Finset Cell := ⟨(([(-4, 1), (-4, 3), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (6, 1)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_449 : Fin 4 → Finset Cell := ![(placedSet 3 (0, -1) required_26), (placedSet 0 (1, 0) required_244), (placedSet 0 (1, 0) required_439), (placedSet 0 (0, -1) required_307)]
def childrenD_449 : Fin 4 → Finset Cell := ![(placedSet 3 (0, -1) envelope_26), (placedSet 0 (1, 0) envelope_244), (placedSet 0 (1, 0) envelope_439), (placedSet 0 (0, -1) envelope_307)]
theorem common_sub_449 : commonEnvelope childrenD_449 ⊆ insert (0, 0) required_449 := by decide
theorem child_required_sub_449 : ∀ j, childrenC_449 j ⊆ insert (0, 0) required_449 := by decide
theorem child_envelope_sub_449 : ∀ j, childrenD_449 j ⊆ envelope_449 := by decide
theorem pivot_mem_449 : (0, 0) ∈ envelope_449 := by decide
theorem children_work_449 : ∀ j, Template HasSnaky 15 (childrenC_449 j) (childrenD_449 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_26 3 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_244 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_439 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_307 0 (0, -1)).mono (by decide)
theorem row_works_449 : Template HasSnaky 16 required_449 envelope_449 := by
  refine compose HasSnaky 15 childrenC_449 childrenD_449 children_work_449 (0, 0)
    required_449 envelope_449 pivot_mem_449 child_required_sub_449 child_envelope_sub_449 ?_
  intro b hb; exact common_sub_449 (mem_commonEnvelope childrenD_449 b hb)
end SnakyConditional

end OAI
