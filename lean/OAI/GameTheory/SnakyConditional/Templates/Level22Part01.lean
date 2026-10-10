import OAI.GameTheory.SnakyConditional.Templates.Level21Part01

namespace OAI

namespace SnakyConditional
def required_443 : Finset Cell := ⟨(([(-3, -1), (-2, -1), (-1, -1), (0, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_443 : Finset Cell := ⟨(([(-4, -1), (-4, 1), (-4, 2), (-4, 3), (-3, -1), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-2, -2), (-2, -1), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 1), (4, 2), (4, 3), (5, 1), (5, 3)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_443 : Fin 2 → Finset Cell := ![(placedSet 0 (1, 0) required_6), (placedSet 0 (-1, 0) required_438)]
def childrenD_443 : Fin 2 → Finset Cell := ![(placedSet 0 (1, 0) envelope_6), (placedSet 0 (-1, 0) envelope_438)]
theorem common_sub_443 : commonEnvelope childrenD_443 ⊆ insert (0, 0) required_443 := by decide
theorem child_required_sub_443 : ∀ j, childrenC_443 j ⊆ insert (0, 0) required_443 := by decide
theorem child_envelope_sub_443 : ∀ j, childrenD_443 j ⊆ envelope_443 := by decide
theorem pivot_mem_443 : (0, 0) ∈ envelope_443 := by decide
theorem children_work_443 : ∀ j, Template HasSnaky 19 (childrenC_443 j) (childrenD_443 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 0 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_438 0 (-1, 0)).mono (by decide)
theorem row_works_443 : Template HasSnaky 20 required_443 envelope_443 := by
  refine compose HasSnaky 19 childrenC_443 childrenD_443 children_work_443 (0, 0)
    required_443 envelope_443 pivot_mem_443 child_required_sub_443 child_envelope_sub_443 ?_
  intro b hb; exact common_sub_443 (mem_commonEnvelope childrenD_443 b hb)
end SnakyConditional

end OAI
