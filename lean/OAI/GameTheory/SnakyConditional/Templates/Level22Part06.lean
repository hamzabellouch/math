import OAI.GameTheory.SnakyConditional.Templates.Level21Part04

namespace OAI

namespace SnakyConditional
def required_468 : Finset Cell := ⟨(([(0, 1), (0, 2), (1, 1), (2, 1), (3, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_468 : Finset Cell := ⟨(([(-2, 8), (-1, 0), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, 1), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (7, 5), (7, 6), (7, 7), (7, 8)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_468 : Fin 2 → Finset Cell := ![(placedSet 6 (-1, 0) required_6), (placedSet 0 (0, 3) required_464)]
def childrenD_468 : Fin 2 → Finset Cell := ![(placedSet 6 (-1, 0) envelope_6), (placedSet 0 (0, 3) envelope_464)]
theorem common_sub_468 : commonEnvelope childrenD_468 ⊆ insert (0, 0) required_468 := by decide
theorem child_required_sub_468 : ∀ j, childrenC_468 j ⊆ insert (0, 0) required_468 := by decide
theorem child_envelope_sub_468 : ∀ j, childrenD_468 j ⊆ envelope_468 := by decide
theorem pivot_mem_468 : (0, 0) ∈ envelope_468 := by decide
theorem children_work_468 : ∀ j, Template HasSnaky 19 (childrenC_468 j) (childrenD_468 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 6 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_464 0 (0, 3)).mono (by decide)
theorem row_works_468 : Template HasSnaky 20 required_468 envelope_468 := by
  refine compose HasSnaky 19 childrenC_468 childrenD_468 children_work_468 (0, 0)
    required_468 envelope_468 pivot_mem_468 child_required_sub_468 child_envelope_sub_468 ?_
  intro b hb; exact common_sub_468 (mem_commonEnvelope childrenD_468 b hb)
end SnakyConditional

end OAI
