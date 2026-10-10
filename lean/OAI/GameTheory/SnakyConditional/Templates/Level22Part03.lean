import OAI.GameTheory.SnakyConditional.Templates.Level21Part03

namespace OAI

namespace SnakyConditional
def required_457 : Finset Cell := ⟨(([(-1, -3), (-1, -1), (0, -1), (1, -1), (2, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_457 : Finset Cell := ⟨(([(-4, 1), (-4, 3), (-3, 1), (-3, 2), (-3, 3), (-2, -2), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 1), (5, 2), (5, 3), (6, 1), (6, 3)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_457 : Fin 2 → Finset Cell := ![(placedSet 7 (-1, -2) required_28), (placedSet 0 (1, 0) required_454)]
def childrenD_457 : Fin 2 → Finset Cell := ![(placedSet 7 (-1, -2) envelope_28), (placedSet 0 (1, 0) envelope_454)]
theorem common_sub_457 : commonEnvelope childrenD_457 ⊆ insert (0, 0) required_457 := by decide
theorem child_required_sub_457 : ∀ j, childrenC_457 j ⊆ insert (0, 0) required_457 := by decide
theorem child_envelope_sub_457 : ∀ j, childrenD_457 j ⊆ envelope_457 := by decide
theorem pivot_mem_457 : (0, 0) ∈ envelope_457 := by decide
theorem children_work_457 : ∀ j, Template HasSnaky 19 (childrenC_457 j) (childrenD_457 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_28 7 (-1, -2)).mono (by decide)
  · exact (placed_template_map row_works_454 0 (1, 0)).mono (by decide)
theorem row_works_457 : Template HasSnaky 20 required_457 envelope_457 := by
  refine compose HasSnaky 19 childrenC_457 childrenD_457 children_work_457 (0, 0)
    required_457 envelope_457 pivot_mem_457 child_required_sub_457 child_envelope_sub_457 ?_
  intro b hb; exact common_sub_457 (mem_commonEnvelope childrenD_457 b hb)
end SnakyConditional

end OAI
