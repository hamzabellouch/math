import OAI.GameTheory.SnakyConditional.Templates.Level17Part04

namespace OAI

namespace SnakyConditional
def required_529 : Finset Cell := ⟨(([(1, 0), (2, 0), (3, 0)] : List Cell) : Multiset Cell), by decide⟩
def envelope_529 : Finset Cell := ⟨(([(-2, -1), (-2, 1), (-2, 4), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 0), (1, 2), (1, 3), (1, 4), (1, 5), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (7, 1), (7, 2), (7, 3), (7, 4)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_529 : Fin 4 → Finset Cell := ![(placedSet 4 (-1, 0) required_55), (placedSet 0 (0, -1) required_441), (placedSet 3 (-1, -1) required_63), (placedSet 6 (3, 1) required_64)]
def childrenD_529 : Fin 4 → Finset Cell := ![(placedSet 4 (-1, 0) envelope_55), (placedSet 0 (0, -1) envelope_441), (placedSet 3 (-1, -1) envelope_63), (placedSet 6 (3, 1) envelope_64)]
theorem common_sub_529 : commonEnvelope childrenD_529 ⊆ insert (0, 0) required_529 := by decide
theorem child_required_sub_529 : ∀ j, childrenC_529 j ⊆ insert (0, 0) required_529 := by decide
theorem child_envelope_sub_529 : ∀ j, childrenD_529 j ⊆ envelope_529 := by decide
theorem pivot_mem_529 : (0, 0) ∈ envelope_529 := by decide
theorem children_work_529 : ∀ j, Template HasSnaky 15 (childrenC_529 j) (childrenD_529 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_55 4 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_441 0 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_63 3 (-1, -1)).mono (by decide)
  · exact (placed_template_map row_works_64 6 (3, 1)).mono (by decide)
theorem row_works_529 : Template HasSnaky 16 required_529 envelope_529 := by
  refine compose HasSnaky 15 childrenC_529 childrenD_529 children_work_529 (0, 0)
    required_529 envelope_529 pivot_mem_529 child_required_sub_529 child_envelope_sub_529 ?_
  intro b hb; exact common_sub_529 (mem_commonEnvelope childrenD_529 b hb)
end SnakyConditional

end OAI
