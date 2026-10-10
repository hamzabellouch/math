import OAI.GameTheory.SnakyConditional.Templates.Level21Part01

namespace OAI

namespace SnakyConditional
def required_446 : Finset Cell := ⟨(([(-1, -1), (1, 0), (2, 0), (3, 0), (3, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_446 : Finset Cell := ⟨(([(-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (1, -1), (1, 0), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, 2), (7, 3), (7, 4), (8, 2), (8, 4)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_446 : Fin 2 → Finset Cell := ![(placedSet 6 (0, -1) required_4), (placedSet 0 (2, 1) required_438)]
def childrenD_446 : Fin 2 → Finset Cell := ![(placedSet 6 (0, -1) envelope_4), (placedSet 0 (2, 1) envelope_438)]
theorem common_sub_446 : commonEnvelope childrenD_446 ⊆ insert (0, 0) required_446 := by decide
theorem child_required_sub_446 : ∀ j, childrenC_446 j ⊆ insert (0, 0) required_446 := by decide
theorem child_envelope_sub_446 : ∀ j, childrenD_446 j ⊆ envelope_446 := by decide
theorem pivot_mem_446 : (0, 0) ∈ envelope_446 := by decide
theorem children_work_446 : ∀ j, Template HasSnaky 19 (childrenC_446 j) (childrenD_446 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_4 6 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_438 0 (2, 1)).mono (by decide)
theorem row_works_446 : Template HasSnaky 20 required_446 envelope_446 := by
  refine compose HasSnaky 19 childrenC_446 childrenD_446 children_work_446 (0, 0)
    required_446 envelope_446 pivot_mem_446 child_required_sub_446 child_envelope_sub_446 ?_
  intro b hb; exact common_sub_446 (mem_commonEnvelope childrenD_446 b hb)
end SnakyConditional

end OAI
