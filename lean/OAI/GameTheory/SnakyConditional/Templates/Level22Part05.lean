import OAI.GameTheory.SnakyConditional.Templates.Level21Part02

namespace OAI

namespace SnakyConditional
def required_463 : Finset Cell := ⟨(([(-2, -2), (-2, -1), (-1, -3), (-1, -1), (0, -1), (1, -1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_463 : Finset Cell := ⟨(([(-5, 1), (-5, 3), (-4, 1), (-4, 2), (-4, 3), (-3, -1), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-2, -2), (-2, -1), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-1, -3), (-1, -2), (-1, -1), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, -2), (2, -1), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (5, 0), (5, 1), (5, 3)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_463 : Fin 3 → Finset Cell := ![(placedSet 0 (2, -1) required_170), (placedSet 1 (-1, -2) required_76), (placedSet 0 (1, 0) required_447)]
def childrenD_463 : Fin 3 → Finset Cell := ![(placedSet 0 (2, -1) envelope_170), (placedSet 1 (-1, -2) envelope_76), (placedSet 0 (1, 0) envelope_447)]
theorem common_sub_463 : commonEnvelope childrenD_463 ⊆ insert (0, 0) required_463 := by decide
theorem child_required_sub_463 : ∀ j, childrenC_463 j ⊆ insert (0, 0) required_463 := by decide
theorem child_envelope_sub_463 : ∀ j, childrenD_463 j ⊆ envelope_463 := by decide
theorem pivot_mem_463 : (0, 0) ∈ envelope_463 := by decide
theorem children_work_463 : ∀ j, Template HasSnaky 19 (childrenC_463 j) (childrenD_463 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_170 0 (2, -1)).mono (by decide)
  · exact (placed_template_map row_works_76 1 (-1, -2)).mono (by decide)
  · exact (placed_template_map row_works_447 0 (1, 0)).mono (by decide)
theorem row_works_463 : Template HasSnaky 20 required_463 envelope_463 := by
  refine compose HasSnaky 19 childrenC_463 childrenD_463 children_work_463 (0, 0)
    required_463 envelope_463 pivot_mem_463 child_required_sub_463 child_envelope_sub_463 ?_
  intro b hb; exact common_sub_463 (mem_commonEnvelope childrenD_463 b hb)
end SnakyConditional

end OAI
