import OAI.GameTheory.SnakyConditional.Templates.Level21Part01

namespace OAI

namespace SnakyConditional
def required_473 : Finset Cell := ⟨(([(-3, 0), (-2, 0), (-1, 0), (-1, 1), (0, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_473 : Finset Cell := ⟨(([(-6, 2), (-6, 4), (-5, 2), (-5, 3), (-5, 4), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-3, 0), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (1, -1), (1, 0), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, -1), (2, 0), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, 0), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 2), (4, 3), (4, 4), (5, 2), (5, 4)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_473 : Fin 3 → Finset Cell := ![(placedSet 5 (1, 0) required_121), (placedSet 0 (-1, 3) required_436), (placedSet 4 (1, 0) required_445)]
def childrenD_473 : Fin 3 → Finset Cell := ![(placedSet 5 (1, 0) envelope_121), (placedSet 0 (-1, 3) envelope_436), (placedSet 4 (1, 0) envelope_445)]
theorem common_sub_473 : commonEnvelope childrenD_473 ⊆ insert (0, 0) required_473 := by decide
theorem child_required_sub_473 : ∀ j, childrenC_473 j ⊆ insert (0, 0) required_473 := by decide
theorem child_envelope_sub_473 : ∀ j, childrenD_473 j ⊆ envelope_473 := by decide
theorem pivot_mem_473 : (0, 0) ∈ envelope_473 := by decide
theorem children_work_473 : ∀ j, Template HasSnaky 19 (childrenC_473 j) (childrenD_473 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_121 5 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_436 0 (-1, 3)).mono (by decide)
  · exact (placed_template_map row_works_445 4 (1, 0)).mono (by decide)
theorem row_works_473 : Template HasSnaky 20 required_473 envelope_473 := by
  refine compose HasSnaky 19 childrenC_473 childrenD_473 children_work_473 (0, 0)
    required_473 envelope_473 pivot_mem_473 child_required_sub_473 child_envelope_sub_473 ?_
  intro b hb; exact common_sub_473 (mem_commonEnvelope childrenD_473 b hb)
end SnakyConditional

end OAI
