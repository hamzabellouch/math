import OAI.GameTheory.SnakyConditional.Templates.Level17Part02

namespace OAI

namespace SnakyConditional
def required_534 : Finset Cell := ⟨(([(-2, -1), (-2, 0), (-2, 2), (-1, -1), (-1, 0), (-1, 2)] : List Cell) : Multiset Cell), by decide⟩
def envelope_534 : Finset Cell := ⟨(([(-5, 3), (-5, 5), (-4, -1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-3, -1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-2, -1), (-2, 0), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 3)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_534 : Fin 2 → Finset Cell := ![(placedSet 0 (0, 2) required_434), (placedSet 6 (-3, -1) required_12)]
def childrenD_534 : Fin 2 → Finset Cell := ![(placedSet 0 (0, 2) envelope_434), (placedSet 6 (-3, -1) envelope_12)]
theorem common_sub_534 : commonEnvelope childrenD_534 ⊆ insert (0, 0) required_534 := by decide
theorem child_required_sub_534 : ∀ j, childrenC_534 j ⊆ insert (0, 0) required_534 := by decide
theorem child_envelope_sub_534 : ∀ j, childrenD_534 j ⊆ envelope_534 := by decide
theorem pivot_mem_534 : (0, 0) ∈ envelope_534 := by decide
theorem children_work_534 : ∀ j, Template HasSnaky 15 (childrenC_534 j) (childrenD_534 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_434 0 (0, 2)).mono (by decide)
  · exact (placed_template_map row_works_12 6 (-3, -1)).mono (by decide)
theorem row_works_534 : Template HasSnaky 16 required_534 envelope_534 := by
  refine compose HasSnaky 15 childrenC_534 childrenD_534 children_work_534 (0, 0)
    required_534 envelope_534 pivot_mem_534 child_required_sub_534 child_envelope_sub_534 ?_
  intro b hb; exact common_sub_534 (mem_commonEnvelope childrenD_534 b hb)
end SnakyConditional

end OAI
