import OAI.GameTheory.SnakyConditional.Templates.Level16Part03

namespace OAI

namespace SnakyConditional
def required_441 : Finset Cell := ⟨(([(0, 1), (1, 1), (2, 1), (3, 1)] : List Cell) : Multiset Cell), by decide⟩
def envelope_441 : Finset Cell := ⟨(([(-2, 5), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 1), (1, 3), (1, 4), (1, 5), (1, 6), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (7, 2), (7, 3), (7, 4), (7, 5)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_441 : Fin 2 → Finset Cell := ![(placedSet 6 (-1, 0) required_6), (placedSet 0 (0, 2) required_435)]
def childrenD_441 : Fin 2 → Finset Cell := ![(placedSet 6 (-1, 0) envelope_6), (placedSet 0 (0, 2) envelope_435)]
theorem common_sub_441 : commonEnvelope childrenD_441 ⊆ insert (0, 0) required_441 := by decide
theorem child_required_sub_441 : ∀ j, childrenC_441 j ⊆ insert (0, 0) required_441 := by decide
theorem child_envelope_sub_441 : ∀ j, childrenD_441 j ⊆ envelope_441 := by decide
theorem pivot_mem_441 : (0, 0) ∈ envelope_441 := by decide
theorem children_work_441 : ∀ j, Template HasSnaky 14 (childrenC_441 j) (childrenD_441 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 6 (-1, 0)).mono (by decide)
  · exact (placed_template_map row_works_435 0 (0, 2)).mono (by decide)
theorem row_works_441 : Template HasSnaky 15 required_441 envelope_441 := by
  refine compose HasSnaky 14 childrenC_441 childrenD_441 children_work_441 (0, 0)
    required_441 envelope_441 pivot_mem_441 child_required_sub_441 child_envelope_sub_441 ?_
  intro b hb; exact common_sub_441 (mem_commonEnvelope childrenD_441 b hb)
def required_471 : Finset Cell := ⟨(([(-1, 0), (-1, 1), (-1, 2), (-1, 3)] : List Cell) : Multiset Cell), by decide⟩
def envelope_471 : Finset Cell := ⟨(([(-6, 1), (-6, 2), (-6, 3), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, 1), (-2, 2), (-2, 3), (-2, 5), (-2, 6), (-2, 7), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, -1), (0, 0), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, 1), (5, 2), (5, 3), (5, 4), (6, 1), (6, 2), (6, 3), (6, 4)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_471 : Fin 2 → Finset Cell := ![(placedSet 5 (0, -1) required_6), (placedSet 0 (1, 2) required_466)]
def childrenD_471 : Fin 2 → Finset Cell := ![(placedSet 5 (0, -1) envelope_6), (placedSet 0 (1, 2) envelope_466)]
theorem common_sub_471 : commonEnvelope childrenD_471 ⊆ insert (0, 0) required_471 := by decide
theorem child_required_sub_471 : ∀ j, childrenC_471 j ⊆ insert (0, 0) required_471 := by decide
theorem child_envelope_sub_471 : ∀ j, childrenD_471 j ⊆ envelope_471 := by decide
theorem pivot_mem_471 : (0, 0) ∈ envelope_471 := by decide
theorem children_work_471 : ∀ j, Template HasSnaky 14 (childrenC_471 j) (childrenD_471 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 5 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_466 0 (1, 2)).mono (by decide)
theorem row_works_471 : Template HasSnaky 15 required_471 envelope_471 := by
  refine compose HasSnaky 14 childrenC_471 childrenD_471 children_work_471 (0, 0)
    required_471 envelope_471 pivot_mem_471 child_required_sub_471 child_envelope_sub_471 ?_
  intro b hb; exact common_sub_471 (mem_commonEnvelope childrenD_471 b hb)
end SnakyConditional

end OAI
