import OAI.GameTheory.SnakyConditional.Templates.Level22Part01

namespace OAI

namespace SnakyConditional
def required_467 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 3)] : List Cell) : Multiset Cell), by decide⟩
def envelope_467 : Finset Cell := ⟨(([(-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (8, 0), (8, 1), (8, 2), (9, 0), (9, 2)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_467 : Fin 3 → Finset Cell := ![(placedSet 7 (1, 3) required_64), (placedSet 6 (1, 0) required_314), (placedSet 1 (1, 3) required_443)]
def childrenD_467 : Fin 3 → Finset Cell := ![(placedSet 7 (1, 3) envelope_64), (placedSet 6 (1, 0) envelope_314), (placedSet 1 (1, 3) envelope_443)]
theorem common_sub_467 : commonEnvelope childrenD_467 ⊆ insert (0, 0) required_467 := by decide
theorem child_required_sub_467 : ∀ j, childrenC_467 j ⊆ insert (0, 0) required_467 := by decide
theorem child_envelope_sub_467 : ∀ j, childrenD_467 j ⊆ envelope_467 := by decide
theorem pivot_mem_467 : (0, 0) ∈ envelope_467 := by decide
theorem children_work_467 : ∀ j, Template HasSnaky 20 (childrenC_467 j) (childrenD_467 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_64 7 (1, 3)).mono (by decide)
  · exact (placed_template_map row_works_314 6 (1, 0)).mono (by decide)
  · exact (placed_template_map row_works_443 1 (1, 3)).mono (by decide)
theorem row_works_467 : Template HasSnaky 21 required_467 envelope_467 := by
  refine compose HasSnaky 20 childrenC_467 childrenD_467 children_work_467 (0, 0)
    required_467 envelope_467 pivot_mem_467 child_required_sub_467 child_envelope_sub_467 ?_
  intro b hb; exact common_sub_467 (mem_commonEnvelope childrenD_467 b hb)
def required_469 : Finset Cell := ⟨(([(0, 1), (0, 2), (0, 3)] : List Cell) : Multiset Cell), by decide⟩
def envelope_469 : Finset Cell := ⟨(([(-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 0), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (8, 0), (8, 1), (8, 2), (9, 0), (9, 2)] : List Cell) : Multiset Cell), by decide⟩
def childrenC_469 : Fin 3 → Finset Cell := ![(placedSet 5 (0, -1) required_55), (placedSet 1 (1, 3) required_443), (placedSet 6 (1, 0) required_314)]
def childrenD_469 : Fin 3 → Finset Cell := ![(placedSet 5 (0, -1) envelope_55), (placedSet 1 (1, 3) envelope_443), (placedSet 6 (1, 0) envelope_314)]
theorem common_sub_469 : commonEnvelope childrenD_469 ⊆ insert (0, 0) required_469 := by decide
theorem child_required_sub_469 : ∀ j, childrenC_469 j ⊆ insert (0, 0) required_469 := by decide
theorem child_envelope_sub_469 : ∀ j, childrenD_469 j ⊆ envelope_469 := by decide
theorem pivot_mem_469 : (0, 0) ∈ envelope_469 := by decide
theorem children_work_469 : ∀ j, Template HasSnaky 20 (childrenC_469 j) (childrenD_469 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_55 5 (0, -1)).mono (by decide)
  · exact (placed_template_map row_works_443 1 (1, 3)).mono (by decide)
  · exact (placed_template_map row_works_314 6 (1, 0)).mono (by decide)
theorem row_works_469 : Template HasSnaky 21 required_469 envelope_469 := by
  refine compose HasSnaky 20 childrenC_469 childrenD_469 children_work_469 (0, 0)
    required_469 envelope_469 pivot_mem_469 child_required_sub_469 child_envelope_sub_469 ?_
  intro b hb; exact common_sub_469 (mem_commonEnvelope childrenD_469 b hb)
end SnakyConditional

end OAI
